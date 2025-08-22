import ast
import concurrent.futures
from collections import defaultdict
from pathlib import Path

import z3

from llm import SYSTEM_PROMPT_GSM, call_llm
from models import LLM, DefaultLLM
from question import GSMMode, Question, VariableType, retrieve_all_questions
from z3_parsing import (
    parse_private_constraint,
    parse_public_constraint,
    z3_parse,
    z3_var_from,
)


TIMEOUT_MS = 5000

def call_llm_logged(mode: GSMMode, file_id: str, prompt: str, model: LLM) -> str:
    p = Path('logs') / model.display_name() / mode.value
    # Path('logs').mkdir(exist_ok=True)
    # Path('logs').mkdir(exist_ok=True, parents=True)
    p.mkdir(exist_ok=True, parents=True)

    print('finding')

    look_for = (p / file_id).with_suffix('.log')
    print(look_for)
    if look_for.exists():
        print('resulted')
        return look_for.read_text().strip()
    else:
        print('calling')
        result = call_llm(SYSTEM_PROMPT_GSM, prompt, model, 10_000, 0.0)
        with open(look_for, 'w+') as f:
            f.write(result)
        return result


def solve(question: Question, generated_response: str, ctx: z3.Context) -> bool:
    if generated_response == '':
        return False

    # if question.gsm_mode != GSMMode.P1 or question.question_id != '0008':
    #     return False

    solver = z3.Solver(ctx=ctx)
    z3_vars = {}
    for var_name, var_type in question.variable_types.items():
        z3_var = z3_var_from(name=var_name, orig_type=var_type, ctx=ctx)
        z3_vars[var_name] = z3_var

        if var_type in (VariableType.INT, VariableType.FLOAT):
            solver.add(z3_var > 0)

    for public_constraint in question.constraints:
        # TODO: Replace the hack (the entire code snippet below)
        # annotation vs 'parse-able' indicator in JSON AND the direct == check
        if (
            'in' in public_constraint.split(' ') or '=' in public_constraint
        ) and 'alphabets' not in public_constraint:
            if (
                public_constraint
                != "unit2 = 'meters' if unit1 == 'meters' else 'yards'"
            ):
                constraint = parse_public_constraint(public_constraint, question, ctx)
                if constraint is not None:
                    solver.add(constraint)
            else:
                unit1_var = z3_var_from('unit1', VariableType.STR, ctx)
                unit2_var = z3_var_from('unit2', VariableType.STR, ctx)
                constraint = unit2_var == z3.If(
                    unit1_var == z3.StringVal('meters', ctx),
                    z3.StringVal('meters', ctx),
                    z3.StringVal('yards', ctx),
                )
                solver.add(constraint)
        ############# (end replacement)

    for private_constraint in question.private_constraints:
        constraint = parse_private_constraint(private_constraint, question, ctx)
        if constraint is not None:
            solver.add(constraint)

    answer_tree = ast.parse(question.answer_expression)
    assert len(answer_tree.body) == 1, 'Unhandled module len > 1'
    base_answer = z3_parse(answer_tree.body[0], question, ctx)

    try:
        generated_tree = ast.parse(generated_response)
    except Exception as e:
        print('=====')
        print(f'WARNING main parsing for {generated_response}: {e}')
        print('=====')
        return False

    # assert len(generated_tree.body) == 1, 'Unhandled module len > 1'
    try:
        symbolic_generated_response = z3_parse(generated_tree.body[0], question, ctx)
    except Exception as e:
        print('=====')
        print('WARNING in model response parsing:', e)
        print('Question mode + id:', question.gsm_mode, question.question_id)
        print('Model generated:', generated_response)
        print('=====')
        return False

    solver.push()

    try:
        solver.set('timeout', TIMEOUT_MS)
        solver.add(base_answer != symbolic_generated_response)
        success = solver.check() == z3.unsat
    except Exception as e:
        print('=====')
        print('Error checking generated response:', e)
        print('Question:', question.question_symbolic, question.question_id)
        print('Question mode + id:', question.gsm_mode, question.question_id)
        print('Model generated:', generated_response)
        print('=====')
        success = False
    if success:
        print('Ok')
    if not success:
        print(
            f'Question: {question.gsm_mode}/{question.question_id} Counterexample for {generated_response}'
        )
        try:
            print(solver.model())
        except z3.Z3Exception:
            print('Model not available')
        print('\n')
    # if (
    #     question.answer.strip()
    #     == 'price - (price * (fee1_percent + fee2_percent) / 100 + loan)'
    # ):
    #     print('counterexample:', solver.model())
    #     print('z3 generated:', generated_response)
    #     print('z3 answer:', base_answer)
    return success


def process_question(question: Question, ctx: z3.Context, llm: LLM) -> bool:
    llm_response = call_llm_logged(
        question.gsm_mode, question.question_id, question.prompt(), llm
    )
    print('Solving:', question.gsm_mode, question.question_id)
    return solve(question, llm_response, ctx)


def main():
    questions = retrieve_all_questions()
    questions = [q for q in questions]

    # llm = DefaultLLM('openai/gpt-5-mini')
    # llm = DefaultLLM('google/gemma-2-9b-it')
    # llm = DefaultLLM('openai/gpt-5')
    # llm = DefaultLLM('openai/gpt-5-nano')
    # llm = DefaultLLM('qwen/qwen3-30b-a3b-instruct-2507')
    llm = DefaultLLM('google/gemma-3-4b-it')


    def process_question_with_context(question: Question):
        ctx = z3.Context()
        return process_question(question, ctx, llm)

    # with concurrent.futures.ThreadPoolExecutor(max_workers=15) as executor:
    #     results = list(executor.map(process_question_with_context, questions))
    results = [process_question_with_context(question) for question in questions]

    stats = defaultdict(
        lambda: {'total': 0, 'correct': 0, 'correct_q': [], 'incorrect_q': []}
    )

    for q, res in zip(questions, results, strict=True):
        s = stats[q.gsm_mode]
        s['total'] += 1
        if res:
            s['correct'] += 1
            s['correct_q'].append(q)
        else:
            s['incorrect_q'].append(q)

    for mode, s in stats.items():
        acc = s['correct'] / s['total'] if s['total'] > 0 else 0
        print(f'{mode}: {acc:.2%} ({s["correct"]} / {s["total"]})')

    total = len(results)
    correct = sum(s['correct'] for s in stats.values())
    print(f'Overall Accuracy: {correct / total:.2%} ({correct} / {total})')

    # print("===")
    # for mode, s in stats.items():
    #     print(f"Incorrect questions for mode {mode}:")
    #     for q in s['incorrect_q']:
    #         print(q)
    #     print("===")


if __name__ == '__main__':
    main()
