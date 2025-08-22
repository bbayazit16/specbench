import os
import re
import sys
import time

from dotenv import load_dotenv
from openai import OpenAI, RateLimitError

from models import LLM


# Note about the prompt: Defined vs Qed doesn't matter; since it'll only be given the
# file up until that point, and nothing else can depend on it. The file should compile
# nonetheless.
def is_before_8_11(version_str):
    major, minor, *_ = map(int, version_str.split('.'))
    return (major, minor) < (8, 11)


# SYSTEM_PROMPT = """\
# You are given grade school-level math questions. Variables are enclosed in backticks (e.g., `x`).

# Carefully analyze each question and solve it step by step.
# Your final answer must be a valid Python expression that, when evaluated, produces the correct result. Keep your
# Python expression simple, that is, do not define any functions, nor import anything. Limit your answers to primarily
# operators and syntax such as *, /, //, int(), -, +, etc. Do note that you may inline if / else expressions, but
# you are not allowed to use them as statements (meaning, you may not use : in statements such as if expressions - all must be inlined, if any is used).

# Be strict about the use of / and //. For anything that is an integer, use // if possible.

# Wrap your final answer in triple backticks (and finish the backticks). Only the last boxed expression will be considered as your final answer,
# although you may include other explanatory text or your thought process.

# Additionally, NEVER output any other Latex INSIDE triple backticks. This means that you SHOULD NOT include things such as \\text{...}, etc.
# Simply output a mathematical expression only.
# """.strip()
SYSTEM_PROMPT_GSM = """\
You are given grade school-level math word problems. Variables are enclosed in backticks (e.g., `x`) and correspond to Python identifiers.

Your task:
1. Carefully read and understand the problem.
2. Solve it step by step.
3. Produce a single valid Python expression that evaluates to the correct result.

Restrictions:
- Allowed elements: literals, parentheses, +, -, *, /, //, **, and inline conditional expressions (a if cond else b). Notice that you are not allowed to use the modulo (%) operator.
- You may NOT use assignments, imports, function definitions, comprehensions, loops, print, int(), round(), or any other functions or libraries.
- Use only the variables provided in the problem. Do not introduce new variable names. Do not change existing variable names.
- Add parentheses to make operator precedence explicit.
- Keep the expression as simple and direct as possible.
- Never use equality or assignment operators (e.g., DO NOT use answer = ..., or total = ...).

Output format:
- Your final answer must be in a single code block fenced with triple backticks.
- The fenced block must contain only the Python expression - no extra text.
- Do not include any LaTeX or explanations inside the fenced block.
- If you include explanations, place them before the final code block.
- Only the last fenced block will be considered as your answer.
""".strip()

SYSTEM_PROMPT_COQ = """\
You are an expert Coq proof assistant working with Coq 8.20. Your task is to generate formal specifications in Coq.

Your task:
1. Carefully read and understand the problem description, signature, imports (if any), and examples provided.
2. Generate a valid Coq definition that matches the given signature exactly.
3. The definition should capture the behavior described in the natural language specification.

Requirements:
- Your output must be a valid Coq definition that starts with "Definition" and ends with a period.
- Use only the signature provided - do not modify parameter names, types, or order.
- The definition must be syntactically correct Coq code.
- Use standard Coq constructs: match expressions, if-then-else, boolean operations (andb, orb, negb), etc.
- Follow the examples provided to understand the expected behavior.
- Do not include any explanations, comments, or additional text.
- Do not use any tactics or proofs, only definitions.
- Do not add additional imports or notations, apart from the ones provided.
- Remember: Your task is to generate a specification, not a proof.

Output format:
- Your final answer must be Coq code fenced with triple backticks.
- The fenced block must contain only the Coq expression - no extra text.
- If you include explanations, place them before the final code block.
- Only the last fenced block will be considered as your answer.
- Start with "Definition" and end with a period.
- Ensure proper Coq syntax and indentation.
""".strip()

load_dotenv(override=True)
for arg in {'OPENAI_BASE_URL', 'OPENAI_API_KEY'}:
    if arg not in os.environ:
        print(f'Missing env variable: {arg}')
        if arg == 'OPENAI_BASE_URL':
            print(
                'Did you mean to use `https://api.openai.com/v1/` (or your Azure endpoint)?'
            )
        sys.exit(1)


client = OpenAI(
    # base_url='http://localhost:11434/v1',
    # api_key='ollama'
    api_key=os.environ['OPENAI_API_KEY'],
    base_url=os.environ['OPENAI_BASE_URL'],
    default_query={'api-version': 'preview'},
)


def call_llm(
    system_prompt: str,
    prompt: str,
    model: LLM,
    max_tokens: int,
    temperature: float,
    debug_info: str = '',
) -> str:
    """
    Return the LLM response.

    To change the generation logic, all you have to do is pass a
    different LLM (see models.py) and modify the logic here if needed.

    The temperature is ignored for reasoning models that do not support the setting.
    `max_tokens` are replaced with `max_completion_tokens` for reasoning models.
    See `models.py`.
    """
    request_params = model.get_request_params(
        temperature, max_tokens, system_prompt, prompt
    )

    wait_time = 10
    while True:
        try:
            print('actually calling')
            response = client.chat.completions.create(**request_params)
            print('Response:',response)
            content = response.choices[0].message.content
            if not content:
                raise ValueError(f'Model returned empty content: {response}')
            return normalized(content)
        except RateLimitError:
            time.sleep(wait_time)
            wait_time = int(wait_time * 1.5)
            if wait_time > 35:
                wait_time = 35
        except Exception as e:
            if debug_info:
                print('call_llm debug for', debug_info)
            print(e)
            continue


def normalized(llm_result: str) -> str:
    """
    Extract the code from triple backticks, ignoring optional language identifiers.
    """
    matches = re.findall(r'```(?:\w+)?\n([\s\S]*?)```', llm_result)
    if matches:
        return matches[-1].strip()
    return llm_result.strip()
