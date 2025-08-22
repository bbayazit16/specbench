import json
from dataclasses import dataclass
from enum import Enum
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parent
SPECBENCH_GSM_DATA_PATH = SCRIPT_DIR / 'specbench-gsm'


class GSMMode(str, Enum):
    P1 = 'p1'
    P2 = 'p2'
    SYMBOLIC = 'symbolic'


class VariableType(str, Enum):
    FLOAT = 'float'
    INT = 'int'
    STR = 'str'


@dataclass
class Question:
    question_symbolic: str
    variable_types: dict[str, VariableType]
    answer_expression: str
    constraints: list[str]
    private_constraints: list[str]
    question_id: str
    gsm_mode: GSMMode

    def prompt(self) -> str:
        parts = [self.question_symbolic.strip()]
        # Note: strip? Probably don't have to if JSON is formatted
        constraints = [
            constraint.strip() for constraint in self.constraints if constraint.strip()
        ]
        if constraints:
            parts.append('Additional constraints:\n' + '\n'.join(constraints))
        return '\n\n'.join(parts)


def retrieve_all_questions() -> list[Question]:
    return [q for mode in GSMMode for q in retrieve_questions_for(mode)]


def retrieve_questions_for(gsm_mode: GSMMode) -> list[Question]:
    jsons_dir = SPECBENCH_GSM_DATA_PATH / gsm_mode.value
    if not jsons_dir.is_dir():
        raise FileNotFoundError(f'Missing directory: {jsons_dir}')

    questions: list[Question] = []
    for path in sorted(jsons_dir.glob('*.json')):
        with path.open('r', encoding='utf-8') as f:
            data = json.load(f)

        q_text = data['question']
        types_raw: dict[str, str] = data['types']
        ans_expr = data['answer']
        constraints = data['constraints']
        private_constraints = data['private_constraints']

        # if constraints:
        #     print(constraints)

        var_types = {k: VariableType(v) for k, v in types_raw.items()}

        questions.append(
            Question(
                question_symbolic=q_text,
                variable_types=var_types,
                answer_expression=ans_expr,
                constraints=list(constraints),
                private_constraints=list(private_constraints),
                question_id=path.stem,
                gsm_mode=gsm_mode,
            )
        )

    return questions
