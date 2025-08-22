import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
import concurrent.futures

from llm import SYSTEM_PROMPT_COQ, call_llm
from models import LLM, DefaultLLM


@dataclass
class CoqFile:
    filepath: Path
    full_content: str
    prompt: str | None = None
    imports: str | None = None
    context: str | None = None
    problem_spec: str | None = None
    generated_spec: str | None = None
    equivalence: str | None = None

    @classmethod
    def from_file(cls, filepath: Path) -> 'CoqFile':
        content = filepath.read_text()

        def extract_section(section_name: str) -> str | None:
            pattern = (
                rf'\(\* start {section_name} \*\)(.*?)\(\* end {section_name} \*\)'
            )
            match = re.search(pattern, content, re.DOTALL)
            return match.group(1).strip() if match else None

        return cls(
            filepath=filepath,
            full_content=content,
            prompt=extract_section('prompt'),
            imports=extract_section('imports'),
            context=extract_section('context'),
            problem_spec=extract_section('problem_spec'),
            generated_spec=extract_section('generated_spec'),
            equivalence=extract_section('equivalence'),
        )

    def llm_prompt(self) -> str:
        if not self.prompt:
            return ''

        prompt_content = self.prompt.strip()

        # Remove comment markers and clean up
        lines = []
        for line in prompt_content.split('\n'):
            line = line.strip()
            if line.startswith('(*') or line.startswith('*)'):
                continue
            if line.startswith('*'):
                line = line[1:].strip()
            lines.append(line)

        prompt_text = '\n'.join(lines).strip()

        # Parse the YAML-like content
        signature = ''
        description = ''
        examples = []
        current_section = None

        for line in prompt_text.split('\n'):
            line = line.strip()
            if line.startswith('signature:'):
                signature = line.replace('signature:', '').strip().strip('"')
                current_section = 'signature'
            elif line.startswith('description:'):
                description = line.replace('description:', '').strip()
                current_section = 'description'
            elif line.startswith('examples:'):
                current_section = 'examples'
            elif line.startswith('- input:'):
                input_part = line.replace('- input:', '').strip()
                examples.append(f'- Input: {input_part}')
            elif line.startswith('output:'):
                output_part = line.replace('output:', '').strip()
                if examples:
                    examples[-1] += f' -> Output: {output_part}'
            elif current_section == 'signature' and line and not line.startswith(('-', 'description:', 'examples:')):
                signature += ' ' + line
            elif current_section == 'description' and line and not line.startswith(('-', 'signature:', 'examples:')):
                description += ' ' + line

        formatted_prompt = f'Signature:\n{signature}\n\nDescription:\n{description}'

        if examples:
            formatted_prompt += '\n\nExamples:'
            for example in examples:
                formatted_prompt += f'\n{example}'

        context_part = ''
        if self.context:
            context_part = f'\n\nGiven types and definitions:\n{self.context}'

        imports_part = ''
        if self.imports:
            imports_part = f'\n\nImports available:\n{self.imports}'

        return f'{formatted_prompt}{imports_part}{context_part}'

    def substitute_generated_spec(self, new_spec: str) -> str:
        pattern = r'\(\* start generated_spec \*\).*?\(\* end generated_spec \*\)'
        replacement = (
            f'(* start generated_spec *)\n{new_spec}\n(* end generated_spec *)'
        )

        return re.sub(pattern, replacement, self.full_content, flags=re.DOTALL)

    def update_hammer_settings(self, atp_limit: int, reconstr_limit: int) -> str:
        content = self.full_content

        if 'Set Hammer ATPLimit' in content:
            content = re.sub(
                r'Set Hammer ATPLimit \d+\.',
                f'Set Hammer ATPLimit {atp_limit}.',
                content,
            )
        else:
            # Add after From Hammer line
            content = re.sub(
                r'(From Hammer Require Import Hammer\.)',
                f'\\1\n\nSet Hammer ATPLimit {atp_limit}.',
                content,
            )

        if 'Set Hammer ReconstrLimit' in content:
            content = re.sub(
                r'Set Hammer ReconstrLimit \d+\.',
                f'Set Hammer ReconstrLimit {reconstr_limit}.',
                content,
            )
        else:
            content = re.sub(
                r'(Set Hammer ATPLimit \d+\.)',
                f'\\1\nSet Hammer ReconstrLimit {reconstr_limit}.',
                content,
            )

        return content


def call_llm_logged(file_id: str, prompt: str, model: LLM) -> str:
    p = Path('logs-coq') / model.display_name()
    p.mkdir(exist_ok=True, parents=True)

    look_for = (p / file_id).with_suffix('.log')
    if look_for.exists():
        return look_for.read_text().strip()
    else:
        result = call_llm(SYSTEM_PROMPT_COQ, prompt, model, 10_000, 0.0)
        with open(look_for, 'w+') as f:
            f.write(result)
        return result


def compile_coq_file(filepath: Path) -> tuple[bool, str]:
    try:
        result = subprocess.run(
            ['coqc', filepath.name],
            capture_output=True,
            text=True,
            timeout=30,
            cwd=filepath.parent,
        )
        # TODO: better handle ATP only success
        # should we consider this a timeout? an external setting?
        out = result.stdout + result.stderr
        atp_only_success = 'Hammer failed: proof reconstruction failed.' in out
        success = (result.returncode == 0) or atp_only_success
        return success, result.stdout + result.stderr
    except subprocess.TimeoutExpired as e:
        partial_output = ''
        if e.stdout:
            partial_output += f'STDOUT:\n{e.stdout.decode() if isinstance(e.stdout, bytes) else e.stdout}\n'
        if e.stderr:
            partial_output += f'STDERR:\n{e.stderr.decode() if isinstance(e.stderr, bytes) else e.stderr}\n'
        atp_only_success = 'Hammer failed: proof reconstruction failed.' in partial_output
        return atp_only_success, f'Compilation timeout\n{partial_output}'
    except FileNotFoundError:
        return False, 'FileNotFoundErr - coqc not found'
    except Exception as e:
        atp_only_success = 'Hammer failed: proof reconstruction failed.' in partial_output
        return atp_only_success, f'Compilation error: {e}'


def benchmark_coq_file(coq_file: CoqFile, model: LLM) -> bool:
    file_id = coq_file.filepath.stem
    print(f'Processing {file_id}')

    prompt = coq_file.llm_prompt()
    llm_response = call_llm_logged(file_id, prompt, model)

    modified_content = coq_file.substitute_generated_spec(llm_response)

    coq_file_with_updated_content = CoqFile(
        filepath=coq_file.filepath,
        full_content=modified_content,
        prompt=coq_file.prompt,
        imports=coq_file.imports,
        context=coq_file.context,
        problem_spec=coq_file.problem_spec,
        generated_spec=coq_file.generated_spec,
        equivalence=coq_file.equivalence,
    )
    modified_content = coq_file_with_updated_content.update_hammer_settings(
        HAMMER_ATP_LIMIT, HAMMER_RECONSTR_LIMIT
    )

    temp_dir = Path('temp')
    temp_dir.mkdir(exist_ok=True)

    temp_file = temp_dir / coq_file.filepath.name
    temp_file.write_text(modified_content)

    success, output = compile_coq_file(temp_file)

    print(f'Compilation result for {file_id}: {success}')
    if output.strip():
        print(f'Compiler output:\n{output}')
    print('-' * 50)

    return success


PARALLEL = False
MAX_WORKERS = 4
HAMMER_ATP_LIMIT = 8
HAMMER_RECONSTR_LIMIT = 8

# GPT-5: 11/12
# GPT-5-mini: 11/12
# GPT-5-nano: 9/12
# qwen/qwen3-30b-a3b-instruct-2507: 7/12
# llm = DefaultLLM('qwen/qwen3-30b-a3b-instruct-2507')
llm = DefaultLLM('google/gemma-3-4b-it')


def main():
    coq_dir = Path('coq-specs')

    if not coq_dir.exists():
        print('Directory not found')
        return

    coq_files = list(coq_dir.glob('*.v'))
    if not coq_files:
        print(f'No .v files in {coq_dir}')
        return

    print(f'Found {len(coq_files)} Coq files')

    parsed_files = []
    for filepath in coq_files:
        try:
            coq_file = CoqFile.from_file(filepath)
            # if coq_file.filepath.stem != 'hard3':
            #     continue
            parsed_files.append(coq_file)
        except Exception as e:
            print(f'Error parsing {filepath}: {e}')

    print(f'Parsed {len(parsed_files)} files')

    def process_single_file(coq_file):
        try:
            return benchmark_coq_file(coq_file, llm)
        except Exception as e:
            print(f'Error processing {coq_file.filepath}: {e}')
            return False

    if PARALLEL:
        with concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
            results = list(executor.map(process_single_file, parsed_files))
    else:
        results = [process_single_file(coq_file) for coq_file in parsed_files]

    total = len(results)
    successful = sum(results)
    print(f'\nSummary: {successful}/{total} files processed successfully')

    Path('temp')

if __name__ == '__main__':
    main()
