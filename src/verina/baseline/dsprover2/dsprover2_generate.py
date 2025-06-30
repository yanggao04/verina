from typing import List, Type

import dspy
from dspy import (
    Module,
)

from verina.baseline.generate import (
    clean_output,
    proof_lean_content_from_input_output,
    proof_task_template_from_input,
)
from verina.benchmark.solution import (
    FewshotExample,
    GenProofInput,
    GenProofOutput,
)


def initial_parse(output: str) -> str:
    if "```lean" not in output:
        raise ValueError("There's not ```lean code block in the final output")
    text = output.split("```lean")[-1]
    if text[0] == "4":
        text = text[1:-1]
    if "```" not in text:
        raise ValueError("```lean4 and ``` delimeters not in pair")
    text = text.split("```")[0].strip()
    return text


def parsing_output(output: str, thm: str) -> GenProofOutput:
    output = initial_parse(output)
    if f"theorem {thm}" not in output:
        raise ValueError(f'theorem "{thm}" is not proven in the output')
    proof_aux = ""
    proof = ""
    imports = ""
    if "import Mathlib" not in output:
        imports = imports + "import Mathlib\n"
    if "import Aesop" not in output:
        imports = imports + "import Aesop\n"
    pf = False
    pfaux = False
    waiting = ""
    for line in output.splitlines():
        if line.strip() == "":
            continue
        if thm in line:
            pf = True
            pfaux = False
            proof = proof + "\n" + waiting + line + "\n"
            waiting = ""
        elif "theorem" in line or "def" in line:
            pfaux = True
            pf = False
            proof_aux = proof_aux + "\n" + waiting + line + "\n"
            waiting = ""
        elif "import" in line:
            imports = imports + line + "\n"
            pf = False
            pfaux = False
            waiting = ""
        elif pf:
            proof = proof + waiting + line + "\n"
        elif pfaux:
            proof_aux = proof_aux + waiting + line + "\n"
        elif "@[" in line:
            waiting = waiting + line + "\n"
        else:
            raise ValueError(
                f"Can not identify what output field does this belong to: {line}"
            )
    return GenProofOutput(
        imports=imports.strip(),
        proof_aux=proof_aux.strip(),
        proof=proof.strip(),
    )


async def dsprover2_generate_proof(
    dspy_module: Type[Module],
    input: GenProofInput,
    fewshot_examples: List[FewshotExample[GenProofInput, GenProofOutput]],
) -> GenProofOutput:
    task_template = proof_task_template_from_input(input)
    messages = []
    prompt = """
    Complete the following Lean 4 code:

    {}

    Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
    The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
    """.strip()
    for example in fewshot_examples:
        i = proof_task_template_from_input(example.example_input)
        o = proof_lean_content_from_input_output(
            example.example_input, example.example_output
        )
        messages.append({"role": "user", "content": prompt.format(i) + "\n\n" + o})
    content = prompt.format(task_template)
    messages.append({"role": "user", "content": content})
    generator = dspy.settings.lm
    output = await generator.acall(messages=messages)
    response = parsing_output(
        output=output[0], thm=input.signature.name + "_postcond_satisfied"
    )
    output = GenProofOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_output(response.proof, isImportsOrAux=False),
    )
    return output


async def dsprover2_generate_proof_with_refinement(
    dspy_module: Type[Module],
    input: GenProofInput,
    prev_output: GenProofOutput,
    prev_error: str,
) -> GenProofOutput:
    generator = dspy.settings.lm
    task_template = proof_task_template_from_input(input)
    prev_code = proof_lean_content_from_input_output(input, prev_output)
    prompt = f"""
    Complete the following Lean 4 code:

    {task_template}

    Given the following pseudo solution

    {prev_code}

    with the error: 

    {prev_error}

    Before producing the Lean 4 code to formally prove the given theorem, provide a detailed proof plan outlining the main proof steps and strategies.
    The plan should highlight key ideas, intermediate lemmas, and proof structures that will guide the construction of the final formal proof.
    """.strip()
    messages = [{"role": "user", "content": prompt}]
    output = await generator.acall(messages=messages)
    response = parsing_output(
        output=output[0], thm=input.signature.name + "_postcond_satisfied"
    )
    output = GenProofOutput(
        imports=clean_output(response.imports, isImportsOrAux=True),
        proof_aux=clean_output(response.proof_aux, isImportsOrAux=True),
        proof=clean_output(response.proof, isImportsOrAux=False),
    )
    return output
