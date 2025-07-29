import re

def extract_proof_from_text(output: str) -> str:
    """
    Parse the proof from the model output for thinking models.
    Takes the last code inside ```lean4 and ``` that has the formal statement inside
    Args:
        output: The model output string.
    Returns:
        The parsed proof string.
    """
    lean4_codes = re.findall(r"```lean4\n(.*?)\n```", output, re.DOTALL)
    words = ["theorem", "by", ":=", "import"]

    for i in range(len(lean4_codes)):
        lean4_code = lean4_codes[-i - 1]
        if all(word in lean4_code for word in words):
            return lean4_code

    return "No proof found in the output."  # this will not pass verification


def extract_by_expression(lean_code: str) -> str:
    """
    Extracts everything after the first standalone `by` keyword from Lean code.
    """
    # Look for the first occurrence of "by" as a word on its own
    match = re.search(r'\bby\b', lean_code)
    if not match:
        return ''
    # Return everything after "by"
    return lean_code[match.end():]
