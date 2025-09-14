from transformers import AutoTokenizer, AutoModelForSeq2SeqLM

def generate_multiple_outputs(model_name: str, input_text: str, num_outputs: int = 1, max_length: int = 4096):
    """
    Generate multiple possible outputs from a ByT5 model for a given input.

    Args:
        model_name (str): Hugging Face model name, e.g. "google/byt5-small".
        input_text (str): Input text string.
        num_outputs (int): Number of different outputs to return.
        max_length (int): Maximum length of each generated output.

    Returns:
        list[str]: A list of generated strings.
    """
    # Load model + tokenizer
    tokenizer = AutoTokenizer.from_pretrained(model_name)
    model = AutoModelForSeq2SeqLM.from_pretrained(model_name)

    # Encode input
    inputs = tokenizer(input_text, return_tensors="pt")

    # Generate multiple outputs (sampling)
    outputs = model.generate(
        **inputs,
        max_length=max_length,
        num_return_sequences=num_outputs,
        do_sample=True,         # enables randomness
        top_k=50,               # restricts sampling pool to top-k tokens
        top_p=0.95,             # nucleus sampling
        temperature=0.9         # controls randomness (lower = more greedy)
    )

    # Decode to text
    return [tokenizer.decode(out, skip_special_tokens=True) for out in outputs]


# Example usage
if __name__ == "__main__":
    input = """
J : Type v
inst✝¹ : SmallCategory J
F : J ⥤ SemiRingCat
inst✝ : IsFiltered J
x : (↑(R F) : Type (max u v))
⊢ 0 * x = 0"""
    print("input:\n", input)
    print("\n--------")
    results = generate_multiple_outputs("UnluckyOrangutan/byt5-tactic-haveDraft2", input, num_outputs=20)
    for i, r in enumerate(results, 1):
        print(f"Output {i}: {r}")
