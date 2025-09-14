from fastapi import FastAPI
from pydantic import BaseModel
from typing import List
from transformers import AutoTokenizer, AutoModelForSeq2SeqLM

# Preload model + tokenizer once (faster than reloading each request)
MODEL_NAME = "UnluckyOrangutan/byt5-tactic-haveDraft2"
tokenizer = AutoTokenizer.from_pretrained(MODEL_NAME)
model = AutoModelForSeq2SeqLM.from_pretrained(MODEL_NAME)

# FastAPI app
app = FastAPI(title="ByT5 Multiple Output Generator")

class GenerateRequest(BaseModel):
    input_text: str
    num_outputs: int = 1
    max_length: int = 4096

@app.post("/generate", response_model=List[str])
def generate(request: GenerateRequest):
    """
    Generate multiple outputs from the model.
    """
    inputs = tokenizer(request.input_text, return_tensors="pt")

    outputs = model.generate(
        **inputs,
        max_length=request.max_length,
        num_return_sequences=1,
        do_sample=True,
        top_k=50,
        top_p=0.95,
        temperature=0.9,
    )

    decoded = tokenizer.decode(outputs[0], skip_special_tokens=True)
    return decoded.split("\n", 1)
