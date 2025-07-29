from typing import Literal
def default_deepseekprover1_5() -> dict:
    return {
        "model": "AI-MO/Kimina-Prover-Distill-8B",
        "custom_llm_provider": "vllm",
        "temperature": 0.6,
        "max_tokens": 8096,
        "n": 16,
        "top_p": 0.95,
        "caching": True,
    }