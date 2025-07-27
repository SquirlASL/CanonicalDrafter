import os
from datasets import load_dataset
from typing import Literal
from lean_interact.utils import clean_last_theorem_string

ROOT_DIR = os.path.dirname(os.path.abspath(__file__))

def load_minif2f_dataset(split: Literal["train", "validation", "test"] = "validation") -> list[dict]:
    """
    Loads the minif2f dataset from Harmonic AI (https://github.com/harmonic-ai/datasets/tree/main/minif2f).
    """
    json_file_link = f"https://raw.githubusercontent.com/harmonic-ai/datasets/main/minif2f/{split}.json"
    dataset = load_dataset("json", data_files=json_file_link, split="train")
    processed_dataset = []
    for item in dataset:
        header = "import Mathlib\nopen BigOperators Real Nat Topology\n"
        processed_dataset.append(
            {
                "id": item["id"],
                "header": header.strip(),
                "formal": clean_last_theorem_string(item["formal"]) + " :=",
                "natural": item["natural"],
                "nl_proof": None,
            },
        )
    return processed_dataset
