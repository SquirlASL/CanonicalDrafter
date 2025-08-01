import json
import subprocess
from datasets import load_dataset, DatasetDict


# CONFIG
DATASET_NAME = "Kevew/minif2f-kiminaprover8b-inferenced"
PROOF_FIELD = "full"
HEADER_FIELD = "header"
OUTPUT_PATH = "with_have_drafts.json"



def extract_have_drafts(proof: str) -> list[str]:
    proof = f'--proof="{proof}"'
    cmd = [
        "lake", "env", "lean",
        "--run", "ExtractProof.lean", 
        proof
    ]
    print(proof)
    completed = subprocess.run(cmd, check=True, capture_output=True, text=True)
    out = completed.stdout
    out = out.strip()

    # expecting exactly one line like: haveDrafts = [ {...}, {...}, … ]
    prefix = "haveDrafts = "
    if not out.startswith(prefix):
        raise RuntimeError(f"Unexpected extractor output:\n{out!r}")
    
    array_json = out[len(prefix):]
    return json.loads(array_json)

def main():
    # load HF dataset
    ds = load_dataset(DATASET_NAME)

    if isinstance(ds, dict):
        ds = DatasetDict(ds)
    try:
        def processor(example):
            header = example[HEADER_FIELD]
            t_proof = example[PROOF_FIELD]
            if t_proof is None:
                example["haveDrafts"] = None
                return example
            proof = header + "\n\n" + t_proof
            try:
                example["haveDrafts"] = extract_have_drafts(proof)
            except subprocess.CalledProcessError as e:
                print(f"Failed to process a proof: {e.stderr}")
                example["haveDrafts"] = None
            return example
        
        for split in ds.keys():
            print(f"Processing split: {split}")
            ds[split] = ds[split].map(processor, num_proc=1)
    except KeyboardInterrupt:
        print("Keyboard lol")

    serialisable = {split: ds[split].to_dict()
                for split in ds.keys()}

    print(f"Saving augmented dataset to {OUTPUT_PATH}")
    with open(OUTPUT_PATH, "w") as out:
        json.dump(serialisable, out, indent=2)


if __name__ == "__main__":
    main()