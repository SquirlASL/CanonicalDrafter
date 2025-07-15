from datasets import load_dataset

# Load the LeanDojo dataset
dataset = load_dataset("tasksource/leandojo", split="train")


# Step 1: Filter each row's traced_tactics to keep only those starting with "have "
def filter_have_tactics(row):
    if "traced_tactics" in row and isinstance(row["traced_tactics"], list):
        row["traced_tactics"] = [
            tac for tac in row["traced_tactics"]
            if isinstance(tac, dict) and "tactic" in tac and tac["tactic"].strip().startswith("have ")
        ]
    return row

filtered_dataset = dataset.map(filter_have_tactics)

# Step 2: Filter out rows where traced_tactics is empty
filtered_dataset = filtered_dataset.filter(lambda row: len(row["traced_tactics"]) > 0)

print(dataset)
print(filtered_dataset)