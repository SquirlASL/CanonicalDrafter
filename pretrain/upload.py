from huggingface_hub import HfApi, Repository

api = HfApi()
user = api.whoami()  # get your HF username
hf_username = user["name"]

repo_name = "byt5-lean-goals"
local_model_dir = "byt5-lean-goals"
repo_url = f"https://huggingface.co/{hf_username}/{repo_name}"

# Initialize a Repository object WITHOUT clone_from,
# assuming local_model_dir is already a git repo linked to HF
repo = Repository(local_model_dir)

# Push local contents to HF Hub
repo.push_to_hub(commit_message="Upload trained byt5-lean-goals model")

print(f"Model uploaded to https://huggingface.co/{hf_username}/{repo_name}")
