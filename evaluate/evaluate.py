import json
import multiprocessing as mp
import os
from collections import Counter
from datetime import datetime
from multiprocessing import Pool
import numpy as np
import pickle

import jsonlines
import litellm
from litellm import completion
from litellm.caching.caching import Cache, LiteLLMCacheType
from rich.console import Console
from rich.syntax import Syntax
from tqdm import tqdm
from vllm import LLM, SamplingParams

from lean_interact import (
    AutoLeanServer,
    Command,
    LeanREPLConfig,
    TempRequireProject,
)
from lean_interact.interface import LeanError
from lean_interact.utils import (
    remove_lean_comments,
)

from evaluate.config import default_deepseekprover1_5
from evaluate.dataset import load_minif2f_dataset
from evaluate.utils import extract_by_expression
from evaluate.utils import extract_proof_from_text

console = Console()
ROOT_DIR = os.path.dirname(os.path.abspath(__file__))
litellm.cache = Cache(type=LiteLLMCacheType.DISK, disk_cache_dir=os.path.join(ROOT_DIR, ".cache/litellm"))

os.environ["TOKENIZERS_PARALLELISM"] = "false"

def check_context_proofs(args: tuple[int, LeanREPLConfig, int, tuple[str, str, list[str]]]) -> tuple[int, str | None]:
    """
    Filter function to check if at least one proof is valid for a given context and declaration to prove.
    """
    idx, repl_config, timeout_per_proof, context_proofs = args
    context_code, formalization_code, proofs = context_proofs

    server = AutoLeanServer(repl_config)
    # using the cache accelerates the verification process by at least one order of magnitude
    # it also drastically reduces the memory usage
    context_res = server.run(Command(cmd=context_code), add_to_session_cache=True)
    assert not isinstance(context_res, LeanError)
    context_env = context_res.env

    for proof in proofs:
        try:
            lean_output = server.run(
                Command(cmd=formalization_code + proof, env=context_env), timeout=timeout_per_proof
            )
            if not isinstance(lean_output, LeanError) and lean_output.lean_code_is_valid(allow_sorry=False):
                return idx, proof
        except (TimeoutError, ConnectionAbortedError, json.JSONDecodeError):
            pass

    return idx, None


def check_proofs(
    context_proofs_list: list[tuple[str, str, list[str]]],
    repl_config: LeanREPLConfig,
    verbose: bool = False,
    nb_process: int | None = None,
    timeout: int = 120,
    timeout_per_proof: int = 60,
) -> list[str | None]:
    """Per context, check if at least one proof is valid.

    Args:
        context_proofs: List of (`context_code`, `formalization_code`, `proofs_list`) tuples. `formalization_code` must end by `:=`.
        verbose: Whether to print additional information during the verification process.
        nb_process: Number of processes to use for the verification. If None, the number of processes is set to the number of CPUs.
        timeout: Timeout in seconds per element in the list. Sometimes, even with timeout per proof, the verification process can get stuck on a single element.
            This parameter ensures that the verification process will finish in finite time.
        timeout_per_proof: Timeout in seconds per proof. This is used to avoid getting stuck on a single proof, but will not interrupt the overall verification process.
        lean_version: Version of Lean to use for the verification.
    """
    assert all([formalization_code.endswith(":=") for _, formalization_code, _ in context_proofs_list])

    # heuristic: sort the contexts by the total length of the proofs to better distribute the work among the processes
    idx_context_proofs = list(enumerate(context_proofs_list))
    idx_context_proofs = sorted(idx_context_proofs, key=lambda x: sum([len(proof) for proof in x[1][2]]), reverse=True)

    res: list[str | None] = [None for _ in context_proofs_list]
    with Pool(nb_process, maxtasksperchild=1) as p:
        iterator = p.imap_unordered(
            check_context_proofs,
            [(idx, repl_config, timeout_per_proof, context_proofs) for idx, context_proofs in idx_context_proofs],
            chunksize=1,
        )
        pbar = tqdm(total=len(context_proofs_list), desc="Checking proofs", disable=not verbose)
        for i, _ in enumerate(idx_context_proofs):
            try:
                idx, proofs_result = iterator.next(timeout)
                res[idx] = proofs_result
                pbar.update(1)
            except mp.TimeoutError:
                console.log(
                    f"Timeout during proof verification. {len(context_proofs_list) - i} elements from the list have been left unchecked."
                )
                p.terminate()
                p.join()
                break

    return res

def generate(prompts: list[str], gen_config: dict) -> list[list[str]]:
    """
    Generate proofs using litellm.

    Args:
        prompts: List of prompts to generate proofs for.
        gen_config: Generation parameters passed to litellm.

    Returns:
        List of lists of generated proofs, one list per prompt.
    """
    if gen_config["custom_llm_provider"] == "vllm":
        # Litellm vLLM local backend does not handle n > 1 generations properly,
        # so we fall back to calling vLLM directly
        sampling_params = SamplingParams(
            temperature=gen_config["temperature"],
            top_p=gen_config["top_p"],
            n=gen_config["n"],
            max_tokens=gen_config["max_tokens"],
        )
        system = "You are a Lean4 proof assistant."
        full_prompts = [f"{system}\n\n{p}" for p in prompts]

        llm = LLM(model=gen_config["model"], swap_space=24, max_num_seqs=96)
        batch_size = 4

        all_proofs = []

        for start in range(0, len(full_prompts), batch_size):
            batch_prompts = full_prompts[start : start + batch_size]
            print(f"Generating raw vLLM outputs for prompts {start}–{start + len(batch_prompts)-1}")
            raw_batch = llm.generate(batch_prompts, sampling_params, use_tqdm=True)
            os.makedirs(os.path.join(ROOT_DIR, "results"), exist_ok=True)
            dump_path = os.path.join(
                ROOT_DIR, "results", f"raw_vllm_outputs_{start:05d}.pkl"
            )
            with open(dump_path, "wb") as f:
                pickle.dump(raw_batch, f)
            print(f"Saved raw vLLM outputs for prompts {start}–{start + len(batch_prompts)-1} to {dump_path}")

            proofs_batch = [
                [extract_proof_from_text(o.text) for o in output.outputs]
                for output in raw_batch
            ]
            all_proofs.extend(proofs_batch)

        return all_proofs
        '''
        llm = LLM(model=gen_config["model"], quantization="fp8", swap_space=24, max_num_seqs=96)
        raw_generated_outputs = llm.generate(full_prompts, sampling_params, use_tqdm=True)
        return [[extract_proof_from_text(o.text) for o in output.outputs] for output in raw_generated_outputs]  # type: ignore
        '''

    else:
        all_proofs = []
        for prompt in tqdm(prompts, desc=f"Generating proofs with {gen_config['model']}"):
            try:
                response = completion(messages=[{"role": "system", "content": "You are an expert in mathematics and Lean 4."},
                {"role": "user", "content": prompt}], **gen_config)
                print(response)
                all_proofs.append([extract_proof_from_text(choice.message.content) for choice in response.choices])  # type: ignore
            except Exception as e:
                console.log(f"Error during generation: {e}")
                all_proofs.append([])
        return all_proofs



def run_proof_generation_pipeline(
    split: str,
    use_nl_proof_hint: bool,
    gen_config: dict,
    lean_version: str,
    verbose: bool = True,
    skip_interactive: bool = False,
):
    """
    Run the complete proof generation and checking pipeline.

    Args:
        split: Split of the dataset.
        use_nl_proof_hint: Whether to use natural language proof to guide proof generation. This task is also known as "proof autoformalization".
        model: Model to use for generation.
        nb_proof_attempts: Number of proof attempts to generate per theorem.
        lean_version: Version of Lean to use.
        verbose: Whether to print additional information.
    """
    model = gen_config["model"]
    console.print(f"[bold]Preparing minif2f dataset ({split} split)[/bold]")
    dataset = load_minif2f_dataset(split)
    console.print(f"Loaded {len(dataset)} theorems")

    prompts = []
    theorem_ids = []
    for i, theorem_data in enumerate(dataset):
        prompt = "Think about and solve the following problem step by step in Lean 4."
        if use_nl_proof_hint and theorem_data["nl_proof"] is not None:
            prompt += f"\n# Problem:{theorem_data['nl_proof']}"""
        prompt += (f"\n# Formal statement:\n```lean4\n{theorem_data['formal']}\n```\n")
        prompts.append(prompt)
        theorem_ids.append(i)

    console.print(f"Created {len(prompts)} prompts")

    outputs = generate(prompts, gen_config)

    context_proofs_list = []
    for output, theorem_id in zip(outputs, theorem_ids):
        theorem_data = dataset[theorem_id]

        # Format generated proofs
        proofs = [remove_lean_comments(proof) for proof in output]  # removing comments as they sometimes cause issues
        proofs = ["by\n" + extract_by_expression(proof) for proof in proofs]

        # Sort the proofs by their frequency and length while keeping only unique proofs
        proofs = sorted(proofs, key=len)
        proofs_freq = Counter(proofs)
        proofs = list(proofs_freq.keys())

        context_proofs_list.append((theorem_data["header"], theorem_data["formal"], proofs))

    console.print(f"[bold]Checking proofs using Lean {lean_version}[/bold]")
    repl_config = LeanREPLConfig(project=TempRequireProject(lean_version=lean_version, require="mathlib"))
    proof_results = check_proofs(context_proofs_list, repl_config, verbose=verbose)

    results = {}
    for theorem_id, proof, (_, _, proof_attempts) in zip(theorem_ids, proof_results, context_proofs_list):
        results[theorem_id] = {
            "id": theorem_id,
            "header": dataset[theorem_id]["header"],
            "formal": dataset[theorem_id]["formal"],
            "proof": proof,
            "success": proof is not None
        }

    os.makedirs(os.path.join(ROOT_DIR, "results"), exist_ok=True)
    temp = str(gen_config["temperature"])
    result_file = os.path.join(
        ROOT_DIR,
        "results",
        f"minif2f_{split}_temp_{temp}.jsonl",
    )
    with jsonlines.open(result_file, "w") as writer:
        for theorem_id, result in results.items():
            writer.write(result)

    nb_theorems = len(results)
    nb_proven = sum(1 for result in results.values() if result["success"])
    console.print()
    console.rule("[bold]Results Summary[/bold]")
    console.print(f"Dataset: [bold]minif2f ({split})[/bold]")
    console.print(f"Model: [bold]{model}[/bold]")
    console.print(f"Proven theorems: {nb_proven}/{nb_theorems} ({nb_proven / nb_theorems:.2%})")
    console.print(f"Results saved to: {result_file}")

    # Sanity
    if not skip_interactive:
        console.print()
        console.rule("[bold]Successful generated proofs[/bold]")
        for theorem_id, result in results.items():
            if result["success"]:
                console.print(f"[bold]Theorem {theorem_id}[/bold]")
                console.print(Syntax(result["header"] + "\n" + result["formal"] + " " + result["proof"], "lean4"))
                if input("Continue? (y/n)") == "n":
                    break
    return {
        "nb_proven": nb_proven,
        "nb_theorems": nb_theorems,
        "success_rate": nb_proven / nb_theorems,
        "result_file": result_file,
    }


if __name__ == "__main__":
    temps = np.linspace(0.6, 0.6, 1)
    freqs = np.linspace(0.2, 0.2, 1) 

    all_stats: list[dict] = []
    for temperature in temps:
        for frequency_penalty in freqs:
            config = default_deepseekprover1_5()
            config["temperature"] = float(temperature)

            stats = run_proof_generation_pipeline(
                split="validation",
                use_nl_proof_hint=False,
                gen_config=config,
                lean_version="v4.19.0",
                verbose=False,   
                skip_interactive=True, 
            )

            stats.update({
                "temperature": float(temperature),
                "frequency_penalty": float(frequency_penalty),
            })
            all_stats.append(stats)

            summary_path = os.path.join(ROOT_DIR, "results", "hyperparam_sweep_summary.json")
            with open(summary_path, "w") as f:
                json.dump(all_stats, f, indent=2)

    print(f"Saved hyperparam sweep summary to {summary_path}")