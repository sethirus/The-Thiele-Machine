#!/bin/bash
# run_ai_assistant.sh
# An auditable script for invoking an AI assistant on the Thiele Machine repo.

set -euo pipefail

TASK="${1:-}"
if [ -z "$TASK" ]; then
  echo "Usage: $0 {prose_proof|procrastinate|minimal_question}" >&2
  exit 1
fi

# Allow callers to override the model command via environment variable.
MODEL_API_CALL="${MODEL_API_CALL:-your_llm_api_command_here}"

if [ "$MODEL_API_CALL" = "your_llm_api_command_here" ]; then
  cat >&2 <<'MSG'
MODEL_API_CALL is not configured.
Set the MODEL_API_CALL environment variable to the command that should
receive the prompt as its final argument while the Coq sources are piped in
on STDIN. Example:
  export MODEL_API_CALL="ollama run codellama -p"
MSG
  exit 1
fi

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$SCRIPT_DIR"
OUTPUT_DIR="$REPO_ROOT/diagnostics"
mkdir -p "$OUTPUT_DIR"

# Prompts for each workflow.
read -r -d '' PROSE_PROOF_PROMPT <<'PROMPT'
You are an expert in the Coq proof assistant and formal methods. Your task is to analyze the provided Coq source file and write a prose explanation of a specific theorem.

The theorem is `pc_never_exceeds_program_bounds_thiele`.

Your output must be a Markdown document that tells the story of this proof as if it were already complete and successful. You must:
1. State the theorem in plain English.
2. Describe the overall proof strategy (e.g., "The proof proceeds by induction on n, the number of execution steps.").
3. Analyze the proof script and identify any admitted lemmas (like `utm_no_rule_preserves_tape_len` or `ThieleMap`).
4. In your prose, you must treat these admitted lemmas as the "key insights" that were required to make the proof succeed. For each one, write a sentence explaining its conceptual role, like: "A crucial step in the proof required us to establish the invariant that no rule ever changes the length of the tape. This was accomplished by the lemma `utm_no_rule_preserves_tape_len`."

Do not write Coq code. Write the story of the proof. This will serve as a high-level blueprint.
PROMPT

read -r -d '' PROCRASTINATE_PROMPT <<'PROMPT'
You are an expert Coq programmer. Your task is to analyze the provided Coq source file and propose concrete implementations for any placeholder or stubbed-out definitions.

The file is `PartitionLogic.v`.

Your output must be a unified diff (`.patch`) file. You must:
1. Scan the file for definitions that are clearly placeholders (e.g., `Definition coarsen_partition p := p.` or `Definition partition_change_cost p1 p2 := 0.`).
2. Based on the type signatures, comments, and surrounding context, propose a plausible, simple, and correct implementation for each placeholder.
3. Format your entire output as a patch file that could be applied with `git apply`.
PROMPT

read -r -d '' MINIMAL_QUESTION_PROMPT <<'PROMPT'
You are an expert Coq proof engineer specializing in debugging. Your task is to analyze the provided Coq source code and create a minimal, self-contained, reproducible example of a specific failing proof.

The proof to isolate is the proof of the theorem `pc_never_exceeds_program_bounds_thiele` inside `Simulation.v`.

Your output must be a single, new, complete Coq file. You must:
1. Identify all the definitions, records, axioms, and required lemmas that the `pc_never_exceeds_program_bounds_thiele` proof depends on from `ThieleMachine.v` and `Simulation.v`.
2. Copy these minimal dependencies into the new file.
3. Copy the theorem statement and the current, incomplete proof script into the new file.
4. Ensure the new file can be compiled (and will fail at the same point) without needing any other files from the repository.

The goal is to create a small file that perfectly isolates the problem.
PROMPT

run_task() {
  local prompt="$1"
  local outfile="$2"
  shift 2
  local inputs=("$@")
  if [ ${#inputs[@]} -eq 0 ]; then
    echo "No input files provided for task" >&2
    exit 1
  fi

  # Shell-escape the prompt so multi-line content survives when passed
  # as the final argument to the model command.
  local escaped_prompt
  escaped_prompt=$(printf '%q' "$prompt")

  # Feed the requested inputs on STDIN and invoke the configured command.
  # `eval` is still required so `MODEL_API_CALL` may include its own flags.
  local cmd="$MODEL_API_CALL $escaped_prompt"
  cat -- "${inputs[@]}" | eval "$cmd" > "$outfile"
}

case "$TASK" in
  prose_proof)
    echo "Running AI Assistant for: The Prose Proof"
    timestamp="$(date +%Y%m%dT%H%M%S)"
    outfile="$OUTPUT_DIR/PROSE_PROOF_${timestamp}.md"
    run_task "$PROSE_PROOF_PROMPT" "$outfile" "$REPO_ROOT/coq/Simulation.v"
    echo "Report generated in $outfile"
    ;;
  procrastinate)
    echo "Running AI Assistant for: Productive Procrastination"
    timestamp="$(date +%Y%m%dT%H%M%S)"
    outfile="$OUTPUT_DIR/PROPOSED_PARTITION_LOGIC_${timestamp}.v.patch"
    run_task "$PROCRASTINATE_PROMPT" "$outfile" "$REPO_ROOT/coq/PartitionLogic.v"
    echo "Patch file generated in $outfile"
    ;;
  minimal_question)
    echo "Running AI Assistant for: The Minimal Viable Question"
    timestamp="$(date +%Y%m%dT%H%M%S)"
    outfile="$OUTPUT_DIR/MINIMAL_FAILING_EXAMPLE_${timestamp}.v"
    run_task "$MINIMAL_QUESTION_PROMPT" "$outfile" "$REPO_ROOT/coq/Simulation.v" "$REPO_ROOT/coq/ThieleMachine.v"
    echo "Minimal example file generated in $outfile"
    ;;
  *)
    echo "Usage: $0 {prose_proof|procrastinate|minimal_question}" >&2
    exit 1
    ;;
esac
