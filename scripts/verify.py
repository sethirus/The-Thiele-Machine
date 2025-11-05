# scripts/verify.py — CI/local verification (non-interactive)
import json, subprocess, sys, pathlib, hashlib, tempfile, os

repo = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(repo))
sys.path.insert(0, str(repo / "scripts" / "experiments"))

from run_partition_experiments import run_tseitin_experiments
from scripts.audit_trace import audit_trace_file

logos = repo / "ouroboros" / "logos.py"
child = repo / "ouroboros" / "witness_in_potentia.py"
wjson = repo / "WITNESS.jsonl"

run_id = os.environ.get('GITHUB_RUN_ID', 'as-above-so-below')
attempt = os.environ.get('GITHUB_RUN_ATTEMPT', '')
anchor = f"ci:{run_id}"
if attempt:
    anchor += f":{attempt}"

out = subprocess.run([sys.executable, str(logos), "--anchor", anchor],
                     capture_output=True, text=True, check=True).stdout

assert "Thesis Verified by Self-Creation: True" in out, "Creator verdict not True"
assert "Universal Thesis Verified: True" in out, "Child verdict not True"
assert child.exists(), "Child script not materialised"
assert wjson.exists(), "WITNESS.jsonl not found"

last = list(open(wjson, encoding="utf-8"))[-1]
rec = json.loads(last)
assert rec["ok"] is True, "Final ok flag is False"
assert rec["isolated_exec"] is True, "Isolated exec flag missing"
assert rec["child_reported_hash"] == rec["written_hash"], "Hash mismatch"
assert rec["anchor"] == anchor, "Anchor mismatch"
expected_bind = hashlib.sha256((rec["written_hash"] + ":" + rec["anchor"]).encode()).hexdigest()
assert rec["anchor_binding"] == expected_bind, "Anchor binding mismatch"
assert rec["coq_compiled"] is True, "Coq compilation failed"
for k, v in rec["external_hashes"].items():
    if v is not None:
        assert v == rec["written_hash"], f"External {k} hash mismatch"

# Run a minimal Tseitin experiment and audit the resulting blind trace
with tempfile.TemporaryDirectory() as tmpdir:
    tmp_path = pathlib.Path(tmpdir)
    results = run_tseitin_experiments(
        partitions=[4],
        repeat=1,
        seed_grid=[0],
        emit_receipts=False,
        mispartition=False,
        shuffle_constraints=False,
        noise=None,
        budget_seconds=None,
        exp_dir=tmp_path,
    )

    assert results, "No experiment results returned"

    for result in results:
        trace_file = result.get("blind_trace_file")
        assert trace_file, "Trace file path missing"
        path = pathlib.Path(trace_file)
        if not path.is_absolute():
            path = tmp_path / path
        assert path.exists(), f"Trace file not found: {path}"
        audit_trace_file(path)

print("OK")
