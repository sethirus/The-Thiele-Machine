import json
import subprocess
import tempfile
from pathlib import Path
import hashlib


CERT = "c"
HASH = hashlib.sha256(CERT.encode()).hexdigest()


def make_receipt(mu):
    return {"steps": [{"idx": 0, "transition": "test", "mu_delta": mu, "step_hash": HASH, "solver": "test", "solver_cmdline": "test"}]}


def test_challenge_verify_accepts(tmp_path):
    d = tmp_path / "r"
    d.mkdir()
    with open(d / "ok.json", "w") as f:
        json.dump(make_receipt(1.0), f)
    r = subprocess.run(["python", "scripts/challenge.py", "verify", str(d)])
    assert r.returncode == 0


def test_challenge_refinement_violation(tmp_path):
    coarse = tmp_path / "coarse"
    refined = tmp_path / "refined"
    coarse.mkdir()
    refined.mkdir()
    with open(coarse / "c.json", "w") as f:
        json.dump(make_receipt(2.0), f)
    with open(refined / "r.json", "w") as f:
        json.dump(make_receipt(1.0), f)
    r = subprocess.run(["python", "scripts/challenge.py", "refinement", str(coarse), str(refined)])
    assert r.returncode != 0
