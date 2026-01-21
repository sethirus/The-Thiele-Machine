def test_check_requirements_runs():
    # Ensure the requirements check runs successfully
    import subprocess
    p = subprocess.run(["python3", "scripts/check_requirements.py"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    out = p.stdout.decode()
    assert p.returncode == 0, f"check_requirements failed: {out}"
    assert "Requirements check OK" in out
