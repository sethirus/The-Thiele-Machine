import subprocess, os, sys

result = subprocess.run(
    ["/usr/bin/coqc", "-Q", "kernel", "Kernel", "-Q", ".", "Top", "kernel/LandauerDerivation.v"],
    cwd="/workspaces/The-Thiele-Machine/coq",
    capture_output=True,
    text=True,
    timeout=180
)
print("STDOUT:", result.stdout)
print("STDERR:", result.stderr)
print("RETURN CODE:", result.returncode)
vo_path = "/workspaces/The-Thiele-Machine/coq/kernel/LandauerDerivation.vo"
if os.path.exists(vo_path):
    print("VO FILE CREATED: YES, size:", os.path.getsize(vo_path))
else:
    print("VO FILE CREATED: NO")
