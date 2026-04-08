import subprocess
import sys

result = subprocess.run(
    ["coqc", "-Q", ".", "Kernel", "-Q", "kernel", "Kernel", "-Q", "kami_hw", "KamiHW",
     "-Q", "nofi", "NoFI", "-Q", "spacetime", "Spacetime", "-Q", "thielemachine", "ThieleMachine",
     "-Q", "physics", "Physics", "-Q", "self_reference", "SelfReference",
     "-Q", "thiele_manifold", "ThieleManifold", "-Q", "thermodynamic", "Thermodynamic",
     "-Q", "tests", "Tests", "-Q", "../vendor/kami/Kami", "Kami",
     "ThieleMachineComplete.v"],
    cwd="/workspaces/The-Thiele-Machine/coq",
    capture_output=True,
    text=True,
    timeout=540
)
output = result.stdout + result.stderr
lines = output.strip().split('\n')
for line in lines[-40:]:
    print(line)
print("---RETURN CODE:", result.returncode)
sys.exit(0)
