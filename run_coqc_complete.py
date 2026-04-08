import subprocess, os, sys

result = subprocess.run(
    ["/usr/bin/coqc", "-Q", ".", "Kernel", "-Q", "kami_hw", "KamiHW",
     "-Q", "../vendor/kami/Kami", "Kami", "ThieleMachineComplete.v"],
    cwd="/workspaces/The-Thiele-Machine/coq",
    capture_output=True,
    text=True,
    timeout=600
)
print("STDOUT:", result.stdout[-3000:] if len(result.stdout) > 3000 else result.stdout)
print("STDERR:", result.stderr[-3000:] if len(result.stderr) > 3000 else result.stderr)
print("RETURN CODE:", result.returncode)
vo_path = "/workspaces/The-Thiele-Machine/coq/ThieleMachineComplete.vo"
if os.path.exists(vo_path):
    st = os.stat(vo_path)
    print(f"VO FILE: exists, size={st.st_size}, mtime={st.st_mtime}")
else:
    print("VO FILE: not found")
