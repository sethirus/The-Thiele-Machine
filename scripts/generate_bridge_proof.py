
output_path = "coq/thielemachine/verification/BridgeProof.v"

with open(output_path, "w") as f:
    f.write("From Coq Require Import Lia.\n")
    f.write("From ThieleMachine Require Import BridgeDefinitions.\n")
    f.write("From ThieleMachine Require Import BridgeCheckpoints.\n\n")

    checkpoints = [0, 3, 9, 15, 19]
    for i in range(len(checkpoints) - 1):
        start = checkpoints[i]
        end = checkpoints[i+1]
        steps = end - start
        f.write(f"Theorem prove_segment_{start}_{end}:\n")
        f.write(f"  check_transition checkpoint_{start} checkpoint_{end} {steps} = true.\n")
        f.write("Proof.\n")
        f.write("  Time vm_compute.\n")
        f.write("  reflexivity.\n")
        f.write("Qed.\n\n")
