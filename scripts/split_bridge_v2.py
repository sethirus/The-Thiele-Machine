
import os

path = "coq/thielemachine/verification/ThieleUniversalBridge.v"
# Read the current file (which might be modified/broken, but I have a backup or I can just re-read what I wrote)
# Actually I overwrote it.
# But I have the original content in memory? No.
# I have `BridgeDefinitions.v` and `ThieleUniversalBridge.v` (the rest).
# I can concatenate them back to restore original?
# Yes.

with open("coq/thielemachine/verification/BridgeDefinitions.v", "r") as f:
    part1 = f.readlines()

with open("coq/thielemachine/verification/ThieleUniversalBridge.v", "r") as f:
    part2 = f.readlines()

# Remove the imports I added to part2
# Imports were lines 0-9 approx.
# "From Coq ... Ltac bridge_checkpoint ..."
# I'll skip until I see "(* State predicates" ?
# The split point was "(* State predicates".

# Let's just reconstruct the file content by joining and then re-splitting.
# But I need to be careful about duplicated imports.
# part1 has imports. part2 has imports.
# I will strip imports from part2.

lines = part1
# Find start of content in part2
# It starts with imports.
start_idx = 0
for i, line in enumerate(part2):
    if "(* State predicates" in line: # This was the split point
        start_idx = i - 1
        break
# Wait, my split script added imports then wrote 'rest'.
# 'rest' started at split_line.
# So I can just take part2 lines from where imports end.
# But I might have lost the separator line if I wasn't careful.

# Simpler: I know what I want.
# I want to move everything up to "Simplified Proof Attempt" to BridgeDefinitions.
# Currently BridgeDefinitions has up to "State predicates".
# ThieleUniversalBridge has from "State predicates".

# So I want to take from "State predicates" up to "Simplified Proof Attempt" from ThieleUniversalBridge
# and append to BridgeDefinitions.

# Let's read ThieleUniversalBridge.
with open("coq/thielemachine/verification/ThieleUniversalBridge.v", "r") as f:
    lines2 = f.readlines()

# Find the section to move.
# It starts after imports.
# Imports end with "Ltac bridge_checkpoint ..." (approx).
# The split point was "(* State predicates".

start_move = 0
for i, line in enumerate(lines2):
    if "(* State predicates" in line:
        start_move = i - 1
        break

end_move = 0
for i, line in enumerate(lines2):
    if "Simplified Proof Attempt" in line:
        end_move = i - 1
        break

to_move = lines2[start_move:end_move]
rest_new = lines2[end_move:]

# Append to BridgeDefinitions
with open("coq/thielemachine/verification/BridgeDefinitions.v", "a") as f:
    f.writelines(to_move)

    # Add the compose lemma
    f.write("\nLemma check_transition_compose : forall s1 s2 s3 n1 n2, \n")
    f.write("  check_transition s1 s2 n1 = true -> \n")
    f.write("  check_transition s2 s3 n2 = true -> \n")
    f.write("  check_transition s1 s3 (n1 + n2) = true.\n")
    f.write("Proof.\n")
    f.write("  unfold check_transition. intros s1 s2 s3 n1 n2 H1 H2.\n")
    f.write("  apply state_eqb_true_iff in H1. \n")
    f.write("  apply state_eqb_true_iff in H2.\n")
    f.write("  rewrite run_n_add. rewrite H1. rewrite H2. \n")
    f.write("  apply state_eqb_refl.\n")
    f.write("Qed.\n")

# Rewrite ThieleUniversalBridge
imports = """From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
From ThieleMachine Require Import BridgeDefinitions.
From ThieleMachine Require Import BridgeCheckpoints.
From ThieleMachine Require Import BridgeProof.
Import ListNotations.

Local Open Scope nat_scope.
Local Notation length := List.length.

Ltac bridge_checkpoint msg :=
  let s := eval compute in msg in idtac "[bridge]" s.

"""

with open("coq/thielemachine/verification/ThieleUniversalBridge.v", "w") as f:
    f.write(imports)
    f.writelines(rest_new)
