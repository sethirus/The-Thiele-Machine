
import os

# Split ThieleUniversalBridge.v
path = "coq/thielemachine/verification/ThieleUniversalBridge.v"
with open(path, "r") as f:
    lines = f.readlines()

split_line = 0
found_split = False
for i, line in enumerate(lines):
    if "(* State predicates and invariants" in line:
        # Line 476 is the text.
        # We want to split before the section header block.
        # (* ----------------------------------------------------------------- *)
        # (* State predicates and invariants                                   *)
        # (* ----------------------------------------------------------------- *)
        split_line = i - 1
        found_split = True
        break

if not found_split:
    print("Error: Could not find split point in ThieleUniversalBridge.v")
    exit(1)

definitions = lines[:split_line]
rest = lines[split_line:]

if not definitions[-1].endswith('\n'):
    definitions[-1] += '\n'

print(f"Splitting at line {split_line}")
print(f"Definitions lines: {len(definitions)}")
print(f"Rest lines: {len(rest)}")

with open("coq/thielemachine/verification/BridgeDefinitions.v", "w") as f:
    f.writelines(definitions)

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

with open(path, "w") as f:
    f.write(imports)
    f.writelines(rest)

# Update _CoqProject
proj_path = "coq/_CoqProject"
with open(proj_path, "r") as f:
    proj_lines = f.readlines()

new_proj_lines = []
inserted = False
for line in proj_lines:
    if "thielemachine/verification/ThieleUniversalBridge.v" in line:
        new_proj_lines.append("thielemachine/verification/BridgeCheckpoints.v\n")
        new_proj_lines.append("thielemachine/verification/BridgeDefinitions.v\n")
        new_proj_lines.append("thielemachine/verification/BridgeProof.v\n")
        new_proj_lines.append("thielemachine/verification/ThieleUniversalBridge.v\n")
        inserted = True
    elif "thielemachine/verification/Bridge" in line:
        continue # remove duplicates/old entries
    else:
        new_proj_lines.append(line)

if not inserted:
    # If not found (e.g. I removed it earlier manually), append
    new_proj_lines.append("thielemachine/verification/BridgeCheckpoints.v\n")
    new_proj_lines.append("thielemachine/verification/BridgeDefinitions.v\n")
    new_proj_lines.append("thielemachine/verification/BridgeProof.v\n")
    new_proj_lines.append("thielemachine/verification/ThieleUniversalBridge.v\n")

with open(proj_path, "w") as f:
    f.writelines(new_proj_lines)
