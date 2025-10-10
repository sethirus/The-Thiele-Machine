# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# Copyright 2025 Devon Thiele
# See the LICENSE file in the repository root for full terms.

from catnet import CatNet

# Let's define a simple rule set.
# Rule 1: "Never classify a 'kitten' (input [1,0]) as 'dangerous' (output [0,1])"
# We can encode this rule as a simple set of axioms. For this demo, let's say
# any axiom list containing the number -1 is a "paradoxical" command.

net = CatNet(2, 2, 2)

# Define a wrapper for the forward pass that includes a policy check.
def controlled_forward(x, policy_axioms):
    print(f"Checking policy {policy_axioms}...")
    if not net.assert_consistency(policy_axioms):
        print("Cannot proceed. The proposed action violates a core axiom.")
        return None
    print("Policy check passed. Proceeding with inference.")
    return net.forward(x)

# --- Scenario 1: A safe command ---
print("--- Scenario 1: Classifying a 'puppy' ---")
puppy_input = [0, 1]
safe_axioms = [1, 2, 3]  # A valid command.
controlled_forward(puppy_input, safe_axioms)

# --- Scenario 2: An unsafe command ---
print("\n--- Scenario 2: Trying to classify a 'kitten' as 'dangerous' ---")
kitten_input = [1, 0]
# Let's say our policy mapping determines this action corresponds to a paradoxical axiom.
unsafe_axioms = [-1]
controlled_forward(kitten_input, unsafe_axioms)

print(f"\nFinal Audit Log:\n{net.export_audit_log()}")
