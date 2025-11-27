
import re

path = "coq/thielemachine/verification/BridgeDefinitions.v"
with open(path, "r") as f:
    content = f.read()

# Remove Axiom
# Be careful not to match too much. The axiom ends with a dot.
# "length (CPU.regs (CPU.step instr st)) <= 10."
pattern_axiom = r"Axiom universal_program_bounded_writes\s*:[\s\S]*?<= 10\."
content = re.sub(pattern_axiom, "", content)

# Remove Lemma length_run_n_eq_bounded
# "Lemma length_run_n_eq_bounded : forall st n," ... "exact Hge].\nQed."
pattern_lemma = r"Lemma length_run_n_eq_bounded\s*:[\s\S]*?Qed\."
content = re.sub(pattern_lemma, "", content)

with open(path, "w") as f:
    f.write(content)
