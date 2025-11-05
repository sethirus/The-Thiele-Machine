From Coq Require Import List.
Require Import Kernel.VMState.
Require Import Kernel.VMStep.

Goal True.
pose (trace := (@nil vm_instruction)).
pose (s := {| vm_graph := (@nil (list nat * list String.string)); vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0 |}; vm_pc := 0; vm_mu := 0; vm_err := false |}).
remember (nth_error trace (vm_pc s)) as maybe_instr eqn:Hfetch.
destruct maybe_instr as [instr|]; simpl; exact I.

Quit.
