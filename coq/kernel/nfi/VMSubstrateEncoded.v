(** VMSubstrateEncoded.v — discharging the Goedel-encoding premises of the
    VM-scoped structural undecidability theorem.

    [vm_structural_shortcut_undecidable] (StructuralUndecidability.v) carries
    five section premises: a Goedel encoding [vm_encode], its decoder
    [vm_decode_safe], the round-trip [vm_encode_decode], the internal
    representability predicate [vm_representable], and the VM's recursion
    theorem [vm_recursion_theorem].

    The first three — the encoding — are not an open problem. The kernel already
    has [program_to_nat] / [nat_to_program] with a proven round-trip
    ([VMInstructionEncoding.nat_to_program_program_to_nat]). This file supplies a
    concrete encoding (store the program's Goedel number in [vm_logic_acc]) and
    discharges those three premises, leaving the VM theorem conditional on
    EXACTLY ONE thing: the VM's internal recursion theorem.

    What remains genuinely open after this file, stated by content and not
    hidden: the recursion theorem itself — a universal interpreter realized as a
    [list vm_instruction], together with its s-m-n parametrization, in the
    unbounded-fuel model. That single premise is named explicitly in
    [vm_structural_shortcut_undecidable_encoded] below. The unconditional
    substrate-level discharge of the limitative theorem already exists at the
    nat-coded substrate
    ([NatSubstrateInstance.nat_structural_shortcut_undecidable], closed under the
    global context); this file tightens the 51-opcode presentation so its only
    remaining hypothesis is the recursion theorem, with the encoding proven. *)

From Coq Require Import List Arith.PeanoNat Bool.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuInitiality.
From Kernel Require Import VMInstructionEncoding.
From Kernel Require Import SimpleMorphShortcut.
From Kernel Require Import VMSubstrateInstance.
From Kernel Require Import StructuralUndecidability.

(** Concrete Goedel encoding of a program as a VM state: store its nat code in
    the logic accumulator, on top of [init_state]. The decoder reads that field
    back. Only [vm_logic_acc] carries information; every other field is
    [init_state]'s, so the encoded state is a well-formed VM state. *)
Definition vm_encode_concrete (p : list vm_instruction) : VMState :=
  {| vm_graph     := init_state.(vm_graph);
     vm_csrs      := init_state.(vm_csrs);
     vm_regs      := init_state.(vm_regs);
     vm_mem       := init_state.(vm_mem);
     vm_pc        := init_state.(vm_pc);
     vm_mu        := init_state.(vm_mu);
     vm_mu_tensor := init_state.(vm_mu_tensor);
     vm_err       := init_state.(vm_err);
     vm_logic_acc := program_to_nat p;
     vm_mstatus   := init_state.(vm_mstatus);
     vm_witness   := init_state.(vm_witness);
     vm_certified := init_state.(vm_certified) |}.

Definition vm_decode_concrete (s : VMState) : list vm_instruction :=
  nat_to_program s.(vm_logic_acc).

(** The round-trip — the encoding premise, discharged. *)
Lemma vm_encode_decode_concrete :
  forall p, vm_decode_concrete (vm_encode_concrete p) = p.
Proof.
  intro p. unfold vm_decode_concrete, vm_encode_concrete. simpl.
  apply nat_to_program_program_to_nat.
Qed.

(** The VM-scoped structural undecidability, with the Goedel encoding now
    PROVEN (not assumed). The only surviving hypotheses are [rep] and [Hrec] —
    the VM's internal recursion theorem. Everything the encoding contributed is
    discharged by [vm_encode_decode_concrete]. *)
Theorem vm_structural_shortcut_undecidable_encoded :
  forall (rep : (list vm_instruction -> list vm_instruction) -> Prop)
         (Hrec : forall f, rep f ->
                   exists q, forall s, vm_run q s = vm_run (f q) s),
    ~ exists (decide : list vm_instruction -> bool),
        rep (fun p => if decide p
                      then (@nil vm_instruction)
                      else simple_morph_trace)
        /\ forall p, decide p = true <-> vm_admits_shortcut_extensional p.
Proof.
  intros rep Hrec.
  exact (vm_structural_shortcut_undecidable
           vm_encode_concrete vm_decode_concrete vm_encode_decode_concrete
           rep Hrec).
Qed.
