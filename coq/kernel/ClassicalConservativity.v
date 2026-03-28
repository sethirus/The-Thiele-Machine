(** ClassicalConservativity.v — D3: Classical Opcode Conservativity

    ==========================================================================
    THE D3 CONSERVATIVITY THEOREM
    ==========================================================================

    The Thiele VM's full ISA includes both structural (categorical) instructions
    and classical instructions. This file proves:

    D3 CONSERVATIVITY: When the Thiele VM executes a program using only
    "classical" opcodes (no PNEW, MORPH, MORPH_ASSERT, LASSERT, LJOIN,
    EMIT, REVEAL, PDISCOVER, CHSH_TRIAL, CERTIFY, TENSOR_SET, and
    the graph-modifying MORPH variants), the morphism graph, the cert
    address channel, and the vm_certified flag are all preserved.

    PRECISE STATEMENT: If all instructions in a trace satisfy
    is_classical_opcode, then:
      (1) vm_graph is unchanged throughout
      (2) csr_cert_addr is unchanged throughout
      (3) vm_certified is unchanged throughout

    This formalizes: "Thiele restricted to classical opcodes does not
    exercise the structural layer — it behaves like a classical machine
    on the (graph, cert) dimensions."

    WHAT THIS DOES NOT PROVE:
    - That the classical opcodes simulate a Turing machine (separate theorem)
    - That the classical behavior equals any specific external model
    - Conservativity on (regs, mem, pc) — those are unconstrained
    - D4 (strictness): that Thiele can distinguish states classical machines cannot

    ==========================================================================
    STATUS: Fully proven. Zero Admitted.
    ==========================================================================
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI.

(** =========================================================================
    PART 1: THE CLASSICAL OPCODE PREDICATE
    =========================================================================

    is_classical_opcode: returns true iff the instruction:
      (a) does not modify vm_graph (morphisms, modules)
      (b) does not modify csr_cert_addr
      (c) does not modify vm_certified
      (d) does not modify vm_witness

    Excluded opcodes:
      - Graph-modifying: pnew, psplit, pmerge, lassert (adds axiom),
        pdiscover, tensor_set (modifies module tensor),
        morph, compose, morph_id, morph_delete, morph_tensor
      - Cert-channel: lassert, ljoin, emit, reveal, morph_assert
      - vm_certified: certify
      - vm_witness: chsh_trial

    Note: mdlacc, morph_get, tensor_get, read_port, write_port, etc.
    are classical — they do not modify graph/cert/witness.
*)

Definition is_classical_opcode (i : vm_instruction) : bool :=
  match i with
  | instr_pnew _ _             => false  (* modifies graph *)
  | instr_psplit _ _ _ _       => false  (* modifies graph *)
  | instr_pmerge _ _ _         => false  (* modifies graph *)
  | instr_lassert _ _ _ _ _      => false  (* modifies graph + cert_addr *)
  | instr_ljoin _ _ _          => false  (* modifies cert_addr *)
  | instr_emit _ _ _           => false  (* modifies cert_addr *)
  | instr_reveal _ _ _ _       => false  (* modifies cert_addr *)
  | instr_pdiscover _ _ _      => false  (* modifies graph *)
  | instr_chsh_trial _ _ _ _ _ => false  (* modifies vm_witness *)
  | instr_certify _            => false  (* modifies vm_certified *)
  | instr_tensor_set _ _ _ _ _ => false  (* modifies graph (module tensor) *)
  | instr_morph _ _ _ _ _      => false  (* modifies graph *)
  | instr_compose _ _ _ _      => false  (* modifies graph *)
  | instr_morph_id _ _ _       => false  (* modifies graph *)
  | instr_morph_delete _ _     => false  (* modifies graph *)
  | instr_morph_assert _ _ _ _ => false  (* modifies cert_addr *)
  | instr_morph_tensor _ _ _ _ => false  (* modifies graph *)
  | _                          => true
  end.

(** =========================================================================
    PART 2: SINGLE-STEP PRESERVATION LEMMAS
    =========================================================================
*)

(** classical_opcode_preserves_graph: classical opcodes preserve vm_graph. *)
Lemma classical_opcode_preserves_graph :
  forall (s : VMState) (i : vm_instruction),
    is_classical_opcode i = true ->
    (vm_apply s i).(vm_graph) = s.(vm_graph).
Proof.
  intros s i Hi.
  destruct i; simpl in Hi; try discriminate;
  unfold vm_apply;
  (* Most classical ops use advance_state_rm or advance_state with s.(vm_graph) *)
  try (unfold advance_state_rm; simpl; reflexivity);
  try (unfold advance_state; simpl; reflexivity);
  try (unfold jump_state; simpl; reflexivity);
  try (unfold jump_state_rm; simpl; reflexivity).
  - (* jnez: two branches; use match goal to find the destruct target *)
    match goal with
    | |- context [Nat.eqb (read_reg ?st ?rs) 0] =>
        destruct (Nat.eqb (read_reg st rs) 0)
    end;
    [unfold advance_state | unfold jump_state]; simpl; reflexivity.
  - (* tensor_get: two branches, both pass s.(vm_graph) *)
    match goal with
    | |- context [Nat.ltb ?a 4 && Nat.ltb ?b 4] =>
        destruct (Nat.ltb a 4 && Nat.ltb b 4)
    end;
    [unfold advance_state_rm | unfold advance_state]; simpl; reflexivity.
  - (* morph_get: two branches, both pass s.(vm_graph) *)
    match goal with
    | |- context [graph_lookup_morphism ?g ?mid] =>
        destruct (graph_lookup_morphism g mid) as [ms|]
    end;
    [unfold advance_state_rm | unfold advance_state]; simpl; reflexivity.
Qed.

(** classical_opcode_preserves_cert_addr: classical opcodes preserve csr_cert_addr.
    Proof: all classical opcodes have cert_addr_setterb = false;
    apply thiele_non_cert_addr_setter_preserves. *)
Lemma classical_opcode_is_not_cert_setter :
  forall (i : vm_instruction),
    is_classical_opcode i = true ->
    cert_addr_setterb i = false.
Proof.
  intros i Hi.
  destruct i; simpl in Hi; simpl; try reflexivity; discriminate.
Qed.

Lemma classical_opcode_preserves_cert_addr :
  forall (s : VMState) (i : vm_instruction),
    is_classical_opcode i = true ->
    (vm_apply s i).(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr).
Proof.
  intros s i Hi.
  apply thiele_non_cert_addr_setter_preserves.
  exact (classical_opcode_is_not_cert_setter i Hi).
Qed.

(** classical_opcode_preserves_certified: classical opcodes preserve vm_certified.
    Proof: only certify sets vm_certified; certify is excluded from is_classical_opcode. *)
Lemma classical_opcode_preserves_certified :
  forall (s : VMState) (i : vm_instruction),
    is_classical_opcode i = true ->
    (vm_apply s i).(vm_certified) = s.(vm_certified).
Proof.
  intros s i Hi.
  destruct i; simpl in Hi; try discriminate;
  unfold vm_apply;
  try (unfold advance_state_rm; simpl; reflexivity);
  try (unfold advance_state; simpl; reflexivity);
  try (unfold jump_state; simpl; reflexivity);
  try (unfold jump_state_rm; simpl; reflexivity).
  - (* jnez *)
    match goal with
    | |- context [Nat.eqb (read_reg ?st ?rs) 0] =>
        destruct (Nat.eqb (read_reg st rs) 0)
    end;
    [unfold advance_state | unfold jump_state]; simpl; reflexivity.
  - (* tensor_get *)
    match goal with
    | |- context [Nat.ltb ?a 4 && Nat.ltb ?b 4] =>
        destruct (Nat.ltb a 4 && Nat.ltb b 4)
    end;
    [unfold advance_state_rm | unfold advance_state]; simpl; reflexivity.
  - (* morph_get *)
    match goal with
    | |- context [graph_lookup_morphism ?g ?mid] =>
        destruct (graph_lookup_morphism g mid) as [ms|]
    end;
    [unfold advance_state_rm | unfold advance_state]; simpl; reflexivity.
Qed.

(** =========================================================================
    PART 3: TRACE-LEVEL PRESERVATION (by induction)
    =========================================================================

    These theorems extend single-step preservation to arbitrary-length traces.
    A classical trace is one where all instructions satisfy is_classical_opcode.
*)

(** classical_trace_preserves_graph: over any classical trace, vm_graph unchanged. *)
Theorem classical_trace_preserves_graph :
  forall (trace : list vm_instruction) (s0 : VMState),
    Forall (fun i => is_classical_opcode i = true) trace ->
    (acm_run thiele_cert_machine trace s0).(vm_graph) = s0.(vm_graph).
Proof.
  induction trace as [| i rest IH]; intros s0 Hforall.
  - simpl. reflexivity.
  - inversion Hforall as [| ? ? Hi Hrest]; subst.
    simpl.
    rewrite (IH (vm_apply s0 i) Hrest).
    exact (classical_opcode_preserves_graph s0 i Hi).
Qed.

(** classical_trace_preserves_cert_addr: over any classical trace,
    csr_cert_addr unchanged. *)
Theorem classical_trace_preserves_cert_addr :
  forall (trace : list vm_instruction) (s0 : VMState),
    Forall (fun i => is_classical_opcode i = true) trace ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) =
    s0.(vm_csrs).(csr_cert_addr).
Proof.
  induction trace as [| i rest IH]; intros s0 Hforall.
  - simpl. reflexivity.
  - inversion Hforall as [| ? ? Hi Hrest]; subst.
    simpl.
    rewrite (IH (vm_apply s0 i) Hrest).
    exact (classical_opcode_preserves_cert_addr s0 i Hi).
Qed.

(** classical_trace_preserves_certified: over any classical trace,
    vm_certified unchanged. *)
Theorem classical_trace_preserves_certified :
  forall (trace : list vm_instruction) (s0 : VMState),
    Forall (fun i => is_classical_opcode i = true) trace ->
    (acm_run thiele_cert_machine trace s0).(vm_certified) = s0.(vm_certified).
Proof.
  induction trace as [| i rest IH]; intros s0 Hforall.
  - simpl. reflexivity.
  - inversion Hforall as [| ? ? Hi Hrest]; subst.
    simpl.
    rewrite (IH (vm_apply s0 i) Hrest).
    exact (classical_opcode_preserves_certified s0 i Hi).
Qed.

(** =========================================================================
    PART 4: D3 — THE CONSERVATIVITY THEOREM
    =========================================================================

    D3 CONSERVATIVITY: A trace using only classical opcodes does not
    exercise the Thiele-specific structural layer.

    The Thiele VM, restricted to classical opcodes, behaves identically
    to any machine that tracks only (regs, mem, pc, mu, err):
      - The morphism graph is unchanged
      - No structural certification occurs (cert_addr stays 0 if it started 0)
      - vm_certified is unchanged

    This is the formal content of "Thiele extends classical machines":
    the classical subset is preserved as-is.
*)

(** D3_conservativity: the complete conservativity statement.
    Over any classical trace:
      (1) vm_graph is unchanged
      (2) csr_cert_addr is unchanged
      (3) vm_certified is unchanged
    Therefore the Thiele VM over classical programs does not exercise
    the structural (categorical) layer. *)
Theorem D3_conservativity :
  forall (trace : list vm_instruction) (s0 : VMState),
    Forall (fun i => is_classical_opcode i = true) trace ->
    (** (1) morphism graph unchanged **)
    (acm_run thiele_cert_machine trace s0).(vm_graph) = s0.(vm_graph) /\
    (** (2) structural cert channel unchanged **)
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) =
      s0.(vm_csrs).(csr_cert_addr) /\
    (** (3) certified flag unchanged **)
    (acm_run thiele_cert_machine trace s0).(vm_certified) = s0.(vm_certified).
Proof.
  intros trace s0 Hclassical.
  refine (conj _ (conj _ _)).
  - exact (classical_trace_preserves_graph trace s0 Hclassical).
  - exact (classical_trace_preserves_cert_addr trace s0 Hclassical).
  - exact (classical_trace_preserves_certified trace s0 Hclassical).
Qed.

(** COROLLARY: A classical program starting with cert_addr = 0 cannot produce
    cert evidence. This is the conservativity direction of NoFI:
    structural certification requires structural opcodes. *)
Corollary classical_trace_cannot_certify :
  forall (trace : list vm_instruction) (s0 : VMState),
    s0.(vm_csrs).(csr_cert_addr) = 0 ->
    Forall (fun i => is_classical_opcode i = true) trace ->
    (acm_run thiele_cert_machine trace s0).(vm_csrs).(csr_cert_addr) = 0.
Proof.
  intros trace s0 Hzero Hclassical.
  rewrite classical_trace_preserves_cert_addr by exact Hclassical.
  exact Hzero.
Qed.
