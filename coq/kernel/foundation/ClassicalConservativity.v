(** ClassicalConservativity.v — D3: Classical Opcode Conservativity

    The Thiele VM's full ISA includes both structural (categorical) instructions
    and classical instructions. D3 says: when the VM executes a program using
    only "classical" opcodes — no PNEW, MORPH, MORPH_ASSERT, LASSERT, LJOIN,
    EMIT, REVEAL, PDISCOVER, CHSH_TRIAL, CERTIFY, TENSOR_SET, or any
    graph-modifying MORPH variants — the morphism graph, the cert address
    channel, and the vm_certified flag are all preserved throughout.

    Precisely: if all instructions satisfy is_classical_opcode, then
    (1) vm_graph is unchanged, (2) csr_cert_addr is unchanged, and
    (3) vm_certified is unchanged. Thiele restricted to classical opcodes does
    not exercise the structural layer — it behaves like a classical machine on
    the (graph, cert) dimensions.

    What this does NOT prove: that classical opcodes simulate a Turing machine
    (separate theorem), that classical behavior equals any specific external
    model, conservativity on (regs, mem, pc) — those are unconstrained —
    or D4 (strictness: that Thiele can distinguish states classical machines
    cannot). Fully proven. Zero Admitted.
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI.

(** is_classical_opcode: true iff the instruction does not modify vm_graph,
    csr_cert_addr, vm_certified, or vm_witness. Excluded:
    - Graph-modifying: pnew, psplit, pmerge, lassert, pdiscover, tensor_set,
      morph, compose, morph_id, morph_delete, morph_tensor
    - Cert-channel: lassert, ljoin, emit, reveal, morph_assert
    - vm_certified: certify
    - vm_witness: chsh_trial
    Instructions like mdlacc, morph_get, tensor_get, read_port, write_port
    are classical — they don't touch graph/cert/witness.
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
  | instr_chsh_lassert _       => false  (* cert-setter: column-contractivity check on witness counters *)
  | _                          => true
  end.


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
  try (unfold jump_state_rm; simpl; reflexivity);
  (* tensor_get: if tensor_indices_ok, both branches preserve graph *)
  try (destruct (tensor_indices_ok _ _);
       [unfold advance_state_rm; simpl; reflexivity
       | unfold advance_state; simpl; reflexivity]);
  (* morph_get: match graph_lookup_morphism, both branches preserve graph *)
  try (destruct (graph_lookup_morphism _ _);
       [unfold advance_state_rm; simpl; reflexivity
       | unfold advance_state; simpl; reflexivity]).
  - (* jnez: two branches; use match goal to find the destruct target *)
    match goal with
    | |- context [Nat.eqb (read_reg ?st ?rs) 0] =>
        destruct (Nat.eqb (read_reg st rs) 0)
    end;
    [unfold advance_state | unfold jump_state]; simpl; reflexivity.
Qed.

(** classical_opcode_is_not_cert_setter: cert_addr_setterb = false for all
    classical opcodes. Used by classical_opcode_preserves_cert_addr. *)
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
    certify is excluded from is_classical_opcode. *)
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
  try (unfold jump_state_rm; simpl; reflexivity);
  try (destruct (tensor_indices_ok _ _);
       [unfold advance_state_rm; simpl; reflexivity
       | unfold advance_state; simpl; reflexivity]);
  try (destruct (graph_lookup_morphism _ _);
       [unfold advance_state_rm; simpl; reflexivity
       | unfold advance_state; simpl; reflexivity]).
  - (* jnez *)
    match goal with
    | |- context [Nat.eqb (read_reg ?st ?rs) 0] =>
        destruct (Nat.eqb (read_reg st rs) 0)
    end;
    [unfold advance_state | unfold jump_state]; simpl; reflexivity.
Qed.

(** Trace-level preservation by induction. A classical trace is one where
    all instructions satisfy is_classical_opcode. *)

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

(** D3 Conservativity. A trace using only classical opcodes does not
    exercise the Thiele-specific structural layer. Thiele restricted to
    classical opcodes behaves identically to any machine tracking only
    (regs, mem, pc, mu, err): the morphism graph is unchanged, no structural
    certification occurs, vm_certified is unchanged. This is the formal
    content of "Thiele extends classical machines." *)

(** D3_conservativity: over any classical trace, (1) vm_graph, (2) csr_cert_addr,
    and (3) vm_certified are all unchanged. Thiele over classical programs
    does not exercise the structural (categorical) layer. *)
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
