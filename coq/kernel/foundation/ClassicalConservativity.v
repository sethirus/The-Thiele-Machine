(** ClassicalConservativity.v: Classical Opcode Conservativity

    The Thiele VM's full ISA includes both structural (categorical) instructions
    and classical instructions. Conservativity says: when the VM executes a program using
    only "classical" opcodes (no PNEW, MORPH, MORPH_ASSERT, LASSERT, LJOIN,
    EMIT, REVEAL, PDISCOVER, CHSH_TRIAL, CERTIFY, TENSOR_SET, or any
    graph-modifying MORPH variants), the morphism graph, the cert address
    channel, and the vm_certified flag are all preserved throughout.

    Precisely: if all instructions satisfy is_classical_opcode, then
    (1) vm_graph is unchanged, (2) csr_cert_addr is unchanged, and
    (3) vm_certified is unchanged. Thiele restricted to classical opcodes does
    not exercise the structural layer; it behaves like a classical machine on
    the (graph, cert) dimensions.

    What this does NOT prove: that classical opcodes simulate a Turing machine
    (separate theorem), that classical behavior equals any specific external
    model, conservativity on (regs, mem, pc), which are unconstrained,
    or strictness (that Thiele can distinguish states classical machines
    cannot, TuringStrictness.v). Fully proven. Zero Admitted.
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI.

(** is_classical_opcode: true for the instructions outside the exclusion list
    below. The list covers every instruction that changes vm_graph,
    csr_cert_addr, vm_certified or vm_witness, and it also covers the members
    of the cert-setter class that change none of them. Excluded:
    - Graph-modifying: pnew, psplit, pmerge, tensor_set, morph, compose,
      morph_id, morph_delete, morph_tensor
    - Writes csr_cert_addr: morph_assert
    - Writes vm_certified: certify
    - Writes vm_witness: chsh_trial
    - In the cert-setter class (they pay the S cost floor) without writing a
      certification field: lassert, ljoin, emit, reveal, the five chsh_lassert
      forms
    - pdiscover, whose step is a pure advance
    Instructions like mdlacc, morph_get, tensor_get, read_port, write_port
    are classical; they don't touch graph/cert/witness.
*)

Definition is_classical_opcode (i : vm_instruction) : bool :=
  match i with
  | instr_pnew _ _             => false  (* modifies graph *)
  | instr_psplit _ _ _ _       => false  (* modifies graph *)
  | instr_pmerge _ _ _         => false  (* modifies graph *)
  | instr_lassert _ _ _ _ _      => false  (* cert-setter class member *)
  | instr_ljoin _ _ _          => false  (* cert-setter class member *)
  | instr_emit _ _ _           => false  (* cert-setter class member *)
  | instr_reveal _ _ _ _       => false  (* cert-setter class member *)
  | instr_pdiscover _ _ _      => false  (* excluded; the step is a pure advance *)
  | instr_chsh_trial _ _ _ _ _ => false  (* modifies vm_witness *)
  | instr_certify _            => false  (* modifies vm_certified *)
  | instr_tensor_set _ _ _ _ _ => false  (* modifies graph (module tensor) *)
  | instr_morph _ _ _ _ _      => false  (* modifies graph *)
  | instr_compose _ _ _ _      => false  (* modifies graph *)
  | instr_morph_id _ _ _       => false  (* modifies graph *)
  | instr_morph_delete _ _     => false  (* modifies graph *)
  | instr_morph_assert _ _ _ _ => false  (* writes cert_addr *)
  | instr_morph_tensor _ _ _ _ => false  (* modifies graph *)
  | instr_chsh_lassert _       => false  (* cert-setter: column-contractivity check on witness counters *)
  | instr_chsh_lassert_1ab _   => false  (* cert-setter: Q_{1+AB} check on witness counters *)
  | instr_chsh_lassert_1ab_g5 _ _ _ => false  (* cert-setter: γ_5-aware Q_{1+AB} check *)
  | instr_chsh_lassert_1ab_g345 _ _ _ _ _ _ _ => false  (* cert-setter: γ_{3,4,5}-aware Q_{1+AB} 4×4 Sylvester check *)
  | instr_chsh_lassert_1ab_g12345 _ _ _ _ _ _ _ _ _ _ _ => false  (* cert-setter: full γ_{1..5}-aware Q_{1+AB} 6×6 Schur cascade *)
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

(** Classical conservativity. A trace using only classical opcodes does not
    exercise the Thiele-specific structural layer: the morphism graph is
    unchanged, no structural certification occurs, vm_certified is
    unchanged. The statement says nothing about regs, mem, pc, mu or err.
    This is the formal content of "Thiele extends classical machines." *)

(** classical_opcodes_preserve_structure: over any classical trace, (1) vm_graph, (2) csr_cert_addr,
    and (3) vm_certified are all unchanged. Thiele over classical programs
    does not exercise the structural (categorical) layer. *)
Theorem classical_opcodes_preserve_structure :
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

(** Conservativity for programs that jump. [run_vm] fetches the instruction
    at the program counter, so a classical program can branch and loop
    ([instr_jump], [instr_jnez], [instr_call], [instr_ret]). When every
    instruction of the program is classical, every fetched instruction is
    classical, and the structural state is unchanged after any number of
    steps. *)
Theorem classical_opcodes_preserve_structure_run_vm :
  forall (fuel : nat) (prog : list vm_instruction) (s0 : VMState),
    Forall (fun i => is_classical_opcode i = true) prog ->
    (run_vm fuel prog s0).(vm_graph) = s0.(vm_graph) /\
    (run_vm fuel prog s0).(vm_csrs).(csr_cert_addr) =
      s0.(vm_csrs).(csr_cert_addr) /\
    (run_vm fuel prog s0).(vm_certified) = s0.(vm_certified).
Proof.
  induction fuel as [| fuel IH]; intros prog s0 Hclassical.
  - simpl. auto.
  - simpl. destruct (nth_error prog (vm_pc s0)) as [i |] eqn:Hfetch.
    + assert (Hi : is_classical_opcode i = true).
      { rewrite Forall_forall in Hclassical. apply Hclassical.
        exact (nth_error_In prog (vm_pc s0) Hfetch). }
      destruct (IH prog (vm_apply s0 i) Hclassical) as [Hg [Hc Hv]].
      rewrite Hg, Hc, Hv.
      refine (conj _ (conj _ _)).
      * exact (classical_opcode_preserves_graph s0 i Hi).
      * exact (classical_opcode_preserves_cert_addr s0 i Hi).
      * exact (classical_opcode_preserves_certified s0 i Hi).
    + auto.
Qed.

(** classical_reachable s s': [s'] is reached from [s] by zero or more
    steps of the step relation, each executing a classical instruction.
    The steps may come in any order, so this covers every control flow a
    classical program can take. *)
Inductive classical_reachable : VMState -> VMState -> Prop :=
| classical_reachable_refl : forall s, classical_reachable s s
| classical_reachable_step : forall s i s' s'',
    is_classical_opcode i = true ->
    vm_step s i s' ->
    classical_reachable s' s'' ->
    classical_reachable s s''.

(** Every classical run is a run of the machine. *)
Lemma classical_reachable_vm_reachable : forall s s',
  classical_reachable s s' -> vm_reachable s s'.
Proof.
  intros s s' H. induction H as [s | s i s' s'' _ Hstep _ IH].
  - apply vm_reachable_refl.
  - exact (vm_reachable_step s i s' s'' Hstep IH).
Qed.

(** A classical run of any shape leaves the graph, the certificate address
    and the certified flag where they started. *)
Theorem classical_reachable_preserves_structure : forall s s',
  classical_reachable s s' ->
  s'.(vm_graph) = s.(vm_graph) /\
  s'.(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr) /\
  s'.(vm_certified) = s.(vm_certified).
Proof.
  intros s s' H. induction H as [s | s i s' s'' Hi Hstep _ [Hg [Hc Hv]]].
  - auto.
  - apply vm_step_vm_apply in Hstep. subst s'.
    rewrite Hg, Hc, Hv.
    refine (conj _ (conj _ _)).
    + exact (classical_opcode_preserves_graph s i Hi).
    + exact (classical_opcode_preserves_cert_addr s i Hi).
    + exact (classical_opcode_preserves_certified s i Hi).
Qed.
