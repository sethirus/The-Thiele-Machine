(** TuringStrictness.v: the VM strictly extends classical runs.

    Strictness. The kernel's [init_state] has no modules. Every state a
    classical run reaches from it keeps that empty graph (classical conservativity). At each such
    state, PNEW of address 0 is a step that issues a module number and raises
    [pg_next_id] from its value to one more. No classical run from
    [init_state], straight-line or jumping, changes [pg_next_id], so the state
    PNEW reaches is one no classical run reaches.

    Strict extension. A classical program leaves the graph, the
    certificate address and the certified flag unchanged, whether it runs as
    an instruction list or under the program-counter runner. Strictness supplies a
    reachable state where one structural step leaves that classical fragment.
*)

From Coq Require Import List Arith.PeanoNat Bool Lia.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof AbstractNoFI
                           ClassicalConservativity ShadowProjection
                           TuringClassicalEmbedding MuInitiality.

(** classical_program_preserves_next_module_id: For any classical trace from s0,
    pg_next_id is preserved (because vm_graph is preserved). *)
Lemma classical_program_preserves_next_module_id :
  forall (trace : list vm_instruction) (s0 : VMState),
    is_classical_program trace ->
    (acm_run thiele_cert_machine trace s0).(vm_graph).(pg_next_id) =
    s0.(vm_graph).(pg_next_id).
Proof.
  intros trace s0 Hclassical.
  assert (Hgraph := classical_trace_preserves_graph trace s0 Hclassical).
  rewrite Hgraph. reflexivity.
Qed.

(** The structural step: PNEW of the range {0}. *)
Definition separating_pnew_step : vm_instruction := instr_pnew [0] 0.

(** Every classical run from [init_state] keeps the initial graph, so PNEW
    of address 0 finds a free module number, an address inside memory and no
    overlapping module. *)
Lemma separating_pnew_step_state : forall s,
  s.(vm_graph) = init_graph ->
  vm_step s separating_pnew_step (vm_apply s separating_pnew_step) /\
  (vm_apply s separating_pnew_step).(vm_graph).(pg_next_id) =
    S s.(vm_graph).(pg_next_id) /\
  (vm_apply s separating_pnew_step).(vm_err) = s.(vm_err).
Proof.
  intros s Hg. unfold separating_pnew_step.
  split; [| split].
  - unfold vm_apply. apply step_pnew. reflexivity.
  - unfold vm_apply. rewrite partition_step_state_graph, Hg. reflexivity.
  - unfold vm_apply, partition_step_state. rewrite Hg. reflexivity.
Qed.

(** pnew_step_separates_thiele_from_classical_reachable. For every state [s] that a classical run
    reaches from [init_state] ([init_state] itself included):
    (1) [s] is reachable by the machine;
    (2) PNEW of address 0 is a step from [s] that raises [pg_next_id] by
        one without setting the error latch;
    (3) every state a classical run reaches from [s], with any control flow,
        has the [pg_next_id] of [s];
    (4) the same holds for the program-counter runner on every classical
        program, for any fuel;
    (5) so the state PNEW reaches differs from every state a classical run
        reaches from [init_state]. *)
Theorem pnew_step_separates_thiele_from_classical_reachable : forall s,
  classical_reachable init_state s ->
  vm_reachable init_state s /\
  vm_step s separating_pnew_step (vm_apply s separating_pnew_step) /\
  (vm_apply s separating_pnew_step).(vm_graph).(pg_next_id) =
    S s.(vm_graph).(pg_next_id) /\
  (vm_apply s separating_pnew_step).(vm_err) = s.(vm_err) /\
  (forall s', classical_reachable s s' ->
     s'.(vm_graph).(pg_next_id) = s.(vm_graph).(pg_next_id)) /\
  (forall fuel prog, is_classical_program prog ->
     (run_vm fuel prog s).(vm_graph).(pg_next_id) =
       s.(vm_graph).(pg_next_id)) /\
  (forall s', classical_reachable init_state s' ->
     s'.(vm_graph) <> (vm_apply s separating_pnew_step).(vm_graph)).
Proof.
  intros s Hs.
  destruct (classical_reachable_preserves_structure _ _ Hs) as [Hg _].
  simpl in Hg.
  destruct (separating_pnew_step_state s Hg) as [Hstep [Hnext Herr]].
  split; [exact (classical_reachable_vm_reachable _ _ Hs) |].
  split; [exact Hstep |].
  split; [exact Hnext |].
  split; [exact Herr |].
  split.
  - intros s' Hs'.
    destruct (classical_reachable_preserves_structure _ _ Hs') as [Hg' _].
    rewrite Hg'. reflexivity.
  - split.
    + intros fuel prog Hprog.
      destruct (classical_opcodes_preserve_structure_run_vm fuel prog s Hprog) as [Hg' _].
      rewrite Hg'. reflexivity.
    + intros s' Hs' Heq.
      destruct (classical_reachable_preserves_structure _ _ Hs') as [Hg' _].
      simpl in Hg'.
      assert (Hn := f_equal pg_next_id Heq).
      rewrite Hnext, Hg', Hg in Hn. simpl in Hn. discriminate.
Qed.

(** The classical run of length zero reaches [init_state], so the theorem
    applies to [init_state] itself: one PNEW step issues module number 0,
    and no classical program run from [init_state] issues any. *)
Corollary pnew_step_separates_thiele_from_classical_at_init :
  vm_step init_state separating_pnew_step (vm_apply init_state separating_pnew_step) /\
  (vm_apply init_state separating_pnew_step).(vm_graph).(pg_next_id) = 1 /\
  (forall fuel prog, is_classical_program prog ->
     (run_vm fuel prog init_state).(vm_graph).(pg_next_id) = 0).
Proof.
  destruct (pnew_step_separates_thiele_from_classical_reachable init_state
              (classical_reachable_refl init_state))
    as [_ [Hstep [Hnext [_ [_ [Hrun _]]]]]].
  split; [exact Hstep |]. split.
  - rewrite Hnext. reflexivity.
  - intros fuel prog Hprog. rewrite (Hrun fuel prog Hprog). reflexivity.
Qed.

(** pnew_step_separates_thiele_from_classical: some state and some structural step change [pg_next_id]
    where every classical instruction-list run from that state keeps it. The
    state is the kernel's [init_state]. *)
Theorem pnew_step_separates_thiele_from_classical :
  exists (s0 : VMState) (thiele_step : vm_instruction),
    vm_reachable init_state s0 /\
    (vm_apply s0 thiele_step).(vm_graph).(pg_next_id) <>
    s0.(vm_graph).(pg_next_id) /\
    (forall (trace : list vm_instruction),
       is_classical_program trace ->
       (acm_run thiele_cert_machine trace s0).(vm_graph).(pg_next_id) =
       s0.(vm_graph).(pg_next_id)).
Proof.
  destruct (pnew_step_separates_thiele_from_classical_reachable init_state
              (classical_reachable_refl init_state))
    as [Hreach [_ [Hnext _]]].
  exists init_state, separating_pnew_step.
  split; [exact Hreach |]. split.
  - rewrite Hnext. lia.
  - intros trace Hclassical.
    exact (classical_program_preserves_next_module_id trace init_state Hclassical).
Qed.

(** thiele_strictly_extends_classical.
    EXTENSION: a classical program leaves the graph, the certificate address
    and the certified flag unchanged, run as an instruction list and run
    under the program-counter runner (which follows jumps), for any fuel.
    STRICTNESS: from every state a classical run reaches from [init_state],
    PNEW of address 0 is a step to a state whose graph no classical run from
    [init_state] reaches. *)
Theorem thiele_strictly_extends_classical :
  (forall (prog : list vm_instruction) (s0 : VMState),
     is_classical_program prog ->
     (acm_run thiele_cert_machine prog s0).(vm_graph) = s0.(vm_graph) /\
     (acm_run thiele_cert_machine prog s0).(vm_csrs).(csr_cert_addr) =
       s0.(vm_csrs).(csr_cert_addr) /\
     (acm_run thiele_cert_machine prog s0).(vm_certified) = s0.(vm_certified)) /\
  (forall (fuel : nat) (prog : list vm_instruction) (s0 : VMState),
     is_classical_program prog ->
     (run_vm fuel prog s0).(vm_graph) = s0.(vm_graph) /\
     (run_vm fuel prog s0).(vm_csrs).(csr_cert_addr) =
       s0.(vm_csrs).(csr_cert_addr) /\
     (run_vm fuel prog s0).(vm_certified) = s0.(vm_certified)) /\
  (forall s, classical_reachable init_state s ->
     vm_step s separating_pnew_step (vm_apply s separating_pnew_step) /\
     (forall s', classical_reachable init_state s' ->
        s'.(vm_graph) <> (vm_apply s separating_pnew_step).(vm_graph))).
Proof.
  split; [| split].
  - intros prog s0 Hclassical.
    exact (classical_opcodes_preserve_structure prog s0 Hclassical).
  - intros fuel prog s0 Hclassical.
    exact (classical_opcodes_preserve_structure_run_vm fuel prog s0 Hclassical).
  - intros s Hs.
    destruct (pnew_step_separates_thiele_from_classical_reachable s Hs)
      as [_ [Hstep [_ [_ [_ [_ Hsep]]]]]].
    split; [exact Hstep | exact Hsep].
Qed.
