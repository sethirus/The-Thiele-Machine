(** =========================================================================
    MuShannonQuantitative: The Correct Quantitative Shannon Bound
    =========================================================================

    WHAT IS PROVEN (no admits, no axioms):

    1. vm_apply_cert_addr_cases: after one step, cert_addr is either
       preserved or set to the instruction's fixed value.

    2. run_vm_cert_addr_in_range: after any execution, cert_addr is either
       the initial value or a value in cert_addr_range(trace).

    3. separation_requires_cert_count (MAIN THEOREM):
       If n states have n distinct nonzero cert_addr values (all starting
       from 0), then the trace has >= n cert_addr-setting instructions.
       Under info-pricing: total cert_addr-setter cost in trace >= n.

    4. conditional_shannon_bound:
       IF cert_setter_executions(fuel, trace, s) >= log2(n) (the decision
       tree hypothesis), THEN delta_mu(s) >= log2(n).

    WHY MuShannonConjecture IS FALSE IN GENERAL:

    cert_addr is SET (not accumulated) to ascii_checksum(payload) where
    the payload is FIXED in the instruction encoding, independent of the
    initial state. Branching (JNEZ etc.) determines which cert instruction
    each state reaches. COUNTEREXAMPLE: a trace that branches 4 ways with
    one EMIT per branch separates 4 states with delta_mu = 1 per state,
    but log2(4) = 2 > 1 = delta_mu. So Conj fails for n > 2.

    THE CORRECT BOUNDS:
    - Trace level: count_cert_addr_setters(trace) >= n   [proven here]
    - Individual delta_mu: delta_mu(s_init) >= log2(n) holds IF the
      program is structured as a binary decision tree [conditional, proven]

    INQUISITOR NOTE: proof-connectivity -- quantitative Shannon bound
    connecting cert_addr range to separation count. Track B completion.
    ========================================================================= *)

From Coq Require Import List Lia Arith.PeanoNat Bool Strings.String.
Import ListNotations.

From Kernel Require Import VMState.
From Kernel Require Import VMStep.
From Kernel Require Import SimulationProof.
From Kernel Require Import MuLedgerConservation.

(** =========================================================================
    SECTION 1: CERT_ADDR RANGE
    =========================================================================
    cert_addr is SET (not accumulated) by EMIT, REVEAL, LJOIN, and LASSERT
    (when the SAT certificate passes). The range of possible final values is
    determined statically by the instruction payloads in the trace.
    ========================================================================= *)

(** cert_addr_value_of: The value this instruction would set cert_addr to.
    Returns None for instructions that do not modify cert_addr.
    Note: CERTIFY sets vm_certified but NOT cert_addr. READ_PORT does not
    modify cert_addr either. EMIT/REVEAL/LJOIN/LASSERT/MORPH_ASSERT do. *)
Definition cert_addr_value_of (i : vm_instruction) : option nat :=
  match i with
  | instr_emit _ payload _                           => Some (ascii_checksum payload)
  | instr_reveal _ _ cert _                          => Some (ascii_checksum cert)
  | instr_ljoin _ _ _                                =>
      None  (* cert strings are now in memory; static value unavailable *)
  | instr_lassert _ _ _ _ _                          => None
  | instr_morph_assert _ property _ _               => Some (ascii_checksum property)
  | _                                                => None
  end.

(** cert_addr_range: All cert_addr values a trace could produce.
    Length equals count_cert_addr_setters. *)
Definition cert_addr_range (trace : list vm_instruction) : list nat :=
  flat_map (fun i => match cert_addr_value_of i with
                     | Some v => [v]
                     | None   => []
                     end) trace.

(** count_cert_addr_setters: Static count of cert_addr-modifying instructions. *)
Fixpoint count_cert_addr_setters (trace : list vm_instruction) : nat :=
  match trace with
  | []        => 0
  | i :: rest =>
    (match cert_addr_value_of i with Some _ => 1 | None => 0 end) +
    count_cert_addr_setters rest
  end.

(** cert_addr_range has length = count_cert_addr_setters. *)
Lemma cert_addr_range_length :
  forall trace,
    List.length (cert_addr_range trace) = count_cert_addr_setters trace.
Proof.
  induction trace as [| i rest IH]; [reflexivity|].
  unfold cert_addr_range in *.
  simpl. destruct (cert_addr_value_of i) as [v|]; simpl; rewrite IH; reflexivity.
Qed.

(** If cert_addr_value_of i = Some v and i is in trace, then v is in the range. *)
Lemma cert_addr_value_in_range :
  forall trace i v,
    In i trace ->
    cert_addr_value_of i = Some v ->
    In v (cert_addr_range trace).
Proof.
  induction trace as [| j rest IH]; intros i v Hin Hval.
  - inversion Hin.
  - destruct Hin as [Heq | Hin'].
    + subst j. unfold cert_addr_range. simpl. rewrite Hval. simpl. left. reflexivity.
    + unfold cert_addr_range. simpl.
      destruct (cert_addr_value_of j) as [u|]; simpl.
      * right. apply IH with i; assumption.
      * apply IH with i; assumption.
Qed.

(** =========================================================================
    SECTION 2: HELPER LEMMAS FOR advance_state / jump_state
    =========================================================================
    All state-advancing functions pass vm_csrs directly, so cert_addr of
    the resulting state is exactly csrs.(csr_cert_addr).
    ========================================================================= *)

Lemma csr_set_status_cert_addr :
  forall csrs status,
    (csr_set_status csrs status).(csr_cert_addr) = csrs.(csr_cert_addr).
Proof. intros. unfold csr_set_status. reflexivity. Qed.

Lemma csr_set_err_cert_addr :
  forall csrs err,
    (csr_set_err csrs err).(csr_cert_addr) = csrs.(csr_cert_addr).
Proof. intros. unfold csr_set_err. reflexivity. Qed.

Lemma csr_set_cert_addr_val :
  forall csrs v,
    (csr_set_cert_addr csrs v).(csr_cert_addr) = v.
Proof. intros. unfold csr_set_cert_addr. reflexivity. Qed.

Lemma advance_state_cert_addr :
  forall s instr graph csrs err,
    (advance_state s instr graph csrs err).(vm_csrs).(csr_cert_addr) =
    csrs.(csr_cert_addr).
Proof. intros. unfold advance_state. reflexivity. Qed.

Lemma advance_state_rm_cert_addr :
  forall s instr graph csrs regs mem err,
    (advance_state_rm s instr graph csrs regs mem err).(vm_csrs).(csr_cert_addr) =
    csrs.(csr_cert_addr).
Proof. intros. unfold advance_state_rm. reflexivity. Qed.

Lemma jump_state_cert_addr :
  forall s instr target,
    (jump_state s instr target).(vm_csrs).(csr_cert_addr) =
    s.(vm_csrs).(csr_cert_addr).
Proof. intros. unfold jump_state. reflexivity. Qed.

Lemma jump_state_rm_cert_addr :
  forall s instr target regs mem,
    (jump_state_rm s instr target regs mem).(vm_csrs).(csr_cert_addr) =
    s.(vm_csrs).(csr_cert_addr).
Proof. intros. unfold jump_state_rm. reflexivity. Qed.

Lemma advance_state_reveal_cert_addr :
  forall s instr flat_idx delta graph csrs err,
    (advance_state_reveal s instr flat_idx delta graph csrs err).(vm_csrs).(csr_cert_addr) =
    csrs.(csr_cert_addr).
Proof. intros. unfold advance_state_reveal. reflexivity. Qed.

(** =========================================================================
    SECTION 3: THE SINGLE-STEP CERT_ADDR LEMMA
    =========================================================================
    After vm_apply, cert_addr is either preserved or set to the value
    from cert_addr_value_of. This proof covers all 40 instructions.
    ========================================================================= *)

Lemma vm_apply_cert_addr_cases :
  forall s i,
    (vm_apply s i).(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr) \/
    cert_addr_value_of i = Some ((vm_apply s i).(vm_csrs).(csr_cert_addr)).
Proof.
  intros s i. unfold vm_apply, cert_addr_value_of.
  (* After destruct, cbv zeta reduces let-bindings without touching advance_state *)
  destruct i;
  (* pnew: destruct the graph pair to expose advance_state *)
  try (left; destruct (graph_pnew _ _) as [g' mid];
       rewrite advance_state_cert_addr; reflexivity);
  (* psplit *)
  try (left; destruct (graph_psplit _ _ _ _) as [[[g' l'] r']|];
       [rewrite advance_state_cert_addr
       |rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr]; reflexivity);
  (* pmerge *)
  try (left; destruct (graph_pmerge _ _ _) as [[g' mid]|];
       [rewrite advance_state_cert_addr
       |rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr]; reflexivity);
  (* lassert: cert_addr NOT set in new ISA; all branches use only csr_set_err/csr_set_status *)
  try (left; cbv zeta;
       destruct cert_kind; [destruct (check_model _ _) | destruct (check_lrat _ _)];
       rewrite advance_state_cert_addr;
       try rewrite csr_set_err_cert_addr;
       try rewrite csr_set_status_cert_addr;
       try rewrite csr_set_err_cert_addr;
       reflexivity);
  (* ljoin: cert_addr NOT set in new ISA *)
  try (left; cbv zeta; destruct (String.eqb _ _);
       rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr; reflexivity);
  (* jnez: no let-binding, conditional advance_state / jump_state *)
  try (left; destruct (Nat.eqb _ 0);
       [rewrite advance_state_cert_addr | rewrite jump_state_cert_addr]; reflexivity);
  (* chsh_trial: inline record (true) or advance_state+err (false) *)
  try (left; destruct (chsh_bits_ok _ _ _ _);
       [reflexivity
       |rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr; reflexivity]);
  (* emit: let csrs' := csr_set_cert_addr ...; cbv zeta exposes it *)
  try (right; cbv zeta; rewrite advance_state_cert_addr;
       rewrite csr_set_cert_addr_val; reflexivity);
  (* reveal: let csrs' := ...; uses advance_state_reveal *)
  try (right; cbv zeta; rewrite advance_state_reveal_cert_addr;
       rewrite csr_set_cert_addr_val; reflexivity);
  (* certify / chsh_trial-true: inline record, definitionally equal *)
  try (left; reflexivity);
  (* advance_state cases: mdlacc, pdiscover, oracle_halts, halt, checkpoint, write_port *)
  try (left; cbv zeta; rewrite advance_state_cert_addr; reflexivity);
  (* advance_state_rm cases: xfer, load/store/ALU, read_port, heap, and/or/shl/shr/mul/lui *)
  try (left; cbv zeta; rewrite advance_state_rm_cert_addr; reflexivity);
  (* jump_state: jump *)
  try (left; rewrite jump_state_cert_addr; reflexivity);
  (* jump_state_rm: call, ret *)
  try (left; cbv zeta; rewrite jump_state_rm_cert_addr; reflexivity);
  (* tensor_set / tensor_get: destruct if andb (Nat.ltb i 4) (Nat.ltb j 4) *)
  try (left; destruct (andb _ _);
       cbv zeta;
       first [rewrite advance_state_rm_cert_addr; reflexivity
             |rewrite advance_state_cert_addr; reflexivity
             |rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr; reflexivity]);
  (* instr_compose / instr_morph_id / instr_morph_tensor: Some (g',id) or None *)
  try (left;
       match goal with
       | |- context [graph_compose_morphisms ?g ?m1 ?m2] =>
           destruct (graph_compose_morphisms g m1 m2) as [[? ?]|]
       | |- context [graph_add_identity ?g ?m] =>
           destruct (graph_add_identity g m) as [[? ?]|]
       | |- context [graph_tensor_morphisms ?g ?f ?h] =>
           destruct (graph_tensor_morphisms g f h) as [[? ?]|]
       end;
       cbv zeta;
       first [rewrite advance_state_rm_cert_addr; reflexivity
             |rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr; reflexivity]);
  (* instr_morph_delete: Some g' or None *)
  try (left;
       match goal with |- context [graph_delete_morphism ?g ?m] =>
         destruct (graph_delete_morphism g m) as [?|]
       end;
       first [rewrite advance_state_cert_addr; reflexivity
             |rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr; reflexivity]);
  (* instr_morph_get: graph_lookup_morphism - advance_state_rm success, advance_state fail *)
  try (left;
       match goal with |- context [graph_lookup_morphism ?g ?m] =>
         destruct (graph_lookup_morphism g m) as [?|]
       end;
       cbv zeta;
       first [rewrite advance_state_rm_cert_addr; reflexivity
             |rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr; reflexivity]);
  (* instr_morph_assert: cert-setter on success (right disjunct), preserve on failure (left) *)
  try (match goal with |- context [graph_lookup_morphism ?g ?m] =>
         destruct (graph_lookup_morphism g m) as [?|]
       end;
       [right; cbv zeta; rewrite advance_state_cert_addr; rewrite csr_set_cert_addr_val;
        reflexivity
       |left; rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr; reflexivity]);
  (* instr_morph: two graph_lookup scrutinees + graph_add_morphism pair destruct.
     The let '(graph', morph_id) := graph_add_morphism ... is an irrefutable pair match,
     which cbv zeta/iota cannot reduce when graph_add_morphism is opaque.
     We must explicitly destruct the pair to expose advance_state_rm. *)
  try (left;
       match goal with |- context [graph_lookup ?g ?m1] =>
         destruct (graph_lookup g m1) as [?|]; cbv beta iota
       end;
       [ match goal with |- context [graph_lookup ?g ?m2] =>
           destruct (graph_lookup g m2) as [?|]; cbv beta iota zeta
         end;
         [ (* Both lookups succeeded: destruct the graph_add_morphism pair *)
           match goal with |- context [graph_add_morphism ?ga ?sm ?dm ?c ?b] =>
             destruct (graph_add_morphism ga sm dm c b) as [? ?]; cbv iota
           end;
           rewrite advance_state_rm_cert_addr; reflexivity
         | rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr; reflexivity ]
       | rewrite advance_state_cert_addr; rewrite csr_set_err_cert_addr; reflexivity ]);
  (* final safety net for lassert/ljoin *)
  try (left; cbv zeta beta iota;
       repeat first
         [ rewrite advance_state_cert_addr
         | rewrite advance_state_rm_cert_addr
         | rewrite csr_set_err_cert_addr
         | rewrite csr_set_status_cert_addr
         | destruct cert_kind
         | destruct (check_model _ _)
         | destruct (check_lrat _ _)
         | destruct (String.eqb _ _)
         | reflexivity ]).
Qed.

(** =========================================================================
    SECTION 4: THE MULTI-STEP CERT_ADDR RANGE LEMMA
    =========================================================================
    By induction on fuel: cert_addr is always the initial value or in
    cert_addr_range(trace).
    ========================================================================= *)

Lemma run_vm_cert_addr_in_range :
  forall fuel trace s,
    (run_vm fuel trace s).(vm_csrs).(csr_cert_addr) = s.(vm_csrs).(csr_cert_addr) \/
    In (run_vm fuel trace s).(vm_csrs).(csr_cert_addr) (cert_addr_range trace).
Proof.
  induction fuel as [| fuel IH]; intros trace s.
  - left. reflexivity.
  - simpl. destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hnth.
    + specialize (IH trace (vm_apply s instr)) as [Hpres | Hrange].
      * (* rest preserves cert_addr from vm_apply *)
        destruct (vm_apply_cert_addr_cases s instr) as [Hstep | Hstep].
        -- left. rewrite Hpres. exact Hstep.
        -- right. rewrite Hpres.
           apply cert_addr_value_in_range with instr.
           ++ apply nth_error_In with (n := s.(vm_pc)). exact Hnth.
           ++ exact Hstep.
      * right. exact Hrange.
    + left. reflexivity.
Qed.

(** =========================================================================
    SECTION 5: COMBINATORIAL PIGEONHOLE LEMMA
    =========================================================================
    A NoDup list included in another list has length <= the other's length.
    This is the key combinatorial fact; m may have duplicate elements.
    ========================================================================= *)

(** Helper: x ≠ a, x ∈ l implies x ∈ (remove a l). *)
Lemma in_remove_intro :
  forall (l : list nat) (a x : nat),
    x <> a -> In x l -> In x (List.remove Nat.eq_dec a l).
Proof.
  induction l as [| h t IH]; intros a x Hne Hin.
  - inversion Hin.
  - simpl. destruct (Nat.eq_dec a h) as [Heq | Hah].
    + destruct Hin as [Heqxh | Hint].
      * subst. subst. contradiction.
      * apply IH; assumption.
    + simpl. destruct Hin as [Heqxh | Hint].
      * left. exact Heqxh.
      * right. apply IH; assumption.
Qed.

(** Helper: NoDup m -> NoDup (remove a m). *)
Lemma remove_NoDup :
  forall (m : list nat) (a : nat),
    NoDup m -> NoDup (List.remove Nat.eq_dec a m).
Proof.
  induction m as [| h t IH]; intros a Hnd.
  - simpl. constructor.
  - inversion Hnd; subst.
    simpl. destruct (Nat.eq_dec a h) as [Heq | Hne].
    + apply IH. exact H2.
    + constructor.
      * intro Hinx. apply H1.
        apply List.in_remove in Hinx. exact (proj1 Hinx).
      * apply IH. exact H2.
Qed.

(** Helper: ~ In a t -> remove a t = t. *)
Lemma remove_notin_id :
  forall (t : list nat) (a : nat),
    ~ In a t -> List.remove Nat.eq_dec a t = t.
Proof.
  induction t as [| x tx IH]; intros a Hnin.
  - reflexivity.
  - simpl. destruct (Nat.eq_dec a x) as [Heq | Hne].
    + subst. exfalso. apply Hnin. left. reflexivity.
    + f_equal. apply IH. intro Hin. apply Hnin. right. exact Hin.
Qed.

(** Helper: NoDup m, In a m -> length (remove a m) = length m - 1. *)
Lemma remove_length_NoDup :
  forall (m : list nat) (a : nat),
    NoDup m -> In a m ->
    List.length (List.remove Nat.eq_dec a m) = List.length m - 1.
Proof.
  induction m as [| h t IH]; intros a Hnd Hin.
  - inversion Hin.
  - inversion Hnd; subst.
    simpl. destruct (Nat.eq_dec a h) as [Heq | Hne].
    + subst a.
      rewrite (remove_notin_id t h H1). lia.
    + destruct Hin as [Heq | Hin'].
      * exfalso. apply Hne. exact (eq_sym Heq).
      * simpl.
        rewrite (IH a H2 Hin').
        enough (List.length t >= 1) by lia.
        destruct t as [| x tx]; [inversion Hin' | simpl; lia].
Qed.

(** Helper: length (nodup l) <= length l. *)
Lemma nodup_length_le :
  forall (l : list nat),
    List.length (nodup Nat.eq_dec l) <= List.length l.
Proof.
  induction l as [| h t IH]; [simpl; lia|].
  simpl. destruct (in_dec Nat.eq_dec h t) as [Hin | Hnin]; simpl; lia.
Qed.

(** PIGEONHOLE: NoDup l, NoDup m, l ⊆ m => length l <= length m. *)
Lemma nodup_incl_nodup_le :
  forall (l m : list nat),
    NoDup l ->
    NoDup m ->
    (forall x, In x l -> In x m) ->
    List.length l <= List.length m.
Proof.
  induction l as [| a l' IH]; intros m Hndl Hndm Hincl.
  - simpl. lia.
  - inversion Hndl as [| x l'' Hnotin Hndl' Heq]; subst.
    simpl.
    assert (Ha : In a m) by (apply Hincl; left; reflexivity).
    assert (Hincl' : forall x, In x l' -> In x (List.remove Nat.eq_dec a m)).
    { intros x Hx.
      apply in_remove_intro.
      - intro Heq. subst. apply Hnotin. exact Hx.
      - apply Hincl. right. exact Hx. }
    pose proof (remove_NoDup m a Hndm) as Hndm_rem.
    pose proof (remove_length_NoDup m a Hndm Ha) as Hlen_rem.
    specialize (IH (List.remove Nat.eq_dec a m) Hndl' Hndm_rem Hincl').
    assert (List.length m >= 1) by (destruct m; [inversion Ha | simpl; lia]).
    lia.
Qed.

(** =========================================================================
    SECTION 6: MAIN THEOREM
    =========================================================================
    n states with distinct nonzero cert_addr values (all starting from 0)
    require at least n cert_addr-setting instructions in the trace.
    ========================================================================= *)

(** MAIN THEOREM: n-way cert_addr separation requires >= n cert_addr setters.

    This bounds the TRACE-LEVEL count of cert_addr-setting instructions,
    NOT the delta_mu of any specific execution. *)
Theorem separation_requires_cert_count :
  forall fuel trace omega,
    (forall s, In s omega -> s.(vm_csrs).(csr_cert_addr) = 0) ->
    (forall s, In s omega -> (run_vm fuel trace s).(vm_csrs).(csr_cert_addr) <> 0) ->
    NoDup (map (fun s => (run_vm fuel trace s).(vm_csrs).(csr_cert_addr)) omega) ->
    List.length omega <= count_cert_addr_setters trace.
Proof.
  intros fuel trace omega Hinit Hnonzero HNoDup.
  set (addrs := map (fun s => (run_vm fuel trace s).(vm_csrs).(csr_cert_addr)) omega).
  assert (Hincl : forall v, In v addrs -> In v (cert_addr_range trace)).
  { intros v Hv. unfold addrs in Hv.
    apply in_map_iff in Hv. destruct Hv as [s [Heq Hs]]. subst v.
    specialize (Hinit s Hs). specialize (Hnonzero s Hs).
    destruct (run_vm_cert_addr_in_range fuel trace s) as [Hpres | Hrange].
    - rewrite Hpres in Hnonzero. rewrite Hinit in Hnonzero. contradiction.
    - exact Hrange. }
  assert (Hlen_addrs : List.length addrs = List.length omega) by apply map_length.
  rewrite <- Hlen_addrs. rewrite <- cert_addr_range_length.
  (* cert_addr_range may have duplicates; dedup it, then pigeonhole *)
  apply Nat.le_trans with (m := List.length (nodup Nat.eq_dec (cert_addr_range trace))).
  - apply nodup_incl_nodup_le.
    + exact HNoDup.
    + apply NoDup_nodup.
    + intros x Hx. apply nodup_In. apply Hincl. exact Hx.
  - apply nodup_length_le.
Qed.

(** =========================================================================
    SECTION 7: INFO-PRICING BOUND
    =========================================================================
    Under info-pricing, cert_addr-setting instructions each cost >= 1.
    ========================================================================= *)

(** Under info-pricing, the total cost of cert_addr setters >= their count. *)
Lemma cert_addr_setters_priced :
  forall trace,
    Forall (fun i => match cert_addr_value_of i with
                     | Some _ => instruction_cost i >= 1
                     | None   => True
                     end) trace ->
    count_cert_addr_setters trace <=
    fold_right (fun i acc =>
      match cert_addr_value_of i with
      | Some _ => instruction_cost i + acc
      | None   => acc
      end) 0 trace.
Proof.
  induction trace as [| i rest IH]; intros Hpriced.
  - simpl. lia.
  - inversion Hpriced; subst. simpl.
    specialize (IH H2).
    destruct (cert_addr_value_of i) as [v|] eqn:Hv; simpl in *; lia.
Qed.

(** COROLLARY: Under info-pricing, n-way separation => total cert cost >= n. *)
Corollary separation_le_cert_cost :
  forall fuel trace omega,
    Forall (fun i => match cert_addr_value_of i with
                     | Some _ => instruction_cost i >= 1
                     | None   => True
                     end) trace ->
    (forall s, In s omega -> s.(vm_csrs).(csr_cert_addr) = 0) ->
    (forall s, In s omega -> (run_vm fuel trace s).(vm_csrs).(csr_cert_addr) <> 0) ->
    NoDup (map (fun s => (run_vm fuel trace s).(vm_csrs).(csr_cert_addr)) omega) ->
    List.length omega <=
    fold_right (fun i acc =>
      match cert_addr_value_of i with
      | Some _ => instruction_cost i + acc
      | None   => acc
      end) 0 trace.
Proof.
  intros fuel trace omega Hpriced Hinit Hnonzero HNoDup.
  transitivity (count_cert_addr_setters trace).
  - exact (separation_requires_cert_count fuel trace omega Hinit Hnonzero HNoDup).
  - apply cert_addr_setters_priced. exact Hpriced.
Qed.

(** =========================================================================
    SECTION 8: CONDITIONAL INDIVIDUAL SHANNON BOUND
    =========================================================================
    Δμ(s_init) >= log2(n) is conditional: it requires the "decision tree
    hypothesis" that cert_setter_executions(s_init) >= log2(n). Under
    that hypothesis, the bound follows from the conservation law.
    ========================================================================= *)

Fixpoint cert_setter_executions_local (fuel : nat) (trace : list vm_instruction)
    (s : VMState) : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
    match nth_error trace s.(vm_pc) with
    | Some instr =>
        (if is_cert_setterb instr then 1 else 0) +
        cert_setter_executions_local fuel' trace (vm_apply s instr)
    | None => 0
    end
  end.

(** Under info-pricing, cert_setter_executions <= delta_mu. *)
Lemma cert_executions_le_delta_mu_local :
  forall fuel trace s,
    Forall (fun i => is_cert_setterb i = true -> instruction_cost i >= 1) trace ->
    cert_setter_executions_local fuel trace s <=
    (run_vm fuel trace s).(vm_mu) - s.(vm_mu).
Proof.
  induction fuel as [| fuel IH]; intros trace s Hpriced; [simpl; lia|].
  simpl. destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hnth; [|simpl; lia].
  pose proof (IH trace (vm_apply s instr) Hpriced) as IH'.
  pose proof (vm_apply_mu s instr) as Hmu. rewrite Hmu in IH'.
  destruct (is_cert_setterb instr) eqn:Hsetter.
  - assert (instruction_cost instr >= 1).
    { apply Forall_forall with (x := instr) in Hpriced.
      - apply Hpriced. exact Hsetter.
      - apply nth_error_In with (n := s.(vm_pc)). exact Hnth. }
    pose proof (run_vm_mu_conservation fuel trace (vm_apply s instr)) as Hcons.
    rewrite Hmu in Hcons.
    lia.
  - lia.
Qed.

(** THEOREM: The Conditional Individual Shannon Bound.
    IF the program is structured as a binary decision tree for s_init
    (cert_setter_executions >= log2(n)), THEN delta_mu >= log2(n).
    This is the individual bound; it does not follow from the VM alone. *)
Theorem conditional_shannon_bound :
  forall fuel trace s n,
    Forall (fun i => is_cert_setterb i = true -> instruction_cost i >= 1) trace ->
    cert_setter_executions_local fuel trace s >= Nat.log2 n ->
    (run_vm fuel trace s).(vm_mu) - s.(vm_mu) >= Nat.log2 n.
Proof.
  intros fuel trace s n Hpriced Hdtree.
  pose proof (cert_executions_le_delta_mu_local fuel trace s Hpriced). lia.
Qed.

(** =========================================================================
    SECTION 9: RELATIONSHIP TO MuShannonConjecture
    =========================================================================
    The MuShannonConjecture states delta_mu(s_init) >= log2(|Omega|/|Omega'|).
    This is FALSE for n > 2 under current VM semantics (see file header).

    What IS true (separation_requires_cert_count):
      count_cert_addr_setters(trace) >= n for n-way separation.

    The individual bound requires the decision tree hypothesis (Section 8).
    ========================================================================= *)

(** SCOPE: The gap between proven results and the conjecture.
    Proven (trace level): count_cert_addr_setters >= n for n-way separation.
    Proven (conditional): delta_mu >= log2(n) IF cert_executions >= log2(n).
    Not proven (individual, unconditional): delta_mu(s) >= log2(n) for all s.
    Reason: cert_addr is set by instruction-fixed values; 1 EMIT separates n
    states via branching with delta_mu = 1, violating log2(n) for n > 2. *)
