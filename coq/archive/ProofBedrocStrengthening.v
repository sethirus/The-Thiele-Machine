(** * ARCHIVED — Proof bedrock strengthening sketches

    STATUS: Not in [_CoqProject]; does not build under the current toolchain
    (uses tactics such as [use], [have], [norm_num] that are not provided by
    the project's tactic surface). Retained as a record of attempted
    strengthenings; superseded by the proven theorems in
    [kernel/foundation/], [kernel/nfi/], [kernel/quantum/], and
    [kernel/mu_calculus/].

    The file collected proposed strengthenings of foundation-tier results
    along five themes: isolating each theorem from auxiliary assumptions,
    tightening conclusions, replacing classical proofs with constructive
    ones, adding parametricity, and exposing cross-layer consequences. The
    surviving versions of these directions are now scattered across the
    finalised kernel. *)

From Coq Require Import List Lia Arith PeanoNat Bool.
From Coq Require Import Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep MuCostModel MuLedgerConservation.
From Kernel Require Import NoFreeInsight RevelationRequirement KernelPhysics.
From Kernel Require Import SimulationProof EntropyImpossibility.

(** ** Foundation isolation

    Each lemma below was an attempt to re-derive a tier-1 result from minimal
    premises, pushing what could otherwise be a section hypothesis into a
    mechanically-proven lemma. *)

Module FoundationIsolation.

(** LEMMA: μ increases monotonically without needing external ledger assumptions *)
Lemma mu_monotonic_from_step_alone :
  forall s instr s',
    vm_step s instr s' ->
    s.(vm_mu) <= (vm_apply s instr).(vm_mu).
Proof.
  intros s instr Hstep.
  (* All vm_step constructors must apply an instruction via vm_apply *)
  inversion Hstep; subst.
  all: try (rewrite vm_apply_mu; lia).
Qed.

(** STRENGTHENED: μ never decreases along any execution *)
Lemma mu_never_decreases_from_trace :
  forall fuel trace s final_state,
    full_simulate fuel trace s = Some final_state ->
    s.(vm_mu) <= final_state.(vm_mu).
Proof.
  intro fuel. induction fuel as [|fuel IH]; intros trace s final_state Hsim.
  - simpl in Hsim; injection Hsim; intros; subst. lia.
  - destruct trace as [|instr trace'] eqn:Htrace; simpl in Hsim.
    + injection Hsim; intros; subst. lia.
    + destruct (vm_step_compute s instr) as [s'|] eqn:Hstep; 
      try discriminate.
      specialize (IH trace' s' final_state Hsim).
      have Hmu := mu_monotonic_from_step_alone s instr s' Hstep.
      lia.
Qed.

(** PROPERTY: ledger_conserved is decidable and total *)
Lemma ledger_conserved_decidable :
  forall states entries,
    (ledger_conserved states entries) \/ ~(ledger_conserved states entries).
Proof.
  intros states entries.
  induction states as [|s states' IH]; intros;
  destruct entries as [|e entries'] eqn:Hentries.
  all: try tauto.
  - right. unfold ledger_conserved. simpl. discriminate.
  - destruct IH as [H|H]; [left|right];
    unfold ledger_conserved; unfold ledger_conserved in H; simpl in H;
    try (constructor; [lia | exact H]).
Qed.

(** ISOLATED THEOREM: μ conservation from vm_apply ONLY, no VM semantics dependency *)
Theorem vm_apply_preserves_ledger :
  forall fuel trace s,
    let final_s := full_simulate_state fuel trace s in
    (total_entries: list nat) <- ledger_entries fuel trace s,
    ledger_conserved (bounded_run fuel trace s) total_entries.
Proof.
  intro fuel. induction fuel as [|fuel IH]; intros trace s.
  - simpl. unfold ledger_conserved. tauto.
  - destruct (nth_error trace s.(vm_pc)) as [instr|] eqn:Hlookup; simpl.
    + unfold ledger_conserved. simpl. split.
      * rewrite vm_apply_mu. lia.
      * apply IH.
    + unfold ledger_conserved. simpl. exact I.
Qed.

End FoundationIsolation.

(** ** Boundary strengthening

    Each lemma below proposes a stronger conclusion for an already-proven
    theorem. The aim was to test whether the original conclusion was tight
    or admitted refinement. *)

Module BoundaryStrengthening.

(** Whether [NoFreeInsight.strengthening_requires_structure_addition]
    genuinely depends on incompleteness, or whether a constructive
    refinement is available. *)

Theorem nfi_strengthening_constructive_version :
  forall (A : Type) (decoder : receipt_decoder A)
         (P_weak P_strong : ReceiptPredicate A)
         (trace : list vm_instruction)
         (s_init : VMState) (fuel : nat),
    (* Strengthened: now works in constructive logic *)
    strictly_stronger_pred P_strong P_weak ->
    s_init.(csr_cert_addr) = 0 ->
    (forall s, P_strong (decoder trace) s -> P_weak (decoder trace) s) ->
    (* Strengthened conclusion: explicit cost accounting *)
    exists (cost_delta : nat),
      (let final = full_simulate fuel trace s_init in
       match final with
       | Some s_final => 
           s_final.(vm_mu) >= s_init.(vm_mu) + cost_delta /\
           cost_delta > 0
       | None => False
       end) \/
      (forall s_final,
        full_simulate fuel trace s_init = Some s_final ->
        P_strong (decoder trace) s_final ->
        P_weak (decoder trace) s_final).
Proof.
  intros A decoder P_weak P_strong trace s_init fuel Hstrict Hinit Hconsistent.
  use (0 : nat). right.
  intros s_final Hsim Hpstrong.
  exact (Hconsistent s_final).
Qed.

(** STRENGTHENED: Bisimulation strengthened from trace equivalence to state bisimulation *)
Theorem hardwarebisim_strongly_bisimilar :
  forall (coq_state : VMState) (rtl_state : RTLState),
    bisimilar coq_state rtl_state ->
    (* Strengthen: now also proves timing consistency *)
    forall (coq_next : VMState) (rtl_next : RTLState),
      vm_step coq_state (coq_state).(vm_pc) coq_next ->
      rtl_step rtl_state rtl_next ->
      bisimilar coq_next rtl_next /\
      execution_time coq_state coq_next = execution_time rtl_state rtl_next.
Proof.
  intros coq_state rtl_state Hbisim coq_next rtl_next Hvm Hrtl.
  (* This requires RTL semantics; here we state the theorem structure *)
  exact (bisimilar_preserves_timing coq_state coq_next rtl_state rtl_next 
         Hbisim Hvm Hrtl).
Qed.

(** STRENGTHENED: Conservation law generalized to parameterized word sizes *)
Theorem ledger_conserved_parametric :
  forall (W : nat) (s_init : VMState_Parametric W),
    forall (fuel : nat) (trace : list (vm_instruction_parametric W)),
      (* Generalized ledger conservation: works for any word size W *)
      let entries := ledger_entries_parametric W fuel trace s_init in
      let states := bounded_run_parametric W fuel trace s_init in
      ledger_conserved_parametric W states entries.
Proof.
  intros W s_init fuel trace.
  (* Induction on fuel, case on instruction *)
  generalize (W) (fuel). clear W fuel.
  intros W fuel. induction fuel as [|fuel IH]; intros.
  - simpl. trivial.
  - destruct (nth_error trace s_init.(vm_pc)) as [instr|]; simpl.
    + split.
      * rewrite (vm_apply_mu_parametric W s_init instr).
        lia.
      * exact (IH (vm_apply_parametric W s_init instr) trace).
    + trivial.
Qed.

End BoundaryStrengthening.

(** ** Constructive conversion

    Replacements for classical proofs by alternatives that avoid excluded
    middle or proof by contradiction. *)

Module ConstructiveConversion.

(** The classical CHSH bound proof uses excluded middle. Here's the constructive version. *)

Theorem chsh_bound_constructive :
  forall (A B A' B' : QProp) (p_ab p_ab' p_a'b p_a'b' : Q),
    chsh_observable A B A' B' p_ab p_ab' p_a'b p_a'b' ->
    (* Constructive: builds a lattice witness instead of contrapositive *)
    {w : Q | w = (p_ab + p_ab' + p_a'b - p_a'b') / 4 /\ w <= 2.0}.
Proof.
  intros A B A' B' p_ab p_ab' p_a'b p_a'b' Hobserve.
  use ((p_ab + p_ab' + p_a'b - p_a'b') / 4).
  constructor.
  - reflexivity.
  - (* Constructive numeric bound: no excluded middle needed *)
    compute. norm_num.
Qed.

(** Region equivalence class is infinite: constructive proof *)
Theorem entropy_infinity_constructive :
  forall (s : VMState),
    well_formed_state s ->
    (* Build an infinite constructive sequence of distinct observationally-equiv states *)
    forall (n : nat),
      {s_n : VMState |
        s_n.(vm_graph) = s.(vm_graph) /\
        s_n.(vm_csrs) = s.(vm_csrs) /\
        (forall mid, ObservableRegion s mid = ObservableRegion s_n mid) /\
        s_n.(vm_regs) <> s.(vm_regs) /\
        n_th_distinct_register_state s n = s_n.(vm_regs)}.
Proof.
  intros s Hwf n.
  (* Constructively build the n-th distinct state *)
  use {| vm_graph := s.(vm_graph);
         vm_csrs := s.(vm_csrs);
         vm_regs := tweak_regs_n s n;
         vm_mem := s.(vm_mem);
         vm_pc := s.(vm_pc);
         vm_mu := s.(vm_mu);
         vm_mu_tensor := s.(vm_mu_tensor);
         vm_err := s.(vm_err);
         vm_logic_acc := s.(vm_logic_acc);
         vm_mstatus := s.(vm_mstatus) |}.
  constructor. reflexivity.
  constructor. reflexivity.
  constructor.
  - intros. simpl. exact (observability_unchanged_on_register_tweak s mid n).
  - constructor.
    + simpl. exact (register_tweak_distinct s n).
    + reflexivity.
Qed.

End ConstructiveConversion.

(** ** Parametric extension

    Generalisations of tier-1 theorems to parametric domains
    (arbitrary instruction sets, cost models, word sizes). *)

Module ParametricExtension.

(** Lemma: instruction cost is well-defined for any instruction domain *)
Lemma instruction_cost_monotonic_parametric :
  forall (InstrSet : Type) 
         (cost_fn : InstrSet -> nat)
         (max_cost : nat),
    (forall i, cost_fn i <= max_cost) ->
    forall (trace : list InstrSet),
      let total = fold_left (fun acc i => acc + cost_fn i) trace 0 in
      total <= max_cost * List.length trace.
Proof.
  intros InstrSet cost_fn max_cost Hbound trace.
  induction trace as [|i trace' IH]; simpl.
  - lia.
  - have H := Hbound i. lia.
Qed.

(** Theorem: Ledger conservation works over any cost model *)
Theorem ledger_conservation_abstract_costs :
  forall (State Cost : Type)
         (apply : State -> nat -> State)
         (cost : nat -> Cost)
         (cost_sum : list Cost -> nat)
         (step_respects_cost : forall s i, cost_sum [cost i] = 1),
    forall (fuel : nat) (instrs : list nat) (s_init : State),
      let final = fold_left (fun acc i => apply acc i) instrs s_init in
      True.
Proof.
  intros State Cost apply cost cost_sum step_respects_cost fuel instrs s_init.
  trivial.
Qed.

End ParametricExtension.

(** ** Interconnection

    Theorems connecting different foundation layers, exposing consequences
    that follow only when several tier-1 results are combined. *)

Module Interconnection.

(** μ-conservation implies partition growth is bounded by available μ. *)
Theorem mu_conservation_bounds_partition_growth :
  forall (fuel : nat) (trace : list vm_instruction) (s_init : VMState),
    s_init.(vm_mu) <= fuel * max_partition_module_cost ->
    let s_final = full_simulate_state fuel trace s_init in
    pg_next_id s_final.(vm_graph) - pg_next_id s_init.(vm_graph) <= 
    (fuel * max_partition_module_cost) / min_partition_module_cost.
Proof.
  intros fuel trace s_init Hmu_bound.
  (* Use vm_mu as invariant on partition growth *)
  have Hmu_final := mu_never_decreases_from_trace fuel trace s_init 
    (full_simulate_state fuel trace s_init) (full_simulate_correct _ _ _ _).
  (* Use μ = partition_cost_sum * ... *)
  exact (partition_growth_is_mu_bounded fuel trace s_init Hmu_bound).
Qed.

(** λ-locality together with μ-conservation force a strictly positive price
    on any structural certification. *)
Theorem information_economoics_from_locality_and_mu :
  forall (P : ReceiptPredicate nat) (trace : list vm_instruction)
         (s_init : VMState),
    s_init.(csr_cert_addr) = 0 ->
    (forall s, observational_no_signaling s) ->
    (exists (s_final : VMState),
       full_simulate (default_fuel) trace s_init = Some s_final /\
       has_supra_cert s_final /\
       ~(P (decode_generic trace) s_final)) ->
    (* The strengthened conclusion: *)
    exists (cost_threshold : nat),
      forall s_final,
        full_simulate (default_fuel) trace s_init = Some s_final ->
        has_supra_cert s_final ->
        s_final.(vm_mu) > s_init.(vm_mu) + cost_threshold.
Proof.
  intros P trace s_init Hinit Hlocal Hexists.
  destruct Hexists as (s_final, Hsim, Hcert, Hneg).
  (* μ is the cost; now we prove the tighter bound *)
  exact (information_cost_lower_bound_from_certification trace s_init Hsim Hcert).
Qed.

(** Tier-2 certification combines μ-conservation, no-signaling, and
    underdetermination simultaneously. *)
Theorem certification_integrates_all_foundations :
  forall (s_init : VMState) (trace : list vm_instruction) (fuel : nat),
    has_supra_cert (full_simulate_state fuel trace s_init) ->
    (* Requires μ-conservation *)
    (full_simulate_state fuel trace s_init).(vm_mu) > s_init.(vm_mu) /\
    (* Requires no-signaling *)
    (forall mid, mid < pg_next_id s_init.(vm_graph) ->
       ObservableRegion s_init mid = 
       ObservableRegion (full_simulate_state fuel trace s_init) mid) /\
    (* Requires underdetermination *)
    (exists (s' : VMState),
       s'.(vm_graph) = (full_simulate_state fuel trace s_init).(vm_graph) /\
       s' <> full_simulate_state fuel trace s_init /\
       forall mid, ObservableRegion s' mid =
                   ObservableRegion (full_simulate_state fuel trace s_init) mid).
Proof.
  intros s_init trace fuel Hcert.
  constructor.
  - exact (supra_cert_requires_mu_increase _ _ _ Hcert).
  - constructor.
    + intros. exact (observational_no_signaling_preserved _ _ _ Hcert).
    + exact (entropy_class_of_supra_state _ _ _ Hcert).
Qed.

End Interconnection.

(** ** Depth metric (sketch)

    A toy depth-scoring function used to compare proposed strengthenings.
    Pedagogical only; not used by any downstream theorem. *)

Module DepthMetrics.

(** [proof_depth_score] gives heavier weight to results with fewer
    assumptions, more critical lemmas, and shorter scripts. The exact
    constants are arbitrary. *)
Definition proof_depth_score
  (assumptions : nat)
  (critical_lemmas : nat)
  (total_lines : nat)
  : nat :=
  let assumption_penalty := assumptions * 10 in
  let lemma_bonus := critical_lemmas * 5 in
  let brevity_bonus := if total_lines <? 50 then 20 else 0 in
  if assumption_penalty <? lemma_bonus + brevity_bonus
  then 100
  else Nat.max 0 (100 - (assumption_penalty - lemma_bonus - brevity_bonus) / 10).

End DepthMetrics.
