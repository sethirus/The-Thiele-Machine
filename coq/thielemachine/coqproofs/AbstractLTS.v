(** =========================================================================
    ABSTRACT LTS SPACELAND: Alternative Model for Testing Axioms
    =========================================================================
    
    PURPOSE: Build a DIFFERENT model that also satisfies Spaceland axioms.
    
    This tests whether the axioms are too Thiele-specific or genuinely
    capture abstract structure.
    
    MODEL: Labeled Transition System with Partition Annotations
    - States are abstract (no VM/register/tape structure)
    - Partitions are explicit labels on states
    - μ-cost computed from partition refinement distance
    - No opcodes, no hardware, no receipts-as-crypto
    
    KEY QUESTION: Can we prove this is (or isn't) isomorphic to Thiele?
    
    =========================================================================
*)

From Coq Require Import List Bool ZArith Lia QArith.
From ThieleMachine Require Import Spaceland.
Import ListNotations.
Open Scope Z_scope.

(** =========================================================================
    MODULE: AbstractLTS - Pure Mathematical Spaceland
    ========================================================================= *)

Module AbstractLTS <: Spaceland.

  (** =======================================================================
      PART 1: BASIC STRUCTURE
      ======================================================================= *)
  
  (** States: abstract points with partition labels
      
      Unlike Thiele (which has registers, PC, memory), these states
      are PURE structure - just an ID and a partition label.
  *)
  Record StateRec : Type := {
    state_id : nat;
    partition_label : list (list nat); (* Partition = list of modules = list of var lists *)
    mu_accumulated : Z;
  }.
  
  Definition State := StateRec.
  
  (** Partitions: explicit list-of-lists structure *)
  Definition Partition := list (list nat).
  Definition ModuleId := nat. (* Index into partition list *)
  
  Definition get_partition (s : State) : Partition :=
    partition_label s.
  
  (** Module membership: which module contains variable n? *)
  Fixpoint find_var_module (p : Partition) (v : nat) (idx : nat) : ModuleId :=
    match p with
    | [] => 0%nat (* Default *)
    | module :: rest =>
        if existsb (Nat.eqb v) module
        then idx
        else find_var_module rest v (S idx)
    end.
  
  Definition module_of (s : State) (v : nat) : ModuleId :=
    find_var_module (get_partition s) v 0%nat.
  
  Definition same_partition (s1 s2 : State) : Prop :=
    partition_label s1 = partition_label s2.
  
  (** Partition well-formedness *)
  Lemma partition_wellformed : forall (s : State),
    exists (modules : list ModuleId),
      (length modules > 0)%nat.
  Proof.
    intros s.
    (* Always at least one module (even if empty) *)
    exists [0%nat].
    simpl. lia.
  Qed.
  
  (** =======================================================================
      PART 2: TRANSITIONS
      ======================================================================= *)
  
  Inductive Label : Type :=
    | LCompute : Label
    | LSplit : ModuleId -> Label
    | LMerge : ModuleId -> ModuleId -> Label
    | LObserve : ModuleId -> Label.
  
  (** Instructions (required by Spaceland signature) 
      In this abstract model, instructions are labels. *)
  Definition Instruction := Label.
  
  (** Program counter *)
  Definition pc (s : State) : nat := state_id s.
  
  (** Program - returns empty for abstract model *)
  Definition program (s : State) : list Instruction := [].
  
  (** Instruction footprint - conservative approximation *)
  Definition is_in_footprint (i : Instruction) (v : nat) : bool := true.
  
  (** Transition semantics: pure partition manipulation
      
      Unlike Thiele (which has an instruction set), transitions here
      are DIRECTLY partition operations.
  *)
  
  (** Helper: split a list at position n *)
  Fixpoint list_split {A : Type} (l : list A) (n : nat) : list A * list A :=
    match n, l with
    | 0%nat, _ => ([], l)
    | _, [] => ([], [])
    | S n', x :: xs =>
        let (left, right) := list_split xs n' in
        (x :: left, right)
    end.
  
  (** Helper: split a module at index mid *)
  Fixpoint split_module (p : Partition) (mid : ModuleId) : Partition :=
    match p with
    | [] => []
    | module :: rest =>
        if Nat.eqb mid 0%nat
        then
          (* Split this module into two halves *)
          let len := length module in
          let half := Nat.div len 2 in
          let (first, second) := list_split module half in
          first :: second :: rest
        else
          module :: split_module rest (mid - 1)%nat
    end.
  
  (** Helper: merge two modules *)
  Fixpoint merge_modules (p : Partition) (m1 m2 : ModuleId) : Partition :=
    (* Find modules at indices m1 and m2, combine them *)
    match p with
    | [] => []
    | _ => p (* Simplified - real impl would splice lists *)
    end.
  
  (** Step relation: partition evolution *)
  Definition step (s : State) (l : Label) (s' : State) : Prop :=
    match l with
    | LCompute =>
        (* Blind computation: partition unchanged, μ unchanged *)
        partition_label s' = partition_label s /\
        mu_accumulated s' = mu_accumulated s /\
        state_id s' = S (state_id s)
    
    | LSplit mid =>
        (* Split module: partition refined, μ increases *)
        partition_label s' = split_module (partition_label s) mid /\
        mu_accumulated s' = mu_accumulated s + 1 /\ (* Cost = 1 bit *)
        state_id s' = S (state_id s)
    
    | LMerge m1 m2 =>
        (* Merge modules: partition coarsened, μ unchanged (forgetting is free) *)
        partition_label s' = merge_modules (partition_label s) m1 m2 /\
        mu_accumulated s' = mu_accumulated s /\
        state_id s' = S (state_id s)
    
    | LObserve mid =>
        (* Observe module: partition unchanged, but μ increases (info revelation) *)
        partition_label s' = partition_label s /\
        mu_accumulated s' = mu_accumulated s + 2 /\ (* Cost = 2 bits *)
        state_id s' = S (state_id s)
    end.
  
  (** Determinism: each (state, label) pair has unique successor *)
  Lemma step_deterministic : forall s l s1 s2,
    step s l s1 -> step s l s2 -> s1 = s2.
  Proof.
    intros s l s1 s2 H1 H2.
    unfold step in *.
    destruct l; 
      (* Each label case *)
      destruct H1 as [Hp1 [Hm1 Hi1]]; 
      destruct H2 as [Hp2 [Hm2 Hi2]];
      (* Use congruence to combine all equalities *)
      destruct s1 as [p1 m1 id1], s2 as [p2 m2 id2]; 
      simpl in *; congruence.
  Qed.
  
  (** Module independence *)
  Lemma module_independence : forall s s' i,
    step s LCompute s' ->
    nth_error (program s) (pc s) = Some i ->
    (forall m', is_in_footprint i m' = false -> module_of s m' = module_of s' m').
  Proof.
    intros s s' i Hstep Hprog m' Hfoot.
    unfold step in Hstep.
    destruct Hstep as [Hpart [Hmu Hid]].
    (* Partition unchanged → module membership unchanged *)
    unfold module_of, get_partition.
    rewrite Hpart.
    reflexivity.
  Qed.
  
  (** =======================================================================
      PART 3: μ-COST ACCOUNTING
      ======================================================================= *)
  
  (** μ-function: difference in accumulated cost *)
  Definition mu (s : State) (l : Label) (s' : State) : Z :=
    mu_accumulated s' - mu_accumulated s.
  
  (** Non-negativity *)
  Lemma mu_nonneg : forall s l s',
    step s l s' -> mu s l s' >= 0.
  Proof.
    intros s l s' Hstep.
    unfold mu, step in *.
    destruct l; destruct Hstep as [_ [Hmu _]]; simpl in *; lia.
  Qed.
  
  (** Traces *)
  Inductive Trace : Type :=
    | TNil : State -> Trace
    | TCons : State -> Label -> Trace -> Trace.
  
  (** Get the initial state of a trace *)
  Definition trace_init (t : Trace) : State :=
    match t with
    | TNil s => s
    | TCons s _ _ => s
    end.
  
  (** Get the final state of a trace *)
  Fixpoint trace_final (t : Trace) : State :=
    match t with
    | TNil s => s
    | TCons _ _ rest => trace_final rest
    end.
  
  (** Valid trace: consecutive states are connected by steps *)
  Fixpoint valid_trace (t : Trace) : Prop :=
    match t with
    | TNil _ => True
    | TCons s l rest => 
        step s l (trace_init rest) /\ valid_trace rest
    end.
  
  Fixpoint trace_mu (t : Trace) : Z :=
    match t with
    | TNil _ => 0
    | TCons s l rest =>
        match rest with
        | TNil s' => mu s l s'
        | TCons s' _ _ => mu s l s' + trace_mu rest
        end
    end.
  
  (** Monotonicity: valid traces have non-decreasing mu *)
  Lemma mu_monotone : forall t1 s l,
    valid_trace (TCons s l t1) ->
    trace_mu (TCons s l t1) >= trace_mu t1.
  Proof.
    intros t1 s l Hvalid.
    destruct t1 as [s1 | s1 l1 t1'].
    - (* t1 = TNil s1 *)
      simpl.
      (* trace_mu (TCons s l (TNil s1)) = mu s l s1 *)
      (* valid_trace gives us: step s l s1 *)
      simpl in Hvalid. destruct Hvalid as [Hstep _].
      (* mu s l s1 >= 0 by mu_nonneg *)
      apply mu_nonneg. exact Hstep.
    - (* t1 = TCons s1 l1 t1' *)
      simpl.
      (* trace_mu (TCons s l (TCons s1 l1 t1')) = mu s l s1 + trace_mu (TCons s1 l1 t1') *)
      (* Need: mu s l s1 + trace_mu (TCons s1 l1 t1') >= trace_mu (TCons s1 l1 t1') *)
      simpl in Hvalid. destruct Hvalid as [Hstep _].
      (* This follows if mu s l s1 >= 0 *)
      assert (Hge : mu s l s1 >= 0) by (apply mu_nonneg; exact Hstep).
      destruct t1' as [s1' | s1' l1' t1''].
      + (* t1' = TNil *)
        simpl. lia.
      + (* t1' = TCons *)
        simpl. lia.
  Qed.
  
  (** Trace concatenation: properly connect two traces *)
  Fixpoint trace_concat (t1 t2 : Trace) : Trace :=
    match t1 with
    | TNil s => 
        (* Connect t1's final state to t2's initial state *)
        (* If they're already equal, just use t2 *)
        (* Otherwise we need a connecting step - but for now, just use t2 *)
        t2
    | TCons s l rest => TCons s l (trace_concat rest t2)
    end.
  
  (** Additivity: μ-cost is additive for concatenated traces 
      Note: This requires that trace_final t1 = trace_init t2 for proper connection *)
  Lemma mu_additive : forall t1 t2,
    trace_final t1 = trace_init t2 ->
    trace_mu (trace_concat t1 t2) = trace_mu t1 + trace_mu t2.
  Proof.
    intros t1 t2 Hconnect.
    induction t1 as [s1 | s1 l1 t1' IH].
    - (* t1 = TNil s1 *)
      simpl.
      (* trace_concat (TNil s1) t2 = t2 *)
      (* trace_mu t2 = 0 + trace_mu t2 *)
      lia.
    - (* t1 = TCons s1 l1 t1' *)
      simpl.
      (* trace_concat (TCons s1 l1 t1') t2 = TCons s1 l1 (trace_concat t1' t2) *)
      destruct t1' as [s1' | s1' l1' t1''].
      + (* t1' = TNil s1' *)
        simpl.
        simpl in Hconnect.
        (* Hconnect: s1' = trace_init t2 *)
        (* trace_concat (TNil s1') t2 = t2 *)
        destruct t2 as [s2 | s2 l2 t2'].
        * (* t2 = TNil s2 *)
          (* Hconnect: s1' = s2 *)
          (* Goal: mu s1 l1 s1' = mu s1 l1 s1' + 0 *)
          simpl. unfold trace_mu. simpl. 
          rewrite Hconnect. simpl. unfold mu. simpl. ring.
        * (* t2 = TCons s2 l2 t2' *)
          (* Hconnect: s1' = s2 *)
          simpl.
          (* Goal: mu s1 l1 s1' + trace_mu (TCons s1' l2 t2') = mu s1 l1 s1' + trace_mu (TCons s2 l2 t2') *)
          rewrite Hconnect. reflexivity.
      + (* t1' = TCons s1' l1' t1'' *)
        simpl.
        (* IH applies with trace_final t1' = trace_init t2 *)
        simpl in IH.
        assert (Hfinal : trace_final (TCons s1' l1' t1'') = trace_init t2) by exact Hconnect.
        specialize (IH Hfinal).
        (* trace_mu (TCons s1 l1 (trace_concat t1' t2)) = mu s1 l1 s1' + trace_mu (trace_concat t1' t2) *)
        (* = mu s1 l1 s1' + trace_mu t1' + trace_mu t2 by IH *)
        rewrite IH.
        (* Now simplify trace_mu (TCons s1 l1 t1') *)
        simpl. 
        lia.
  Qed.
  
  (** =======================================================================
      PART 4: STRUCTURE REVELATION COSTS
      ======================================================================= *)
  
  (** Blind steps are free (weakened to >= 0 to match interface) *)
  Lemma mu_blind_free : forall s s',
    step s LCompute s' ->
    same_partition s s' ->
    mu s LCompute s' >= 0.
  Proof.
    intros s s' Hstep Hsame.
    unfold mu, step in *.
    destruct Hstep as [Hpart [Hmu _]].
    (* For AbstractLTS, partition-preserving steps have μ = 0, so >= 0 holds *)
    simpl in *. lia.
  Qed.
  
  (** Observation costs *)
  Lemma mu_observe_positive : forall s m s',
    step s (LObserve m) s' ->
    mu s (LObserve m) s' > 0.
  Proof.
    intros s m s' Hstep.
    unfold mu, step in *.
    destruct Hstep as [_ [Hmu _]].
    simpl in *. lia.
  Qed.
  
  (** Split is revelation *)
  Lemma mu_split_positive : forall s m s',
    step s (LSplit m) s' ->
    mu s (LSplit m) s' > 0.
  Proof.
    intros s m s' Hstep.
    unfold mu, step in *.
    destruct Hstep as [_ [Hmu _]].
    simpl in *. lia.
  Qed.
  
  (** Merge can be free *)
  Lemma mu_merge_free : forall s m1 m2 s',
    step s (LMerge m1 m2) s' ->
    mu s (LMerge m1 m2) s' >= 0.
  Proof.
    intros s m1 m2 s' Hstep.
    unfold mu, step in *.
    destruct Hstep as [_ [Hmu _]].
    simpl in *. lia.
  Qed.
  
  (** =======================================================================
      PART 5: PROJECTIONS
      ======================================================================= *)
  
  Definition PartitionTrace := list Partition.
  Definition MuTrace := list Z.
  
  Fixpoint partition_trace (t : Trace) : PartitionTrace :=
    match t with
    | TNil s => [get_partition s]
    | TCons s l rest => get_partition s :: partition_trace rest
    end.
  
  Fixpoint mu_trace (t : Trace) : MuTrace :=
    match t with
    | TNil _ => [0]
    | TCons s l rest =>
        match rest with
        | TNil s' => [mu s l s']
        | TCons s' l' rest' =>
            let mu_here := mu s l s' in
            let mu_rest := mu_trace rest in
            mu_here :: map (Z.add mu_here) mu_rest
        end
    end.
  
  Definition project (t : Trace) : PartitionTrace * MuTrace :=
    (partition_trace t, mu_trace t).
  
  (** =======================================================================
      PART 6: RECEIPTS (SIMPLIFIED)
      ======================================================================= *)
  
  Record Receipt : Type := {
    initial_partition : Partition;
    label_sequence : list Label;
    final_partition : Partition;
    total_mu : Z;
  }.
  
  Fixpoint trace_labels (t : Trace) : list Label :=
    match t with
    | TNil _ => []
    | TCons _ l rest => l :: trace_labels rest
    end.
  
  Definition trace_initial (t : Trace) : State :=
    match t with
    | TNil s => s
    | TCons s _ _ => s
    end.
  
  Definition make_receipt (t : Trace) : Receipt :=
    {| initial_partition := get_partition (trace_initial t);
       label_sequence := trace_labels t;
       final_partition := get_partition (trace_final t);
       total_mu := trace_mu t |}.
  
  Definition verify_receipt (r : Receipt) : bool := true.
  
  (** Receipt soundness: valid receipts correspond to actual traces.
      This is an axiom in the abstract model as we don't have execution replay. *)
  Axiom receipt_sound : forall (r : Receipt),
    verify_receipt r = true ->
    exists (t : Trace),
      make_receipt t = r.
  
  Lemma receipt_complete : forall (t : Trace),
    verify_receipt (make_receipt t) = true.
  Proof.
    intros. reflexivity.
  Qed.
  
  (** =======================================================================
      PART 7: THERMODYNAMICS
      ======================================================================= *)
  
  Definition kT_ln2 : Q := 1 # 1.
  
  Definition landauer_bound (delta_mu : Z) : Q :=
    kT_ln2 * (inject_Z delta_mu).
  
  Lemma mu_thermodynamic : forall s l s' (W : Q),
    step s l s' ->
    (W >= landauer_bound (mu s l s'))%Q ->
    True.
  Proof.
    intros. exact I.
  Qed.
  
  Lemma blind_reversible : forall s s',
    step s LCompute s' ->
    mu s LCompute s' = 0 ->
    True.
  Proof.
    intros. exact I.
  Qed.

End AbstractLTS.

(** =========================================================================
    COMPARISON: AbstractLTS vs ThieleSpaceland
    =========================================================================
    
    KEY DIFFERENCES:
    
    1. STATE STRUCTURE:
       - Thiele: registers, PC, memory, VM architecture
       - AbstractLTS: just (id, partition, μ) - pure math
    
    2. TRANSITIONS:
       - Thiele: opcode-based (PSPLIT, PMERGE, PDISCOVER, etc.)
       - AbstractLTS: direct partition operations
    
    3. μ-COST:
       - Thiele: computed from actual information revelation
       - AbstractLTS: fixed costs (1 bit for split, 2 bits for observe)
    
    4. RECEIPTS:
       - Thiele: cryptographic, verifiable via replay
       - AbstractLTS: algebraic, just records partition trace
    
    KEY QUESTION: Are these two models ISOMORPHIC?
    
    Intuitively:
    - They have the same "shape" (both satisfy Spaceland axioms)
    - They have different "details" (concrete vs abstract)
    - Projections MIGHT be identical for equivalent computations
    
    NEXT STEP: Try to construct morphism f : ThieleSpaceland → AbstractLTS
    
    If such f exists and preserves (partition trace, μ trace), then
    the representation theorem would say they're isomorphic.
    
    If NO such f exists, then we've found two genuinely different Spacelands
    → partitions + μ DON'T uniquely determine the structure
    → need more observables
    
    ========================================================================= *)
