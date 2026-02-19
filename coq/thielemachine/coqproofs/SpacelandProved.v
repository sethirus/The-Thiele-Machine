(** ===================================================================
    SpacelandProved: Representation Theorem with NO Admits
    =================================================================== *)

From Coq Require Import List Bool ZArith Lia.
Import ListNotations.

Module SimpleSpaceland.
  Definition Partition := list (list nat).
  Definition State := (Partition * Z)%type.
  
  Inductive Label :=
    | LCompute : Label
    | LSplit : nat -> Label.
  
  Fixpoint split_module (p : Partition) (idx : nat) : Partition :=
    match p, idx with
    | [], _ => []
    | m :: rest, O =>
        let mid := Nat.div (length m) 2 in
        (firstn mid m) :: (skipn mid m) :: rest
    | m :: rest, S i' => m :: split_module rest i'
    end.
  
  Inductive step : State -> Label -> State -> Prop :=
    | SCompute : forall p mu,
        step (p, mu) LCompute (p, mu)
    | SSplit : forall p mu i,
        step (p, mu) (LSplit i) (split_module p i, (mu + 1)%Z).
  
  Definition mu_cost (s : State) (l : Label) (s' : State) : Z :=
    (snd s' - snd s)%Z.
  
  (** [step_det]: formal specification. *)
  Lemma step_det : forall s l s1 s2,
    step s l s1 -> step s l s2 -> s1 = s2.
  Proof. intros. destruct H; inversion H0; reflexivity. Qed.
  
  (** [mu_nonneg]: formal specification. *)
  Lemma mu_nonneg : forall s l s',
    step s l s' -> (mu_cost s l s' >= 0)%Z.
  Proof. intros. unfold mu_cost. destruct H; simpl; lia. Qed.
  
  (** [mu_blind]: formal specification. *)
  Lemma mu_blind : forall s s',
    step s LCompute s' -> fst s = fst s' -> mu_cost s LCompute s' = 0%Z.
  Proof. intros. inversion H; subst; unfold mu_cost; simpl; lia. Qed.

End SimpleSpaceland.

Module Observables.
  Import SimpleSpaceland.
  
  Inductive Trace :=
    | TNil : State -> Trace
    | TCons : State -> Label -> Trace -> Trace.
  
  Definition partition_seq (t : Trace) : list Partition :=
    let fix aux t :=
      match t with
      | TNil s => [fst s]
      | TCons s _ t' => fst s :: aux t'
      end
    in aux t.
  
  Fixpoint mu_total (t : Trace) : Z :=
    match t with
    | TNil _ => 0%Z
    | TCons s l (TNil s') => mu_cost s l s'
    | TCons s l ((TCons s' _ _) as t') => (mu_cost s l s' + mu_total t')%Z
    end.
  
  Definition observable (t : Trace) := (partition_seq t, mu_total t).
  
  (** Partition differences are observable *)
  Theorem partition_observable : forall p1 p2 m1 m2,
    p1 <> p2 ->
    observable (TNil (p1, m1)) <> observable (TNil (p2, m2)).
  Proof.
    intros p1 p2 m1 m2 Hneq Heq.
    unfold observable in Heq. simpl in Heq.
    congruence.
  Qed.
  
  (** Absolute μ NOT observable - gauge freedom *)
  (* DEFINITIONAL — observable reads partition only, not μ *)
  (** [mu_gauge_freedom]: formal specification. *)
  Lemma mu_gauge_freedom : forall p m1 m2,
    observable (TNil (p, m1)) = observable (TNil (p, m2)).
  Proof.
    intros. unfold observable. simpl. reflexivity.
  Qed.

End Observables.

Module RepresentationTheorem.
  Import SimpleSpaceland Observables.
  
  (** REPRESENTATION THEOREM: Partition determines observable *)
  Theorem representation : forall s1 s2,
    fst s1 = fst s2 ->
    partition_seq (TNil s1) = partition_seq (TNil s2).
  Proof.
    intros [p1 m1] [p2 m2] H. simpl in *. congruence.
  Qed.
  
  (** Converse: Different partitions → different observables *)
  Theorem completeness : forall s1 s2,
    partition_seq (TNil s1) <> partition_seq (TNil s2) ->
    fst s1 <> fst s2.
  Proof.
    intros [p1 m1] [p2 m2] Hneq Heq. simpl in *. congruence.
  Qed.
  
  (** Full characterization *)
  Theorem bijection : forall s1 s2,
    fst s1 = fst s2 <-> partition_seq (TNil s1) = partition_seq (TNil s2).
  Proof.
    intros. split; [apply representation | ].
    intros H. destruct s1, s2. simpl in *. congruence.
  Qed.

End RepresentationTheorem.

(** ===================================================================
    SUMMARY - WHAT THIS FILE ACTUALLY PROVES
    ===================================================================
    
    PROVEN (no admits):
    ✅ step_det: Deterministic transitions
    ✅ mu_nonneg: Non-negative μ costs  
    ✅ mu_blind: Blind steps cost nothing
    ✅ partition_observable: p1≠p2 → [p1]≠[p2] (tautological)
    ✅ mu_gauge_freedom: ([p],0) = ([p],0) for any μ values
    ✅ representation: p1=p2 → [p1]=[p2]
    ✅ completeness: [p1]≠[p2] → p1≠p2
    ✅ bijection: p1=p2 ↔ [p1]=[p2]
    
    WHAT THIS MEANS:
    
    For SINGLE-STATE traces (TNil s), the observable is just ([p], 0).
    The map p ↦ [p] is injective. That's all.
    
    LIMITATIONS:
    
    ❌ Does NOT use multi-step traces or `step` relation
    ❌ Does NOT show μ matters (mu_total is always 0 for TNil)
    ❌ Does NOT prove observational equivalence over dynamics
    ❌ Does NOT connect to real Thiele machine semantics
    ❌ Does NOT prove "partitions+μ characterize all Spaceland models"
    
    STATUS: Clean starting point, but needs extension to:
    1. Prove observational equivalence over multi-step traces
    2. Show μ gauge freedom in actual dynamics (not just static)
    3. Define "two Spaceland models are isomorphic iff same observables"
    4. Connect SimpleSpaceland to actual Thiele implementation
    
    This is a TOY MODEL with correct proofs, not yet the full
    representation theorem claimed in earlier documentation.
    
    =================================================================== *)
