(** NecFCounter: the counter, checked.

    The book argues these on the page; here they are proved over any counter
    machine (Definition "A counter kept by a price list").

    - Conservation: the counter at the end of a run is its start plus the
      price of the run ([nec_f_conservation]); it never decreases
      ([nec_f_counter_monotone]). The one-step rule is exactly what
      conservation needs: conservation for every run holds if and only if the
      rule holds ([nec_f_conservation_iff_rule]).
    - Only one honest count: books that start at zero and follow the price
      list agree with the counter on every reachable state
      ([nec_f_initiality]). The step rule is needed only on reachable states
      ([nec_f_initiality_reachable_rule]); starting at zero is needed
      ([nec_f_initiality_needs_zero_start]); reachability is needed
      ([nec_f_initiality_needs_reachable]). Agreement on reachable states is
      in fact equivalent to the step rule there ([nec_f_initiality_iff]).
    - A horizon: on a finite machine an honest counter can charge nothing at
      all ([nec_f_finite_counter_charges_nothing]). So any running total a
      finite machine keeps for itself fails the counter rule somewhere once
      a move costs at least one.
    - The fold is the one map from lists that starts right and keeps in step
      ([nec_f_fold_unique]). It comes down to states exactly when the
      descent condition holds ([nec_f_descent_iff_functional]); a toll does
      not force descent ([nec_f_descent_fails_for_history]).
    - The potential method: its bound holds for every run exactly when every
      step has non-negative amortized cost ([nec_f_potential_bound_iff]), and
      it is met with equality by runs whose steps have zero amortized cost
      ([nec_f_potential_bound_exact]). *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import PermanentCertification.
From Kernel Require Import CostSemanticsComparison.
From Kernel Require Import NecFFloor.

(** * Counter machines *)

Record NecFCounterMachine := nec_f_mk_counter {
  nec_f_cm_state : Type;
  nec_f_cm_move : Type;
  nec_f_cm_apply : nec_f_cm_state -> nec_f_cm_move -> nec_f_cm_state;
  nec_f_cm_init : nec_f_cm_state;
  nec_f_cm_c : nec_f_cm_move -> nat;
  nec_f_cm_mu : nec_f_cm_state -> nat;
  nec_f_cm_mu_init : nec_f_cm_mu nec_f_cm_init = 0;
  nec_f_cm_mu_step : forall s i, nec_f_cm_mu (nec_f_cm_apply s i) = nec_f_cm_mu s + nec_f_cm_c i
}.

Section Counter.

Variable M : NecFCounterMachine.
Notation St := (nec_f_cm_state M).
Notation Mv := (nec_f_cm_move M).
Notation apply := (nec_f_cm_apply M).
Notation c := (nec_f_cm_c M).
Notation mu := (nec_f_cm_mu M).
Notation init := (nec_f_cm_init M).

Fixpoint nec_f_cm_run (t : list Mv) (s : St) : St :=
  match t with [] => s | i :: t' => nec_f_cm_run t' (apply s i) end.

Fixpoint nec_f_cm_price (t : list Mv) : nat :=
  match t with [] => 0 | i :: t' => c i + nec_f_cm_price t' end.

Theorem nec_f_conservation : forall t s, mu (nec_f_cm_run t s) = mu s + nec_f_cm_price t.
Proof.
  induction t as [| i t IH]; intros s; simpl; [lia |].
  rewrite IH, (nec_f_cm_mu_step M). lia.
Qed.

Corollary nec_f_counter_monotone : forall t s, mu s <= mu (nec_f_cm_run t s).
Proof. intros t s. rewrite nec_f_conservation. lia. Qed.

Inductive nec_f_cm_reach : St -> Prop :=
| nec_f_cmr_init : nec_f_cm_reach init
| nec_f_cmr_step : forall s i, nec_f_cm_reach s -> nec_f_cm_reach (apply s i).

(** The step rule for the books is needed only on reachable states. *)
Theorem nec_f_initiality_reachable_rule :
  forall B : St -> nat,
    B init = 0 ->
    (forall s i, nec_f_cm_reach s -> B (apply s i) = B s + c i) ->
    forall s, nec_f_cm_reach s -> B s = mu s.
Proof.
  intros B H0 Hstep s Hs. induction Hs as [| s i Hs IH].
  - rewrite H0, (nec_f_cm_mu_init M). reflexivity.
  - rewrite (Hstep s i Hs), IH, (nec_f_cm_mu_step M). reflexivity.
Qed.

(** The book's statement. *)
Theorem nec_f_initiality :
  forall B : St -> nat,
    B init = 0 ->
    (forall s i, B (apply s i) = B s + c i) ->
    forall s, nec_f_cm_reach s -> B s = mu s.
Proof.
  intros B H0 Hstep. apply nec_f_initiality_reachable_rule; [exact H0 |].
  intros s i _. apply Hstep.
Qed.

(** For books that start at zero, agreeing with the counter on the reachable
    states is the same as following the price list there. *)
Theorem nec_f_initiality_iff :
  forall B : St -> nat,
    B init = 0 ->
    ((forall s, nec_f_cm_reach s -> B s = mu s) <->
     (forall s i, nec_f_cm_reach s -> B (apply s i) = B s + c i)).
Proof.
  intros B H0. split.
  - intros Hagree s i Hs.
    rewrite (Hagree _ (nec_f_cmr_step s i Hs)), (Hagree s Hs). apply (nec_f_cm_mu_step M).
  - intro Hstep. apply nec_f_initiality_reachable_rule; assumption.
Qed.

(** Conservation for every run is exactly the one-step rule. *)
Theorem nec_f_conservation_iff_rule :
  forall m : St -> nat,
    (forall t s, m (nec_f_cm_run t s) = m s + nec_f_cm_price t) <->
    (forall s i, m (apply s i) = m s + c i).
Proof.
  intro m. split.
  - intros H s i. specialize (H [i] s). simpl in H. lia.
  - intros H t. induction t as [| i t IH]; intros s; simpl; [lia |].
    rewrite IH, H. lia.
Qed.

(** A horizon. On a finite machine, an honest counter charges nothing. *)
Theorem nec_f_finite_counter_charges_nothing :
  forall all : list St, finite_states all -> forall i, c i = 0.
Proof.
  intros all [_ Hall] i.
  (* a state of largest counter value *)
  assert (Hmax : exists s, forall t, In t (init :: all) -> mu t <= mu s).
  { generalize (init :: all) as l. induction l as [| a l IH].
    - exists init. intros t [].
    - destruct IH as [s Hs]. destruct (le_lt_dec (mu a) (mu s)) as [Hle | Hlt].
      + exists s. intros t [<- | Ht]; [exact Hle | apply Hs; exact Ht].
      + exists a. intros t [<- | Ht]; [lia | pose proof (Hs t Ht); lia]. }
  destruct Hmax as [s Hs].
  pose proof (Hs (apply s i) (or_intror (Hall _))) as H1.
  rewrite (nec_f_cm_mu_step M) in H1. lia.
Qed.

End Counter.

(** * Starting at zero and reachability are both needed *)

(** Books shifted by one follow the price list and never agree. *)
Theorem nec_f_initiality_needs_zero_start :
  forall M : NecFCounterMachine,
    let B := fun s => nec_f_cm_mu M s + 1 in
    (forall s i, B (nec_f_cm_apply M s i) = B s + nec_f_cm_c M i) /\
    (forall s, B s <> nec_f_cm_mu M s).
Proof.
  intros M B. split.
  - intros s i. unfold B. rewrite (nec_f_cm_mu_step M). lia.
  - intros s. unfold B. lia.
Qed.

(** A counter machine with an unreachable state on which honest books
    disagree with the counter. States are bits, the start is false, the one
    move does nothing and costs nothing. *)
Definition nec_f_idle_cm : NecFCounterMachine :=
  {| nec_f_cm_state := bool; nec_f_cm_move := unit;
     nec_f_cm_apply := fun s _ => s; nec_f_cm_init := false;
     nec_f_cm_c := fun _ => 0;
     nec_f_cm_mu := fun s => if s then 5 else 0;
     nec_f_cm_mu_init := eq_refl;
     nec_f_cm_mu_step := fun s _ => eq_sym (Nat.add_0_r _) |}.

Theorem nec_f_initiality_needs_reachable :
  let B := fun s : bool => if s then 7 else 0 in
  B (nec_f_cm_init nec_f_idle_cm) = 0 /\
  (forall s i, B (nec_f_cm_apply nec_f_idle_cm s i) = B s + nec_f_cm_c nec_f_idle_cm i) /\
  ~ nec_f_cm_reach nec_f_idle_cm true /\
  B true <> nec_f_cm_mu nec_f_idle_cm true.
Proof.
  intro B. split; [reflexivity | split; [intros s i; simpl; lia | split]].
  - intro H. remember true as b eqn:Hb. induction H as [| s i Hs IH]; [discriminate | exact (IH Hb)].
  - simpl. discriminate.
Qed.

(** * The fold, and when it comes down to states *)

Section Fold.

Variables (I T : Type).
Variable tstep : T -> I -> T.
Variable t0 : T.

Definition nec_f_fold (l : list I) : T := fold_left tstep l t0.

(** The fold is the one map from lists that starts at t0 and keeps in step as
    the list grows by one move at the end. *)
Theorem nec_f_fold_unique :
  forall g : list I -> T,
    g [] = t0 ->
    (forall l i, g (l ++ [i]) = tstep (g l) i) ->
    forall l, g l = nec_f_fold l.
Proof.
  intros g H0 Hs l. induction l as [| l i IH] using rev_ind.
  - exact H0.
  - rewrite Hs, IH. unfold nec_f_fold. rewrite fold_left_app. reflexivity.
Qed.

(** The price of a list is the one function on lists that adds up over
    appends and agrees with the price list on single moves. *)
Theorem nec_f_additive_is_price :
  forall (c : I -> nat) (g : list I -> nat),
    (forall l l', g (l ++ l') = g l + g l') ->
    (forall i, g [i] = c i) ->
    forall l, g l = fold_right (fun i acc => c i + acc) 0 l.
Proof.
  intros c g Hadd H1 l.
  assert (H0 : g [] = 0) by (pose proof (Hadd [] []) as E; simpl in E; lia).
  induction l as [| i l IH]; simpl; [exact H0 |].
  rewrite <- IH, <- H1. change (i :: l) with ([i] ++ l). apply Hadd.
Qed.

Variable S : Type.
Variable apply : S -> I -> S.
Variable s0 : S.

Definition nec_f_src (l : list I) : S := fold_left apply l s0.

(** Descent: lists that leave the source in the same state leave the target
    in the same state. *)
Definition nec_f_descent : Prop :=
  forall l l', nec_f_src l = nec_f_src l' -> nec_f_fold l = nec_f_fold l'.

(** The relation "some list leads to this state here and to that state there". *)
Definition nec_f_descends (s : S) (t : T) : Prop :=
  exists l, nec_f_src l = s /\ nec_f_fold l = t.

(** A map from states through which the fold factors gives descent. *)
Theorem nec_f_factor_gives_descent :
  (exists h : S -> T, forall l, h (nec_f_src l) = nec_f_fold l) -> nec_f_descent.
Proof.
  intros [h Hh] l l' E. rewrite <- (Hh l), <- (Hh l'), E. reflexivity.
Qed.

(** Descent holds exactly when the relation is a function on the reachable
    states: each reachable state goes to one target state. *)
Theorem nec_f_descent_iff_functional :
  nec_f_descent <-> (forall s t t', nec_f_descends s t -> nec_f_descends s t' -> t = t').
Proof.
  split.
  - intros D s t t' [l [Hl Ht]] [l' [Hl' Ht']]. subst. apply D. congruence.
  - intros F l l' E. apply (F (nec_f_src l)); [exists l | exists l']; split; auto.
Qed.

End Fold.

(** A toll does not force descent. The source is the bit with a paid SET and
    a free RESET, which meets A2; the target keeps its whole history, which
    obeys any toll. SET and RESET, SET leave the bit in the same state and the
    history in two. *)
Theorem nec_f_descent_fails_for_history :
  CostSemanticsComparison.a2 bool NecFBitOp nec_f_bit_step nec_f_bit_cost (fun b => b) /\
  ~ nec_f_descent NecFBitOp (list NecFBitOp) (fun h i => i :: h) [] bool nec_f_bit_step false.
Proof.
  split; [exact nec_f_bit_a2 |].
  intro D. specialize (D [NecFSet] [NecFReset; NecFSet] eq_refl).
  unfold nec_f_fold in D. simpl in D. discriminate.
Qed.

(** * The potential method, at its limit *)

Section Potential.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cost : I -> nat.

Notation run := (CostSemanticsComparison.run S I step).
Notation total := (CostSemanticsComparison.total I cost).

(** The potential bound for every run holds exactly when every step has
    non-negative amortized cost. *)
Theorem nec_f_potential_bound_iff :
  forall Phi : S -> nat,
    amortized_nonneg S I step cost Phi <-> (forall t s, total t + Phi (run t s) >= Phi s).
Proof.
  intro Phi. split.
  - apply potential_telescoping.
  - intros H s i. specialize (H [i] s). simpl in H. lia.
Qed.

Fixpoint nec_f_zero_amortized (Phi : S -> nat) (t : list I) (s : S) : Prop :=
  match t with
  | [] => True
  | i :: t' => cost i + Phi (step s i) = Phi s /\ nec_f_zero_amortized Phi t' (step s i)
  end.

(** Equality holds along a run whose every step has zero amortized cost. *)
Theorem nec_f_potential_bound_exact :
  forall Phi t s, nec_f_zero_amortized Phi t s -> total t + Phi (run t s) = Phi s.
Proof.
  intros Phi t. induction t as [| i t IH]; intros s H; simpl in *; [lia |].
  destruct H as [H1 H2]. specialize (IH _ H2). lia.
Qed.

End Potential.

(** The potential bound and its corollary "at least 1 - 0 = 1" are attained:
    one SET of the bit, from no, under the certification potential. *)
Theorem nec_f_potential_one_attained :
  nec_f_zero_amortized bool NecFBitOp nec_f_bit_step nec_f_bit_cost
    (cert_potential bool (fun b => b)) [NecFSet] false /\
  CostSemanticsComparison.total NecFBitOp nec_f_bit_cost [NecFSet] = 1.
Proof. split; [split; [reflexivity | exact I] | reflexivity]. Qed.

Print Assumptions nec_f_conservation.
Print Assumptions nec_f_counter_monotone.
Print Assumptions nec_f_initiality_reachable_rule.
Print Assumptions nec_f_initiality.
Print Assumptions nec_f_initiality_iff.
Print Assumptions nec_f_conservation_iff_rule.
Print Assumptions nec_f_finite_counter_charges_nothing.
Print Assumptions nec_f_initiality_needs_zero_start.
Print Assumptions nec_f_initiality_needs_reachable.
Print Assumptions nec_f_fold_unique.
Print Assumptions nec_f_additive_is_price.
Print Assumptions nec_f_factor_gives_descent.
Print Assumptions nec_f_descent_iff_functional.
Print Assumptions nec_f_descent_fails_for_history.
Print Assumptions nec_f_potential_bound_iff.
Print Assumptions nec_f_potential_bound_exact.
Print Assumptions nec_f_potential_one_attained.
