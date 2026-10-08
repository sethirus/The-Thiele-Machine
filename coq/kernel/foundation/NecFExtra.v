(** NecFExtra: the eight-state machine's prices, undoing a move that merges
    nothing, and why the small machine sits outside the finite theorems.

    - The eight-state machine's price list (stamp 1, jump 2, next 0) is the
      least that meets the halving price: every halving-priced cost charges
      at least as much on every move ([nec_f_fin_cost_minimal]). Merge
      pricing alone forces only one for the jump
      ([nec_f_fin_merge_pricing_jump_one]); the second unit comes from the
      four-fold squeeze.
    - On a finite set a move that merges nothing can be undone
      ([nec_f_finite_injective_undoable]).
    - The small machine has infinitely many states
      ([nec_f_small_machine_infinite]); with its free merge
      (frag_small_dec_free_merge) it misses both premises of the finite
      theorems, as the book says. *)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Logic.FinFun.
Import ListNotations.
Require Minimal.EarnedCore.
From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import FiniteCertMachine.

Module E := Minimal.EarnedCore.

(** * The eight-state machine's prices are the least halving prices *)

Theorem nec_f_fin_cost_minimal :
  forall cost : FInstr -> nat,
    compression_priced fstep cost fstate_eq_dec -> forall i, fcost i <= cost i.
Proof.
  intros cost Hp i. destruct i as [| a |]; simpl.
  - pose proof (Hp FCertify [(L0, false); (L0, true)]) as H.
    assert (Hnd : NoDup [(L0, false); (L0, true)])
      by (repeat constructor; simpl; intuition discriminate).
    specialize (H Hnd). unfold image_size in H. vm_compute in H.
    destruct (cost FCertify); [simpl in H; lia | lia].
  - pose proof (Hp (FJump a) [(L0, false); (L1, false); (L2, false); (L3, false)]) as H.
    assert (Hnd : NoDup [(L0, false); (L1, false); (L2, false); (L3, false)])
      by (repeat constructor; simpl; intuition discriminate).
    specialize (H Hnd). unfold image_size in H.
    destruct a; vm_compute in H;
      (destruct (cost (FJump _)) as [| [| c]]; simpl in H; lia).
  - lia.
Qed.

(** Merge pricing alone is met with the jump at one. *)
Definition nec_f_fin_cost_jump_one (i : FInstr) : nat :=
  match i with FCertify => 1 | FJump _ => 1 | FNext => 0 end.

Theorem nec_f_fin_merge_pricing_jump_one :
  merging_steps_priced fstep nec_f_fin_cost_jump_one /\
  ~ compression_priced fstep nec_f_fin_cost_jump_one fstate_eq_dec.
Proof.
  split.
  - intros i Hm. destruct i; simpl; [lia | lia | exfalso; exact (Hm fnext_injective)].
  - intro H. pose proof (nec_f_fin_cost_minimal _ H (FJump L0)). simpl in *. lia.
Qed.

(** * On a finite set, a move that merges nothing can be undone *)

Theorem nec_f_finite_injective_undoable :
  forall (S I : Type) (step : S -> I -> S) (eq_dec : forall a b : S, {a = b} + {a <> b})
         (all : list S) (i : I),
    finite_states all -> step_injective step i ->
    exists g : S -> S, (forall x, g (step x i) = x) /\ (forall y, step (g y) i = y).
Proof.
  intros S I step eq_dec all i [Hnd Hall] Hinj.
  assert (Hsurj : forall y, exists x, In x all /\ step x i = y).
  { assert (HndM : NoDup (map (fun x => step x i) all)).
    { apply Injective_map_NoDup; [intros a b E; exact (Hinj a b E) | exact Hnd]. }
    assert (Hback : incl all (map (fun x => step x i) all)).
    { apply NoDup_length_incl; [exact HndM | rewrite map_length; lia | intros y _; apply Hall]. }
    intro y. pose proof (Hback y (Hall y)) as Hy. apply in_map_iff in Hy as [x [E Hx]].
    exists x. split; assumption. }
  set (hit := fun y x => if eq_dec (step x i) y then true else false).
  exists (fun y => match find (hit y) all with Some x => x | None => y end).
  assert (Hfound : forall y, step (match find (hit y) all with Some x => x | None => y end) i = y).
  { intro y. destruct (find (hit y) all) as [x |] eqn:Hf.
    - apply find_some in Hf as [_ Hh]. unfold hit in Hh.
      destruct (eq_dec (step x i) y); [assumption | discriminate].
    - exfalso. destruct (Hsurj y) as [x [Hx E]].
      pose proof (find_none _ _ Hf x Hx) as Hh. unfold hit in Hh.
      destruct (eq_dec (step x i) y); [discriminate | contradiction]. }
  split; [| exact Hfound].
  intro x. apply Hinj. apply Hfound.
Qed.

(** * The small machine has infinitely many states *)

Theorem nec_f_small_machine_infinite : ~ exists all : list E.state, forall s, In s all.
Proof.
  intros [all Hall].
  set (M := list_max (map E.mu all)).
  assert (HM : Forall (fun k => k <= M) (map E.mu all)) by (apply list_max_le; lia).
  set (s := E.mkst (E.start_core 0 0) (S M) false).
  rewrite Forall_forall in HM.
  specialize (HM (E.mu s) (in_map E.mu all s (Hall s))). simpl in HM. lia.
Qed.

Print Assumptions nec_f_fin_cost_minimal.
Print Assumptions nec_f_fin_merge_pricing_jump_one.
Print Assumptions nec_f_finite_injective_undoable.
Print Assumptions nec_f_small_machine_infinite.
