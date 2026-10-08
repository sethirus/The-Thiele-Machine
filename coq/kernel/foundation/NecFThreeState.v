(** NecFThreeState: requirements that name no reading don't pick out the
    toll; a requirement that names the record does.

    Three states, blank, once and twice, with once and twice reading yes. The
    flip takes blank to once and leaves the other two where they are; the
    smooth takes once and twice to twice and leaves blank alone. A bill
    charges each step: a whole number for a move taken at a state, and a run
    costs the sum of its steps' charges.

    - Six requirements that name no reading: no charge on a step that changes
      nothing; none on a move that forgets nothing; the same bill under every
      renaming of the states that respects the moves; a total that adds up
      along a run (the run cost is that sum, by definition); a charge that
      looks only at the step, the state before and the state after; and one
      mark on the flip from blank ([nec_f_three_reading_free]).
    - The toll, the bill that charges the flip from blank and nothing else,
      meets all six, and so does the price on merging, which charges the
      smooth from once as well ([nec_f_three_toll_meets],
      [nec_f_three_merge_meets]); they differ on the smooth
      ([nec_f_three_bills_differ]).
    - The only renaming of the states that respects the moves is the identity
      ([nec_f_three_automorphism_id]), so the renaming requirement constrains
      nothing here.
    - On any machine, a bill that charges every raise at least one and whose
      total over every run is at most the number of raises is exactly one mark
      per raise and nothing else ([nec_f_record_ceiling_unique]). On the three
      states that bill is the toll, and the price on merging fails the ceiling
      ([nec_f_three_ceiling_picks_toll], [nec_f_three_merge_fails_ceiling]).
    - Priced per move, flip one mark and smooth free, the three states are a
      certification system, and its universal floor holds
      ([nec_f_three_cs_floor]). *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.
From Kernel Require Import UniversalCertificationCost.

(** * Any machine: the ceiling and the floor fix the bill *)

Section Ceiling.

Variables (S M : Type).
Variable step : S -> M -> S.
Variable read : S -> bool.

Definition nec_f_raise (s : S) (m : M) : nat :=
  if negb (read s) && read (step s m) then 1 else 0.

Fixpoint nec_f_total (c : S -> M -> nat) (s : S) (tr : list M) : nat :=
  match tr with [] => 0 | m :: rest => c s m + nec_f_total c (step s m) rest end.

Fixpoint nec_f_raises (s : S) (tr : list M) : nat :=
  match tr with [] => 0 | m :: rest => nec_f_raise s m + nec_f_raises (step s m) rest end.

Theorem nec_f_record_ceiling_unique : forall c : S -> M -> nat,
  (forall s m, read s = false -> read (step s m) = true -> c s m >= 1) ->
  (forall s tr, nec_f_total c s tr <= nec_f_raises s tr) ->
  forall s m, c s m = nec_f_raise s m.
Proof.
  intros c Hfloor Hceil s m. pose proof (Hceil s [m]) as H. simpl in H.
  unfold nec_f_raise in *.
  destruct (read s) eqn:Es; destruct (read (step s m)) eqn:Et; simpl in *; try lia.
  pose proof (Hfloor s m Es Et). lia.
Qed.

End Ceiling.

(** * The three states *)

Inductive nec_f_st : Type := Blank | Once | Twice.
Inductive nec_f_mv : Type := Flip | Smooth.

Definition nec_f_step (s : nec_f_st) (m : nec_f_mv) : nec_f_st :=
  match m, s with
  | Flip, Blank => Once
  | Flip, s => s
  | Smooth, Blank => Blank
  | Smooth, _ => Twice
  end.

Definition nec_f_read (s : nec_f_st) : bool := match s with Blank => false | _ => true end.

Definition nec_f_toll (s : nec_f_st) (m : nec_f_mv) : nat :=
  match m, s with Flip, Blank => 1 | _, _ => 0 end.

Definition nec_f_merge_price (s : nec_f_st) (m : nec_f_mv) : nat :=
  match m, s with Flip, Blank => 1 | Smooth, Once => 1 | _, _ => 0 end.

Definition nec_f_injective_move (m : nec_f_mv) : Prop :=
  forall a b, nec_f_step a m = nec_f_step b m -> a = b.

Definition nec_f_automorphism (phi : nec_f_st -> nec_f_st) : Prop :=
  (forall a b, phi a = phi b -> a = b) /\
  (forall s m, phi (nec_f_step s m) = nec_f_step (phi s) m).

(** The six requirements that name no reading. *)
Definition nec_f_three_reading_free (c : nec_f_st -> nec_f_mv -> nat) : Prop :=
  (forall s m, nec_f_step s m = s -> c s m = 0) /\
  (forall m, nec_f_injective_move m -> forall s, c s m = 0) /\
  (forall phi, nec_f_automorphism phi -> forall s m, c (phi s) m = c s m) /\
  (forall s tr1 tr2, nec_f_total _ _ nec_f_step c s (tr1 ++ tr2) =
     nec_f_total _ _ nec_f_step c s tr1 +
     nec_f_total _ _ nec_f_step c (fold_left nec_f_step tr1 s) tr2) /\
  (exists g, forall s m, c s m = g s (nec_f_step s m)) /\
  c Blank Flip = 1.

Lemma nec_f_three_both_merge : forall m, ~ nec_f_injective_move m.
Proof.
  intros [] H.
  - specialize (H Blank Once eq_refl). discriminate.
  - specialize (H Once Twice eq_refl). discriminate.
Qed.

Theorem nec_f_three_automorphism_id : forall phi, nec_f_automorphism phi -> forall s, phi s = s.
Proof.
  intros phi [Hinj Hcom].
  assert (HT : phi Twice = Twice).
  { pose proof (Hcom Twice Smooth) as H1. pose proof (Hcom Twice Flip) as H2. simpl in H1, H2.
    destruct (phi Twice); simpl in *; congruence. }
  assert (HO : phi Once = Once).
  { pose proof (Hcom Once Flip) as H1. simpl in H1.
    destruct (phi Once) eqn:E; simpl in *; try congruence.
    exfalso. rewrite <- HT in E. apply Hinj in E. discriminate. }
  assert (HB : phi Blank = Blank).
  { destruct (phi Blank) eqn:E; [reflexivity | |].
    - rewrite <- HO in E. apply Hinj in E. discriminate.
    - rewrite <- HT in E. apply Hinj in E. discriminate. }
  intros []; assumption.
Qed.

Lemma nec_f_three_total_app : forall c s tr1 tr2,
  nec_f_total _ _ nec_f_step c s (tr1 ++ tr2) =
  nec_f_total _ _ nec_f_step c s tr1 + nec_f_total _ _ nec_f_step c (fold_left nec_f_step tr1 s) tr2.
Proof.
  intros c s tr1. revert s. induction tr1 as [| m tr1 IH]; intros s tr2; simpl; [reflexivity |].
  rewrite IH. lia.
Qed.

Lemma nec_f_three_common : forall c,
  (forall s m, nec_f_step s m = s -> c s m = 0) ->
  (exists g, forall s m, c s m = g s (nec_f_step s m)) ->
  c Blank Flip = 1 ->
  nec_f_three_reading_free c.
Proof.
  intros c H1 H5 H6. split; [exact H1 | split; [| split; [| split; [| split; [exact H5 | exact H6]]]]].
  - intros m Hinj. exfalso. exact (nec_f_three_both_merge m Hinj).
  - intros phi Hphi s m. rewrite (nec_f_three_automorphism_id phi Hphi s). reflexivity.
  - apply nec_f_three_total_app.
Qed.

Theorem nec_f_three_toll_meets : nec_f_three_reading_free nec_f_toll.
Proof.
  apply nec_f_three_common.
  - intros [] []; simpl; congruence.
  - exists (fun a b => match a, b with Blank, Once => 1 | _, _ => 0 end).
    intros [] []; reflexivity.
  - reflexivity.
Qed.

Theorem nec_f_three_merge_meets : nec_f_three_reading_free nec_f_merge_price.
Proof.
  apply nec_f_three_common.
  - intros [] []; simpl; congruence.
  - exists (fun a b => match a, b with Blank, Once => 1 | Once, Twice => 1 | _, _ => 0 end).
    intros [] []; reflexivity.
  - reflexivity.
Qed.

Theorem nec_f_three_bills_differ : nec_f_toll Once Smooth <> nec_f_merge_price Once Smooth.
Proof. discriminate. Qed.

Theorem nec_f_three_ceiling_picks_toll : forall c : nec_f_st -> nec_f_mv -> nat,
  (forall s m, nec_f_read s = false -> nec_f_read (nec_f_step s m) = true -> c s m >= 1) ->
  (forall s tr, nec_f_total _ _ nec_f_step c s tr <= nec_f_raises _ _ nec_f_step nec_f_read s tr) ->
  forall s m, c s m = nec_f_toll s m.
Proof.
  intros c Hf Hc s m. rewrite (nec_f_record_ceiling_unique _ _ nec_f_step nec_f_read c Hf Hc s m).
  destruct s, m; reflexivity.
Qed.

Theorem nec_f_three_merge_fails_ceiling :
  ~ (forall s tr, nec_f_total _ _ nec_f_step nec_f_merge_price s tr <=
                  nec_f_raises _ _ nec_f_step nec_f_read s tr).
Proof. intro H. specialize (H Once [Smooth]). simpl in H. lia. Qed.

(** * The three states as a certification system *)

(** Priced per move, the toll charges the flip one mark and the smooth
    nothing; only the flip from blank raises the reading, so this is a
    certification system, and its universal floor applies: every run from
    blank to a yes-state costs at least one ([nec_f_three_cs_floor]). *)
Definition nec_f_move_toll (m : nec_f_mv) : nat := match m with Flip => 1 | Smooth => 0 end.

Lemma nec_f_three_cs_costs : forall s m,
  nec_f_read s = false -> nec_f_read (nec_f_step s m) = true -> nec_f_move_toll m >= 1.
Proof. intros [] []; simpl; intros; try discriminate; lia. Qed.

Definition nec_f_three_cs : CertificationSystem :=
  mk_cert_system nec_f_st nec_f_mv nec_f_step nec_f_move_toll nec_f_read nec_f_three_cs_costs.

Theorem nec_f_three_cs_floor : forall tr,
  nec_f_read (cs_run nec_f_three_cs tr Blank) = true ->
  cs_total_cost nec_f_three_cs tr >= 1.
Proof.
  intros tr H. exact (universal_nfi_any_substrate nec_f_three_cs tr Blank eq_refl H).
Qed.

Print Assumptions nec_f_three_cs_floor.
Print Assumptions nec_f_record_ceiling_unique.
Print Assumptions nec_f_three_automorphism_id.
Print Assumptions nec_f_three_toll_meets.
Print Assumptions nec_f_three_merge_meets.
Print Assumptions nec_f_three_bills_differ.
Print Assumptions nec_f_three_ceiling_picks_toll.
Print Assumptions nec_f_three_merge_fails_ceiling.
