(** LiftModels: concrete bases, and the limit of one counter.

    1. Two concrete universal bases lift to Thiele-complete machines with the
       earned layer of LiftCore.v (cap 16, as in the repository):
         lift_ex_thiele_complete    the machine on numbers of LiftExec.v;
         lift_ram_thiele_complete   the Cook-Reckhow RAM of LiftRAM.v.
    2. The step of the machine on numbers is computable in the lambda calculus
       L and in the vendored Minsky machines with arithmetic (MMA)
       [lift_ex_in_L, lift_ex_in_MMA]; see LiftModelsAll.v for the other models.
    3. Two-counter halting is not reducible to one-counter halting
       [lift_no_oc_translation]: a translation of two-counter instances into
       one-counter instances that preserves halting would make the complement
       of Turing-machine halting enumerable, which is what undecidability means
       in the vendored library (Forster, Kirst, Smolka).  This is the content
       of "two counters is the fewest": one counter has decidable halting
       (LiftOneCounter.v), two have undecidable halting.                      *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Coq Require Import Relations.Relation_Operators Relations.Operators_Properties.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.TM Require Import SBTM.
From Undecidability.MinskyMachines Require Import MM2 MM2_undec MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
From Undecidability.L Require Import L.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.
From Minimal Require Import LiftCore LiftOneCounter.
From Kernel Require Import LiftExec LiftRAM.

(** * Two concrete bases lift *)

Theorem lift_ex_thiele_complete :
  T.thiele_complete (lift_machine lift_ex_machine (lift_window_lang lift_ex_machine lift_ex_base) 16).
Proof. apply lift_window_thiele_complete. lia. Qed.

Theorem lift_ram_thiele_complete :
  T.thiele_complete (lift_machine lift_ram_machine (lift_window_lang lift_ram_machine lift_ram_base) 16).
Proof. apply lift_window_thiele_complete. lia. Qed.

(** * The step of the machine on numbers is computable in L and in MMA *)

Theorem lift_ex_in_L : L_computable lift_ex_rel.
Proof. exact lift_ex_L_computable. Qed.

Theorem lift_ex_in_MMA : MMA_computable lift_ex_rel.
Proof. apply L_computable_to_MMA_computable. exact lift_ex_L_computable. Qed.

(** * The vendored two-counter machine is the machine of ThieleComplete.v *)

Definition lift_to_cm (i : mm2_instr) : T.cm_instr :=
  match i with
  | mm2_inc_a => T.CINC T.RA
  | mm2_inc_b => T.CINC T.RB
  | mm2_dec_a j => T.CDEC T.RA j
  | mm2_dec_b j => T.CDEC T.RB j
  end.

Definition lift_mm2_fetch (P : list mm2_instr) (n : nat) : option mm2_instr :=
  match n with 0 => None | S m => nth_error P m end.

Lemma lift_mm2_instr_at_cm : forall (r : mm2_instr) i P,
  mm2_instr_at r i P <-> lift_mm2_fetch P i = Some r.
Proof.
  intros r i P. split.
  - intros [l [rest [-> <-]]]. simpl.
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  - destruct i as [| i]; simpl; [discriminate |]. intro H.
    destruct (nth_error_split P i H) as [l [rest [-> Hl]]].
    exists l, rest. split; [reflexivity | lia].
Qed.

Lemma lift_cm_fetch_map : forall P i,
  T.cm_fetch (map lift_to_cm P) i = match lift_mm2_fetch P i with Some r => Some (lift_to_cm r) | None => None end.
Proof.
  intros P [| i]; [reflexivity |]. simpl. rewrite nth_error_map.
  destruct (nth_error P i); reflexivity.
Qed.

Lemma lift_mm2_step_cm : forall P x y,
  mm2_step P x y <-> T.cm_step (map lift_to_cm P) x = Some y.
Proof.
  intros P [i [a b]] y. unfold mm2_step, T.cm_step. simpl.
  rewrite lift_cm_fetch_map. split.
  - intros [r [Hat Hr]]. apply lift_mm2_instr_at_cm in Hat. simpl in Hat.
    rewrite Hat. inversion Hr; subst; reflexivity.
  - destruct (lift_mm2_fetch P i) as [r |] eqn:Hf; simpl; [| discriminate].
    intro H. exists r. split; [apply lift_mm2_instr_at_cm; exact Hf |].
    destruct r; simpl in H;
      [ | | destruct a | destruct b]; injection H as <-; constructor.
Qed.

Lemma lift_mm2_stop_cm : forall P x, mm2_stop P x <-> T.cm_step (map lift_to_cm P) x = None.
Proof.
  intros P x. unfold mm2_stop. split.
  - intro H. destruct (T.cm_step (map lift_to_cm P) x) as [y |] eqn:Hm; [| reflexivity].
    exfalso. apply (H y). apply lift_mm2_step_cm. exact Hm.
  - intros H y Hs. apply lift_mm2_step_cm in Hs. congruence.
Qed.

Lemma lift_mm2_terminates_cm : forall P x,
  mm2_terminates P x <->
  exists n, T.cm_step (map lift_to_cm P) (T.cm_run n (map lift_to_cm P) x) = None.
Proof.
  intros P x. unfold mm2_terminates. split.
  - intros [z [Hrt Hstop]]. apply clos_rt_rt1n_iff in Hrt.
    induction Hrt as [x | x y z Hs _ IH].
    + exists 0. simpl. apply lift_mm2_stop_cm. exact Hstop.
    + destruct (IH Hstop) as [n Hn]. exists (S n). simpl.
      apply lift_mm2_step_cm in Hs. unfold T.cm_run in *. simpl in *.
      replace (T.cm_step (map lift_to_cm P) x) with (Some y) by (symmetry; exact Hs).
      exact Hn.
  - intros [n Hn]. revert x Hn. induction n as [| n IH]; intros x Hn; simpl in Hn.
    + exists x. split; [apply rt_refl | apply lift_mm2_stop_cm; exact Hn].
    + simpl in Hn. destruct (T.cm_step (map lift_to_cm P) x) as [y |] eqn:Hm.
      * destruct (IH y Hn) as [z [Hrt Hstop]]. exists z. split; [| exact Hstop].
        apply rt_trans with y; [apply rt_step, lift_mm2_step_cm; exact Hm | exact Hrt].
      * exists x. split; [apply rt_refl | apply lift_mm2_stop_cm; exact Hm].
Qed.

(** Halting of the machine of ThieleComplete.v, as a problem on programs. *)
Definition lift_CM_HALTING (q : list T.cm_instr * nat * nat) : Prop :=
  let '(P, a, b) := q in
  exists n, T.cm_step P (T.cm_run n P (1, (a, b))) = None.

Theorem lift_mm2_halting_cm : forall P a b,
  MM2_HALTING (P, a, b) <-> lift_CM_HALTING (map lift_to_cm P, a, b).
Proof. intros P a b. simpl. apply lift_mm2_terminates_cm. Qed.

Theorem lift_cm_halting_undecidable : undecidable lift_CM_HALTING.
Proof.
  apply (undecidability_from_reducibility MM2_HALTING_undec).
  exists (fun q => let '(P, a, b) := q in (map lift_to_cm P, a, b)).
  intros [[P a] b]. apply lift_mm2_halting_cm.
Qed.

(** * One counter is not enough *)

(** No translation of two-counter instances into one-counter instances
    preserves halting: it would decide two-counter halting, and the vendored
    library's undecidability of two-counter halting would then make the
    complement of Turing-machine halting enumerable. *)
Theorem lift_no_oc_translation : forall (tr : list T.cm_instr * nat * nat -> list lift_oc_instr * lift_oc_conf),
  (forall q, lift_CM_HALTING q <-> lift_oc_halts (fst (tr q)) (snd (tr q))) ->
  decidable lift_CM_HALTING.
Proof.
  intros tr H. exists (fun q => if lift_oc_halts_dec (fst (tr q)) (snd (tr q)) then true else false).
  intro q. unfold reflects. destruct (lift_oc_halts_dec (fst (tr q)) (snd (tr q))) as [h | nh].
  - split; [intros _; reflexivity | intros _; apply H; exact h].
  - split; [intro c; exfalso; apply nh; apply H; exact c | intro e; discriminate].
Qed.

Corollary lift_no_oc_translation_undecidability : forall (tr : list T.cm_instr * nat * nat -> list lift_oc_instr * lift_oc_conf),
  (forall q, lift_CM_HALTING q <-> lift_oc_halts (fst (tr q)) (snd (tr q))) ->
  enumerable (complement SBTM_HALT).
Proof.
  intros tr H. exact (lift_cm_halting_undecidable (@lift_no_oc_translation tr H)).
Qed.

Print Assumptions lift_ex_thiele_complete.
Print Assumptions lift_ram_thiele_complete.
Print Assumptions lift_ex_in_MMA.
Print Assumptions lift_cm_halting_undecidable.
Print Assumptions lift_no_oc_translation_undecidability.
