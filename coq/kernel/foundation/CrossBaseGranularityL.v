(** An executable L base for the cross-base comparison.

    [LRecursion.step] is a relation, while [BaseMachine] needs a total next
    function. L's weak call-by-value step is decidable, so it is computed by
    a structural function, proved equal to the relation, and totalized by
    stuttering on terms that do not step. No choice principle is used. *)

From Coq Require Import Arith.PeanoNat.
From Kernel Require Import StructuralCoreAnyBase StructuralRecordAxis CrossBaseGranularityCore LRecursion.

(** * The step relation as a function *)

Fixpoint l_step_fun (s : term) : option term :=
  match s with
  | app s1 s2 =>
      match l_step_fun s1 with
      | Some s1' => Some (app s1' s2)
      | None =>
          match s1 with
          | lam b =>
              match s2 with
              | lam _ => Some (subst b 0 s2)
              | _ =>
                  match l_step_fun s2 with
                  | Some s2' => Some (app s1 s2')
                  | None => None
                  end
              end
          | _ => None
          end
      end
  | _ => None
  end.

Lemma l_step_fun_value : forall b, l_step_fun (lam b) = None.
Proof. reflexivity. Qed.

Theorem l_step_fun_sound : forall s t, l_step_fun s = Some t -> step s t.
Proof.
  induction s as [n | s1 IH1 s2 IH2 | b IHb]; intros t H; simpl in H;
    try discriminate.
  destruct (l_step_fun s1) as [s1' |] eqn:E1.
  - inversion H; subst. apply stepL. exact (IH1 _ eq_refl).
  - destruct s1 as [n | u1 u2 | b]; try discriminate.
    destruct s2 as [m | v1 v2 | c].
    + discriminate.
    + destruct (l_step_fun (app v1 v2)) as [s2' |] eqn:E2; try discriminate.
      inversion H; subst. apply stepR.
      * exists b. reflexivity.
      * exact (IH2 _ eq_refl).
    + inversion H; subst. apply stepBeta. exists c. reflexivity.
Qed.

Theorem l_step_fun_complete : forall s t, step s t -> l_step_fun s = Some t.
Proof.
  intros s t H. induction H as [b v Hv | s s' t Hs IH | v t t' Hv Ht IH].
  - destruct Hv as [c ->]. reflexivity.
  - simpl. rewrite IH. reflexivity.
  - destruct Hv as [b ->]. simpl.
    destruct t as [n | t1 t2 | c].
    + inversion Ht.
    + rewrite IH. reflexivity.
    + exfalso. exact (value_no_step (lam c) t' (ex_intro _ c eq_refl) Ht).
Qed.

Theorem l_step_fun_correct : forall s t, step s t <-> l_step_fun s = Some t.
Proof.
  split; [apply l_step_fun_complete | apply l_step_fun_sound].
Qed.

(** * The base *)

Definition l_next (s : term) : term :=
  match l_step_fun s with
  | Some t => t
  | None => s
  end.

Definition l_base : BaseMachine := {|
  b_state := term;
  b_next := l_next;
  b_init := fun _ => True;
  b_halted := fun s => l_step_fun s = None
|}.

(** Every L step is one base step. *)
Theorem l_base_next_is_step : forall s t, step s t -> b_next l_base s = t.
Proof.
  intros s t H. simpl. unfold l_next.
  rewrite (l_step_fun_complete _ _ H). reflexivity.
Qed.

(** The base halts exactly on the terms L cannot reduce. *)
Theorem l_base_halted_iff_irreducible :
  forall s, b_halted l_base s <-> forall t, ~ step s t.
Proof.
  intro s. simpl. split.
  - intros Hnone t Hstep.
    rewrite (l_step_fun_complete _ _ Hstep) in Hnone. discriminate.
  - intros Hirr. destruct (l_step_fun s) as [t |] eqn:E; [| reflexivity].
    exfalso. exact (Hirr t (l_step_fun_sound _ _ E)).
Qed.

(** A base step from a reducible term is the L step; from an irreducible
    term it stutters. *)
Theorem l_base_next_cases : forall s,
  step s (b_next l_base s) \/
  ((forall t, ~ step s t) /\ b_next l_base s = s).
Proof.
  intro s. simpl. unfold l_next.
  destruct (l_step_fun s) as [t |] eqn:E.
  - left. exact (l_step_fun_sound _ _ E).
  - right. split; [| reflexivity].
    intros t Hstep. rewrite (l_step_fun_complete _ _ Hstep) in E. discriminate.
Qed.

(** Running the base for any number of steps is an L reduction sequence. *)
Theorem l_base_run_is_star : forall n s, star s (base_run l_base n s).
Proof.
  induction n as [| n IH]; intro s; [apply star_refl |].
  unfold base_run in *. rewrite Nat.iter_succ_r.
  destruct (l_base_next_cases s) as [Hstep | [_ Hstay]].
  - eapply star_step; [exact Hstep | apply IH].
  - rewrite Hstay. apply IH.
Qed.

(** Every L reduction sequence is reached by running the base. *)
Theorem star_is_l_base_run : forall s t, star s t -> exists n, base_run l_base n s = t.
Proof.
  intros s t H. induction H as [s | s t u Hst Hstar IH].
  - exists 0. reflexivity.
  - destruct IH as [n Hn]. exists (S n).
    unfold base_run in *. rewrite Nat.iter_succ_r.
    rewrite (l_base_next_is_step _ _ Hst). exact Hn.
Qed.

(** The record axis is a latch on the L base, by the same base-parametric
    theorem used for the TM base. *)
Theorem record_axis_is_latch_on_l_holds : record_axis_is_latch_on l_base.
Proof.
  intros M C Hhonest.
  exact (record_axis_is_latch_holds M _ C Hhonest).
Qed.

Print Assumptions l_step_fun_correct.
Print Assumptions l_base_halted_iff_irreducible.
Print Assumptions l_base_run_is_star.
Print Assumptions star_is_l_base_run.
Print Assumptions record_axis_is_latch_on_l_holds.
