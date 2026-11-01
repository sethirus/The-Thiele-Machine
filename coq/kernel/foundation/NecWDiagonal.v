(** NecWDiagonal: the "no inside decider" theorem pushed to its limits.

    Each hypothesis of [structural_shortcut_undecidable] is needed:

    - Both witnesses. In the repository's own nat substrate, a constant
      predicate (true everywhere, or false everywhere) has a correct
      decider whose flip is representable.
    - The representability of the flip. On a substrate where nothing is
      representable (so the recursion field holds vacuously), a predicate
      with both witnesses and extensional is decided by the identity.
    - Extensionality. On a substrate where every two programs are
      equivalent and every transformer is representable, the predicate
      "the program is true" has both witnesses, is not extensional, and is
      decided by the identity with a representable flip.
    - The recursion theorem. The Substrate class bundles it, so it cannot
      be dropped inside the class; on the same data as the second case,
      with every transformer representable, the recursion statement fails
      and the identity decides an extensional predicate with both
      witnesses.

    The nat family: every d is wrong at program 2, and one d is right at
    every other program, so exactly one error is unavoidable. *)

From Coq Require Import Arith.PeanoNat Lia Bool.
From Kernel Require Import Substrate StructuralUndecidability NatSubstrateInstance.

(* ================================================================= *)
(** * 1. Both witnesses are needed                                    *)
(* ================================================================= *)

(** A predicate true of every program: decided, with a representable flip,
    in the nat substrate of the constant-true parameter. *)
Theorem nec_w_constant_true_predicate_decided : forall Pi : nat -> Prop,
  (forall p, Pi p) ->
  exists decide : nat -> bool,
    @Representable (nat_substrate (fun _ => true))
      (fun p => if decide p then 1 else 0) /\
    (forall p1 p2, @prog_equiv (nat_substrate (fun _ => true)) p1 p2 ->
       (Pi p1 <-> Pi p2)) /\
    forall p, decide p = true <-> Pi p.
Proof.
  intros Pi HPi.
  (* SAFE: the predicate holds of every program on purpose; the constant decider is the intended witness. *)
  exists (fun _ => true). split; [| split].
  - intros p. reflexivity.
  - intros p1 p2 _. split; intros _; apply HPi.
  - intros p. split; intros _; [apply HPi | reflexivity].
Qed.

(** A predicate false of every program: decided, with a representable
    flip, in the nat substrate of the constant-false parameter. *)
Theorem nec_w_constant_false_predicate_decided :
  exists decide : nat -> bool,
    @Representable (nat_substrate (fun _ => false))
      (fun p => if decide p then 1 else 0) /\
    forall p, decide p = true <-> False.
Proof.
  (* SAFE: the predicate fails of every program on purpose; the constant decider is the intended witness. *)
  exists (fun _ => false). split.
  - intros p. reflexivity.
  - intros p. split; [discriminate | contradiction].
Qed.

(* ================================================================= *)
(** * 2. The representable flip is needed                             *)
(* ================================================================= *)

Definition nec_w_brun (p s : bool) : option bool := if p then Some s else None.

(** A substrate on which nothing is representable. *)
Definition nec_w_norep_sub : Substrate.
Proof.
  refine (Build_Substrate bool bool nec_w_brun (fun _ => 0) (fun _ _ _ => False)
            _ (fun p => p) (fun s => s) _ (fun _ => False) _).
  - intros p s s' H. destruct H.
  - intros p. reflexivity.
  - intros f H. destruct H.
Defined.

Lemma nec_w_brun_equiv : forall p1 p2,
  (forall s, nec_w_brun p1 s = nec_w_brun p2 s) -> p1 = p2.
Proof.
  intros [] [] H; try reflexivity; specialize (H true); discriminate.
Qed.

Definition nec_w_norep_shortcut : @WithShortcutPredicate nec_w_norep_sub.
Proof.
  refine (@Build_WithShortcutPredicate nec_w_norep_sub (fun p => p = true) true _ false _ _).
  - reflexivity.
  - discriminate.
  - intros p1 p2 H. apply nec_w_brun_equiv in H. subst. tauto.
Defined.

Theorem nec_w_rep_needed :
  (exists decide : bool -> bool,
     forall p, decide p = true <-> @AdmitsShortcut nec_w_norep_sub nec_w_norep_shortcut p) /\
  forall decide : bool -> bool,
    ~ @Representable nec_w_norep_sub
        (fun p => if decide p
                  then @no_program nec_w_norep_sub nec_w_norep_shortcut
                  else @yes_program nec_w_norep_sub nec_w_norep_shortcut).
Proof.
  split.
  - exists (fun p => p). intros p. tauto.
  - intros decide H. exact H.
Qed.

(* ================================================================= *)
(** * 3. Extensionality is needed                                     *)
(* ================================================================= *)

(** A substrate on which every two programs are equivalent and every
    transformer is representable. *)
Definition nec_w_flat_sub : Substrate.
Proof.
  refine (Build_Substrate bool bool (fun _ _ => None) (fun _ => 0) (fun _ _ _ => False)
            _ (fun p => p) (fun s => s) _ (fun _ => True) _).
  - intros p s s' H. destruct H.
  - intros p. reflexivity.
  - intros f _. exists true. intros s. reflexivity.
Defined.

Theorem nec_w_extensional_needed :
  exists (A : @Program nec_w_flat_sub -> Prop) (y n : @Program nec_w_flat_sub),
    A y /\ ~ A n /\
    ~ (forall p1 p2, @prog_equiv nec_w_flat_sub p1 p2 -> (A p1 <-> A p2)) /\
    exists decide : @Program nec_w_flat_sub -> bool,
      @Representable nec_w_flat_sub (fun p => if decide p then n else y) /\
      forall p, decide p = true <-> A p.
Proof.
  exists (fun p : bool => p = true), true, false.
  split; [reflexivity | split; [discriminate | split]].
  - intros H. specialize (H true false (fun s => eq_refl)). destruct H as [H _].
    specialize (H eq_refl). discriminate.
  - exists (fun p : bool => p). split; [exact I | intros p; tauto].
Qed.

(* ================================================================= *)
(** * 4. The recursion theorem is needed                              *)
(* ================================================================= *)

(** The Substrate class contains the recursion theorem as a field, so it
    is tested on the bare data: programs and states are bits, a program
    true returns its input and false diverges, every transformer is
    allowed. Negation has no fixed point, and the identity decides an
    extensional predicate with both witnesses. *)
Theorem nec_w_recursion_needed :
  ~ (forall f : bool -> bool, exists p, forall s, nec_w_brun p s = nec_w_brun (f p) s) /\
  (forall p1 p2, (forall s, nec_w_brun p1 s = nec_w_brun p2 s) -> (p1 = true <-> p2 = true)) /\
  exists decide : bool -> bool, forall p, decide p = true <-> p = true.
Proof.
  split; [| split].
  - intros H. destruct (H negb) as [p Hp]. apply nec_w_brun_equiv in Hp.
    destruct p; discriminate.
  - intros p1 p2 H. apply nec_w_brun_equiv in H. subst. tauto.
  - exists (fun p => p). intros p. tauto.
Qed.

(* ================================================================= *)
(** * 5. The nat family: exactly one unavoidable error                *)
(* ================================================================= *)

Theorem nec_w_nat_family_wrong_at_two :
  forall d : nat -> bool, ~ (d 2 = true <-> nat_admits d 2).
Proof.
  intros d H. unfold nat_admits, nat_run in H.
  destruct (d 2).
  - destruct H as [H _]. specialize (H eq_refl). discriminate.
  - destruct H as [_ H]. specialize (H eq_refl). discriminate.
Qed.

Theorem nec_w_nat_family_one_error_tight :
  (forall d : nat -> bool, ~ (d 2 = true <-> nat_admits d 2)) /\
  exists d : nat -> bool, forall p, p <> 2 -> (d p = true <-> nat_admits d p).
Proof.
  split; [exact nec_w_nat_family_wrong_at_two |].
  exists (fun p => Nat.eqb p 0). intros p Hp. unfold nat_admits, nat_run.
  destruct p as [| [| [| p]]].
  - split; reflexivity.
  - split; discriminate.
  - contradiction.
  - split; discriminate.
Qed.

Print Assumptions nec_w_constant_true_predicate_decided.
Print Assumptions nec_w_constant_false_predicate_decided.
Print Assumptions nec_w_rep_needed.
Print Assumptions nec_w_extensional_needed.
Print Assumptions nec_w_recursion_needed.
Print Assumptions nec_w_nat_family_wrong_at_two.
Print Assumptions nec_w_nat_family_one_error_tight.
