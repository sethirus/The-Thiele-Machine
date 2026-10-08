(** FiniteSums: sums over finite lists of indices, their algebra, and the
    Cauchy-Schwarz inequality, for the files that reason about finite
    vectors and distributions (QuantumStrategies.v, RelaxationEntropy.v). *)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics. No definition or theorem here mentions a certification
   system, a ledger or a machine step, and it imports no kernel module.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. The standalone boundary is stated here rather than inferred from
   an import. *)

From Coq Require Import List Reals Lra Psatz.
Import ListNotations.
Open Scope R_scope.

Definition sumL {A : Type} (l : list A) (f : A -> R) : R :=
  fold_right (fun x acc => f x + acc) 0 l.

Lemma sumL_nil : forall A (f : A -> R), sumL [] f = 0.
Proof. reflexivity. Qed.

Lemma sumL_cons : forall A (x : A) l f, sumL (x :: l) f = f x + sumL l f.
Proof. reflexivity. Qed.

Lemma sumL_ext : forall A (l : list A) f g,
  (forall x, In x l -> f x = g x) -> sumL l f = sumL l g.
Proof.
  intros A l f g H. induction l as [| x l IH]; [reflexivity |].
  rewrite !sumL_cons, (H x (or_introl eq_refl)), IH; [reflexivity |].
  intros y Hy. apply H. right. exact Hy.
Qed.

Lemma sumL_plus : forall A (l : list A) f g,
  sumL l (fun x => f x + g x) = sumL l f + sumL l g.
Proof. intros A l f g. induction l as [| x l IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma sumL_minus : forall A (l : list A) f g,
  sumL l (fun x => f x - g x) = sumL l f - sumL l g.
Proof. intros A l f g. induction l as [| x l IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma sumL_scale_l : forall A (l : list A) c f,
  sumL l (fun x => c * f x) = c * sumL l f.
Proof. intros A l c f. induction l as [| x l IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma sumL_scale_r : forall A (l : list A) c f,
  sumL l (fun x => f x * c) = sumL l f * c.
Proof. intros A l c f. induction l as [| x l IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma sumL_zero : forall A (l : list A), sumL l (fun _ => 0) = 0.
Proof. intros A l. induction l as [| x l IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma sumL_swap : forall A B (l1 : list A) (l2 : list B) (f : A -> B -> R),
  sumL l1 (fun x => sumL l2 (fun y => f x y)) = sumL l2 (fun y => sumL l1 (fun x => f x y)).
Proof.
  intros A B l1 l2 f. induction l1 as [| x l1 IH]; simpl.
  - symmetry. apply sumL_zero.
  - rewrite IH. rewrite <- sumL_plus. reflexivity.
Qed.

Lemma sumL_mult : forall A B (l1 : list A) (l2 : list B) f g,
  sumL l1 f * sumL l2 g = sumL l1 (fun x => sumL l2 (fun y => f x * g y)).
Proof.
  intros A B l1 l2 f g. rewrite <- sumL_scale_r. apply sumL_ext. intros x _.
  rewrite <- sumL_scale_l. reflexivity.
Qed.

Lemma sumL_nonneg : forall A (l : list A) f, (forall x, In x l -> 0 <= f x) -> 0 <= sumL l f.
Proof.
  intros A l f H. induction l as [| x l IH]; simpl; [lra |].
  pose proof (H x (or_introl eq_refl)) as Hx.
  assert (Hl : 0 <= sumL l f). { apply IH. intros y Hy. apply H. right. exact Hy. }
  lra.
Qed.

Lemma sumL_delta : forall A (eq_dec : forall a b : A, {a = b} + {a <> b}) (l : list A) a f,
  NoDup l -> In a l -> sumL l (fun x => (if eq_dec a x then 1 else 0) * f x) = f a.
Proof.
  intros A eq_dec l a f Hnd Hin. induction l as [| x l IH]; [destruct Hin |].
  inversion Hnd as [| ? ? Hx Hnd']; subst. rewrite sumL_cons.
  destruct (eq_dec a x) as [<- | Hne].
  - assert (Hz : sumL l (fun y => (if eq_dec a y then 1 else 0) * f y) = 0).
    { transitivity (sumL l (fun _ : A => 0)); [| apply sumL_zero].
      apply sumL_ext. intros y Hy.
      destruct (eq_dec a y) as [<- | _]; [contradiction | cbn iota; lra]. }
    rewrite Hz. cbn iota. lra.
  - destruct Hin as [Hxa | Hin]; [subst; contradiction |]. rewrite IH by assumption. cbn iota. lra.
Qed.

Lemma sumL_app : forall A (l1 l2 : list A) f, sumL (l1 ++ l2) f = sumL l1 f + sumL l2 f.
Proof. intros A l1 l2 f. induction l1 as [| x l1 IH]; simpl; [lra | rewrite IH; lra]. Qed.

Lemma sumL_map : forall A B (g : A -> B) (l : list A) f, sumL (map g l) f = sumL l (fun y => f (g y)).
Proof. intros A B g l f. induction l as [| x l IH]; simpl; [lra | rewrite IH; lra]. Qed.

(** Sums over the pairs of two lists are the nested sums. *)
Lemma sumL_prod : forall A B (l1 : list A) (l2 : list B) (f : A -> B -> R),
  sumL (list_prod l1 l2) (fun p => f (fst p) (snd p)) = sumL l1 (fun x => sumL l2 (fun y => f x y)).
Proof.
  intros A B l1 l2 f. induction l1 as [| x l1 IH]; [reflexivity |].
  simpl. rewrite sumL_app, sumL_map, IH. simpl. reflexivity.
Qed.

Lemma sq_nonneg : forall x : R, 0 <= x * x.
Proof. intro x. pose proof (Rle_0_sqr x) as H. unfold Rsqr in H. exact H. Qed.

(** A nonnegative number dominates anything whose square is no bigger. *)
Lemma le_of_sq_le : forall x y : R, 0 <= x -> y * y <= x * x -> y <= x.
Proof.
  intros x y Hx Hsq. destruct (Rle_or_lt y x) as [H | H]; [exact H |].
  exfalso. assert (x * x < y * y) by (apply Rmult_le_0_lt_compat; lra). lra.
Qed.

(** Cauchy-Schwarz for finite sums. *)
Lemma sumL_cauchy_schwarz : forall A (l : list A) (u v : A -> R),
  sumL l (fun x => u x * v x) * sumL l (fun x => u x * v x) <=
  sumL l (fun x => u x * u x) * sumL l (fun x => v x * v x).
Proof.
  intros A l u v. induction l as [| x l IH]; simpl; [lra |].
  set (B := sumL l (fun y => u y * v y)) in *.
  set (P := sumL l (fun y => u y * u y)) in *.
  set (Q := sumL l (fun y => v y * v y)) in *.
  assert (HP : 0 <= P) by (apply sumL_nonneg; intros; apply sq_nonneg).
  assert (HQ : 0 <= Q) by (apply sumL_nonneg; intros; apply sq_nonneg).
  set (a := u x). set (b := v x).
  assert (Hab : 0 <= (a * b) * (a * b)) by apply sq_nonneg.
  assert (Hx : 0 <= P * (b * b) + (a * a) * Q).
  { pose proof (sq_nonneg a). pose proof (sq_nonneg b).
    apply Rplus_le_le_0_compat; apply Rmult_le_pos; assumption. }
  assert (Hkey : 2 * B * (a * b) <= P * (b * b) + (a * a) * Q).
  { apply le_of_sq_le; [exact Hx |].
    assert (E : (P * (b * b) + (a * a) * Q) * (P * (b * b) + (a * a) * Q) -
                (2 * B * (a * b)) * (2 * B * (a * b)) =
                (P * (b * b) - (a * a) * Q) * (P * (b * b) - (a * a) * Q) +
                4 * ((a * b) * (a * b)) * (P * Q - B * B)) by ring.
    pose proof (sq_nonneg (P * (b * b) - (a * a) * Q)) as H1.
    assert (H2 : 0 <= 4 * ((a * b) * (a * b)) * (P * Q - B * B)).
    { apply Rmult_le_pos; [lra | lra]. }
    lra. }
  assert (E2 : (a * b + B) * (a * b + B) = (a * b) * (a * b) + 2 * B * (a * b) + B * B) by ring.
  assert (E3 : (a * a + P) * (b * b + Q) = (a * b) * (a * b) + (P * (b * b) + (a * a) * Q) + P * Q) by ring.
  rewrite E2, E3. lra.
Qed.


