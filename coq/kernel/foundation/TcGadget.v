(** TcGadget.v: the vendored counter gadgets, read on states written
    (counter A, counter B) = (a, b).

    Counter A is register 1 of the vendored two-register machine and counter B
    is register 0, as in TcBridge.v. The gadgets are the vendored
    multiplication by a constant, addition of a constant, subtraction of a
    constant and division by a constant with a test, each restated for
    states [tc_tovec a b], plus the loop that divides by k as often as it
    can [tc_div_loop].

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, TcBridge.v, EarnedCore.v. No axioms and no unfinished proofs.                           *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils gcd pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs mma_utils.
Require Import Kernel.TcBridge.
Require Minimal.EarnedCore.
Set Default Goal Selector "!".

Definition tcA : pos 2 := pos1.
Definition tcB : pos 2 := pos0.

Lemma tc_AB : tcA <> tcB.
Proof. unfold tcA, tcB. discriminate. Qed.

Lemma tc_change_A : forall a b n, vec_change (tc_tovec a b) tcA n = tc_tovec n b.
Proof. reflexivity. Qed.

Lemma tc_change_B : forall a b n, vec_change (tc_tovec a b) tcB n = tc_tovec a n.
Proof. reflexivity. Qed.

Lemma tc_posA : forall a b, vec_pos (tc_tovec a b) tcA = a.
Proof. reflexivity. Qed.

Lemma tc_posB : forall a b, vec_pos (tc_tovec a b) tcB = b.
Proof. reflexivity. Qed.

(* multiplication of A by a constant, with B as the spare *)
Lemma tc_mult : forall k i a,
  sss_progress (@mma_sss 2) (i, mma_mult_cst_with_zero tcA tcB k i)
    (i, tc_tovec a 0) (8 + k + i, tc_tovec (k * a) 0).
Proof.
  intros k i a. apply mma_mult_cst_with_zero_progress.
  - exact tc_AB.
  - reflexivity.
  - reflexivity.
Qed.

(* addition of a constant *)
Lemma tc_incs : forall k i a b,
  sss_compute (@mma_sss 2) (i, mma_incs tcA k) (i, tc_tovec a b) (k + i, tc_tovec (k + a) b).
Proof.
  intros k i a b. apply mma_incs_compute. reflexivity.
Qed.

(* subtraction of a constant *)
Lemma tc_decs : forall p q k i a b, k <= a ->
  sss_progress (@mma_sss 2) (i, mma_decs tcA p q k i) (i, tc_tovec a b) (p, tc_tovec (a - k) b).
Proof.
  intros p q k i a b Hk. apply mma_decs_le_progress.
  - exact Hk.
  - reflexivity.
Qed.

(* division by a constant with a test *)
Lemma tc_div_yes : forall k i j a a',
  0 < k -> a = a' * k ->
  sss_progress (@mma_sss 2) (i, mma_div_branch tcA tcB k i j) (i, tc_tovec a 0) (j, tc_tovec a' 0).
Proof.
  intros k i j a a' Hk Ha. apply mma_div_branch_0_progress with (a := a').
  - exact tc_AB.
  - reflexivity.
  - exact Hk.
  - exact Ha.
  - reflexivity.
Qed.

Lemma tc_div_no : forall k i j a,
  0 < k -> ~ divides k a ->
  sss_progress (@mma_sss 2) (i, mma_div_branch tcA tcB k i j) (i, tc_tovec a 0) (16 + 7 * k + i, tc_tovec a 0).
Proof.
  intros k i j a Hk Hd. apply mma_div_branch_1_progress.
  - exact tc_AB.
  - reflexivity.
  - exact Hk.
  - exact Hd.
  - reflexivity.
Qed.

(* dividing by k as long as possible *)
Lemma tc_div_loop : forall k i y, 0 < k -> ~ divides k y -> forall c,
  sss_compute (@mma_sss 2) (i, mma_div_branch tcA tcB k i i)
    (i, tc_tovec (y * k ^ c) 0) (16 + 7 * k + i, tc_tovec y 0).
Proof.
  intros k i y Hk Hy c. induction c as [| c IH].
  - assert (E : y * k ^ 0 = y) by (simpl; lia). rewrite E.
    apply sss_progress_compute. apply tc_div_no; assumption.
  - assert (E : y * k ^ S c = (y * k ^ c) * k) by (simpl; ring).
    rewrite E.
    eapply sss_compute_trans; [apply sss_progress_compute; apply tc_div_yes; [exact Hk | reflexivity] | exact IH].
Qed.

Print Assumptions tc_div_loop.
