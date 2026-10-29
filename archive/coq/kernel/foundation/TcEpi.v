(** TcEpi.v: an epilogue for vendored alternate-Minsky programs, and a cast
    between register counts.

    [tc_epi n0 i] is code, placed at address i, for a machine with 3 + n0
    registers: it empties every register but register 0 and then moves
    register 0 into register 1. From any register file v it reaches the file
    that is 0 everywhere except register 1, which holds v's register 0
    [tc_epi_run]. It uses the vendored emptying and transfer gadgets.

    [tc_cast_output], [tc_cast_terminates]: a program over n registers and
    the same program over m registers when n = m, with the states carried
    along, run alike. Used to pass from 3 + n0 registers to 3 + n0 + 0.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library. No axioms and no unfinished proofs.                                       *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils gcd pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs mma_utils.
Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

Definition tc_L (n0 : nat) : list (pos (3 + n0)) :=
  filter (fun p => if pos_eq_dec p (pos0 : pos (3 + n0)) then false else true) (pos_list (3 + n0)).

Definition tc_epi (n0 : nat) (i : nat) : list (mm_instr (pos (3 + n0))) :=
  mma_null_list (tc_L n0) i ++ mma_transfert (pos0 : pos (3 + n0)) (pos1 : pos (3 + n0)) (length (tc_L n0) + i).

Definition tc_keep0 (n0 : nat) (v : vec nat (3 + n0)) : vec nat (3 + n0) :=
  vec_set_pos (fun p => if pos_eq_dec p (pos0 : pos (3 + n0)) then v#>pos0 else 0).

Definition tc_unit1 (n0 : nat) (m : nat) : vec nat (3 + n0) :=
  vec_set_pos (fun p => if pos_eq_dec p (pos1 : pos (3 + n0)) then m else 0).

Lemma tc_L_in : forall n0 p, In p (tc_L n0) <-> p <> (pos0 : pos (3 + n0)).
Proof.
  intros n0 p. unfold tc_L. rewrite filter_In. split.
  - intros [_ H] Hp. subst p. destruct (pos_eq_dec (pos0 : pos (3 + n0)) pos0); [discriminate | contradiction].
  - intro H. split; [apply pos_list_prop |]. destruct (pos_eq_dec p (pos0 : pos (3 + n0))); [contradiction | reflexivity].
Qed.

Lemma tc_epi_length : forall n0 i, length (tc_epi n0 i) = length (tc_L n0) + 3.
Proof.
  intros n0 i. unfold tc_epi. rewrite app_length, mma_null_list_length. reflexivity.
Qed.

Lemma tc_epi_run : forall n0 i (v : vec nat (3 + n0)),
  sss_compute (@mma_sss (3 + n0)) (i, tc_epi n0 i) (i, v)
    (length (tc_L n0) + 3 + i, tc_unit1 n0 (v#>pos0)).
Proof.
  intros n0 i v. unfold tc_epi.
  eapply subcode_sss_compute_trans.
  - instantiate (1 := (i, mma_null_list (tc_L n0) i)). exists [], (mma_transfert (pos0 : pos (3 + n0)) (pos1 : pos (3 + n0)) (length (tc_L n0) + i)).
    split; [reflexivity | simpl; lia].
  - apply mma_null_list_spec with (w := tc_keep0 n0 v).
    + intros p Hp. unfold tc_keep0. rewrite vec_pos_set.
      destruct (pos_eq_dec p (pos0 : pos (3 + n0))) as [E | E]; [| reflexivity].
      exfalso. apply (proj1 (tc_L_in n0 p) Hp). exact E.
    + intros p Hp. unfold tc_keep0. rewrite vec_pos_set.
      destruct (pos_eq_dec p (pos0 : pos (3 + n0))) as [E | E]; [subst p; reflexivity |].
      exfalso. apply Hp. apply tc_L_in. exact E.
  - apply sss_progress_compute.
    apply (subcode_sss_progress (P := (length (tc_L n0) + i,
              mma_transfert (pos0 : pos (3 + n0)) (pos1 : pos (3 + n0)) (length (tc_L n0) + i)))).
    + exists (mma_null_list (tc_L n0) i), []. split; [rewrite app_nil_r; reflexivity |].
      rewrite mma_null_list_length. lia.
    + apply mma_transfert_progress.
      * discriminate.
      * f_equal; [lia |]. unfold tc_keep0, tc_unit1. apply vec_pos_ext. intro p.
        rewrite vec_pos_set.
        destruct (pos_eq_dec p (pos1 : pos (3 + n0))) as [E1 | E1].
        -- subst p. rewrite vec_change_eq by reflexivity.
           rewrite !vec_pos_set.
           destruct (pos_eq_dec (pos1 : pos (3 + n0)) pos0) as [E2 | E2]; [discriminate E2 |].
           destruct (pos_eq_dec (pos0 : pos (3 + n0)) pos0) as [E3 | E3]; [| contradiction].
           lia.
        -- destruct (pos_eq_dec p (pos0 : pos (3 + n0))) as [E2 | E2].
           ++ subst p. rewrite vec_change_neq by (intro H; apply E1; symmetry; exact H). rewrite vec_change_eq by reflexivity. reflexivity.
           ++ rewrite vec_change_neq by (intro H; apply E1; symmetry; exact H).
              rewrite vec_change_neq by (intro H; apply E2; symmetry; exact H).
              rewrite vec_pos_set.
              destruct (pos_eq_dec p (pos0 : pos (3 + n0))) as [E3 | E3]; [contradiction | reflexivity].
Qed.

(* casting *)
Definition tc_castP {n m : nat} (H : n = m) (P : list (mm_instr (pos n))) : list (mm_instr (pos m)) :=
  match H in (_ = k) return list (mm_instr (pos k)) with eq_refl => P end.

Definition tc_castv {n m : nat} (H : n = m) (v : vec nat n) : vec nat m :=
  match H in (_ = k) return vec nat k with eq_refl => v end.

Lemma tc_cast_output : forall n m (H : n = m) P i v j w,
  sss_output (@mma_sss n) (1, P) (i, v) (j, w) <->
  sss_output (@mma_sss m) (1, tc_castP H P) (i, tc_castv H v) (j, tc_castv H w).
Proof. intros n m H. destruct H. intros. reflexivity. Qed.

Lemma tc_cast_terminates : forall n m (H : n = m) P i v,
  sss_terminates (@mma_sss n) (1, P) (i, v) <->
  sss_terminates (@mma_sss m) (1, tc_castP H P) (i, tc_castv H v).
Proof. intros n m H. destruct H. intros. reflexivity. Qed.

Print Assumptions tc_epi_run.
Print Assumptions tc_cast_output.
