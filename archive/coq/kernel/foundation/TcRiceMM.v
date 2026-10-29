(** TcRiceMM.v: the two-register machine hidden inside one number, with the
    input riding along.

    The vendored compiler of TcCompile.v runs any two-register program P on
    the exponents of 2 and 3 inside one counter. Here the compiled code is
    packaged for use in a reduction:

      [tc_Q P i]  the compiled code of P placed at address i. It does not
                  depend on the residue (see [tc_Q_indep] in TcCompile use).
      [tc_Q_halts]    if P stops on (a0, b0) with (a1, b1) then, from a
                  counter holding res * 2^b0 * 3^a0 (and 0 in the other
                  counter), the compiled code stops with res * 2^b1 * 3^a1
                  one past its end. Here res is any number prime to 2 and 3.
      [tc_Q_diverges]  if P does not stop, the compiled code does not stop.

    The number res is the part of the counter that is not touched. When
    res = 6n + 5 it carries a plain input n: it is prime to 2 and 3, so the
    coding never confuses it with the exponents.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, TcGodel.v, TcCompile.v, TcBridge.v. No axioms and no unfinished proofs.    *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils gcd godel_coding pos vec subcode sss compiler_correction.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs mma_utils.
Require Import Kernel.TcGodel Kernel.TcCompile Kernel.TcBridge.
Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

Definition tc_ms : vec nat 2 := 2 ## 3 ## vec_nil.

Lemma tc_ms_ok : tc_moduli_ok tc_ms.
Proof.
  split.
  - intro p. pos_inv p; simpl; [lia |]. pos_inv p; simpl; [lia | invert pos p].
  - intros p q Hpq. pos_inv p; pos_inv q; simpl.
    + exfalso. apply Hpq. reflexivity.
    + pos_inv q; simpl; [reflexivity | invert pos q].
    + pos_inv p; simpl; [reflexivity | invert pos p].
    + pos_inv p; pos_inv q; simpl.
      * exfalso. apply Hpq. reflexivity.
      * invert pos q.
      * invert pos p.
      * invert pos p.
Qed.

Definition tc_gc2 : godel_coding 2 := tc_gc tc_ms_ok.

Lemma tc_gc2_one : forall p : pos 2, Nat.gcd (gc_pr tc_gc2 p) 1 = 1.
Proof. intro p. apply Nat.divide_1_r. apply Nat.gcd_divide_r. Qed.

Definition tc_cc := tc_compiler_res tc_gc2 0 1 tc_gc2_one.

Definition tc_Q (P : list (mm_instr (pos 2))) (i : nat) : list (mm_instr (pos 2)) :=
  gc_code tc_cc (1, P) i.

(* the code of a register file *)
Definition tc_code (v : vec nat 2) : nat := gc_enc tc_gc2 v.

Lemma tc_code_tovec : forall a b, tc_code (tc_tovec a b) = 2 ^ b * (3 ^ a * 1).
Proof. intros a b. reflexivity. Qed.

(* the simulation relation, made explicit *)
Lemma tc_simul_iff : forall res a b w,
  (let (v1, v2) := vec_split 2 0 (tc_tovec a b) in
   let (w1, w2) := vec_split 2 0 w in
   w1 = 0 ## res * gc_enc tc_gc2 v1 ## vec_nil /\ w2 = v2)
  <-> w = tc_tovec (res * tc_code (tc_tovec a b)) 0.
Proof.
  intros res a b w. destruct (tc_vec2_ex w) as [c [d ->]]. 
  unfold tc_tovec. simpl. split.
  - intros [H _]. exact H.
  - intros H. split; [exact H | reflexivity].
Qed.

Lemma tc_Q_halts : forall P a0 b0 j a1 b1,
  sss_output (@mma_sss 2) (1, P) (1, tc_tovec a0 b0) (j, tc_tovec a1 b1) ->
  forall res (Hres : forall p, Nat.gcd (gc_pr tc_gc2 p) res = 1) i,
  sss_output (@mma_sss 2) (i, tc_Q P i) (i, tc_tovec (res * tc_code (tc_tovec a0 b0)) 0)
             (i + length (tc_Q P i), tc_tovec (res * tc_code (tc_tovec a1 b1)) 0).
Proof.
  intros P a0 b0 j a1 b1 Hout res Hres i.
  set (c := tc_compiler_res tc_gc2 0 res Hres).
  assert (Hs0 : (let (v1, v2) := vec_split 2 0 (tc_tovec a0 b0) in
                 let (w1, w2) := vec_split 2 0 (tc_tovec (res * tc_code (tc_tovec a0 b0)) 0) in
                 w1 = 0 ## res * gc_enc tc_gc2 v1 ## vec_nil /\ w2 = v2)).
  { apply tc_simul_iff. reflexivity. }
  destruct (@compiler_t_output_sound' _ _ _ _ _ _ _ c (1, P) i (tc_tovec a0 b0)
              (tc_tovec (res * tc_code (tc_tovec a0 b0)) 0) j (tc_tovec a1 b1)
              Hs0 Hout) as [w' [Hw' Hs1]].
  apply tc_simul_iff in Hs1. subst w'. exact Hw'.
Qed.

Lemma tc_Q_diverges : forall P a0 b0,
  ~ sss_terminates (@mma_sss 2) (1, P) (1, tc_tovec a0 b0) ->
  forall res (Hres : forall p, Nat.gcd (gc_pr tc_gc2 p) res = 1) i,
  ~ sss_terminates (@mma_sss 2) (i, tc_Q P i) (i, tc_tovec (res * tc_code (tc_tovec a0 b0)) 0).
Proof.
  intros P a0 b0 Hnt res Hres i.
  set (c := tc_compiler_res tc_gc2 0 res Hres).
  assert (Hs0 : (let (v1, v2) := vec_split 2 0 (tc_tovec a0 b0) in
                 let (w1, w2) := vec_split 2 0 (tc_tovec (res * tc_code (tc_tovec a0 b0)) 0) in
                 w1 = 0 ## res * gc_enc tc_gc2 v1 ## vec_nil /\ w2 = v2)).
  { apply tc_simul_iff. reflexivity. }
  intro Ht. apply Hnt.
  apply (@compiler_t_term_equiv _ _ _ _ _ _ _ c (1, P) i (tc_tovec a0 b0)
           (tc_tovec (res * tc_code (tc_tovec a0 b0)) 0) Hs0).
  exact Ht.
Qed.

Print Assumptions tc_Q_halts.
Print Assumptions tc_Q_diverges.
