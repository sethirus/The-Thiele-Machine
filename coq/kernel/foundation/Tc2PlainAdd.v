(** Tc2PlainAdd.v: the transformation "add L(length p) + 1 to the input" is carried out
    by a program on program numbers, for an explicit computable L; the old conditional
    in its corrected form.

    The earlier statement of plain recursion (TcPlain.v) quantified over every function
    F of programs; classically that is false by diagonalisation, so the conditional
    "a growth bound L on the constants a program of s lines can add makes plain
    recursion false" said nothing. The meaningful statement quantifies over the F that a
    program carries out on program numbers ([tc2_PlainRecursion], Tc2Plain.v). Here the
    additive transformation is shown to be of that kind for the explicit bound
    L(s) = c(s) of Tc2Mult.v, so [tc2_plain_recursion_needs_LL] has content: it is the
    conditional for this L. (Tc2Plain.v refutes plain recursion outright, with the
    multiplicative transformation, without any bound of this kind.)

    Dependencies: the Tc files, Tc2Plain.v. MetaCoq extraction tactic. No axioms
    and no unfinished proofs.                                               *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.MinskyMachines Require Import MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
Require Minimal.UniversalCodes.
Require Import Minimal.TcBlocks Kernel.TcRice Kernel.TcCodes Kernel.TcInterp Kernel.TcEvalL Kernel.TcFuel Kernel.TcPacked Kernel.TcPlain.
Require Import Minimal.Tc2Embed Minimal.Tc2Mult Kernel.Tc2Plain.
Module E := Minimal.EarnedCore.
Set Default Goal Selector "!".

Fixpoint tc2_krep (k : nat) : list tc_ki := match k with 0 => [] | S m => tc_KInc 0 :: tc2_krep m end.

Lemma tc2_krep_eq : forall k, map tc_ofki (tc2_krep k) = tc_adder k.
Proof. induction k as [| k IH]; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

Instance term_tc2_krep : computable tc2_krep. Proof. extract. Qed.

(* the explicit bound *)
Definition tc2_L0 (s : nat) : nat := tc2_cx s.

(* As in Tc2Plain.v, tc2_cx is kept opaque while the functions that call it are extracted. *)
Opaque tc2_cx.

Definition tc2_addcode (n : nat) : nat :=
  tc_kpcode (map tc_knorm (tc2_krep (tc2_L0 (length (tc_kpdec n)) + 1))).

Instance term_tc2_L0 : computable tc2_L0. Proof. extract. Qed.
Instance term_tc2_addcode : computable tc2_addcode. Proof. extract. Qed.

Definition tc2_addfx (d fuel x c : nat) : option nat := Some (tc2_addcode x).

Instance term_tc2_addfx : computable tc2_addfx. Proof. extract. Qed.

Transparent tc2_cx.

(* Definitional witness for the compiler interface: tc2_addfx ignores fuel. *)
Definition tc2_addfx_mono : forall n n' x c m, tc2_addfx 0 n x c = Some m -> n <= n' -> tc2_addfx 0 n' x c = Some m.
Proof. intros n n' x c m H _. exact H. Qed.

Definition tc2_Raddfx (v : Vector.t nat 2) (m : nat) : Prop :=
  exists n, tc2_addfx 0 n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m.

Theorem tc2_addfx_MMA : MMA_computable tc2_Raddfx.
Proof.
  apply L_computable_to_MMA_computable.
  exact (@tc_L_computable_fuel2 nat _ tc2_addfx _ 0 tc2_addfx_mono).
Qed.

Definition tc2_Fadd (p : list E.instr) : list E.instr := tc_adder (tc2_L0 (length p) + 1).

Lemma tc2_addcode_pcode : forall p, tc2_addcode (tc_pcode p) = tc_pcode (tc2_Fadd p).
Proof.
  intro p.
  assert (Hl : length (tc_kpdec (tc_pcode p)) = length p).
  { unfold tc_pcode. rewrite tc_kpdec_kpcode. apply map_length. }
  unfold tc2_addcode. rewrite Hl. unfold tc2_Fadd. rewrite <- tc2_krep_eq.
  unfold tc_pcode. f_equal. rewrite map_map. apply map_ext. intro i. apply tc_knorm_eq.
Qed.

Theorem tc2_Fadd_computed : exists T : list E.instr, tc_computes_map T tc2_Fadd.
Proof.
  destruct (tc_MMA_to_packed tc2_addfx_MMA) as [U HU]. exists U. intro p.
  assert (H2 : tc_pk2 U (tc_pcode p) 0 (tc_pcode (tc2_Fadd p))).
  { apply HU. unfold tc2_Raddfx. simpl. exists 0. unfold tc2_addfx. f_equal. apply tc2_addcode_pcode. }
  unfold tc_pk, tc_pk2 in *. rewrite Nat.pow_0_r, Nat.mul_1_r in H2. exact H2.
Qed.

(* the conditional, with the transformation shown to be computed *)
Corollary tc2_plain_recursion_needs_LL0 : tc_LL tc2_L0 -> ~ tc2_PlainRecursion.
Proof.
  intro HL. destruct tc2_Fadd_computed as [T HT].
  exact (@tc2_plain_recursion_needs_LL tc2_L0 T HT HL).
Qed.

Print Assumptions tc2_Fadd_computed.
Print Assumptions tc2_plain_recursion_needs_LL0.
