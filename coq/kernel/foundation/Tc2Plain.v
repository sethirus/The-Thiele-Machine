(** Tc2Plain.v: the recursion theorem is false for the plain reading.

    A program computes y from x in the plain reading, [tc_plain_fun P x y],
    when started with x in counter A and 0 in counter B it stops with y in
    counter A. Kleene's recursion theorem for this reading would say: for
    every transformation F of programs that some program T carries out on
    program numbers (in the packed reading, [tc_computes_map T F]) there is a
    program e that computes the same plain function as F e.

    That is false. Take the transformation

        F(p) = the program that multiplies counter A by c(p), where
               c(p) = N! + 1 and N = 4 * Nb(length p)

    (Tc2Mult.v: c(p) is coprime to every number up to N, and the control of
    any program of the length of p has at most Nb(length p) states). A
    program T carries F out on program numbers (the same lambda calculus
    route as TcNoFine.v). A fixed point e would multiply every input by
    c(e), and no program multiplies every input by c of its own length
    ([tc2_no_mult]).

    The earlier conditional statement (plain recursion fails if some
    computable bound L on the constant a program of s lines can add to every
    input exists) is kept in its corrected form: the quantifier over the
    transformations is now over those a program carries out.

    Dependencies: the Tc files, Tc2Mult.v, MetaCoq (the extraction tactic).
    No axioms and no unfinished proofs.                                                 *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
Require Minimal.UniversalCodes.
Require Import Kernel.TcGodel Kernel.TcBridge Minimal.TcBlocks Kernel.TcRice Kernel.TcCompose Kernel.TcCodes Kernel.TcInterp Kernel.TcEvalL
  Kernel.TcFuel Kernel.TcPacked Kernel.TcPlain.
Require Import Minimal.Tc2Embed Minimal.Tc2Mult.
Module E := Minimal.EarnedCore.
Module UC := Minimal.UniversalCodes.
Set Default Goal Selector "!".

(* ------------------------------------------------------------------ *)
(* the two readings of the plain function                              *)
(* ------------------------------------------------------------------ *)

Lemma tc2_plain_pf : forall P x y, tc_plain_fun P x y <-> tc2_pf P x y.
Proof.
  intros P x y. unfold tc_plain_fun, tc_ends, tc2_pf. split.
  - intros (s & (N & -> & Hh) & Hy). exists N. split; assumption.
  - intros (N & Hh & Hy). exists (E.run_prog N P (E.start x 0)). split; [exists N; split; [reflexivity | exact Hh] | exact Hy].
Qed.

(* ------------------------------------------------------------------ *)
(* the program that multiplies the input by k                          *)
(* ------------------------------------------------------------------ *)

Definition tc2_mulprog (k : nat) : list E.instr := map tc_ofki (tc_kmulchain k 1 1).

Lemma tc2_mulprog_fun : forall k x, tc_plain_fun (tc2_mulprog k) x (k * x).
Proof.
  intros k x. unfold tc2_mulprog.
  assert (Hrun : sss_output (@mma_sss 2) (1, tc_vchain k 1 1) (1, tc_tovec x 0)
                            (1 * (8 + k) + 1, tc_tovec (k ^ 1 * x) 0)).
  { split.
    - exact (tc_vchain_run k 1 1 x).
    - unfold out_code, code_end. cbn [fst snd]. right. rewrite tc_vchain_length. lia. }
  apply tc_output_iff in Hrun. destruct Hrun as [m [Hsteps Hstop]].
  change (tc_ofvec (tc_tovec x 0)) with (x, 0) in Hsteps.
  change (tc_ofvec (tc_tovec (k ^ 1 * x) 0)) with (k ^ 1 * x, 0) in Hsteps, Hstop.
  destruct (tc_ends_compile (tc_P (tc_vchain k 1 1)) x m (1 * (8 + k) + 1, (k ^ 1 * x, 0)) Hsteps Hstop)
    as (s & Hs & Ha & Hb).
  rewrite tc_kmulchain_eq. exists s. split; [exact Hs |]. rewrite Ha. cbn [fst snd]. rewrite Nat.pow_1_r. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* the transformation, as a computable function of the program number  *)
(* ------------------------------------------------------------------ *)

Definition tc2_Nbx (n : nat) : nat := S n * 4 * tc2_pw (S (2 * n)) 16.
Definition tc2_cx (n : nat) : nat := tc2_fact (4 * tc2_Nbx n) + 1.

Lemma tc2_cx_eq : forall n, tc2_cx n = tc2_c n.
Proof. intro n. reflexivity. Qed.

Instance term_tc2_pw : computable tc2_pw. Proof. extract. Qed.
Instance term_tc2_fact : computable tc2_fact. Proof. extract. Qed.
Instance term_tc2_Nbx : computable tc2_Nbx. Proof. extract. Qed.
Instance term_tc2_cx : computable tc2_cx. Proof. extract. Qed.

(* The extraction tactic unfolds definitions it is given; tc2_cx is a factorial of a
   symbolic number, and unfolding it never ends. It is kept opaque while the
   functions that call it are extracted. *)
Opaque tc2_cx.

Definition tc2_fcode (n : nat) : nat :=
  tc_kpcode (map tc_knorm (tc_kmulchain (tc2_cx (length (tc_kpdec n))) 1 1)).

Instance term_tc2_fcode : computable tc2_fcode. Proof. extract. Qed.

Definition tc2_fx (d fuel x c : nat) : option nat := Some (tc2_fcode x).

Instance term_tc2_fx : computable tc2_fx. Proof. extract. Qed.

Transparent tc2_cx.

Lemma tc2_fx_mono : forall n n' x c m, tc2_fx 0 n x c = Some m -> n <= n' -> tc2_fx 0 n' x c = Some m.
Proof. intros n n' x c m H _. exact H. Qed.

Definition tc2_Rfx (v : Vector.t nat 2) (m : nat) : Prop :=
  exists n, tc2_fx 0 n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m.

Theorem tc2_fx_MMA : MMA_computable tc2_Rfx.
Proof.
  apply L_computable_to_MMA_computable.
  exact (@tc_L_computable_fuel2 nat _ tc2_fx _ 0 tc2_fx_mono).
Qed.

(* the transformation F(p) = multiply counter A by c(length p) *)
Definition tc2_F (p : list E.instr) : list E.instr := tc2_mulprog (tc2_c (length p)).

Lemma tc2_fcode_pcode : forall p, tc2_fcode (tc_pcode p) = tc_pcode (tc2_F p).
Proof.
  intro p.
  assert (Hl : length (tc_kpdec (tc_pcode p)) = length p).
  { unfold tc_pcode. rewrite tc_kpdec_kpcode. apply map_length. }
  unfold tc2_fcode. rewrite Hl, tc2_cx_eq. unfold tc2_F, tc2_mulprog.
  unfold tc_pcode. f_equal. rewrite map_map. apply map_ext. intro i. apply tc_knorm_eq.
Qed.

Theorem tc2_F_computed : exists T : list E.instr, tc_computes_map T tc2_F.
Proof.
  destruct (tc_MMA_to_packed tc2_fx_MMA) as [U HU]. exists U. intro p.
  assert (H2 : tc_pk2 U (tc_pcode p) 0 (tc_pcode (tc2_F p))).
  { apply HU. unfold tc2_Rfx. simpl. exists 0. unfold tc2_fx. f_equal. apply tc2_fcode_pcode. }
  unfold tc_pk, tc_pk2 in *. rewrite Nat.pow_0_r, Nat.mul_1_r in H2. exact H2.
Qed.

(* ------------------------------------------------------------------ *)
(* the recursion theorem for the plain reading is false                *)
(* ------------------------------------------------------------------ *)

Theorem tc2_plain_recursion_false :
  exists (F : list E.instr -> list E.instr) (T : list E.instr),
    tc_computes_map T F /\ forall e, ~ (forall x y, tc_plain_fun e x y <-> tc_plain_fun (F e) x y).
Proof.
  destruct tc2_F_computed as [T HT].
  refine (ex_intro _ tc2_F (ex_intro _ T (conj HT _))).
  intros e He. apply (tc2_no_mult e). intro x.
  apply tc2_plain_pf. apply (proj2 (He x _)). apply tc2_mulprog_fun.
Qed.

(* plain recursion, stated for the transformations that a program carries out *)
Definition tc2_PlainRecursion : Prop :=
  forall (T : list E.instr) (F : list E.instr -> list E.instr), tc_computes_map T F ->
    exists e, forall x y, tc_plain_fun e x y <-> tc_plain_fun (F e) x y.

Corollary tc2_plain_recursion_refuted : ~ tc2_PlainRecursion.
Proof.
  intro H. destruct tc2_plain_recursion_false as (F & T & Hc & Hno).
  destruct (H T F Hc) as (e & He). exact (Hno e He).
Qed.

(* the earlier conditional, corrected: if some program carries out the transformation
   "add L(length p) + 1 to the input" on program numbers and L bounds every added constant,
   plain recursion fails (this follows now from the theorem above, without the bound) *)
Theorem tc2_plain_recursion_needs_LL : forall L T,
  tc_computes_map T (fun p => tc_adder (L (length p) + 1)) -> tc_LL L -> ~ tc2_PlainRecursion.
Proof.
  intros L T HT HL HR.
  destruct (HR T (fun p => tc_adder (L (length p) + 1)) HT) as [e He].
  assert (Hadd : tc_adds e (L (length e) + 1)).
  { intro x. apply He. simpl. apply tc_adder_ends. }
  pose proof (HL e _ Hadd). lia.
Qed.

Print Assumptions tc2_plain_pf.
Print Assumptions tc2_mulprog_fun.
Print Assumptions tc2_F_computed.
Print Assumptions tc2_plain_recursion_false.
Print Assumptions tc2_plain_recursion_refuted.
Print Assumptions tc2_plain_recursion_needs_LL.
