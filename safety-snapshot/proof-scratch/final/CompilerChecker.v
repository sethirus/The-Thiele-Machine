(** CompilerChecker.v: one fixed, total checker for the guests the compiler
    produces.

    The property language is cg_uprop: UBase q is a property of the
    counter language of EarnedGeneric.v (zero, even, at least n), and
    URun r names a reading routine by its code r (CompilerCodes.v). The
    checker cg_ueval decides UBase q with the counter checker, and decides
    URun r on a counter value v as follows: decode r into
    (ig, R, xS, xB, xT, m); read the register file from v through the prime
    exponents, keeping only the registers below m; run the counter program
    R placed at ig for at most t steps, where t is the exponent of the
    prime of register xT in v; accept exactly when the run has left R and
    register xB holds 1.

    cg_ueval is a closed Coq function: it is the same for every machine,
    and it answers on every input [cg_ueval_total]. Its meaning is given by
    cg_uholds [cg_ueval_iff].

    For a routine that computes a reading in the shape of the vendored
    compiler from recursive algorithms to counter programs (the
    ra_compiled specification, with one input register), acceptance means
    the routine reads 1 on the input [cg_checker_sound]. At a point where
    the guest's registers are the routine's start state and register xT
    holds at least the routine's measured step count, the checker accepts
    exactly when the routine reads 1 [cg_checker_exact].

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, EarnedGeneric.v and CompilerCodes.v. No axioms, no Admitted. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Minimal.EarnedGeneric.
Module G := Minimal.EarnedGeneric.
Require Import Minimal.CompilerCodes.

(* ================================================================= *)
(* The property language and the checker.                              *)
(* ================================================================= *)

Inductive cg_uprop : Type :=
| UBase (q : G.cprop)
| URun (r : nat).

Definition cg_uprop_eqb (p q : cg_uprop) : bool :=
  match p, q with
  | UBase a, UBase b => G.cprop_eqb a b
  | URun a, URun b => Nat.eqb a b
  | _, _ => false
  end.

Lemma cg_uprop_eqb_eq : forall p q, cg_uprop_eqb p q = true <-> p = q.
Proof.
  intros [a | a] [b | b]; simpl; split; intros H; try discriminate.
  - apply G.cprop_eqb_eq in H. subst. reflexivity.
  - injection H as ->. apply G.cprop_eqb_eq. reflexivity.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - injection H as ->. apply Nat.eqb_refl.
Qed.

(* The routine's start state read off a counter value: register x below m
   holds the exponent of qs x in v, every other register holds 0. *)
Definition cg_env_chk (m v : nat) : env nat nat :=
  fun x => if Nat.ltb x m then cg_expo (qs x) v else 0.

Definition cg_out_codeb (P : nat * list (mm_instr nat)) (i : nat) : bool :=
  Nat.ltb i (fst P) || Nat.leb (fst P + length (snd P)) i.

Lemma cg_out_codeb_spec : forall P i, cg_out_codeb P i = true <-> out_code i P.
Proof.
  intros [i0 R] i. unfold cg_out_codeb, out_code, code_start, code_end. simpl.
  rewrite orb_true_iff, Nat.ltb_lt, Nat.leb_le. tauto.
Qed.

Definition cg_run_check (rc : cg_routine_code) (v : nat) : bool :=
  match rc with
  | (ig, R, xS, xB, xT, m) =>
      let st := cg_mme_run_fuel (cg_expo (qs xT) v) (ig, R) (ig, cg_env_chk m v) in
      cg_out_codeb (ig, R) (fst st) && Nat.eqb (get_env (snd st) xB) 1
  end.

Definition cg_ueval (p : cg_uprop) (v : nat) : bool :=
  match p with
  | UBase q => G.ceval q v
  | URun r =>
      match cg_rdec r with
      | Some rc => cg_run_check rc v
      | None => false
      end
  end.

Theorem cg_ueval_total : forall p v, cg_ueval p v = true \/ cg_ueval p v = false.
Proof. intros p v. destruct (cg_ueval p v); auto. Qed.

(* What the checker means. *)
Definition cg_uholds (p : cg_uprop) (v : nat) : Prop :=
  match p with
  | UBase q => G.cholds q v
  | URun r =>
      exists ig R xS xB xT m k st,
        cg_rdec r = Some (ig, R, xS, xB, xT, m) /\
        k <= cg_expo (qs xT) v /\
        sss_steps (mm_sss_env eq_nat_dec) (ig, R) k (ig, cg_env_chk m v) st /\
        out_code (fst st) (ig, R) /\
        get_env (snd st) xB = 1
  end.

Theorem cg_ueval_iff : forall p v, cg_ueval p v = true <-> cg_uholds p v.
Proof.
  intros [q | r] v; cbn [cg_ueval cg_uholds].
  - apply G.ceval_iff.
  - split.
    + destruct (cg_rdec r) as [[[[[[ig R] xS] xB] xT] m] |] eqn:E; [| discriminate].
      unfold cg_run_check. rewrite andb_true_iff, Nat.eqb_eq, cg_out_codeb_spec.
      intros [Hout HB].
      destruct (cg_mme_run_fuel_sound (cg_expo (qs xT) v) (ig, R) (ig, cg_env_chk m v))
        as (k & Hk & Hs).
      exists ig, R, xS, xB, xT, m, k,
        (cg_mme_run_fuel (cg_expo (qs xT) v) (ig, R) (ig, cg_env_chk m v)).
      repeat split; assumption.
    + intros (ig & R & xS & xB & xT & m & k & st & E & Hk & Hs & Hout & HB).
      rewrite E. unfold cg_run_check.
      rewrite (cg_mme_run_fuel_complete _ _ _ _ Hs Hout _ Hk).
      rewrite andb_true_iff, Nat.eqb_eq, cg_out_codeb_spec. auto.
Qed.

(* ================================================================= *)
(* Reading routines.                                                   *)
(* ================================================================= *)

(* A routine computing the relation rd, in the shape of the vendored
   ra_compiled specification with one input: R placed at ig, input in
   register xS, answer in register xB, every register from m on is spare
   and starts at 0. From such a start, every answer x of the input is
   reached at the end of R with only register xB changed to x, and a run
   that leaves R happens only when the input has an answer. *)
Definition cg_routine (rd : nat -> nat -> Prop) (ig : nat) (R : list (mm_instr nat))
  (xS xB m : nat) : Prop :=
  forall e : env nat nat,
    (forall i, m <= i -> get_env e i = 0) ->
    (forall x, rd (get_env e xS) x ->
       exists e', (forall y, get_env e' y = get_env (set_env eq_nat_dec e xB x) y) /\
                  sss_compute (mm_sss_env eq_nat_dec) (ig, R) (ig, e) (length R + ig, e')) /\
    (sss_terminates (mm_sss_env eq_nat_dec) (ig, R) (ig, e) ->
       exists x, rd (get_env e xS) x).

Lemma cg_env_chk_spare : forall m v i, m <= i -> get_env (cg_env_chk m v) i = 0.
Proof.
  intros m v i H. rewrite cg_get_env. unfold cg_env_chk.
  destruct (Nat.ltb_spec i m); [lia | reflexivity].
Qed.

Lemma cg_mm_sss_env_fun : forall i s t1 t2,
  mm_sss_env eq_nat_dec i s t1 -> mm_sss_env eq_nat_dec i s t2 -> t1 = t2.
Proof. intros i s t1 t2 H1 H2. exact (mm_sss_env_fun H1 H2). Qed.

Lemma cg_routine_end_out : forall (ig : nat) (R : list (mm_instr nat)),
  out_code (length R + ig) (ig, R).
Proof. intros. unfold out_code, code_end. simpl. lia. Qed.

(* A routine's output after its run, when the input has answer x. *)
Lemma cg_routine_output : forall rd ig R xS xB m e x st,
  cg_routine rd ig R xS xB m ->
  (forall i, m <= i -> get_env e i = 0) ->
  rd (get_env e xS) x ->
  sss_compute (mm_sss_env eq_nat_dec) (ig, R) (ig, e) st ->
  out_code (fst st) (ig, R) ->
  get_env (snd st) xB = x.
Proof.
  intros rd ig R xS xB m e x st HR He Hx Hc Hout.
  destruct (proj1 (HR e He) x Hx) as (e' & He' & Hc').
  assert (st = (length R + ig, e')) as ->.
  { apply (sss_compute_fun cg_mm_sss_env_fun (st2 := st) (st3 := (length R + ig, e'))
             Hout (cg_routine_end_out ig R) Hc Hc'). }
  simpl. rewrite He'. apply get_set_env_eq. reflexivity.
Qed.

(* Acceptance means the routine reads 1 on the input it was given. *)
Theorem cg_checker_sound : forall rd r ig R xS xB xT m v,
  cg_rdec r = Some (ig, R, xS, xB, xT, m) ->
  cg_routine rd ig R xS xB m ->
  cg_ueval (URun r) v = true ->
  rd (get_env (cg_env_chk m v) xS) 1.
Proof.
  intros rd r ig R xS xB xT m v E HR Hev.
  cbn [cg_ueval] in Hev. rewrite E in Hev. unfold cg_run_check in Hev.
  set (st := cg_mme_run_fuel (cg_expo (qs xT) v) (ig, R) (ig, cg_env_chk m v)) in Hev.
  apply andb_true_iff in Hev as [Hout HB].
  apply cg_out_codeb_spec in Hout. apply Nat.eqb_eq in HB.
  assert (Ho : sss_output (mm_sss_env eq_nat_dec) (ig, R) (ig, cg_env_chk m v) st)
    by (apply cg_mme_run_fuel_output; exact Hout).
  destruct (proj2 (HR (cg_env_chk m v) (cg_env_chk_spare m v)) (ex_intro _ st Ho))
    as (x & Hx).
  rewrite (cg_routine_output rd ig R xS xB m (cg_env_chk m v) x st HR
                (cg_env_chk_spare m v) Hx (proj1 Ho) Hout) in HB.
  subst x. exact Hx.
Qed.

(* At a guest register file e (registers from k on are 0), the routine's
   start state is e itself below m. *)
Lemma cg_env_chk_gk : forall k e m x,
  (forall y, k <= y -> e y = 0) ->
  get_env (cg_env_chk m (cg_gk k e)) x = if Nat.ltb x m then e x else 0.
Proof.
  intros k e m x H. rewrite cg_get_env. unfold cg_env_chk.
  destruct (Nat.ltb x m); [apply cg_expo_gk_zero; exact H | reflexivity].
Qed.

(* With the measured step count t in register xT (or more), the checker's
   answer is the routine's answer. *)
Theorem cg_checker_exact_run : forall k e r ig R xS xB xT m t st,
  cg_rdec r = Some (ig, R, xS, xB, xT, m) ->
  (forall y, k <= y -> e y = 0) ->
  sss_steps (mm_sss_env eq_nat_dec) (ig, R) t (ig, cg_env_chk m (cg_gk k e)) st ->
  out_code (fst st) (ig, R) ->
  t <= e xT ->
  cg_ueval (URun r) (cg_gk k e) = Nat.eqb (get_env (snd st) xB) 1.
Proof.
  intros k e r ig R xS xB xT m t st E He Hs Hout Ht.
  cbn [cg_ueval]. rewrite E. unfold cg_run_check.
  rewrite (cg_mme_run_fuel_complete _ _ _ _ Hs Hout)
    by (rewrite cg_expo_gk_zero by exact He; exact Ht).
  replace (cg_out_codeb (ig, R) (fst st)) with true
    by (symmetry; apply cg_out_codeb_spec; exact Hout).
  reflexivity.
Qed.

Theorem cg_checker_exact : forall rd k e r ig R xS xB xT m t st,
  cg_rdec r = Some (ig, R, xS, xB, xT, m) ->
  cg_routine rd ig R xS xB m ->
  (forall y, k <= y -> e y = 0) ->
  xS < m ->
  sss_steps (mm_sss_env eq_nat_dec) (ig, R) t (ig, cg_env_chk m (cg_gk k e)) st ->
  out_code (fst st) (ig, R) ->
  t <= e xT ->
  (cg_ueval (URun r) (cg_gk k e) = true <-> rd (e xS) 1).
Proof.
  intros rd k e r ig R xS xB xT m t st E HR He HS Hs Hout Ht.
  assert (HxS : get_env (cg_env_chk m (cg_gk k e)) xS = e xS).
  { rewrite cg_env_chk_gk by exact He.
    destruct (Nat.ltb_spec xS m); [reflexivity | lia]. }
  split.
  - intros Hev. rewrite <- HxS. exact (cg_checker_sound rd r ig R xS xB xT m _ E HR Hev).
  - intros Hrd. rewrite (cg_checker_exact_run k e r ig R xS xB xT m t st E He Hs Hout Ht).
    rewrite (cg_routine_output rd ig R xS xB m (cg_env_chk m (cg_gk k e)) 1 st HR
               (cg_env_chk_spare m _)); [reflexivity | | | exact Hout].
    + rewrite HxS. exact Hrd.
    + exists t. exact Hs.
Qed.
