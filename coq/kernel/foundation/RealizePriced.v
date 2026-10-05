(** RealizePriced.v: the priced host that runs U_P, made extractable, and the
    proof that it is the host the theorems of UniversalPRun.v are about.

    The host is the machine of EarnedMultiPriced.v (with PAY) over the one
    property PSlot of UniversalPCodes.v, whose checker is the universal
    checker cg_ueval of CompilerChecker.v. The host program is U_P
    (UniversalPLayout.v). This file is the priced counterpart of Realize.v
    and has the same extraction constraints (see there); two further things
    were needed.

    1. The prime stream. cg_ueval reads the prime stream qs of the vendored
       library (prime_seq.v). qs is defined through the existence proof
       first_prime_above, which is closed with Qed, so Coq can neither
       evaluate nor extract it. Here a computable search is written
       (rlz_scan, rlz_nxtprime, rlz_nthprime_with, rlz_qs) and proved equal
       to qs for every argument (rlz_qs_eq). The search is bounded by a fuel
       argument: rlz_scan_ok proves that any fuel larger than the distance
       to the next prime gives the right answer, and rlz_nxtprime_le proves
       that fact n + 1 is such a fuel. The extracted code uses that fuel;
       the unit tests evaluate the same function in Coq with a small
       explicit fuel (rlz_nxtprime_with), since Coq cannot hold fact n in
       unary.

    2. The property and instruction types. cg_uprop (CompilerChecker.v)
       and the guest instruction type of EarnedPriced.v live in files Coq
       cannot extract from. The extracted code uses two copies of the data
       types, rlz_uprop and rlz_pinstr, with the maps rlz_of_cg, rlz_to_cg,
       rlz_to_pr back to the originals, and every function that reads them
       (the checker rlz_ueval_with, the program code rlz_pu_prog_code, the
       loader rlz_phost_load) is proved equal to the original composed with
       the map: rlz_ueval_with_eq, rlz_pu_prog_code_eq, rlz_phost_load_eq.
       The counter-program interpreter of CompilerCodes.v is copied
       (rlz_mme_run_fuel) and proved to give the same program counter and
       the same register reads (rlz_run_fuel_sim).

    A run of the machine under an evaluation that agrees pointwise with
    another is the same run, with equal states (rlz_pu_run_prog_ext), so the
    extracted host is state for state the host of the theorems:
    rlz_phost_run_prog_eq, rlz_phost_at_eq.

    Dependencies: Realize.v, RealizePrograms.v, the files they name, and the
    vendored coq-undecidability library. No axioms, no Admitted.          *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file only re-proves; the claims about these machines are in the files
   named above. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_list gcd prime.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Import Kernel.RealizeNames.
Require Kernel.RealizePrograms Kernel.Realize.

(* ================================================================= *)
(* 1. The prime stream, computably.                                   *)
(* ================================================================= *)

Lemma rlz_nxtprime_le : forall n, nxtprime n <= fact n + 1.
Proof.
  intro n.
  destruct (prime_factor (n := fact n + 1)) as (p & Hp & Hd).
  - pose proof (lt_O_fact n); lia.
  - assert (Hnp : n < p).
    { destruct (Nat.lt_ge_cases n p) as [H | H]; [exact H |].
      exfalso.
      eapply divides_plus_inv in Hd.
      + eapply divides_1_inv in Hd; subst. destruct Hp; lia.
      + eapply divides_fact. eapply prime_ge_2 in Hp; eauto. }
    pose proof (proj2_sig (first_prime_above n)) as (_ & _ & Hmin).
    change (nxtprime n) with (proj1_sig (first_prime_above n)).
    pose proof (Hmin p Hnp Hp) as H1.
    assert (Hne : fact n + 1 <> 0) by lia.
    pose proof (divides_le Hne Hd) as H2.
    lia.
Qed.

(* Look for a prime from m up, giving up (and returning m) when the fuel
   runs out. *)
Fixpoint rlz_scan (fuel m : nat) : nat :=
  match fuel with
  | 0 => m
  | S f => if prime_bool m then m else rlz_scan f (S m)
  end.

(* Any fuel larger than the distance to the next prime finds it. *)
Lemma rlz_scan_ok : forall n fuel m,
  n < m -> m <= nxtprime n -> nxtprime n - m < fuel -> rlz_scan fuel m = nxtprime n.
Proof.
  intro n.
  pose proof (proj2_sig (first_prime_above n)) as (Hlt & Hpr & Hmin).
  change (n < nxtprime n) in Hlt. change (prime (nxtprime n)) in Hpr.
  change (forall q, n < q -> prime q -> nxtprime n <= q) in Hmin.
  induction fuel as [| f IH]; intros m H1 H2 H3; [lia |].
  simpl. destruct (prime_bool m) eqn:Hb.
  - apply prime_bool_spec in Hb. pose proof (Hmin m H1 Hb). lia.
  - destruct (Nat.eq_dec m (nxtprime n)) as [E | E].
    + exfalso. subst. apply prime_bool_spec in Hpr. congruence.
    + apply IH; lia.
Qed.

(* nxtprime with an explicit fuel. *)
Definition rlz_nxtprime_with (fuel n : nat) : nat := rlz_scan fuel (S n).

Theorem rlz_nxtprime_with_eq : forall fuel n,
  nxtprime n - S n < fuel -> rlz_nxtprime_with fuel n = nxtprime n.
Proof.
  intros fuel n H. unfold rlz_nxtprime_with. apply rlz_scan_ok.
  - lia.
  - pose proof (nxtprime_spec1 n). lia.
  - exact H.
Qed.

(* The fuel fact n + 1 always suffices. *)
Definition rlz_nxtprime (n : nat) : nat := rlz_nxtprime_with (S (fact n)) n.

Theorem rlz_nxtprime_eq : forall n, rlz_nxtprime n = nxtprime n.
Proof.
  intro n. unfold rlz_nxtprime. apply rlz_nxtprime_with_eq.
  pose proof (rlz_nxtprime_le n). lia.
Qed.

(* nthprime and qs built from any nxtprime-like step. *)
Definition rlz_nthprime_with (nx : nat -> nat) (n : nat) : nat := iter nx 2 n.
Definition rlz_qs_with (nx : nat -> nat) (i : nat) : nat := rlz_nthprime_with nx (1 + 2 * i).

Lemma rlz_iter_ext : forall (f g : nat -> nat), (forall x, f x = g x) ->
  forall n x, iter f x n = iter g x n.
Proof.
  intros f g H n. induction n as [| n IH]; intro x; simpl; [reflexivity |].
  rewrite H. apply IH.
Qed.

Theorem rlz_qs_with_eq : forall nx, (forall n, nx n = nxtprime n) ->
  forall i, rlz_qs_with nx i = qs i.
Proof.
  intros nx H i. unfold rlz_qs_with, rlz_nthprime_with.
  change (qs i) with (nthprime (1 + 2 * i)). unfold nthprime.
  apply rlz_iter_ext, H.
Qed.

Definition rlz_qs : nat -> nat := rlz_qs_with rlz_nxtprime.

Theorem rlz_qs_eq : forall i, rlz_qs i = qs i.
Proof. exact (rlz_qs_with_eq rlz_nxtprime rlz_nxtprime_eq). Qed.

(* ================================================================= *)
(* 2. The counter-program checker, over a computable prime stream.    *)
(* ================================================================= *)

(* CompilerCodes.v cg_expo_fuel, cg_expo. *)
Fixpoint rlz_expo_fuel (f p n : nat) : nat :=
  match f with
  | 0 => 0
  | S f' =>
      if Nat.eqb (n mod p) 0 && Nat.ltb 0 n && Nat.ltb 1 p
      then S (rlz_expo_fuel f' p (n / p))
      else 0
  end.

Definition rlz_expo (p n : nat) : nat := rlz_expo_fuel n p n.

(* The counter-program instructions of CompilerCodes.v (mm_instr nat). *)
Inductive rlz_mm : Type := RInc (x : nat) | RDec (x j : nat).

Definition rlz_of_mm (I : mm_instr nat) : rlz_mm :=
  match I with mm_inc x => RInc x | mm_dec x j => RDec x j end.

(* CompilerCodes.v cg_idec, cg_pdec_list, cg_pdec, cg_rdec. *)
Definition rlz_idec (n : nat) : option rlz_mm :=
  match Minimal.EarnedGeneric.decode n with
  | [0; x] => Some (RInc x)
  | [1; x; j] => Some (RDec x j)
  | _ => None
  end.

Fixpoint rlz_pdec_list (l : list nat) : option (list rlz_mm) :=
  match l with
  | [] => Some []
  | n :: l' =>
      match rlz_idec n, rlz_pdec_list l' with
      | Some J, Some R => Some (J :: R)
      | _, _ => None
      end
  end.

Definition rlz_pdec_prog (n : nat) : option (list rlz_mm) :=
  rlz_pdec_list (Minimal.EarnedGeneric.decode n).

Definition rlz_rdec (r : nat) : option (nat * list rlz_mm * nat * nat * nat * nat) :=
  match Minimal.EarnedGeneric.decode r with
  | [ig; xS; xB; xT; m; rc] =>
      match rlz_pdec_prog rc with
      | Some R => Some (ig, R, xS, xB, xT, m)
      | None => None
      end
  | _ => None
  end.

(* CompilerCodes.v cg_mme_fetch, cg_mme_exec, cg_mme_step, cg_mme_run_fuel,
   with the register file a function and set_env its update. *)
Definition rlz_mstate : Type := (nat * (nat -> nat))%type.

Definition rlz_set (e : nat -> nat) (x v : nat) : nat -> nat :=
  fun y => if Nat.eqb x y then v else e y.

Definition rlz_mme_fetch (P : nat * list rlz_mm) (i : nat) : option rlz_mm :=
  if Nat.leb (fst P) i then nth_error (snd P) (i - fst P) else None.

Definition rlz_mme_exec (I : rlz_mm) (st : rlz_mstate) : rlz_mstate :=
  let (i, e) := st in
  match I with
  | RInc x => (S i, rlz_set e x (S (e x)))
  | RDec x j =>
      match e x with
      | 0 => (j, e)
      | S u => (S i, rlz_set e x u)
      end
  end.

Definition rlz_mme_step (P : nat * list rlz_mm) (st : rlz_mstate) : option rlz_mstate :=
  match rlz_mme_fetch P (fst st) with
  | Some J => Some (rlz_mme_exec J st)
  | None => None
  end.

Fixpoint rlz_mme_run_fuel (n : nat) (P : nat * list rlz_mm) (st : rlz_mstate) : rlz_mstate :=
  match n with
  | 0 => st
  | S n' =>
      match rlz_mme_step P st with
      | Some st' => rlz_mme_run_fuel n' P st'
      | None => st
      end
  end.

Definition rlz_out_codeb (P : nat * list rlz_mm) (i : nat) : bool :=
  Nat.ltb i (fst P) || Nat.leb (fst P + length (snd P)) i.

(* The universal properties (CompilerChecker.v cg_uprop). *)
Inductive rlz_uprop : Type :=
| RUBase (q : Minimal.EarnedGeneric.cprop)
| RURun (r : nat).

Definition rlz_of_cg (p : CK.cg_uprop) : rlz_uprop :=
  match p with CK.UBase q => RUBase q | CK.URun r => RURun r end.

Definition rlz_to_cg (p : rlz_uprop) : CK.cg_uprop :=
  match p with RUBase q => CK.UBase q | RURun r => CK.URun r end.

(* cg_env_chk, cg_run_check, cg_ueval with qs replaced by qs'. *)
Definition rlz_env_chk (qs' : nat -> nat) (m v : nat) : nat -> nat :=
  fun x => if Nat.ltb x m then rlz_expo (qs' x) v else 0.

Definition rlz_run_check_with (qs' : nat -> nat)
  (rc : nat * list rlz_mm * nat * nat * nat * nat) (v : nat) : bool :=
  match rc with
  | (ig, R, xS, xB, xT, m) =>
      let st := rlz_mme_run_fuel (rlz_expo (qs' xT) v) (ig, R) (ig, rlz_env_chk qs' m v) in
      rlz_out_codeb (ig, R) (fst st) && Nat.eqb (snd st xB) 1
  end.

Definition rlz_ueval_with (qs' : nat -> nat) (p : rlz_uprop) (v : nat) : bool :=
  match p with
  | RUBase q => Minimal.EarnedGeneric.ceval q v
  | RURun r =>
      match rlz_rdec r with
      | Some rc => rlz_run_check_with qs' rc v
      | None => false
      end
  end.

(* ----- the proof that this is cg_ueval ----- *)

Local Transparent get_env set_env.

(* A counter-program state of the original and one of the copy agree when
   the program counters are equal and every register reads the same. *)
Definition rlz_st_rel (a : CC.cg_mstate) (b : rlz_mstate) : Prop :=
  fst a = fst b /\ forall x, get_env (snd a) x = snd b x.

Lemma rlz_expo_fuel_eq : forall f p n, rlz_expo_fuel f p n = CC.cg_expo_fuel f p n.
Proof. reflexivity. Qed.

Lemma rlz_expo_eq : forall p n, rlz_expo p n = CC.cg_expo p n.
Proof. reflexivity. Qed.

Lemma rlz_idec_eq : forall n, rlz_idec n = option_map rlz_of_mm (CC.cg_idec n).
Proof.
  intro n. unfold rlz_idec, CC.cg_idec.
  destruct (Minimal.EarnedGeneric.decode n) as [| a l1]; [reflexivity |].
  destruct a as [| [| a]]; destruct l1 as [| b [| c l2]]; try reflexivity;
    destruct l2; reflexivity.
Qed.

Lemma rlz_pdec_list_eq : forall l,
  rlz_pdec_list l = option_map (map rlz_of_mm) (CC.cg_pdec_list l).
Proof.
  induction l as [| n l IH]; [reflexivity |]. simpl.
  rewrite rlz_idec_eq, IH.
  destruct (CC.cg_idec n) as [J |]; [| reflexivity]. simpl.
  destruct (CC.cg_pdec_list l); reflexivity.
Qed.

Lemma rlz_pdec_prog_eq : forall n,
  rlz_pdec_prog n = option_map (map rlz_of_mm) (CC.cg_pdec n).
Proof. intro n. apply rlz_pdec_list_eq. Qed.

Lemma rlz_rdec_eq : forall r,
  rlz_rdec r = option_map (fun rc : CC.cg_routine_code =>
    let '(ig, R, xS, xB, xT, m) := rc in (ig, map rlz_of_mm R, xS, xB, xT, m)) (CC.cg_rdec r).
Proof.
  intro r. unfold rlz_rdec, CC.cg_rdec.
  destruct (Minimal.EarnedGeneric.decode r)
    as [| a1 [| a2 [| a3 [| a4 [| a5 [| a6 l]]]]]]; try reflexivity.
  destruct l; [| reflexivity].
  rewrite rlz_pdec_prog_eq.
  destruct (CC.cg_pdec a6); reflexivity.
Qed.

Lemma rlz_exec_sim : forall I a b, rlz_st_rel a b ->
  rlz_st_rel (CC.cg_mme_exec I a) (rlz_mme_exec (rlz_of_mm I) b).
Proof.
  intros I [i e] [j f] [Hij He]. unfold rlz_st_rel in *. simpl in Hij, He.
  subst j. unfold get_env in He.
  destruct I as [x | x j]; unfold CC.cg_mme_exec, rlz_mme_exec, rlz_set, set_env, get_env; simpl.
  - split; [reflexivity |]. intro y. cbn.
    destruct (Nat.eq_dec x y) as [Hxy | Hxy].
    + subst y. rewrite Nat.eqb_refl. now rewrite (He x).
    + rewrite (proj2 (Nat.eqb_neq x y) Hxy). apply He.
  - rewrite (He x). destruct (f x) as [| u].
    + split; [reflexivity |]. intro y. cbn. apply He.
    + split; [reflexivity |]. intro y. cbn.
      destruct (Nat.eq_dec x y) as [Hxy | Hxy].
      * subst y. now rewrite Nat.eqb_refl.
      * rewrite (proj2 (Nat.eqb_neq x y) Hxy). apply He.
Qed.

Lemma rlz_run_fuel_sim : forall n R ig a b, rlz_st_rel a b ->
  rlz_st_rel (CC.cg_mme_run_fuel n (ig, R) a)
             (rlz_mme_run_fuel n (ig, map rlz_of_mm R) b).
Proof.
  induction n as [| n IH]; intros R ig a b H; [exact H |].
  simpl. unfold CC.cg_mme_step, rlz_mme_step, CC.cg_mme_fetch, rlz_mme_fetch.
  destruct H as [Hf He]. simpl. rewrite <- Hf.
  destruct (Nat.leb ig (fst a)); simpl.
  - rewrite nth_error_map.
    destruct (nth_error R (fst a - ig)) as [J |]; simpl.
    + apply IH. apply rlz_exec_sim. split; assumption.
    + split; assumption.
  - split; assumption.
Qed.

Lemma rlz_out_codeb_eq : forall ig R i,
  rlz_out_codeb (ig, map rlz_of_mm R) i = CK.cg_out_codeb (ig, R) i.
Proof.
  intros ig R i. unfold rlz_out_codeb, CK.cg_out_codeb. simpl.
  rewrite map_length. reflexivity.
Qed.

Theorem rlz_ueval_with_eq : forall qs', (forall i, qs' i = qs i) ->
  forall p v, rlz_ueval_with qs' (rlz_of_cg p) v = CK.cg_ueval p v.
Proof.
  intros qs' H [q | r] v; [reflexivity |].
  unfold rlz_of_cg, rlz_ueval_with, CK.cg_ueval. rewrite rlz_rdec_eq.
  destruct (CC.cg_rdec r) as [[[[[[ig R] xS] xB] xT] m] |]; [| reflexivity].
  cbv beta iota zeta delta [option_map].
  unfold rlz_run_check_with, CK.cg_run_check.
  rewrite rlz_expo_eq, (H xT).
  assert (Hst : rlz_st_rel
    (CC.cg_mme_run_fuel (CC.cg_expo (qs xT) v) (ig, R) (ig, CK.cg_env_chk m v))
    (rlz_mme_run_fuel (CC.cg_expo (qs xT) v) (ig, map rlz_of_mm R) (ig, rlz_env_chk qs' m v))).
  { apply rlz_run_fuel_sim. split; [reflexivity |]. intro x.
    unfold rlz_env_chk, CK.cg_env_chk, get_env. cbn [snd].
    destruct (Nat.ltb x m); [| reflexivity].
    rewrite (H x). reflexivity. }
  destruct Hst as [Hf He]. rewrite <- Hf, <- (He xB), rlz_out_codeb_eq. reflexivity.
Qed.

Definition rlz_ueval : rlz_uprop -> nat -> bool := rlz_ueval_with rlz_qs.

Theorem rlz_ueval_eq : forall p v, rlz_ueval (rlz_of_cg p) v = CK.cg_ueval p v.
Proof. exact (rlz_ueval_with_eq rlz_qs rlz_qs_eq). Qed.

(* ================================================================= *)
(* 3. The property PSlot of the priced host.                          *)
(* ================================================================= *)

(* UniversalPCodes.v pu_cpdec, pu_pdec, pu_heval, pu_hprop_eqb. The pairing
   functions are those of Realize.v (equal to pu_pair, pu_unpair, which are
   equal to pair, unpair). *)
Definition rlz_pu_cpdec (n : nat) : Minimal.EarnedGeneric.cprop :=
  match n with
  | 0 => Minimal.EarnedGeneric.PZero
  | 1 => Minimal.EarnedGeneric.PEven
  | S (S m) => Minimal.EarnedGeneric.PGe m
  end.

Definition rlz_pu_pdec (n : nat) : rlz_uprop :=
  if Nat.even n then RUBase (rlz_pu_cpdec (Nat.div2 n)) else RURun (Nat.div2 n).

Definition rlz_pu_heval_with (qs' : nat -> nat) (p : Kernel.UniversalPCodes.pu_hprop) (x : nat) : bool :=
  match Kernel.Realize.rlz_unpair x with
  | Some (m, v) => rlz_ueval_with qs' (rlz_pu_pdec m) v
  | None => false
  end.

Definition rlz_pu_heval : Kernel.UniversalPCodes.pu_hprop -> nat -> bool :=
  rlz_pu_heval_with rlz_qs.

Definition rlz_phost_prop_eqb (p q : Kernel.UniversalPCodes.pu_hprop) : bool :=
  match p, q with Kernel.UniversalPCodes.PSlot, Kernel.UniversalPCodes.PSlot => true end.

Lemma rlz_phost_prop_eqb_is : rlz_phost_prop_eqb = UPC.pu_hprop_eqb. Proof. reflexivity. Qed.

Lemma rlz_pu_pdec_eq : forall n, rlz_pu_pdec n = rlz_of_cg (UPC.pu_pdec n).
Proof.
  intro n. unfold rlz_pu_pdec, UPC.pu_pdec. destruct (Nat.even n); reflexivity.
Qed.

Theorem rlz_pu_heval_with_eq : forall qs', (forall i, qs' i = qs i) ->
  forall p x, rlz_pu_heval_with qs' p x = UPC.pu_heval p x.
Proof.
  intros qs' H p x. unfold rlz_pu_heval_with, UPC.pu_heval.
  rewrite Kernel.Realize.rlz_unpair_is. fold UC.unpair.
  change (UC.unpair x) with (UPC.pu_unpair x).
  destruct (UPC.pu_unpair x) as [[m v] |]; [| reflexivity].
  rewrite rlz_pu_pdec_eq. apply rlz_ueval_with_eq, H.
Qed.

Theorem rlz_pu_heval_eq : forall p x, rlz_pu_heval p x = UPC.pu_heval p x.
Proof. exact (rlz_pu_heval_with_eq rlz_qs rlz_qs_eq). Qed.

(* ================================================================= *)
(* 4. A run under pointwise-equal evaluations is the same run.        *)
(* ================================================================= *)

Section Ext.
Variable prop : Type.
Variable prop_eqb : prop -> prop -> bool.
Variables e1 e2 : prop -> nat -> bool.
Hypothesis Heq : forall p x, e1 p x = e2 p x.

Lemma rlz_pu_check_ok_ext : forall k p r,
  PM.pu_check_ok e1 k p r = PM.pu_check_ok e2 k p r.
Proof. intros k p r. unfold PM.pu_check_ok. rewrite Heq. reflexivity. Qed.

Lemma rlz_pu_cexec_ext : forall k i,
  PM.pu_cexec prop_eqb e1 k i = PM.pu_cexec prop_eqb e2 k i.
Proof.
  intros k i. unfold PM.pu_cexec.
  destruct (PM.err k); [reflexivity |].
  destruct i; try reflexivity.
  rewrite rlz_pu_check_ok_ext. reflexivity.
Qed.

Lemma rlz_pu_exec_ext : forall s i,
  PM.pu_exec prop_eqb e1 s i = PM.pu_exec prop_eqb e2 s i.
Proof.
  intros s i. unfold PM.pu_exec. rewrite rlz_pu_cexec_ext. reflexivity.
Qed.

Theorem rlz_pu_run_prog_ext : forall n P s,
  PM.pu_run_prog prop_eqb e1 n P s = PM.pu_run_prog prop_eqb e2 n P s.
Proof.
  induction n as [| n IH]; intros P s; [reflexivity |].
  simpl. unfold PM.pu_step.
  destruct (PM.pu_next_instr P (PM.core_of s)) as [i |].
  - rewrite rlz_pu_exec_ext. apply IH.
  - apply IH.
Qed.

Lemma rlz_pr_check_ok_ext : forall k p c,
  G.check_ok e1 k p c = G.check_ok e2 k p c.
Proof. intros k p c. unfold G.check_ok. rewrite Heq. reflexivity. Qed.

Lemma rlz_pr_cexec_ext : forall k i,
  PG.pr_cexec prop_eqb e1 k i = PG.pr_cexec prop_eqb e2 k i.
Proof.
  intros k i. unfold PG.pr_cexec.
  destruct (G.err k); [reflexivity |].
  destruct i; try reflexivity.
  rewrite rlz_pr_check_ok_ext. reflexivity.
Qed.

Lemma rlz_pr_exec_ext : forall s i,
  PG.pr_exec prop_eqb e1 s i = PG.pr_exec prop_eqb e2 s i.
Proof.
  intros s i. unfold PG.pr_exec. rewrite rlz_pr_cexec_ext. reflexivity.
Qed.

Theorem rlz_pr_run_prog_ext : forall n P s,
  PG.pr_run_prog prop_eqb e1 n P s = PG.pr_run_prog prop_eqb e2 n P s.
Proof.
  induction n as [| n IH]; intros P s; [reflexivity |].
  simpl. unfold PG.pr_step.
  destruct (PG.pr_next_instr P (G.core_of s)) as [i |].
  - rewrite rlz_pr_exec_ext. apply IH.
  - apply IH.
Qed.
End Ext.

(* ================================================================= *)
(* 5. The priced host and its loader.                                 *)
(* ================================================================= *)

Definition rlz_phost_exec :=
  Minimal.EarnedMultiPriced.pu_exec rlz_phost_prop_eqb rlz_pu_heval.
Definition rlz_phost_run :=
  Minimal.EarnedMultiPriced.pu_run rlz_phost_prop_eqb rlz_pu_heval.
Definition rlz_phost_step :=
  Minimal.EarnedMultiPriced.pu_step rlz_phost_prop_eqb rlz_pu_heval.
Definition rlz_phost_run_prog :=
  Minimal.EarnedMultiPriced.pu_run_prog rlz_phost_prop_eqb rlz_pu_heval.
Definition rlz_phost_trace_of :=
  Minimal.EarnedMultiPriced.pu_trace_of rlz_phost_prop_eqb rlz_pu_heval.
Definition rlz_phost_start :=
  @Minimal.EarnedMultiPriced.pu_start Kernel.UniversalPCodes.pu_hprop.

(* U_P: the literal list of RealizePrograms.v, proved equal to U_P. *)
Definition rlz_phost_program :
  list (@Minimal.EarnedMultiPriced.pu_instr Kernel.UniversalPCodes.pu_hprop) :=
  Kernel.RealizePrograms.rlz_phost_program.

Lemma rlz_phost_program_is : rlz_phost_program = UPL.U_P.
Proof. exact Kernel.RealizePrograms.rlz_phost_program_is. Qed.

(* The guest instructions of U_P, a copy of the type of UniversalPCodes.v
   E.instr (the priced guest over cg_uprop). *)
Inductive rlz_ctr : Type := RCA | RCB.

Inductive rlz_pinstr : Type :=
| PINC (c : rlz_ctr)
| PDEC (c : rlz_ctr) (j : nat)
| PHALT
| PCHECK (p : rlz_uprop) (c : rlz_ctr)
| PCOMMIT (p : rlz_uprop) (c : rlz_ctr)
| PCERTIFY
| PPAY.

Definition rlz_to_ctr (c : rlz_ctr) : G.ctr := match c with RCA => G.CA | RCB => G.CB end.

Definition rlz_to_pr (i : rlz_pinstr) : UPC.E.instr :=
  match i with
  | PINC c => PG.INC (rlz_to_ctr c)
  | PDEC c j => PG.DEC (rlz_to_ctr c) j
  | PHALT => PG.HALT
  | PCHECK p c => PG.CHECK (rlz_to_cg p) (rlz_to_ctr c)
  | PCOMMIT p c => PG.COMMIT (rlz_to_cg p) (rlz_to_ctr c)
  | PCERTIFY => PG.CERTIFY
  | PPAY => PG.PAY
  end.

(* UniversalPCodes.v pu_pcode, pu_cpcode, pu_ccode, pu_icode, pu_prog_code. *)
Definition rlz_pu_cpcode (q : Minimal.EarnedGeneric.cprop) : nat :=
  match q with
  | Minimal.EarnedGeneric.PZero => 0
  | Minimal.EarnedGeneric.PEven => 1
  | Minimal.EarnedGeneric.PGe n => n + 2
  end.

Definition rlz_pu_pcode (p : rlz_uprop) : nat :=
  match p with RUBase q => 2 * rlz_pu_cpcode q | RURun r => S (2 * r) end.

Definition rlz_pu_ccode (c : rlz_ctr) : nat := match c with RCA => 0 | RCB => 1 end.

Definition rlz_pu_icode (i : rlz_pinstr) : nat :=
  match i with
  | PINC c => Kernel.Realize.rlz_pair 0 (rlz_pu_ccode c)
  | PDEC c j => Kernel.Realize.rlz_pair 1 (Kernel.Realize.rlz_pair (rlz_pu_ccode c) j)
  | PHALT => Kernel.Realize.rlz_pair 2 0
  | PCHECK p c => Kernel.Realize.rlz_pair 3 (Kernel.Realize.rlz_pair (rlz_pu_ccode c) (rlz_pu_pcode p))
  | PCOMMIT p c => Kernel.Realize.rlz_pair 4 (Kernel.Realize.rlz_pair (rlz_pu_ccode c) (rlz_pu_pcode p))
  | PCERTIFY => Kernel.Realize.rlz_pair 5 0
  | PPAY => Kernel.Realize.rlz_pair 6 0
  end.

Definition rlz_pu_prog_code (P : list rlz_pinstr) : nat :=
  Minimal.EarnedGeneric.encode (map rlz_pu_icode P).

Lemma rlz_pu_ccode_eq : forall c, rlz_pu_ccode c = UPC.pu_ccode (rlz_to_ctr c).
Proof. intros []; reflexivity. Qed.

Lemma rlz_pu_cpcode_eq : forall q, rlz_pu_cpcode q = UPC.pu_cpcode q.
Proof. intros [| | n]; reflexivity. Qed.

Lemma rlz_pu_pcode_eq : forall p, rlz_pu_pcode p = UPC.pu_pcode (rlz_to_cg p).
Proof.
  intros [q | r]; cbn [rlz_pu_pcode rlz_to_cg].
  - unfold UPC.pu_pcode. rewrite rlz_pu_cpcode_eq. reflexivity.
  - reflexivity.
Qed.

Lemma rlz_pu_icode_eq : forall i, rlz_pu_icode i = UPC.pu_icode (rlz_to_pr i).
Proof.
  intros [c | c j | | p c | p c | |]; cbn [rlz_pu_icode rlz_to_pr];
    unfold UPC.pu_icode;
    rewrite ?rlz_pu_ccode_eq, ?rlz_pu_pcode_eq; reflexivity.
Qed.

Lemma rlz_pu_prog_code_eq : forall P,
  rlz_pu_prog_code P = UPC.pu_prog_code (map rlz_to_pr P).
Proof.
  intro P. unfold rlz_pu_prog_code, UPC.pu_prog_code. f_equal.
  rewrite map_map. apply map_ext. intro i. apply rlz_pu_icode_eq.
Qed.

(* The loader: pu_hregs, pu_hload (UniversalPSim.v). *)
Definition rlz_phost_regs (P : list rlz_pinstr) (x y r : nat) : nat :=
  if Nat.eqb r 0 then x else
  if Nat.eqb r 1 then y else
  if Nat.eqb r 2 then rlz_pu_prog_code P else
  if Nat.eqb r 3 then 1 else 0.

Definition rlz_phost_load (P : list rlz_pinstr) (x y : nat)
  : @Minimal.EarnedMultiPriced.pu_state Kernel.UniversalPCodes.pu_hprop :=
  rlz_phost_start (rlz_phost_regs P x y).

Theorem rlz_phost_load_eq : forall P x y,
  rlz_phost_load P x y = UPS.pu_hload (map rlz_to_pr P) x y.
Proof.
  intros P x y. unfold rlz_phost_load, UPS.pu_hload, rlz_phost_start, rlz_phost_regs, UPS.pu_hregs.
  rewrite rlz_pu_prog_code_eq. reflexivity.
Qed.

(* The extracted host run is the run of the theorems, state for state. *)
Theorem rlz_phost_run_prog_eq : forall n P s,
  rlz_phost_run_prog n P s =
  PM.pu_run_prog UPC.pu_hprop_eqb UPC.pu_heval n P s.
Proof.
  intros n P s. unfold rlz_phost_run_prog.
  apply rlz_pu_run_prog_ext. exact rlz_pu_heval_eq.
Qed.

(* The host after n steps of U_P from the loaded priced guest P. *)
Definition rlz_phost_at (P : list rlz_pinstr) (x y n : nat)
  : @Minimal.EarnedMultiPriced.pu_state Kernel.UniversalPCodes.pu_hprop :=
  rlz_phost_run_prog n rlz_phost_program (rlz_phost_load P x y).

Theorem rlz_phost_at_eq : forall P x y n,
  rlz_phost_at P x y n =
  PM.pu_run_prog UPC.pu_hprop_eqb UPC.pu_heval n UPL.U_P (UPS.pu_hload (map rlz_to_pr P) x y).
Proof.
  intros P x y n. unfold rlz_phost_at.
  rewrite rlz_phost_load_eq, rlz_phost_program_is. apply rlz_phost_run_prog_eq.
Qed.

(* ================================================================= *)
(* 6. The priced guest, for the unit tests (not extracted).           *)
(* ================================================================= *)

(* The priced guest over cg_uprop with the checker built from a given
   prime stream. With qs' = qs this is the guest of UniversalPRun.v
   (rlz_pguest_run_prog_eq); the unit tests give a table for qs' that Coq
   can evaluate. *)
Definition rlz_ueval_cg_with (qs' : nat -> nat) (p : CK.cg_uprop) (v : nat) : bool :=
  rlz_ueval_with qs' (rlz_of_cg p) v.

Definition rlz_pguest_run_prog_with (qs' : nat -> nat) :=
  PG.pr_run_prog CK.cg_uprop_eqb (rlz_ueval_cg_with qs').

Definition rlz_pguest_step_with (qs' : nat -> nat) :=
  PG.pr_step CK.cg_uprop_eqb (rlz_ueval_cg_with qs').

Theorem rlz_pguest_run_prog_eq : forall n P s,
  rlz_pguest_run_prog_with qs n P s =
  PG.pr_run_prog CK.cg_uprop_eqb CK.cg_ueval n P s.
Proof.
  intros n P s. unfold rlz_pguest_run_prog_with.
  apply rlz_pr_run_prog_ext. intros p x. unfold rlz_ueval_cg_with.
  apply rlz_ueval_with_eq. intro i. reflexivity.
Qed.

(* The host of the unit tests: the priced host with a given prime stream. *)
Definition rlz_phost_step_with (qs' : nat -> nat) :=
  PM.pu_step UPC.pu_hprop_eqb (rlz_pu_heval_with qs').

Theorem rlz_phost_run_prog_with_eq : forall n P s,
  PM.pu_run_prog UPC.pu_hprop_eqb (rlz_pu_heval_with qs) n P s =
  PM.pu_run_prog UPC.pu_hprop_eqb UPC.pu_heval n P s.
Proof.
  intros n P s. apply rlz_pu_run_prog_ext. apply rlz_pu_heval_with_eq. intro i. reflexivity.
Qed.
