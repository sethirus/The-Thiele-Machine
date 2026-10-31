(** CompilerCodes.v: the codes the compiler from many-register counter
    machines to two-counter guests relies on.

      1. The Godel code of a register file: cg_gk k e is the product of
         qs x ^ e x over the registers x < k, where qs is the vendored
         stream of distinct primes. The exponent reader cg_expo is a plain
         total function, and cg_expo (qs x) (cg_gk k e) = e x
         [cg_expo_gk_zero]. Incrementing register x multiplies the code by
         qs x [cg_gk_inc]; decrementing a positive register divides it by
         qs x [cg_gk_dec]; a zero register leaves the code not divisible by
         qs x [cg_gk_zero_not_div].
      2. A code for a reading routine: a start address, a counter program
         and four register indices packed into one number, with a decoder
         that inverts the encoder [cg_rdec_renc].
      3. A fuel interpreter for counter programs with registers held in an
         environment (the vendored mm_sss_env semantics, which jumps when
         the register is zero). One interpreter step is exactly one step of
         the vendored semantics [cg_mme_step_sound, cg_mme_step_complete];
         running with fuel n is a run of at most n steps
         [cg_mme_run_fuel_sound], and reaches the exit of any run of at
         most n steps that leaves the code [cg_mme_run_fuel_complete].
         Environments equal at every register give runs equal at every
         register [cg_mme_run_ext].

    Dependencies: Coq standard library, the vendored coq-undecidability
    library (prime stream, counter machine semantics, code lemmas) and
    EarnedGeneric.v (list encoding). No axioms, no Admitted. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the presented universal machine of
   PresentedUniversal.v and imports only the Coq standard library, the
   vendored coq-undecidability library and the standard-library files under
   minimal/. Its link to the abstract record (the priced host as a
   CertificationSystem, the cost floor of its runs, and the undecidability
   of U_P's halting problem) lives in PricedHostLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.Shared.Libs.DLW.Utils Require Import gcd prime.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
From Undecidability.MinskyMachines Require Import MM.
From Undecidability.MinskyMachines.MMenv Require Import env mme_defs.
Require Minimal.EarnedGeneric.
Module G := Minimal.EarnedGeneric.


(* ================================================================= *)
(* 1. Exponents and the Godel code of a register file.                 *)
(* ================================================================= *)

(* The number of times p divides n, with n itself as fuel. *)
Fixpoint cg_expo_fuel (f p n : nat) : nat :=
  match f with
  | 0 => 0
  | S f' =>
      if Nat.eqb (n mod p) 0 && Nat.ltb 0 n && Nat.ltb 1 p
      then S (cg_expo_fuel f' p (n / p))
      else 0
  end.

Definition cg_expo (p n : nat) : nat := cg_expo_fuel n p n.

Lemma cg_divides_mod : forall p n, 0 < p -> (n mod p = 0 <-> divides p n).
Proof.
  intros p n Hp. split.
  - intros H. exists (n / p).
    rewrite (Nat.div_mod n p) at 1 by lia. rewrite H. lia.
  - intros [q ->]. apply Nat.Div0.mod_mul.
Qed.

Lemma cg_expo_fuel_spec : forall p a b f,
  1 < p -> ~ divides p b -> 0 < b -> a < f ->
  cg_expo_fuel f p (p ^ a * b) = a.
Proof.
  intros p a b f Hp Hb Hb0. revert f.
  induction a as [| a IH]; intros f Hf.
  - destruct f as [| f]; [lia |]. simpl.
    rewrite Nat.add_0_r.
    destruct (Nat.eqb (b mod p) 0) eqn:E; [| reflexivity].
    apply Nat.eqb_eq, cg_divides_mod in E; [contradiction | lia].
  - destruct f as [| f]; [lia |]. simpl.
    assert (Hpa : 0 < p ^ a) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    replace (p * p ^ a * b) with ((p ^ a * b) * p) by ring.
    rewrite Nat.Div0.mod_mul. rewrite Nat.div_mul by lia.
    replace (Nat.ltb 0 (p ^ a * b * p)) with true
      by (symmetry; apply Nat.ltb_lt; nia).
    replace (Nat.ltb 1 p) with true by (symmetry; apply Nat.ltb_lt; lia).
    simpl. f_equal. apply IH. lia.
Qed.

(* The exponent of p in p ^ a * b, for b positive and not divisible by p. *)
Theorem cg_expo_spec : forall p a b,
  1 < p -> ~ divides p b -> 0 < b -> cg_expo p (p ^ a * b) = a.
Proof.
  intros p a b Hp Hb Hb0. unfold cg_expo. apply cg_expo_fuel_spec; auto.
  assert (a < p ^ a) by (apply Nat.pow_gt_lin_r; lia). nia.
Qed.

Lemma cg_qs_prime : forall x, prime (qs x).
Proof. intros x. apply str_prime. Qed.

Lemma cg_qs_gt1 : forall x, 1 < qs x.
Proof. intros x. generalize (prime_ge_2 (cg_qs_prime x)). lia. Qed.

(* The Godel code of the first k registers of e. *)
Fixpoint cg_gk (k : nat) (e : nat -> nat) : nat :=
  match k with
  | 0 => 1
  | S k' => cg_gk k' e * qs k' ^ e k'
  end.

Lemma cg_gk_pos : forall k e, 0 < cg_gk k e.
Proof.
  induction k as [| k IH]; intros e; simpl; [lia |].
  assert (0 < qs k ^ e k)
    by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; generalize (cg_qs_gt1 k); lia).
  apply Nat.mul_pos_pos; auto.
Qed.

Lemma cg_gk_ext : forall k e e',
  (forall y, y < k -> e y = e' y) -> cg_gk k e = cg_gk k e'.
Proof.
  induction k as [| k IH]; intros e e' H; simpl; [reflexivity |].
  rewrite (IH e e') by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma cg_gk_not_div : forall k e x,
  (x < k -> e x = 0) -> ~ divides (qs x) (cg_gk k e).
Proof.
  induction k as [| k IH]; intros e x Hx Hd; cbn [cg_gk] in Hd.
  - apply divides_1_inv in Hd. generalize (cg_qs_gt1 x). lia.
  - apply prime_div_mult in Hd; [| apply cg_qs_prime].
    destruct Hd as [Hd | Hd].
    + apply (IH e x); [intros; apply Hx; lia | exact Hd].
    + assert (Hxk : x = k).
      { apply (primestream_divides qs).
        apply divides_pow with (k := e k); [apply cg_qs_prime | exact Hd]. }
      subst k. rewrite Hx in Hd by lia. rewrite Nat.pow_0_r in Hd.
      apply divides_1_inv in Hd. generalize (cg_qs_gt1 x). lia.
Qed.

(* The register file with register x set to 0. *)
Definition cg_zero_at (e : nat -> nat) (x : nat) : nat -> nat :=
  fun y => if Nat.eqb y x then 0 else e y.

Lemma cg_gk_split : forall k e x, x < k ->
  cg_gk k e = qs x ^ e x * cg_gk k (cg_zero_at e x).
Proof.
  induction k as [| k IH]; intros e x Hx; [lia |].
  cbn [cg_gk]. unfold cg_zero_at at 2.
  destruct (Nat.eq_dec x k) as [-> | Hne].
  - rewrite Nat.eqb_refl. simpl.
    rewrite (cg_gk_ext k (cg_zero_at e k) e).
    + ring.
    + intros y Hy. unfold cg_zero_at.
      destruct (Nat.eqb_spec y k); [lia | reflexivity].
  - destruct (Nat.eqb_spec k x); [lia |].
    rewrite (IH e x) by lia. ring.
Qed.

Theorem cg_expo_gk : forall k e x,
  cg_expo (qs x) (cg_gk k e) = if Nat.ltb x k then e x else 0.
Proof.
  intros k e x. destruct (Nat.ltb_spec x k) as [Hx | Hx].
  - rewrite (cg_gk_split k e x Hx). apply cg_expo_spec.
    + apply cg_qs_gt1.
    + apply cg_gk_not_div. intros _. unfold cg_zero_at. rewrite Nat.eqb_refl. reflexivity.
    + apply cg_gk_pos.
  - replace (cg_gk k e) with (qs x ^ 0 * cg_gk k e) by (simpl; lia).
    apply cg_expo_spec.
    + apply cg_qs_gt1.
    + apply cg_gk_not_div. lia.
    + apply cg_gk_pos.
Qed.

Corollary cg_expo_gk_zero : forall k e x,
  (forall y, k <= y -> e y = 0) -> cg_expo (qs x) (cg_gk k e) = e x.
Proof.
  intros k e x H. rewrite cg_expo_gk.
  destruct (Nat.ltb_spec x k); [reflexivity | symmetry; apply H; lia].
Qed.

(* The code determines the register file on the first k registers. *)
Corollary cg_gk_inj : forall k e e',
  (forall y, k <= y -> e y = 0) -> (forall y, k <= y -> e' y = 0) ->
  cg_gk k e = cg_gk k e' -> forall y, e y = e' y.
Proof.
  intros k e e' He He' Heq y.
  rewrite <- (cg_expo_gk_zero k e y He), <- (cg_expo_gk_zero k e' y He'), Heq.
  reflexivity.
Qed.

Lemma cg_get_env : forall (e : env nat nat) x, get_env e x = e x.
Proof. intros. unfold get_env. reflexivity. Qed.

Lemma cg_set_env_eq : forall (e : env nat nat) x v, set_env eq_nat_dec e x v x = v.
Proof.
  intros. unfold set_env. destruct (eq_nat_dec x x); [reflexivity | congruence].
Qed.

Lemma cg_set_env_neq : forall (e : env nat nat) x v y,
  x <> y -> set_env eq_nat_dec e x v y = e y.
Proof.
  intros. unfold set_env. destruct (eq_nat_dec x y); [congruence | reflexivity].
Qed.

Lemma cg_zero_at_set : forall e x v,
  forall y, cg_zero_at (set_env eq_nat_dec e x v) x y = cg_zero_at e x y.
Proof.
  intros e x v y. unfold cg_zero_at.
  destruct (Nat.eqb_spec y x); [reflexivity |].
  apply cg_set_env_neq. auto.
Qed.

(* Incrementing register x multiplies the code by qs x. *)
Theorem cg_gk_inc : forall k e x, x < k ->
  cg_gk k (set_env eq_nat_dec e x (S (e x))) = qs x * cg_gk k e.
Proof.
  intros k e x Hx.
  rewrite (cg_gk_split k (set_env eq_nat_dec e x (S (e x))) x Hx).
  rewrite (cg_gk_split k e x Hx).
  rewrite cg_set_env_eq.
  rewrite (cg_gk_ext k (cg_zero_at (set_env eq_nat_dec e x (S (e x))) x)
             (cg_zero_at e x)) by (intros; apply cg_zero_at_set).
  simpl. ring.
Qed.

(* Decrementing a positive register x divides the code by qs x. *)
Theorem cg_gk_dec : forall k e x u, x < k -> e x = S u ->
  cg_gk k e = qs x * cg_gk k (set_env eq_nat_dec e x u).
Proof.
  intros k e x u Hx Hu.
  rewrite (cg_gk_split k (set_env eq_nat_dec e x u) x Hx).
  rewrite (cg_gk_split k e x Hx).
  rewrite cg_set_env_eq, Hu.
  rewrite (cg_gk_ext k (cg_zero_at (set_env eq_nat_dec e x u) x)
             (cg_zero_at e x)) by (intros; apply cg_zero_at_set).
  simpl. ring.
Qed.

(* A zero register leaves the code not divisible by its prime. *)
Theorem cg_gk_zero_not_div : forall k e x,
  e x = 0 -> ~ divides (qs x) (cg_gk k e).
Proof. intros k e x H. apply cg_gk_not_div. auto. Qed.

(* ================================================================= *)
(* 2. The code of a reading routine.                                   *)
(* ================================================================= *)

(* A routine is (ig, R, xS, xB, xT, m): the counter program R placed at
   address ig, the register xS holding its input, the register xB holding
   its answer, the register xT holding a step budget, and the bound m
   below which registers are passed to the routine. *)
Definition cg_routine_code : Type :=
  (nat * list (mm_instr nat) * nat * nat * nat * nat)%type.

Definition cg_icode (I : mm_instr nat) : nat :=
  match I with
  | mm_inc x => G.encode [0; x]
  | mm_dec x j => G.encode [1; x; j]
  end.

Definition cg_idec (n : nat) : option (mm_instr nat) :=
  match G.decode n with
  | [0; x] => Some (mm_inc x)
  | [1; x; j] => Some (mm_dec x j)
  | _ => None
  end.

Lemma cg_idec_icode : forall I, cg_idec (cg_icode I) = Some I.
Proof.
  intros [x | x j]; unfold cg_idec, cg_icode; rewrite G.decode_encode; reflexivity.
Qed.

Fixpoint cg_pdec_list (l : list nat) : option (list (mm_instr nat)) :=
  match l with
  | [] => Some []
  | n :: l' =>
      match cg_idec n, cg_pdec_list l' with
      | Some J, Some R => Some (J :: R)
      | _, _ => None
      end
  end.

Definition cg_penc (R : list (mm_instr nat)) : nat := G.encode (map cg_icode R).
Definition cg_pdec (n : nat) : option (list (mm_instr nat)) := cg_pdec_list (G.decode n).

Lemma cg_pdec_penc : forall R, cg_pdec (cg_penc R) = Some R.
Proof.
  intros R. unfold cg_pdec, cg_penc. rewrite G.decode_encode.
  induction R as [| I R IH]; simpl; [reflexivity |].
  rewrite cg_idec_icode, IH. reflexivity.
Qed.

Definition cg_renc (ig : nat) (R : list (mm_instr nat)) (xS xB xT m : nat) : nat :=
  G.encode [ig; xS; xB; xT; m; cg_penc R].

Definition cg_rdec (r : nat) : option cg_routine_code :=
  match G.decode r with
  | [ig; xS; xB; xT; m; rc] =>
      match cg_pdec rc with
      | Some R => Some (ig, R, xS, xB, xT, m)
      | None => None
      end
  | _ => None
  end.

Theorem cg_rdec_renc : forall ig R xS xB xT m,
  cg_rdec (cg_renc ig R xS xB xT m) = Some (ig, R, xS, xB, xT, m).
Proof.
  intros. unfold cg_rdec, cg_renc. rewrite G.decode_encode, cg_pdec_penc.
  reflexivity.
Qed.

(* ================================================================= *)
(* 3. A fuel interpreter for counter programs over environments.       *)
(* ================================================================= *)

Definition cg_mstate : Type := (nat * env nat nat)%type.

Definition cg_mme_fetch (P : nat * list (mm_instr nat)) (i : nat)
  : option (mm_instr nat) :=
  if Nat.leb (fst P) i then nth_error (snd P) (i - fst P) else None.

Definition cg_mme_exec (I : mm_instr nat) (st : cg_mstate) : cg_mstate :=
  let (i, e) := st in
  match I with
  | mm_inc x => (S i, set_env eq_nat_dec e x (S (get_env e x)))
  | mm_dec x j =>
      match get_env e x with
      | 0 => (j, e)
      | S u => (S i, set_env eq_nat_dec e x u)
      end
  end.

Definition cg_mme_step (P : nat * list (mm_instr nat)) (st : cg_mstate)
  : option cg_mstate :=
  match cg_mme_fetch P (fst st) with
  | Some J => Some (cg_mme_exec J st)
  | None => None
  end.

Fixpoint cg_mme_run_fuel (n : nat) (P : nat * list (mm_instr nat)) (st : cg_mstate)
  : cg_mstate :=
  match n with
  | 0 => st
  | S n' =>
      match cg_mme_step P st with
      | Some st' => cg_mme_run_fuel n' P st'
      | None => st
      end
  end.

Lemma cg_mme_exec_sound : forall I st,
  mm_sss_env eq_nat_dec I st (cg_mme_exec I st).
Proof.
  intros [x | x j] [i e]; simpl.
  - constructor.
  - destruct (get_env e x) as [| u] eqn:E; constructor; auto.
Qed.

Lemma cg_mme_fetch_some : forall P i I,
  cg_mme_fetch P i = Some I ->
  exists l r, snd P = l ++ I :: r /\ i = fst P + length l.
Proof.
  intros [i0 R] i I. unfold cg_mme_fetch. simpl.
  destruct (Nat.leb_spec i0 i) as [Hle | Hlt]; [| discriminate].
  intros H. apply nth_error_split in H. destruct H as (l & r & H1 & H2).
  exists l, r. split; [exact H1 | lia].
Qed.

Lemma cg_mme_fetch_at : forall i0 l I r,
  cg_mme_fetch (i0, l ++ I :: r) (i0 + length l) = Some I.
Proof.
  intros. unfold cg_mme_fetch. simpl.
  replace (Nat.leb i0 (i0 + length l)) with true by (symmetry; apply Nat.leb_le; lia).
  replace (i0 + length l - i0) with (length l) by lia.
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma cg_mme_fetch_none : forall P i, cg_mme_fetch P i = None <-> out_code i P.
Proof.
  intros [i0 R] i. unfold cg_mme_fetch, out_code, code_start, code_end. simpl.
  destruct (Nat.leb_spec i0 i) as [Hle | Hlt].
  - rewrite nth_error_None. split; intros; lia.
  - split; intros; [lia | reflexivity].
Qed.

Theorem cg_mme_step_sound : forall P st st',
  cg_mme_step P st = Some st' -> sss_step (mm_sss_env eq_nat_dec) P st st'.
Proof.
  intros [i0 R] st st'. unfold cg_mme_step.
  destruct (cg_mme_fetch (i0, R) (fst st)) as [J |] eqn:E; [| discriminate].
  intros H. injection H as <-.
  apply cg_mme_fetch_some in E. destruct E as (l & r & H1 & H2). simpl in H1, H2.
  subst R. apply in_sss_step; [exact H2 | apply cg_mme_exec_sound].
Qed.

Theorem cg_mme_step_complete : forall P st st',
  sss_step (mm_sss_env eq_nat_dec) P st st' -> cg_mme_step P st = Some st'.
Proof.
  intros P st st' (k & l & I & r & d & HP & Hst & Hstep). subst P.
  unfold cg_mme_step. rewrite Hst. simpl fst. rewrite cg_mme_fetch_at.
  f_equal. rewrite <- Hst. apply (mm_sss_env_fun (cg_mme_exec_sound I st)).
  rewrite Hst in Hstep |- *. exact Hstep.
Qed.

Theorem cg_mme_step_none : forall P st,
  cg_mme_step P st = None <-> out_code (fst st) P.
Proof.
  intros P st. unfold cg_mme_step. rewrite <- cg_mme_fetch_none.
  destruct (cg_mme_fetch P (fst st)); split; intros; congruence.
Qed.

Theorem cg_mme_run_fuel_sound : forall n P st,
  exists k, k <= n /\
    sss_steps (mm_sss_env eq_nat_dec) P k st (cg_mme_run_fuel n P st).
Proof.
  induction n as [| n IH]; intros P st; simpl.
  - exists 0. split; [lia | constructor].
  - destruct (cg_mme_step P st) as [st' |] eqn:E.
    + destruct (IH P st') as (k & Hk & Hs). exists (S k). split; [lia |].
      econstructor; [apply cg_mme_step_sound; exact E | exact Hs].
    + exists 0. split; [lia | constructor].
Qed.

Theorem cg_mme_run_fuel_complete : forall P k st st',
  sss_steps (mm_sss_env eq_nat_dec) P k st st' -> out_code (fst st') P ->
  forall n, k <= n -> cg_mme_run_fuel n P st = st'.
Proof.
  intros P k st st' H. induction H as [st | k st1 st2 st3 H1 H2 IH]; intros Hout n Hn.
  - destruct n as [| n]; simpl; [reflexivity |].
    replace (cg_mme_step P st) with (@None cg_mstate)
      by (symmetry; apply cg_mme_step_none; exact Hout).
    reflexivity.
  - destruct n as [| n]; [lia |]. simpl.
    rewrite (cg_mme_step_complete _ _ _ H1). apply IH; [exact Hout | lia].
Qed.

(* A run that leaves the code within its fuel is an output of the code. *)
Corollary cg_mme_run_fuel_output : forall n P st,
  out_code (fst (cg_mme_run_fuel n P st)) P ->
  sss_output (mm_sss_env eq_nat_dec) P st (cg_mme_run_fuel n P st).
Proof.
  intros n P st Hout. destruct (cg_mme_run_fuel_sound n P st) as (k & _ & Hs).
  split; [exists k; exact Hs | exact Hout].
Qed.

Lemma cg_mme_exec_ext : forall I i e1 e2,
  (forall x, get_env e1 x = get_env e2 x) ->
  fst (cg_mme_exec I (i, e1)) = fst (cg_mme_exec I (i, e2)) /\
  (forall x, get_env (snd (cg_mme_exec I (i, e1))) x
             = get_env (snd (cg_mme_exec I (i, e2))) x).
Proof.
  intros [x | x j] i e1 e2 H; simpl.
  - split; [reflexivity |]. intros y. rewrite !cg_get_env.
    destruct (Nat.eq_dec x y) as [-> | Hne].
    + rewrite !cg_set_env_eq. rewrite H. reflexivity.
    + rewrite !cg_set_env_neq by exact Hne.
      rewrite <- (cg_get_env e1 y), <- (cg_get_env e2 y). apply H.
  - rewrite (H x). destruct (get_env e2 x) as [| u]; simpl.
    + split; [reflexivity | exact H].
    + split; [reflexivity |]. intros y. rewrite !cg_get_env.
      destruct (Nat.eq_dec x y) as [-> | Hne].
      * rewrite !cg_set_env_eq. reflexivity.
      * rewrite !cg_set_env_neq by exact Hne.
      rewrite <- (cg_get_env e1 y), <- (cg_get_env e2 y). apply H.
Qed.

(* Environments equal at every register run alike. *)
Theorem cg_mme_run_ext : forall n P i e1 e2,
  (forall x, get_env e1 x = get_env e2 x) ->
  fst (cg_mme_run_fuel n P (i, e1)) = fst (cg_mme_run_fuel n P (i, e2)) /\
  (forall x, get_env (snd (cg_mme_run_fuel n P (i, e1))) x
             = get_env (snd (cg_mme_run_fuel n P (i, e2))) x).
Proof.
  induction n as [| n IH]; intros P i e1 e2 H; [simpl; split; auto |].
  cbn [cg_mme_run_fuel]. unfold cg_mme_step. cbn [fst].
  destruct (cg_mme_fetch P i) as [J |]; [| split; auto].
  destruct (cg_mme_exec_ext J i e1 e2 H) as [H1 H2].
  destruct (cg_mme_exec J (i, e1)) as [j1 f1] eqn:E1.
  destruct (cg_mme_exec J (i, e2)) as [j2 f2] eqn:E2.
  simpl in H1, H2. subst j2. apply IH. exact H2.
Qed.

Print Assumptions cg_divides_mod.
Print Assumptions cg_expo_fuel_spec.
Print Assumptions cg_expo_spec.
Print Assumptions cg_qs_prime.
Print Assumptions cg_qs_gt1.
Print Assumptions cg_gk_pos.
Print Assumptions cg_gk_ext.
Print Assumptions cg_gk_not_div.
Print Assumptions cg_gk_split.
Print Assumptions cg_expo_gk.
Print Assumptions cg_expo_gk_zero.
Print Assumptions cg_gk_inj.
Print Assumptions cg_get_env.
Print Assumptions cg_set_env_eq.
Print Assumptions cg_set_env_neq.
Print Assumptions cg_zero_at_set.
Print Assumptions cg_gk_inc.
Print Assumptions cg_gk_dec.
Print Assumptions cg_gk_zero_not_div.
Print Assumptions cg_idec_icode.
Print Assumptions cg_pdec_penc.
Print Assumptions cg_rdec_renc.
Print Assumptions cg_mme_exec_sound.
Print Assumptions cg_mme_fetch_some.
Print Assumptions cg_mme_fetch_at.
Print Assumptions cg_mme_fetch_none.
Print Assumptions cg_mme_step_sound.
Print Assumptions cg_mme_step_complete.
Print Assumptions cg_mme_step_none.
Print Assumptions cg_mme_run_fuel_sound.
Print Assumptions cg_mme_run_fuel_complete.
Print Assumptions cg_mme_run_fuel_output.
Print Assumptions cg_mme_exec_ext.
Print Assumptions cg_mme_run_ext.
