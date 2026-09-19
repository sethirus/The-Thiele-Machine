(** LassertSpec.v: the LASSERT SAT-witness scan. [hw_scan] is the scan the
    hardware FSM performs, over natural-number words; [hw_scan_certcheck] proves
    it returns the kernel's model and countermodel checks whenever the formula
    declares at least one clause and its literal words contain a terminator
    for every declared clause. *)
From Coq Require Import Arith ZArith Lia Bool List.
Import ListNotations.
Require Import Kernel.CertCheck.
Import CertCheck.
Local Open Scope nat_scope.

(** * The SAT witness scan, as the kernel states it *)

Definition lsat_spec (g : nat -> nat) (w : nat) : bool :=
  let lit := word32_to_signed w in
  let var := Z.to_nat (Z.abs lit) in
  if (lit >? 0)%Z then negb (Nat.eqb (g var) 0) else negb (negb (Nat.eqb (g var) 0)).

Fixpoint spec_scan (g : nat -> nat) (n : nat) (words : list nat) (ndone : nat) (sat : bool) : bool :=
  if Nat.eqb ndone n then true
  else match words with
       | [] => false
       | w :: ws =>
           if Nat.eqb w 0 then (if sat then spec_scan g n ws (S ndone) false else false)
           else spec_scan g n ws ndone (orb sat (lsat_spec g w))
       end.

Local Transparent check_model_binary_fn check_countermodel_binary_fn.

Lemma check_model_binary_fn_scan : forall a b n ws g,
  check_model_binary_fn (a :: b :: n :: ws) g = spec_scan g n ws 0 false.
Proof.
  intros a b n ws g. unfold check_model_binary_fn. cbv beta iota zeta.
  match goal with |- ?F ws 0%nat false = _ =>
    enough (H : forall l nd s, F l nd s = spec_scan g n l nd s) by apply H
  end.
  intro l. induction l as [|w l IH]; intros nd s; cbn [spec_scan]; [reflexivity|].
  destruct (Nat.eqb nd n); [reflexivity|].
  destruct (Nat.eqb w 0); [destruct s; [apply IH|reflexivity]|].
  unfold lsat_spec. apply IH.
Qed.

Lemma check_countermodel_binary_fn_scan : forall a b n ws g,
  check_countermodel_binary_fn (a :: b :: n :: ws) g = negb (spec_scan g n ws 0 false).
Proof. intros. unfold check_countermodel_binary_fn. rewrite check_model_binary_fn_scan. reflexivity. Qed.

(** * The scan as the hardware performs it *)

(** A nonzero literal word is negative when bit 31 is set; its variable is the
    32-bit two's-complement magnitude. An assignment word is true when nonzero. *)
Definition lit_neg (w : nat) : bool := Nat.leb (2 ^ 31) w.
Definition lit_var (w : nat) : nat := if lit_neg w then 2 ^ 32 - w else w.
Definition hw_lsat (g : nat -> nat) (w : nat) : bool :=
  if lit_neg w then Nat.eqb (g (lit_var w)) 0 else negb (Nat.eqb (g (lit_var w)) 0).

(** [None]: the words ran out before the scan terminated. *)
Fixpoint hw_scan (gm gc : nat -> nat) (ws : list nat) (clen : nat) (sat csat cfail : bool) : option bool :=
  match ws with
  | [] => None
  | w :: ws' =>
      if Nat.eqb w 0 then
        if negb sat then Some false
        else if Nat.leb clen 1 then Some (orb cfail (negb csat))
        else hw_scan gm gc ws' (clen - 1) false false (orb cfail (negb csat))
      else hw_scan gm gc ws' clen (orb sat (hw_lsat gm w)) (orb csat (hw_lsat gc w)) cfail
  end.

Lemma lsat_spec_hw : forall g w, 0 < w -> w < 2 ^ 32 -> lsat_spec g w = hw_lsat g w.
Proof.
  intros g w Hpos Hw. unfold lsat_spec, hw_lsat, lit_var, lit_neg, word32_to_signed.
  assert (P31 : Z.of_nat (2 ^ 31) = 2147483648%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  assert (P32 : Z.of_nat (2 ^ 32) = 4294967296%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
  destruct (Nat.leb_spec (2 ^ 31) w) as [Hn|Hn].
  - rewrite (proj2 (Z.ltb_ge _ _)) by lia.
    replace (Z.to_nat (Z.abs (Z.of_nat w - 4294967296))) with (2 ^ 32 - w) by lia.
    rewrite Z.gtb_ltb, (proj2 (Z.ltb_ge _ _)) by lia.
    rewrite negb_involutive. reflexivity.
  - rewrite (proj2 (Z.ltb_lt _ _)) by lia.
    replace (Z.to_nat (Z.abs (Z.of_nat w))) with w by lia.
    rewrite Z.gtb_ltb, (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma spec_scan_done : forall g n ws s, spec_scan g n ws n s = true.
Proof. intros g n ws s. destruct ws; unfold spec_scan; rewrite Nat.eqb_refl; reflexivity. Qed.

Fixpoint count_zeros (ws : list nat) : nat :=
  match ws with
  | [] => 0
  | w :: ws' => (if Nat.eqb w 0 then 1 else 0) + count_zeros ws'
  end.

(** The hardware scan agrees with the model check and the countermodel check
    whenever at least one clause remains and the remaining words contain a
    terminator for every remaining clause. *)
Theorem hw_scan_spec : forall gm gc ws k ndone n sat csat cfail,
  n = ndone + k -> 1 <= k -> k <= count_zeros ws ->
  Forall (fun w => w < 2 ^ 32) ws ->
  hw_scan gm gc ws k sat csat cfail =
  Some (andb (spec_scan gm n ws ndone sat) (orb cfail (negb (spec_scan gc n ws ndone csat)))).
Proof.
  intros gm gc ws. induction ws as [|w ws IH]; intros k ndone n sat csat cfail Hn Hk Hz Hb.
  - cbn in Hz. lia.
  - inversion Hb as [|? ? Hw Hb']; subst.
    cbn [hw_scan spec_scan count_zeros] in *.
    rewrite (proj2 (Nat.eqb_neq ndone (ndone + k))) by lia.
    destruct (Nat.eqb_spec w 0) as [Ew|Ew].
    + destruct sat; cbn [negb].
      * destruct (Nat.leb_spec k 1) as [Lk|Lk].
        -- assert (k = 1) by lia. subst k.
           rewrite ?Nat.add_1_r, !spec_scan_done. destruct csat, cfail; reflexivity.
        -- rewrite (IH (k - 1) (S ndone) (ndone + k)) by (cbn in Hz; lia || exact Hb').
           replace (S ndone + (k - 1)) with (ndone + k) by lia.
           destruct csat; cbn [andb orb negb]; rewrite ?orb_false_r, ?orb_true_r; reflexivity.
      * reflexivity.
    + rewrite (IH k ndone (ndone + k)) by (cbn in Hz; lia || exact Hb').
      rewrite !lsat_spec_hw by lia. reflexivity.
Qed.

(** The whole scan from the first literal word, against the kernel's two checks. *)
Corollary hw_scan_certcheck : forall gm gc a nv n ws,
  1 <= n -> n <= count_zeros ws -> Forall (fun w => w < 2 ^ 32) ws ->
  hw_scan gm gc ws n false false false =
  Some (andb (check_model_binary_fn (a :: nv :: n :: ws) gm)
             (check_countermodel_binary_fn (a :: nv :: n :: ws) gc)).
Proof.
  intros gm gc a nv n ws Hn Hz Hb.
  rewrite (hw_scan_spec gm gc ws n 0 n) by (lia || exact Hb).
  rewrite check_model_binary_fn_scan, check_countermodel_binary_fn_scan. reflexivity.
Qed.
