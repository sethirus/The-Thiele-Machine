(** TcGodel.v: Goedel codes for any number of registers, from any list of
    pairwise coprime moduli larger than 1.

    A register file v is written as the number
        tc_enc ms v = ms_0^(v_0) * ms_1^(v_1) * ... * ms_(k-1)^(v_(k-1)).
    With moduli 2, 3, 5, ... this is Minsky's coding. Only two things are
    used about it: multiplying by the modulus of register p adds one to
    register p, and the modulus of register p does not divide the code when
    register p holds 0. Pairwise coprime moduli larger than 1 are enough, so
    no prime numbers are needed; [tc_moduli_exist] builds them for every k
    (each new modulus is one more than the product of the old ones).

    Dependencies: Coq standard library and the vendored coq-undecidability
    library (Shared/Libs/DLW). No axioms and no unfinished proofs.                      *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia.
From Undecidability.Shared.Libs.DLW Require Import utils gcd pos vec godel_coding.
Set Implicit Arguments.
Set Default Goal Selector "!".

#[local] Notation "e #> x" := (vec_pos e x).
#[local] Notation "e [ v / x ]" := (vec_change e x v).

Fixpoint tc_enc (k : nat) : vec nat k -> vec nat k -> nat :=
  match k with
  | 0 => fun _ _ => 1
  | S k' => fun ms v => (vec_head ms) ^ (vec_head v) * @tc_enc k' (vec_tail ms) (vec_tail v)
  end.

Definition tc_moduli_ok (k : nat) (ms : vec nat k) : Prop :=
  (forall p, 1 < ms#>p) /\ (forall p q, p <> q -> Nat.gcd (ms#>p) (ms#>q) = 1).

Lemma tc_gcd_1_r : forall n, Nat.gcd n 1 = 1.
Proof. intro n. apply Nat.divide_1_r. apply Nat.gcd_divide_r. Qed.

Lemma tc_gcd_mul : forall m a b, Nat.gcd m a = 1 -> Nat.gcd m b = 1 -> Nat.gcd m (a * b) = 1.
Proof.
  intros m a b Ha Hb.
  set (g := Nat.gcd m (a * b)).
  assert (Hgm : Nat.divide g m) by apply Nat.gcd_divide_l.
  assert (Hgab : Nat.divide g (a * b)) by apply Nat.gcd_divide_r.
  assert (Hga : Nat.gcd g a = 1).
  { apply Nat.divide_1_r. rewrite <- Ha. apply Nat.gcd_greatest.
    - apply (Nat.divide_trans _ g); [apply Nat.gcd_divide_l | exact Hgm].
    - apply Nat.gcd_divide_r. }
  apply Nat.gauss in Hgab; [| exact Hga].
  apply Nat.divide_1_r. rewrite <- Hb. apply Nat.gcd_greatest; [exact Hgm | exact Hgab].
Qed.

Lemma tc_gcd_pow : forall m a x, Nat.gcd m a = 1 -> Nat.gcd m (a ^ x) = 1.
Proof.
  intros m a x H. induction x as [| x IH]; simpl.
  - apply tc_gcd_1_r.
  - apply tc_gcd_mul; assumption.
Qed.

Lemma tc_cons_pos0 : forall k m (ms : vec nat k), (m ## ms)#>pos0 = m.
Proof. reflexivity. Qed.

Lemma tc_cons_nxt : forall k m (ms : vec nat k) q, (m ## ms)#>(pos_nxt q) = ms#>q.
Proof. reflexivity. Qed.

Lemma tc_cons_inv : forall k (ms : vec nat (S k)), exists m ms', ms = m ## ms'.
Proof.
  intros k ms. exists (vec_head ms), (vec_tail ms).
  refine (Vector.caseS' ms (fun ms => ms = vec_head ms ## vec_tail ms) _). intros h t. reflexivity.
Qed.

Lemma tc_enc_cons : forall k m x (ms v : vec nat k), tc_enc (m ## ms) (x ## v) = m ^ x * tc_enc ms v.
Proof. reflexivity. Qed.

Lemma tc_pow_pos : forall m x, 0 < m -> 0 < m ^ x.
Proof. intros m x H. induction x as [| x IH]; simpl; [lia | apply Nat.mul_pos_pos; assumption]. Qed.

Lemma tc_enc_pos : forall k (ms v : vec nat k), (forall p, 0 < ms#>p) -> 0 < tc_enc ms v.
Proof.
  induction k as [| k IH]; intros ms v H.
  - simpl. lia.
  - destruct (tc_cons_inv ms) as [m [ms' ->]]. destruct (tc_cons_inv v) as [x [v' ->]].
    rewrite tc_enc_cons. apply Nat.mul_pos_pos.
    + apply tc_pow_pos. apply (H pos0).
    + apply IH. intro q. apply (H (pos_nxt q)).
Qed.

(* a number coprime to every modulus is coprime to every code *)
Lemma tc_gcd_enc : forall k (ms v : vec nat k) m,
  (forall p, Nat.gcd m (ms#>p) = 1) -> Nat.gcd m (tc_enc ms v) = 1.
Proof.
  induction k as [| k IH]; intros ms v m H.
  - simpl. apply tc_gcd_1_r.
  - destruct (tc_cons_inv ms) as [m0 [ms' ->]]. destruct (tc_cons_inv v) as [x [v' ->]].
    rewrite tc_enc_cons. apply tc_gcd_mul.
    + apply tc_gcd_pow. apply (H pos0).
    + apply IH. intro q. apply (H (pos_nxt q)).
Qed.

Lemma tc_enc_succ : forall k (ms v : vec nat k) p,
  (ms#>p) * tc_enc ms v = tc_enc ms (v[(S (v#>p))/p]).
Proof.
  induction k as [| k IH]; intros ms v p.
  - invert pos p.
  - destruct (tc_cons_inv ms) as [m [ms' ->]]. destruct (tc_cons_inv v) as [x [v' ->]].
    invert pos p.
    + ring.
    + rewrite <- IH. ring.
Qed.

Lemma tc_enc_not_div : forall k (ms v : vec nat k) p,
  tc_moduli_ok ms -> v#>p = 0 -> ~ divides (ms#>p) (tc_enc ms v).
Proof.
  induction k as [| k IH]; intros ms v p Hok Hv.
  - invert pos p.
  - destruct (tc_cons_inv ms) as [m [ms' ->]]. destruct (tc_cons_inv v) as [x [v' ->]].
    destruct Hok as [Hgt Hcop].
    invert pos p.
    + simpl in Hv. subst x. rewrite Nat.pow_0_r, Nat.mul_1_l.
      assert (Hg : Nat.gcd m (tc_enc ms' v') = 1).
      { apply tc_gcd_enc. intro q. apply (Hcop pos0 (pos_nxt q)). discriminate. }
      intros [c Hc].
      assert (Hd : Nat.divide m (tc_enc ms' v')) by (exists c; rewrite Hc; lia).
      assert (Hm : Nat.divide m 1) by (rewrite <- Hg; apply Nat.gcd_greatest; [apply Nat.divide_refl | exact Hd]).
      apply Nat.divide_1_r in Hm. pose proof (Hgt pos0) as H1. simpl vec_pos in H1. lia.
    + simpl in Hv.
      intros [c Hc].
      assert (Hg : Nat.gcd (ms'#>p) (m ^ x) = 1).
      { apply tc_gcd_pow. rewrite Nat.gcd_comm. apply (Hcop pos0 (pos_nxt p)). discriminate. }
      assert (Hd : Nat.divide (ms'#>p) (m ^ x * tc_enc ms' v')) by (exists c; rewrite Hc; lia).
      apply Nat.gauss in Hd; [| exact Hg].
      refine (IH ms' v' p _ Hv Hd). split.
      * intro r. apply (Hgt (pos_nxt r)).
      * intros r s Hrs. apply (Hcop (pos_nxt r) (pos_nxt s)). intro E. apply Hrs. apply pos_nxt_inj. exact E.
Qed.

(* the code, as a vendored godel_coding *)
Definition tc_gc (k : nat) (ms : vec nat k) (Hok : tc_moduli_ok ms) : godel_coding k.
Proof.
  refine {| gc_pr := fun p => ms#>p; gc_enc := fun v => tc_enc ms v |}.
  - intro p. destruct Hok as [H _]. pose proof (H p). lia.
  - intros p v Hv. apply tc_enc_not_div; assumption.
  - intros p v. apply tc_enc_succ.
Defined.

(* moduli exist for every number of registers *)
Fixpoint tc_prod (k : nat) : vec nat k -> nat :=
  match k with 0 => fun _ => 1 | S k' => fun ms => vec_head ms * @tc_prod k' (vec_tail ms) end.

Lemma tc_prod_pos : forall k (ms : vec nat k), (forall p, 0 < ms#>p) -> 0 < tc_prod ms.
Proof.
  induction k as [| k IH]; intros ms H; simpl; [lia |].
  destruct (tc_cons_inv ms) as [m [ms' ->]]. simpl.
  apply Nat.mul_pos_pos; [apply (H pos0) | apply IH; intro q; apply (H (pos_nxt q))].
Qed.

Lemma tc_prod_div : forall k (ms : vec nat k) p, Nat.divide (ms#>p) (tc_prod ms).
Proof.
  induction k as [| k IH]; intros ms p; [invert pos p |].
  destruct (tc_cons_inv ms) as [m [ms' ->]]. invert pos p.
  - exists (tc_prod ms'). simpl. lia.
  - simpl. apply Nat.divide_mul_r. apply IH.
Qed.

Lemma tc_gcd_succ : forall c m, Nat.gcd m (1 + c * m) = 1.
Proof. intros c m. rewrite Nat.gcd_add_mult_diag_r. apply tc_gcd_1_r. Qed.

Theorem tc_moduli_exist : forall k, exists ms : vec nat k, tc_moduli_ok ms.
Proof.
  induction k as [| k IH].
  - exists vec_nil. split; intro p; invert pos p.
  - destruct IH as [ms [Hgt Hcop]].
    pose proof (tc_prod_pos ms (fun p => ltac:(pose proof (Hgt p); lia))) as Hpos.
    exists ((1 + tc_prod ms) ## ms). split.
    + intro p. invert pos p.
      * lia.
      * apply Hgt.
    + intros p q Hpq. pos_inv p; pos_inv q; simpl vec_pos.
      * exfalso. apply Hpq. reflexivity.
      * destruct (tc_prod_div ms q) as [c Hc]. rewrite Hc.
        rewrite Nat.gcd_comm. apply tc_gcd_succ.
      * destruct (tc_prod_div ms p) as [c Hc]. rewrite Hc.
        apply tc_gcd_succ.
      * apply Hcop. intro E. apply Hpq. f_equal. exact E.
Qed.

Print Assumptions tc_enc_not_div.
Print Assumptions tc_moduli_exist.
