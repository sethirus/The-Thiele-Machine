(** NecWCT: the RFC 9162 inclusion check, its boundary pushed to the
    limit.

    The book: for every input with m = N, the inclusion check rejects.
    Stronger, and exact: for every hash whose equality test is reflexive,
    some leaf, root and path are accepted at index m in a tree of size N
    exactly when m < N. Every m >= N is rejected, and every m < N has an
    accepted input (a path of the right length and the root it folds to).
    The symbolic hash qualifies. *)

(* SCOPE NOTE: standalone proof scope. The inclusion check of RFC 9162 over
   an abstract hash algebra; no machine is fixed. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import RFC9162MerkleTarget RFC9162Merkle.

Theorem nec_w_inclusion_rejects_beyond :
  forall (entry digest : Type) (H : HashAlgorithm entry digest) m N leaf root path,
    N <= m -> verify_inclusion H m N leaf root path = false.
Proof.
  intros entry digest H m N leaf root path Hle. unfold verify_inclusion.
  replace (Nat.ltb m N) with false by (symmetry; apply Nat.ltb_ge; exact Hle).
  reflexivity.
Qed.

(** The index pair after one step of the fold. *)
Definition nec_w_ct_nxt (fn sn : nat) : nat * nat :=
  if (Nat.odd fn || Nat.eqb fn sn)%bool then
    let '(fn0, sn0) :=
      if Nat.odd fn then (fn, sn) else shift_until_odd_or_zero (S fn) fn sn in
    (Nat.div2 fn0, Nat.div2 sn0)
  else (Nat.div2 fn, Nat.div2 sn).

Lemma nec_w_ct_fold_step : forall (entry digest : Type) (H : HashAlgorithm entry digest)
    p path fn sn r,
  sn <> 0 ->
  exists r', inclusion_fold H (p :: path) fn sn r =
             inclusion_fold H path (fst (nec_w_ct_nxt fn sn)) (snd (nec_w_ct_nxt fn sn)) r'.
Proof.
  intros entry digest H p path fn sn r Hsn. cbn [inclusion_fold].
  replace (Nat.eqb sn 0) with false by (symmetry; apply Nat.eqb_neq; exact Hsn).
  unfold nec_w_ct_nxt.
  destruct (Nat.odd fn || Nat.eqb fn sn)%bool.
  - destruct (if Nat.odd fn then (fn, sn) else shift_until_odd_or_zero (S fn) fn sn) as [fn0 sn0].
    eexists. reflexivity.
  - eexists. reflexivity.
Qed.

Lemma nec_w_div2_le : forall n, Nat.div2 n <= n.
Proof. intros n. rewrite Nat.div2_div. apply Nat.Div0.div_le_upper_bound; lia. Qed.

Lemma nec_w_div2_lt : forall n, 0 < n -> Nat.div2 n < n.
Proof. intros n Hn. rewrite Nat.div2_div. apply Nat.div_lt; lia. Qed.

Lemma nec_w_shift_snd_le : forall fuel fn sn, snd (shift_until_odd_or_zero fuel fn sn) <= sn.
Proof.
  induction fuel as [| fuel IH]; intros fn sn; simpl; [lia |].
  destruct (Nat.eqb fn 0 || Nat.odd fn)%bool; simpl; [lia |].
  pose proof (IH (Nat.div2 fn) (Nat.div2 sn)). pose proof (nec_w_div2_le sn). lia.
Qed.

Lemma nec_w_ct_nxt_decreases : forall fn sn, 0 < sn -> snd (nec_w_ct_nxt fn sn) < sn.
Proof.
  intros fn sn Hsn. unfold nec_w_ct_nxt.
  destruct (Nat.odd fn || Nat.eqb fn sn)%bool; [| simpl; apply nec_w_div2_lt; exact Hsn].
  destruct (Nat.odd fn).
  - simpl. apply nec_w_div2_lt. exact Hsn.
  - pose proof (nec_w_shift_snd_le (S fn) fn sn) as Hle.
    destruct (shift_until_odd_or_zero (S fn) fn sn) as [fn0 sn0]. simpl in *.
    assert (Nat.div2 sn0 <= Nat.div2 sn).
    { rewrite !Nat.div2_div. apply Nat.Div0.div_le_mono; lia. }
    pose proof (nec_w_div2_lt sn Hsn). lia.
Qed.

Fixpoint nec_w_ct_fill {digest : Type} (filler : digest) (fuel fn sn : nat) : list digest :=
  match fuel with
  | 0 => []
  | S f => if Nat.eqb sn 0 then []
           else filler :: nec_w_ct_fill filler f (fst (nec_w_ct_nxt fn sn)) (snd (nec_w_ct_nxt fn sn))
  end.

Lemma nec_w_ct_fill_reaches_zero : forall (entry digest : Type) (H : HashAlgorithm entry digest)
    (filler : digest) fuel fn sn r,
  sn < fuel ->
  exists fn' r', inclusion_fold H (nec_w_ct_fill filler fuel fn sn) fn sn r = Some (fn', 0, r').
Proof.
  intros entry digest H filler fuel. induction fuel as [| f IH]; intros fn sn r Hlt; [lia |].
  simpl. destruct (Nat.eqb_spec sn 0) as [-> | Hne].
  - exists fn, r. reflexivity.
  - destruct (nec_w_ct_fold_step entry digest H filler
               (nec_w_ct_fill filler f (fst (nec_w_ct_nxt fn sn)) (snd (nec_w_ct_nxt fn sn)))
               fn sn r Hne) as [r' E].
    rewrite E. apply IH.
    pose proof (nec_w_ct_nxt_decreases fn sn ltac:(lia)). lia.
Qed.

(** Exactly the indices below the tree size have an accepted input. *)
Theorem nec_w_inclusion_accepts_iff :
  forall (entry digest : Type) (H : HashAlgorithm entry digest),
    (forall d, digest_eqb H d d = true) ->
    forall (leaf : digest) m N,
      (exists root path, verify_inclusion H m N leaf root path = true) <-> m < N.
Proof.
  intros entry digest H Hrefl leaf m N. split.
  - intros [root [path Hv]]. destruct (Nat.lt_ge_cases m N) as [Hlt | Hge]; [exact Hlt |].
    rewrite (nec_w_inclusion_rejects_beyond entry digest H m N leaf root path Hge) in Hv. discriminate.
  - intros Hlt.
    destruct (nec_w_ct_fill_reaches_zero entry digest H leaf N m (N - 1) leaf ltac:(lia))
      as [fn' [r' E]].
    exists r', (nec_w_ct_fill leaf N m (N - 1)).
    unfold verify_inclusion.
    replace (Nat.ltb m N) with true by (symmetry; apply Nat.ltb_lt; exact Hlt).
    rewrite E. simpl. apply Hrefl.
Qed.

Corollary nec_w_inclusion_accepts_iff_symbolic :
  forall (leaf : SymbolicDigest) m N,
    (exists root path, verify_inclusion symbolic_hash m N leaf root path = true) <-> m < N.
Proof.
  intros leaf m N. apply nec_w_inclusion_accepts_iff. exact symbolic_digest_eqb_refl.
Qed.

Print Assumptions nec_w_inclusion_rejects_beyond.
Print Assumptions nec_w_inclusion_accepts_iff.
Print Assumptions nec_w_inclusion_accepts_iff_symbolic.
