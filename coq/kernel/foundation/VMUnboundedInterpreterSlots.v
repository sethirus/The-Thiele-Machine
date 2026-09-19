(** VMUnboundedInterpreterSlots.v — the bit-slicing spec layer for the B3
    self-interpreter, built on VMUnboundedStep.v's unbounded VM sibling.

    There is no division or modulo instruction anywhere in vm_instruction
    (checked exhaustively against VMStep.v's inductive definition), which
    rules out Cantor-pairing-style packing: its inverse needs a square root
    or a division-based search. Fixed-width base-2^K positional packing
    needs only shift/and/or, all present (instr_shl/instr_shr/instr_and/
    instr_or), so that is the encoding this file specifies: a packed nat
    holds a sequence of K-bit slots (K = 64, matching the physical word
    size for a first, comparable target — a later phase can widen K or
    make it variable once the interpreter loop itself is validated; that
    is a separate, later refinement, not assumed here).

    This file is pure specification and combinatorics: get_slot/set_slot
    as plain Coq functions, and their correctness (read-after-write, and
    non-interference between distinct slots), proved once via bit
    extensionality (N.bits_inj) rather than per-case algebra. The actual
    host instruction sequences that compute get_slot/set_slot using
    vm_apply_u, and the guest/host simulation theorem, are the next file;
    this one is their load-bearing dependency, kept separate so it can be
    fully checked before any instruction-sequence tracing is attempted. *)

From Coq Require Import Arith Lia Bool.
From Coq Require Import NArith.NArith.
From Kernel Require Import VMUnboundedStep.

(** * 1. The slot width and the packed representation, at the N level
    (bit lemmas are native there; nat wrappers follow). *)

Definition K : N := 64%N.

Definition get_slot_N (packed : N) (i : nat) : N :=
  N.land (N.shiftr packed (N.of_nat i * K)) (N.ones K).

Definition set_slot_N (packed : N) (i : nat) (v : N) : N :=
  let shift : N := (N.of_nat i * K)%N in
  let v' : N := N.land v (N.ones K) in
  let low_part : N := N.land packed (N.ones shift) in
  let high_part : N := N.shiftl (N.shiftr packed (shift + K)%N) (shift + K)%N in
  N.lor high_part (N.lor low_part (N.shiftl v' shift)).

(** * 2. The one load-bearing fact: set_slot_N's bit content, everywhere.
    Inside slot i's window it is v's corresponding bit; everywhere else it
    is packed's original bit, unchanged. Both correctness lemmas below are
    direct corollaries of this one characterization. *)

Lemma set_slot_N_testbit : forall packed i v m,
  N.testbit (set_slot_N packed i v) m =
    if andb (N.leb (N.of_nat i * K) m) (N.ltb m (N.of_nat i * K + K)) then
      N.testbit v (m - N.of_nat i * K)
    else
      N.testbit packed m.
Proof.
  intros packed i v m. unfold set_slot_N. cbv zeta.
  set (shift := (N.of_nat i * K)%N).
  rewrite N.lor_spec, N.lor_spec.
  destruct (N.leb shift m) eqn:Hge; destruct (N.ltb m (shift + K)) eqn:Hlt; cbn [andb].
  - (* shift <= m < shift + K: inside slot i's window *)
    apply N.leb_le in Hge. apply N.ltb_lt in Hlt.
    assert (Hhigh : N.testbit (N.shiftl (N.shiftr packed (shift + K)) (shift + K)) m = false).
    { apply N.shiftl_spec_low. lia. }
    assert (Hlow : N.testbit (N.land packed (N.ones shift)) m = false).
    { rewrite N.land_spec, N.ones_spec_high by lia. apply Bool.andb_false_r. }
    assert (Hval : N.testbit (N.shiftl (N.land v (N.ones K)) shift) m = N.testbit v (m - shift)).
    { replace m with ((m - shift) + shift)%N at 1 by lia.
      rewrite N.shiftl_spec_alt.
      rewrite N.land_spec, N.ones_spec_low by lia.
      apply Bool.andb_true_r. }
    rewrite Hhigh, Hlow, Hval. reflexivity.
  - (* not (m < shift + K), i.e. m >= shift + K: above the window *)
    apply N.leb_le in Hge. apply N.ltb_ge in Hlt.
    assert (Hval : N.testbit (N.shiftl (N.land v (N.ones K)) shift) m = false).
    { rewrite N.shiftl_spec_high' by lia.
      rewrite N.land_spec, N.ones_spec_high by lia. apply Bool.andb_false_r. }
    assert (Hlow : N.testbit (N.land packed (N.ones shift)) m = false).
    { rewrite N.land_spec, N.ones_spec_high by lia. apply Bool.andb_false_r. }
    assert (Hhigh : N.testbit (N.shiftl (N.shiftr packed (shift + K)) (shift + K)) m
                    = N.testbit packed m).
    { rewrite N.shiftl_spec_high' by lia.
      rewrite N.shiftr_spec' by lia.
      f_equal. lia. }
    rewrite Hhigh, Hlow, Hval. destruct (N.testbit packed m); reflexivity.
  - (* m < shift: below the window *)
    apply N.leb_gt in Hge.
    assert (Hval : N.testbit (N.shiftl (N.land v (N.ones K)) shift) m = false).
    { apply N.shiftl_spec_low. lia. }
    assert (Hhigh : N.testbit (N.shiftl (N.shiftr packed (shift + K)) (shift + K)) m = false).
    { apply N.shiftl_spec_low. lia. }
    assert (Hlow : N.testbit (N.land packed (N.ones shift)) m = N.testbit packed m).
    { rewrite N.land_spec, N.ones_spec_low by lia. apply Bool.andb_true_r. }
    rewrite Hhigh, Hlow, Hval. destruct (N.testbit packed m); reflexivity.
  - (* m < shift and not (m < shift + K): contradictory *)
    apply N.leb_gt in Hge. apply N.ltb_ge in Hlt. lia.
Qed.

(** * 3. The two correctness lemmas an interpreter build needs, as direct
    corollaries of the single testbit characterization above. *)

Lemma get_slot_N_set_slot_N_same : forall packed i v,
  get_slot_N (set_slot_N packed i v) i = N.land v (N.ones K).
Proof.
  intros packed i v. apply N.bits_inj. intro m.
  unfold get_slot_N. rewrite N.land_spec, N.shiftr_spec'.
  rewrite set_slot_N_testbit.
  destruct (N.leb (N.of_nat i * K) (m + N.of_nat i * K)) eqn:Hge1;
  destruct (N.ltb (m + N.of_nat i * K) (N.of_nat i * K + K)) eqn:Hlt1; cbn [andb].
  - replace (m + N.of_nat i * K - N.of_nat i * K)%N with m by lia.
    rewrite N.land_spec. reflexivity.
  - apply N.ltb_ge in Hlt1.
    rewrite (N.ones_spec_high K m ltac:(lia)), Bool.andb_false_r.
    rewrite N.land_spec, (N.ones_spec_high K m ltac:(lia)), Bool.andb_false_r.
    reflexivity.
  - apply N.leb_gt in Hge1. lia.
  - apply N.leb_gt in Hge1. lia.
Qed.

Lemma get_slot_N_set_slot_N_other : forall packed i j v,
  i <> j -> get_slot_N (set_slot_N packed i v) j = get_slot_N packed j.
Proof.
  intros packed i j v Hne. apply N.bits_inj. intro m.
  unfold get_slot_N. rewrite N.land_spec, N.land_spec, N.shiftr_spec', N.shiftr_spec'.
  rewrite set_slot_N_testbit.
  destruct (N.ltb m K) eqn:HmK.
  - (* m < K: the ones-K mask is true on both sides, so this is the bit that
       matters; show m + j*K cannot also lie in i's disjoint window. *)
    apply N.ltb_lt in HmK.
    destruct (andb (N.leb (N.of_nat i * K) (m + N.of_nat j * K))
                    (N.ltb (m + N.of_nat j * K) (N.of_nat i * K + K))) eqn:Hcond.
    + exfalso. apply andb_true_iff in Hcond. destruct Hcond as [Hge Hlt].
      apply N.leb_le in Hge. apply N.ltb_lt in Hlt.
      assert (i < j \/ j < i)%nat as [Hlt2 | Hlt2] by lia.
      * assert (Hij : (N.of_nat i + 1 <= N.of_nat j)%N) by lia.
        pose proof (N.mul_le_mono_r _ _ K Hij) as Hmono.
        rewrite N.mul_add_distr_r, N.mul_1_l in Hmono.
        lia.
      * assert (Hij : (N.of_nat j + 1 <= N.of_nat i)%N) by lia.
        pose proof (N.mul_le_mono_r _ _ K Hij) as Hmono.
        rewrite N.mul_add_distr_r, N.mul_1_l in Hmono.
        lia.
    + reflexivity.
  - (* m >= K: the ones-K mask is false on both sides, so both sides are false. *)
    apply N.ltb_ge in HmK.
    rewrite (N.ones_spec_high K m HmK), Bool.andb_false_r, Bool.andb_false_r.
    reflexivity.
Qed.

(** * 4. nat-level wrappers, matching how the actual host instruction
    sequences (u_shr/u_and/u_shl/u_or/u_sub, all nat-typed) will compute
    them, so the next file's host-code proofs connect directly to these. *)

Definition Kn : nat := 64.
Definition slot_mask : nat := N.to_nat (N.ones K).

(** slot_mask's value is 2^64 - 1. It must never be unfolded and reduced:
    converting that value to a *unary* nat (which is what N.to_nat's own
    computation rule would do if forced) is computationally catastrophic,
    exactly the trap VMWord64BoundednessObstruction.v's two64 avoided by
    staying symbolic. slot_mask_N_eq is proved once, here, while the
    definition is still transparent, by directly instantiating the
    generic (already-proved-by-induction, not by evaluating this specific
    huge value) stdlib lemma N2Nat.id — no reduction of the actual value
    occurs. Every later proof uses this equation, never `unfold slot_mask`. *)
Lemma slot_mask_N_eq : N.of_nat slot_mask = N.ones K.
Proof. unfold slot_mask. apply N2Nat.id. Qed.

Global Opaque slot_mask.

Definition get_slot (packed i : nat) : nat :=
  N.to_nat (get_slot_N (N.of_nat packed) i).

Definition set_slot (packed i v : nat) : nat :=
  N.to_nat (set_slot_N (N.of_nat packed) i (N.of_nat v)).

Lemma get_slot_set_slot_same : forall packed i v,
  get_slot (set_slot packed i v) i = u_and v slot_mask.
Proof.
  intros packed i v. unfold get_slot, set_slot, u_and.
  rewrite N2Nat.id, get_slot_N_set_slot_N_same, <- slot_mask_N_eq.
  reflexivity.
Qed.

Lemma get_slot_set_slot_other : forall packed i j v,
  i <> j -> get_slot (set_slot packed i v) j = get_slot packed j.
Proof.
  intros packed i j v Hne. unfold get_slot, set_slot.
  rewrite N2Nat.id, (get_slot_N_set_slot_N_other _ _ _ _ Hne). reflexivity.
Qed.

(** get_slot/set_slot are exactly u_shr/u_and and the corresponding
    u_shl/u_or/u_sub composite, matching what the host instruction
    sequence will literally compute — restated so the next file can
    `unfold get_slot, u_shr, u_and` etc. and match host-register content
    to these definitions directly rather than re-deriving them. *)

Lemma get_slot_unfold : forall packed i,
  get_slot packed i = u_and (u_shr packed (i * Kn)) slot_mask.
Proof.
  intros packed i. unfold get_slot, get_slot_N, u_and, u_shr.
  rewrite N2Nat.id, Nat2N.inj_mul, slot_mask_N_eq.
  reflexivity.
Qed.

Lemma K_eq : N.of_nat Kn = K.
Proof. reflexivity. Qed.

(** The "low mask" 2^shift - 1 computed the way a host program actually
    would (SHL 1 by shift, then SUB 1 — no N.ones primitive exists in the
    ISA) equals N.ones shift exactly. *)
Lemma nat_ones_eq : forall n : nat,
  u_sub (u_shl 1 n) 1 = N.to_nat (N.ones (N.of_nat n)).
Proof.
  intro n. unfold u_sub, u_shl.
  replace (N.of_nat 1) with 1%N by reflexivity.
  rewrite N.shiftl_1_l, N.ones_equiv, N2Nat.inj_pred, Nat.sub_1_r.
  reflexivity.
Qed.

(** N.of_nat pushed through each u_* operation, generically. *)
Lemma N_of_nat_u_or : forall a b, N.of_nat (u_or a b) = N.lor (N.of_nat a) (N.of_nat b).
Proof. intros. unfold u_or. apply N2Nat.id. Qed.

Lemma N_of_nat_u_and : forall a b, N.of_nat (u_and a b) = N.land (N.of_nat a) (N.of_nat b).
Proof. intros. unfold u_and. apply N2Nat.id. Qed.

Lemma N_of_nat_u_shl : forall a b, N.of_nat (u_shl a b) = N.shiftl (N.of_nat a) (N.of_nat b).
Proof. intros. unfold u_shl. apply N2Nat.id. Qed.

Lemma N_of_nat_u_shr : forall a b, N.of_nat (u_shr a b) = N.shiftr (N.of_nat a) (N.of_nat b).
Proof. intros. unfold u_shr. apply N2Nat.id. Qed.

(** Same restatement for set_slot, matching set_slot_N's high/low/shifted-
    value split term for term (right-associated OR, matching set_slot_N's
    own grouping exactly, so the host program's instruction order needs no
    separate associativity lemma). *)

Lemma set_slot_unfold : forall packed i v,
  set_slot packed i v =
    u_or (u_shl (u_shr packed ((i + 1) * Kn)) ((i + 1) * Kn))
         (u_or (u_and packed (u_sub (u_shl 1 (i * Kn)) 1))
               (u_shl (u_and v slot_mask) (i * Kn))).
Proof.
  intros packed i v.
  unfold set_slot, set_slot_N. cbv zeta.
  unfold u_or at 1 2. rewrite N2Nat.id.
  f_equal. f_equal.
  - rewrite N_of_nat_u_shl, N_of_nat_u_shr.
    rewrite !Nat2N.inj_mul, !Nat2N.inj_add, K_eq.
    replace (N.of_nat 1) with 1%N by reflexivity.
    rewrite N.mul_add_distr_r, N.mul_1_l.
    reflexivity.
  - f_equal.
    + rewrite N_of_nat_u_and. f_equal.
      rewrite nat_ones_eq, N2Nat.id, Nat2N.inj_mul, K_eq.
      reflexivity.
    + rewrite N_of_nat_u_shl, N_of_nat_u_and, slot_mask_N_eq, Nat2N.inj_mul, K_eq.
      reflexivity.
Qed.

(** * 7. Two-write facts, needed so encode_regs can track a guest register
    file written via a sequence of set_slot calls (a whole ADD/etc. block),
    not just one call in isolation: overwriting the same slot again
    discards the intervening value, and writes to different slots commute.
    Both are direct corollaries of set_slot_N_testbit, the same technique
    as every other fact in this file. *)

Lemma set_slot_N_set_slot_N_same : forall packed i r v,
  set_slot_N (set_slot_N packed i r) i v = set_slot_N packed i v.
Proof.
  intros packed i r v. apply N.bits_inj. intro m.
  rewrite (set_slot_N_testbit (set_slot_N packed i r) i v m).
  rewrite (set_slot_N_testbit packed i v m).
  destruct (andb (N.leb (N.of_nat i * K) m) (N.ltb m (N.of_nat i * K + K))) eqn:E.
  - reflexivity.
  - rewrite (set_slot_N_testbit packed i r m), E. reflexivity.
Qed.

Lemma set_slot_N_comm : forall packed i j vi vj,
  i <> j ->
  set_slot_N (set_slot_N packed i vi) j vj = set_slot_N (set_slot_N packed j vj) i vi.
Proof.
  intros packed i j vi vj Hne. apply N.bits_inj. intro m.
  rewrite (set_slot_N_testbit (set_slot_N packed i vi) j vj m).
  rewrite (set_slot_N_testbit (set_slot_N packed j vj) i vi m).
  destruct (andb (N.leb (N.of_nat j * K) m) (N.ltb m (N.of_nat j * K + K))) eqn:Ej;
  destruct (andb (N.leb (N.of_nat i * K) m) (N.ltb m (N.of_nat i * K + K))) eqn:Ei.
  - exfalso. apply andb_true_iff in Ei. apply andb_true_iff in Ej.
    destruct Ei as [Ei1 Ei2]. destruct Ej as [Ej1 Ej2].
    apply N.leb_le in Ei1. apply N.ltb_lt in Ei2.
    apply N.leb_le in Ej1. apply N.ltb_lt in Ej2.
    assert (i < j \/ j < i)%nat as [Hlt | Hlt] by lia.
    + assert (Hij : (N.of_nat i + 1 <= N.of_nat j)%N) by lia.
      pose proof (N.mul_le_mono_r _ _ K Hij) as Hmono.
      rewrite N.mul_add_distr_r, N.mul_1_l in Hmono. lia.
    + assert (Hij : (N.of_nat j + 1 <= N.of_nat i)%N) by lia.
      pose proof (N.mul_le_mono_r _ _ K Hij) as Hmono.
      rewrite N.mul_add_distr_r, N.mul_1_l in Hmono. lia.
  - rewrite (set_slot_N_testbit packed j vj m), Ej. reflexivity.
  - rewrite (set_slot_N_testbit packed i vi m), Ei. reflexivity.
  - rewrite (set_slot_N_testbit packed j vj m), Ej.
    rewrite (set_slot_N_testbit packed i vi m), Ei.
    reflexivity.
Qed.

Lemma set_slot_set_slot_same : forall packed i r v,
  set_slot (set_slot packed i r) i v = set_slot packed i v.
Proof.
  intros packed i r v. unfold set_slot.
  rewrite N2Nat.id, set_slot_N_set_slot_N_same. reflexivity.
Qed.

Lemma set_slot_comm : forall packed i j vi vj,
  i <> j -> set_slot (set_slot packed i vi) j vj = set_slot (set_slot packed j vj) i vi.
Proof.
  intros packed i j vi vj Hne. unfold set_slot.
  rewrite N2Nat.id, N2Nat.id.
  rewrite (set_slot_N_comm (N.of_nat packed) i j (N.of_nat vi) (N.of_nat vj) Hne).
  reflexivity.
Qed.
