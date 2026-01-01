Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qring.
Require Import Coq.Setoids.Setoid.

Local Open Scope Q_scope.

Definition bit_sign (n : nat) : Q := 
  if Nat.eqb n 0%nat then 1#1 else if Nat.eqb n 1%nat then (-1)#1 else 0#1.

Lemma Qopp_0_le: forall x : Q, 0 <= x -> - x <= 0.
Proof.
  intros.
  apply <- Qle_minus_iff.
  assert (Hrw: 0 + - (- x) == x) by ring.
  setoid_rewrite Hrw.
  exact H.
Qed.

Lemma minimal_normalized_E_bound:
  forall p00 p01 p10 p11 : Q,
    0#1 <= p00 -> 0#1 <= p01 -> 0#1 <= p10 -> 0#1 <= p11 ->
    p00 + p01 + p10 + p11 == 1#1 ->
    Qabs (p00 - p01 - p10 + p11) <= 1#1.
Proof.
  intros p00 p01 p10 p11 Hp00 Hp01 Hp10 Hp11 Hsum.
  (* Use Qabs_Qle_condition: |E| <= 1 iff -1 <= E <= 1 *)
  setoid_rewrite Qabs_Qle_condition.
  split.
  - (* Show -1 <= p00 - p01 - p10 + p11 *)
    (* Equivalently: (p00 - p01 - p10 + p11) - (-1) >= 0, i.e., (p00 - p01 - p10 + p11) + 1 >= 0 *)
    (* Use that sum = 1, so (p00 - p01 - p10 + p11) + (p00 + p01 + p10 + p11) = 2*p00 + 2*p11 >= 0 *)
    assert (Heq: (p00 - p01 - p10 + p11) + 1 == (p00 - p01 - p10 + p11) + (p00 + p01 + p10 + p11)).
    { setoid_rewrite Hsum. ring. }
    assert (H_pos: 0 <= (p00 - p01 - p10 + p11) + 1).
    { setoid_rewrite Heq.
      assert (Hrw2: (p00 - p01 - p10 + p11) + (p00 + p01 + p10 + p11) == (p00 + p00) + (p11 + p11)) by ring.
      setoid_rewrite Hrw2.
      assert (H00: 0 <= p00 + p00).
      { assert (Hrw: 0 == 0 + 0) by ring. setoid_rewrite Hrw.
        apply Qplus_le_compat; [exact Hp00 | exact Hp00]. }
      assert (H11: 0 <= p11 + p11).
      { assert (Hrw: 0 == 0 + 0) by ring. setoid_rewrite Hrw.
        apply Qplus_le_compat; [exact Hp11 | exact Hp11]. }
      assert (Hrw3: 0 == 0 + 0) by ring.
      setoid_rewrite Hrw3.
      apply Qplus_le_compat; [exact H00 | exact H11]. }
    (* Now use H_pos to derive -1 <= p00 - p01 - p10 + p11 *)
    (* Note: -1 <= E is equivalent to E - (-1) >= 0, i.e., E + 1 >= 0 *)
    assert (Hrw_final: forall a b, 0 <= a - b -> b <= a).
    { intros. apply <- Qle_minus_iff. exact H. }
    apply (Hrw_final (p00 - p01 - p10 + p11) (-1)).
    assert (Heq2: (p00 - p01 - p10 + p11) - (-1) == (p00 - p01 - p10 + p11) + 1) by ring.
    setoid_rewrite Heq2. exact H_pos.
  - (* Show p00 - p01 - p10 + p11 <= 1 *)
    assert (H_bound: p00 + p11 <= 1).
    { apply (Qle_trans _ (p00 + p01 + p10 + p11) _).
      - assert (H0: 0 <= p01 + p10).
        { assert (Hrw: 0 == 0 + 0) by ring. setoid_rewrite Hrw.
          apply Qplus_le_compat; [exact Hp01 | exact Hp10]. }
        assert (H_prep: (p00 + p11) + 0 <= (p00 + p11) + (p01 + p10)).
        { apply Qplus_le_compat; [apply Qle_refl | exact H0]. }
        assert (Hrw1: (p00 + p11) + 0 == p00 + p11) by ring.
        assert (Hrw2: (p00 + p11) + (p01 + p10) == p00 + p01 + p10 + p11) by ring.
        setoid_rewrite Hrw1 in H_prep.
        setoid_rewrite Hrw2 in H_prep.
        exact H_prep.
      - setoid_rewrite Hsum. apply Qle_refl. }
    apply (Qle_trans _ (p00 + p11) _); [|exact H_bound].
    assert (H0: 0 <= p01 + p10).
    { assert (Hrw: 0 == 0 + 0) by ring. setoid_rewrite Hrw.
      apply Qplus_le_compat; [exact Hp01 | exact Hp10]. }
    apply <- Qle_minus_iff.
    assert (Hrw: p00 + p11 - (p00 - p01 - p10 + p11) == p01 + p10) by ring.
    setoid_rewrite Hrw.
    exact H0.
Qed.

Close Scope Q_scope.
