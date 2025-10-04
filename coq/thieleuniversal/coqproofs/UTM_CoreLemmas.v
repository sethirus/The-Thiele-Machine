Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Require Import CPU.
Require Import TM.
Require Import ZArith.
Require Import UTM_Encode.
Require Import UTM_Program.
Import ListNotations.
Import CPU.
Import UTM_Encode.
Import UTM_Program.
Open Scope nat_scope.

Lemma length_encode_rule : forall r,
  length (encode_rule r) = 5.
Proof.
  intros [[[[q s] q'] w] m]. simpl. reflexivity.
Qed.

Lemma flat_map_cons {A B} (f : A -> list B) (x : A) (xs : list A) :
  flat_map f (x :: xs) = f x ++ flat_map f xs.
Proof. reflexivity. Qed.

Lemma nth_app_lt {A} (l1 l2 : list A) n d :
  n < length l1 -> nth n (l1 ++ l2) d = nth n l1 d.
Proof.
  revert n.
  induction l1 as [|x xs IH]; intros [|n] Hlt; simpl in *; try lia; auto.
  apply IH. lia.
Qed.

Lemma nth_app_ge {A} (l1 l2 : list A) n d :
  n >= length l1 -> nth n (l1 ++ l2) d = nth (n - length l1) l2 d.
Proof.
  revert n.
  induction l1 as [|x xs IH]; intros n Hge; simpl in *.
  - replace (n - 0) with n by lia. reflexivity.
  - destruct n; simpl in *; try lia.
    specialize (IH n).
    assert (Hge' : n >= length xs) by lia.
    specialize (IH Hge').
    replace (S n - S (length xs)) with (n - length xs) by lia.
    exact IH.
Qed.

Lemma nth_add_skipn {A} (l : list A) base k d :
  nth (base + k) l d = nth k (skipn base l) d.
Proof.
  revert l k.
  induction base as [|base IH]; intros l k; simpl.
  - reflexivity.
  - destruct l as [|x xs]; simpl; auto.
    destruct k; simpl; auto using IH.
Qed.

Lemma nth_firstn_lt {A} (n m : nat) (l : list A) d :
  n < m -> nth n (firstn m l) d = nth n l d.
Proof.
  revert n l.
  induction m as [|m IH]; intros [|n] l Hlt; simpl in *; try lia.
  - destruct l; reflexivity.
  - destruct l as [|x xs]; simpl; [reflexivity|].
    apply IH. lia.
Qed.

Lemma length_skipn_succ : forall (A : Type) r (xs : list A),
  r < length xs -> length (skipn r xs) = S (length (skipn (S r) xs)).
Proof.
  intros A r.
  induction r as [|r IH]; intros xs Hr; simpl in *.
  - destruct xs as [|x xs']. 
    + exfalso. apply Nat.nlt_0_r in Hr. exact Hr.
    + reflexivity.
  - destruct xs as [|x xs'].
    + exfalso. apply Nat.nlt_0_r in Hr. exact Hr.
    + simpl in Hr.
      apply IH.
      apply Nat.succ_lt_mono.
      exact Hr.
Qed.

Lemma length_update_firstn_skipn : forall (A : Type) (l : list A) r (v : A),
  r < length l -> length (firstn r l ++ v :: skipn (S r) l) = length l.
Proof.
  intros A l.
  induction l as [|x xs IH]; intros r v Hr; simpl in *; try lia.
  destruct r as [|r']; simpl in *.
  - reflexivity.
  - assert (Hr' : r' < length xs) by lia.
    simpl.
    specialize (IH r' v Hr').
    rewrite IH.
    reflexivity.
Qed.

Lemma nth_update_firstn_skipn_same : forall (A : Type) (l : list A) r (x d : A),
  r < length l -> nth r (firstn r l ++ x :: skipn (S r) l) d = x.
Proof.
  intros A l.
  induction l as [|a xs IH]; intros r x d Hr; simpl in *; try lia.
  destruct r as [|r']; simpl in *.
  - reflexivity.
  - apply IH.
    lia.
Qed.

Lemma nth_update_firstn_skipn_other : forall (A : Type) (l : list A) r1 r2 (x d : A),
  r1 < length l ->
  r2 < length l ->
  r1 <> r2 ->
  nth r2 (firstn r1 l ++ x :: skipn (S r1) l) d = nth r2 l d.
Proof.
  intros A l.
  induction l as [|a xs IH]; intros r1 r2 x d Hr1 Hr2 Hneq; simpl in *; try lia.
  destruct r1 as [|r1']; simpl in *.
  - destruct r2 as [|r2']; simpl in *; try lia.
    reflexivity.
  - destruct r2 as [|r2']; simpl in *.
    + reflexivity.
    + assert (Hr1' : r1' < length xs) by lia.
      assert (Hr2' : r2' < length xs) by lia.
      specialize (IH r1' r2' x d Hr1' Hr2').
      simpl in IH.
      apply IH.
      lia.
Qed.

Lemma length_encode_rules : forall rs,
  length (encode_rules rs) = 5 * length rs.
Proof.
  induction rs as [|r rs IH]; simpl; auto.
  rewrite app_length, length_encode_rule, IH. lia.
Qed.

Lemma encode_rules_cons : forall r rs,
  encode_rules (r :: rs) = encode_rule r ++ encode_rules rs.
Proof.
  intros r rs. unfold encode_rules. simpl. reflexivity.
Qed.

Lemma nth_encode_rules :
  forall rs i j d,
    i < length rs -> j < 5 ->
    nth (i * 5 + j) (encode_rules rs) d =
    match nth i rs (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        match j with
        | 0 => q_rule
        | 1 => sym_rule
        | 2 => q_next
        | 3 => w_next
        | _ => encode_z m_next
        end
    end.
Proof.
  induction rs as [|r rs IH]; intros i j d Hi Hj; simpl in *; try lia.
  destruct i.
  - destruct r as [[[[q_rule sym_rule] q_next] w_next] m_next].
    destruct j; simpl in *; try lia; try reflexivity.
    destruct j; simpl in *; try lia; try reflexivity.
    destruct j; simpl in *; try lia; try reflexivity.
    destruct j; simpl in *; try lia; try reflexivity.
    destruct j; simpl in *; try lia; try reflexivity.
  - replace (S i * 5 + j) with (5 + (i * 5 + j)) by lia.
    simpl encode_rules.
    assert (Hge : 5 + (i * 5 + j) >= length (encode_rule r)).
    { rewrite length_encode_rule. lia. }
    rewrite (nth_app_ge (encode_rule r) (encode_rules rs) (5 + (i * 5 + j)) d Hge).
    rewrite length_encode_rule.
    replace (5 + (i * 5 + j) - 5) with (i * 5 + j) by lia.
    pose proof IH as IH'.
    specialize (IH' i j d).
    assert (Hi' : i < length rs) by lia.
    specialize (IH' Hi' Hj).
    rewrite IH'.
    destruct (nth i rs (0,0,0,0,0%Z)) as [[[[q1 s1] q1'] w1'] m1'].
    simpl. destruct j; simpl in *; try lia; reflexivity.
Qed.

Lemma skipn_ge_length : forall (A : Type) (l : list A) n,
  length l <= n -> skipn n l = [].
Proof.
  intros A l.
  induction l as [|x xs IH]; intros n Hlen; simpl in *.
  - destruct n; reflexivity.
  - destruct n as [|n].
    + exfalso. simpl in Hlen. lia.
    + apply IH. simpl in Hlen. lia.
Qed.

Lemma length_skipn_general : forall (A : Type) n (l : list A),
  length (skipn n l) = length l - n.
Proof.
  intros A n l.
  revert n.
  induction l as [|x xs IH]; intros [|n]; simpl; try reflexivity.
  rewrite IH. lia.
Qed.

Lemma skipn_app_exact : forall (A : Type) (l1 l2 : list A) n,
  skipn (length l1 + n) (l1 ++ l2) = skipn n l2.
Proof.
  intros A l1 l2 n.
  rewrite skipn_app.
  assert (Hskip : skipn (length l1 + n) l1 = []).
  { apply skipn_ge_length. lia. }
  rewrite Hskip.
  simpl.
  replace (length l1 + n - length l1) with n by lia.
  reflexivity.
Qed.

Lemma skipn_encode_rules :
  forall rs i,
    skipn (i * 5) (encode_rules rs) = encode_rules (skipn i rs).
Proof.
  induction rs as [|r rs IH]; intros i.
  - destruct i; reflexivity.
  - destruct i as [|i].
    + reflexivity.
    + rewrite encode_rules_cons.
      replace (skipn (S i) (r :: rs)) with (skipn i rs) by reflexivity.
      replace (S i * 5) with (length (encode_rule r) + i * 5)
        by (rewrite length_encode_rule; lia).
      rewrite (skipn_app_exact nat (encode_rule r) (encode_rules rs) (i * 5)).
      replace (length (encode_rule r) + i * 5 - length (encode_rule r)) with (i * 5)
        by (rewrite length_encode_rule; lia).
      apply IH.
Qed.

Lemma firstn_encode_rules :
  forall rs i,
    firstn (i * 5) (encode_rules rs) = encode_rules (firstn i rs).
Proof.
  induction rs as [|r rs IH]; intros i.
  - destruct i; reflexivity.
  - destruct i as [|i].
    + reflexivity.
    + replace (firstn (S i) (r :: rs)) with (r :: firstn i rs) by reflexivity.
      rewrite encode_rules_cons.
      replace (S i * 5) with (length (encode_rule r) + i * 5)
        by (rewrite length_encode_rule; lia).
      rewrite (@firstn_app_2 nat (i * 5) (encode_rule r) (encode_rules rs)).
      simpl.
      f_equal.
      apply IH.
Qed.

Lemma read_mem_rule_component_from_table :
  forall (rules : list (nat * nat * nat * nat * Z)) (st : State)
         (i offset : nat),
    firstn (length (encode_rules rules))
          (skipn RULES_START_ADDR (mem st)) = encode_rules rules ->
    i < length rules ->
    offset < 5 ->
    nth (RULES_START_ADDR + i * 5 + offset) (mem st) 0 =
      match nth i rules (0, 0, 0, 0, 0%Z) with
      | (q_rule, sym_rule, q_next, w_next, m_next) =>
          match offset with
          | 0 => q_rule
          | 1 => sym_rule
          | 2 => q_next
          | 3 => w_next
          | _ => encode_z m_next
          end
      end.
Proof.
  intros rules st i offset Htable Hi Hoffset.
  pose proof (length_encode_rules rules) as Hlen.
  assert (Hlt : i * 5 + offset < length (encode_rules rules)).
  { rewrite Hlen. lia. }
  replace (RULES_START_ADDR + i * 5 + offset)
    with (RULES_START_ADDR + (i * 5 + offset)) by lia.
  rewrite (@nth_add_skipn nat (mem st) RULES_START_ADDR (i * 5 + offset) 0).
  assert (Hnth_firstn :
            nth (i * 5 + offset) (skipn RULES_START_ADDR (mem st)) 0 =
            nth (i * 5 + offset)
                (firstn (length (encode_rules rules))
                        (skipn RULES_START_ADDR (mem st))) 0).
  { symmetry.
    apply nth_firstn_lt.
    rewrite Hlen. lia. }
  rewrite Hnth_firstn.
  rewrite Htable.
  apply (nth_encode_rules rules i offset 0); lia.
Qed.

Lemma nat_eqb_sub_zero_false_of_lt : forall a b,
  b < a -> Nat.eqb (a - b) 0 = false.
Proof.
  intros a b Hlt.
  apply Nat.eqb_neq.
  intros Hsub.
  lia.
Qed.

Lemma length_regs_write_reg : forall st r v,
  r < length (regs st) ->
  length (regs (write_reg r v st)) = length (regs st).
Proof.
  intros st r v Hr.
  unfold write_reg; simpl.
  apply length_update_firstn_skipn.
  exact Hr.
Qed.

Lemma read_reg_write_reg_same : forall st r v,
  r < length (regs st) ->
  read_reg r (write_reg r v st) = v.
Proof.
  intros st r v Hr.
  unfold read_reg, write_reg.
  apply nth_update_firstn_skipn_same.
  exact Hr.
Qed.

Lemma read_reg_write_reg_other : forall st r1 r2 v,
  r1 < length (regs st) ->
  r2 < length (regs st) ->
  r1 <> r2 ->
  read_reg r2 (write_reg r1 v st) = read_reg r2 st.
Proof.
  intros st r1 r2 v Hr1 Hr2 Hneq.
  unfold read_reg, write_reg.
  apply nth_update_firstn_skipn_other.
  - exact Hr1.
  - exact Hr2.
  - exact Hneq.
Qed.

Lemma read_reg_ge_length : forall st r,
  r >= length (regs st) -> read_reg r st = 0.
Proof.
  intros st r Hge.
  unfold read_reg.
  apply nth_overflow.
  exact Hge.
Qed.

Lemma nth_overflow_nat : forall n l,
  length l <= n -> nth n l 0 = 0.
Proof.
  intros n l Hlen.
  apply nth_overflow.
  exact Hlen.
Qed.

Lemma read_reg_nonzero_implies_in_bounds : forall st r,
  read_reg r st <> 0 -> r < length (regs st).
Proof.
  intros st r Hnz.
  destruct (le_lt_dec (length (regs st)) r) as [Hle|Hlt].
  { exfalso.
    rewrite (read_reg_ge_length st r Hle) in Hnz.
    apply Hnz. reflexivity. }
  { exact Hlt. }
Qed.

Lemma length_firstn_le : forall (A : Type) (l : list A) n,
  n <= length l -> length (firstn n l) = n.
Proof.
  intros A l n.
  revert l.
  induction n as [|n IH]; intros l Hle.
  - reflexivity.
  - destruct l as [|x xs]; simpl in *; try lia.
    simpl. f_equal. apply IH. lia.
Qed.

Lemma find_rule_some_split :
  forall rules q sym q' w m,
    find_rule rules q sym = Some (q', w, m) ->
    exists prefix suffix,
      rules = prefix ++ (q, sym, q', w, m) :: suffix.
Proof.
  induction rules as [|r rs IH]; intros q sym q' w m Hfind; simpl in Hfind.
  - discriminate Hfind.
  - destruct r as [[[[q_rule sym_rule] q_next] w_next] m_next].
    destruct (andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym)) eqn:Hmatch.
    + inversion Hfind; subst.
      apply andb_true_iff in Hmatch as [Hq_eq Hsym_eq].
      apply Nat.eqb_eq in Hq_eq.
      apply Nat.eqb_eq in Hsym_eq.
      subst q_rule sym_rule.
      exists [], rs.
      reflexivity.
    + specialize (IH q sym q' w m Hfind) as [prefix [suffix Heq]].
      exists ((q_rule, sym_rule, q_next, w_next, m_next) :: prefix), suffix.
      simpl. now rewrite Heq.
Qed.

Lemma find_rule_skipn_index :
  forall rules i q sym q' w m,
    find_rule (skipn i rules) q sym = Some (q', w, m) ->
    exists j,
      i <= j /\ j < length rules /\
      nth j rules (0,0,0,0,0%Z) = (q, sym, q', w, m).
Proof.
  intros rules i q sym q' w m Hfind.
  pose proof (find_rule_some_split (skipn i rules) q sym q' w m Hfind)
    as [prefix [suffix Hsplit]].
  set (rule := (q, sym, q', w, m)).
  set (j := i + length prefix).
  assert (Hlen_skip : length (skipn i rules) = length prefix + S (length suffix)).
  { rewrite Hsplit, app_length. simpl. lia. }
  assert (Hi_le : i <= length rules).
  { rewrite length_skipn_general in Hlen_skip. lia. }
  assert (Hlen_firstn : length (firstn i rules) = i)
    by (apply length_firstn_le; exact Hi_le).
  assert (Hlen_rules : length rules = i + length prefix + S (length suffix)).
  { rewrite length_skipn_general in Hlen_skip. lia. }
  exists j.
  repeat split.
  - unfold j. lia.
  - unfold j. rewrite Hlen_rules. lia.
  - unfold j.
    rewrite <- firstn_skipn with (l:=rules) (n:=i) at 1.
    rewrite Hsplit.
    rewrite app_assoc.
    rewrite nth_app_ge with (l1 := firstn i rules ++ prefix).
    2:{ rewrite app_length, Hlen_firstn. lia. }
    replace (i + length prefix - length (firstn i rules ++ prefix)) with 0.
    2:{ rewrite app_length, Hlen_firstn. lia. }
    simpl. reflexivity.
Qed.
