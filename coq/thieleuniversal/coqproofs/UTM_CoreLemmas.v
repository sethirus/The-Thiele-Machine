(* ...existing code... *)

(* ...existing code... *)

Require Import ThieleUniversal.CPU.
Require Import ThieleUniversal.UTM_Encode.
Require Import ThieleUniversal.UTM_Program.
Open Scope nat_scope.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Bool.Bool.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Classes.RelationClasses.
Require Import ThieleUniversal.TM.
Require Import ZArith.
Import ListNotations.
Import ThieleUniversal.TM.
Import ThieleUniversal.UTM_Encode.
Import ThieleUniversal.UTM_Program.

Lemma length_UTM_Encode_encode_rule : forall r,
  length (UTM_Encode.encode_rule r) = 5.
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

(* Local version of [set_nth] and its basic lemmas so other modules can use them
   without creating import cycles. *)
Fixpoint set_nth_local (l:list nat) (idx:nat) (v:nat) : list nat :=
  match l, idx with
  | [], _ => []
  | _::tl, 0 => v::tl
  | hd::tl, S i => hd :: set_nth_local tl i v
  end.

Lemma length_set_nth_local : forall l idx v,
  length (set_nth_local l idx v) = length l.
Proof.
  induction l as [|hd tl IH]; intros [|idx] v; simpl; auto.
Qed.

Lemma nth_set_nth_local_eq : forall l idx v d,
  idx < length l ->
  nth idx (set_nth_local l idx v) d = v.
Proof.
  induction l as [|hd tl IH].
  - intros idx v d Hidx. inversion Hidx.
  - intros idx v d Hidx.
    destruct idx as [|idx']; simpl in *.
    + auto.
    + apply IH.
      lia.
Qed.

Lemma nth_set_nth_local_neq : forall l idx j v d,
  idx < length l -> j < length l -> idx <> j ->
  nth j (set_nth_local l idx v) d = nth j l d.
Proof.
  induction l as [|hd tl IH]; intros [|idx] [|j] v d Hidx Hj Hneq; simpl in *; try lia; auto.
  - eapply IH; lia.
Qed.

Lemma set_nth_eq_update : forall l r v,
  r < length l ->
  firstn r l ++ v :: skipn (S r) l = set_nth_local l r v.
Proof.
  induction l as [|hd tl IH]; intros r v Hr; simpl in *.
  - (* impossible: r < 0 *) lia.
  - destruct r as [|r']; simpl.
    + reflexivity.
    + assert (Hr' : r' < length tl) by lia.
    f_equal; apply IH; exact Hr'.
Qed.

(* Helper tactic: normalize an explicit [firstn r l ++ x :: skipn (S r) l]
   occurrence into the canonical [set_nth_local l r x] form so rewrites
   that expect [set_nth_local] will succeed irrespective of syntactic
   differences introduced by local computation. This avoids brittle
   rewrite patterns across the development. *)
Ltac normalize_set_nth :=
  match goal with
  | |- context[firstn ?r ?l ++ ?x :: skipn (S ?r) ?l] =>
      let H := fresh "Hupd" in
      assert (H: firstn r l ++ x :: skipn (S r) l = set_nth_local l r x) by (apply set_nth_eq_update; try lia);
      rewrite H; clear H
  | H: context[firstn ?r ?l ++ ?x :: skipn (S ?r) ?l] |- _ =>
      let Hupd := fresh "Hupd" in
      assert (Hupd: firstn r l ++ x :: skipn (S r) l = set_nth_local l r x) by (apply set_nth_eq_update; try lia);
      rewrite Hupd in H; clear Hupd
  end.



Lemma skipn_cons_nth : forall (A : Type) (l : list A) n d,
  n < length l ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof.
  intros A l n d Hlt.
  revert l d Hlt.
  induction n as [|n IH]; intros l d Hlt.
  - destruct l as [|x xs]; simpl in *; try lia; reflexivity.
  - destruct l as [|x xs]; simpl in *; try lia.
    apply IH. simpl in Hlt. lia.
Qed.

Lemma nth_update_firstn_skipn_other : forall (l : list nat) r1 r2 (x d : nat),
  r1 < length l ->
  r2 < length l ->
  r1 <> r2 ->
  nth r2 (firstn r1 l ++ x :: skipn (S r1) l) d = nth r2 l d.
Proof.
  intros l r1 r2 x d Hr1 Hr2 Hneq.
  assert (Hupd : firstn r1 l ++ x :: skipn (S r1) l = set_nth_local l r1 x).
  { apply set_nth_eq_update. exact Hr1. }
  rewrite Hupd.
  unfold set_nth_local.
  apply nth_set_nth_local_neq; assumption.
Qed.
Lemma nth_update_firstn_skipn_commute : forall (l : list nat) r1 r2 (v1 v2 : nat) r (d : nat),
  r1 < length l ->
  r2 < length l ->
  r < length l ->
  r1 <> r2 ->
  r <> r1 ->
  r <> r2 ->
  nth r (firstn r1 l ++ v1 :: skipn (S r1) l) d = nth r (firstn r2 l ++ v2 :: skipn (S r2) l) d.
Proof.
  intros l r1 r2 v1 v2 r d Hr1 Hr2 Hr Hneq12 Hr1r Hr2r.
  pose proof (not_eq_sym Hr1r) as Hneq_r1.
  pose proof (not_eq_sym Hr2r) as Hneq_r2.
  rewrite (nth_update_firstn_skipn_other l r1 r v1 d Hr1 Hr Hneq_r1).
  rewrite (nth_update_firstn_skipn_other l r2 r v2 d Hr2 Hr Hneq_r2).
  reflexivity.
Qed.

Lemma length_UTM_Encode_encode_rules : forall rs,
  length (UTM_Encode.encode_rules rs) = 5 * length rs.
Proof.
  induction rs as [|r rs IH]; simpl; auto.
  rewrite app_length, length_UTM_Encode_encode_rule, IH. lia.
Qed.

Lemma encode_rules_cons : forall r rs,
  UTM_Encode.encode_rules (r :: rs) = UTM_Encode.encode_rule r ++ UTM_Encode.encode_rules rs.
Proof.
  intros r rs. unfold UTM_Encode.encode_rules. simpl. reflexivity.
Qed.

Lemma nth_encode_rules :
  forall rs i j d,
    i < length rs -> j < 5 ->
    nth (i * 5 + j) (UTM_Encode.encode_rules rs) d =
    match nth i rs (0,0,0,0,0%Z) with
    | (q_rule, sym_rule, q_next, w_next, m_next) =>
        match j with
        | 0 => q_rule
        | 1 => sym_rule
        | 2 => q_next
        | 3 => w_next
        | _ => UTM_Encode.encode_z m_next
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
    simpl UTM_Encode.encode_rules.
    assert (Hge : 5 + (i * 5 + j) >= length (UTM_Encode.encode_rule r)).
    { rewrite length_UTM_Encode_encode_rule. lia. }
    rewrite (nth_app_ge (UTM_Encode.encode_rule r) (UTM_Encode.encode_rules rs) (5 + (i * 5 + j)) d Hge).
    rewrite length_UTM_Encode_encode_rule.
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
    skipn (i * 5) (UTM_Encode.encode_rules rs) = UTM_Encode.encode_rules (skipn i rs).
Proof.
  induction rs as [|r rs IH]; intros i.
  - destruct i; reflexivity.
  - destruct i as [|i].
    + reflexivity.
    + rewrite encode_rules_cons.
      replace (skipn (S i) (r :: rs)) with (skipn i rs) by reflexivity.
      replace (S i * 5) with (length (UTM_Encode.encode_rule r) + i * 5)
        by (rewrite length_UTM_Encode_encode_rule; lia).
      rewrite (skipn_app_exact nat (UTM_Encode.encode_rule r) (UTM_Encode.encode_rules rs) (i * 5)).
      replace (length (UTM_Encode.encode_rule r) + i * 5 - length (UTM_Encode.encode_rule r)) with (i * 5)
        by (rewrite length_UTM_Encode_encode_rule; lia).
      apply IH.
Qed.

Lemma firstn_encode_rules :
  forall rs i,
    firstn (i * 5) (UTM_Encode.encode_rules rs) = UTM_Encode.encode_rules (firstn i rs).
Proof.
  induction rs as [|r rs IH]; intros i.
  - destruct i; reflexivity.
  - destruct i as [|i].
    + reflexivity.
    + replace (firstn (S i) (r :: rs)) with (r :: firstn i rs) by reflexivity.
      rewrite encode_rules_cons.
      replace (S i * 5) with (length (UTM_Encode.encode_rule r) + i * 5)
        by (rewrite length_UTM_Encode_encode_rule; lia).
      rewrite (@firstn_app_2 nat (i * 5) (UTM_Encode.encode_rule r) (UTM_Encode.encode_rules rs)).
      simpl.
      f_equal.
      apply IH.
Qed.

Lemma read_mem_rule_component_from_table :
  forall (rules : list (nat * nat * nat * nat * Z)) (st : CPU.State)
         (i offset : nat),
    firstn (length (UTM_Encode.encode_rules rules))
          (skipn UTM_Program.RULES_START_ADDR (CPU.mem st)) = UTM_Encode.encode_rules rules ->
    i < length rules ->
    offset < 5 ->
    nth (UTM_Program.RULES_START_ADDR + i * 5 + offset) (CPU.mem st) 0 =
      match nth i rules (0, 0, 0, 0, 0%Z) with
      | (q_rule, sym_rule, q_next, w_next, m_next) =>
          match offset with
          | 0 => q_rule
          | 1 => sym_rule
          | 2 => q_next
          | 3 => w_next
          | _ => UTM_Encode.encode_z m_next
          end
      end.
Proof.
  intros rules st i offset Htable Hi Hoffset.
  pose proof (length_UTM_Encode_encode_rules rules) as Hlen.
  assert (Hlt : i * 5 + offset < length (UTM_Encode.encode_rules rules)).
  { rewrite Hlen. lia. }
  replace (UTM_Program.RULES_START_ADDR + i * 5 + offset)
    with (UTM_Program.RULES_START_ADDR + (i * 5 + offset)) by lia.
  rewrite (@nth_add_skipn nat (CPU.mem st) UTM_Program.RULES_START_ADDR (i * 5 + offset) 0).
  assert (Hnth_firstn :
            nth (i * 5 + offset) (skipn UTM_Program.RULES_START_ADDR (CPU.mem st)) 0 =
            nth (i * 5 + offset)
                (firstn (length (UTM_Encode.encode_rules rules))
                        (skipn UTM_Program.RULES_START_ADDR (CPU.mem st))) 0).
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
  r < length (CPU.regs st) ->
  length (CPU.regs (CPU.write_reg r v st)) = length (CPU.regs st).
Proof.
  intros st r v Hr.
  unfold CPU.write_reg; simpl.
  apply length_update_firstn_skipn.
  exact Hr.
Qed.

Lemma read_reg_write_reg_same : forall st r v,
  r < length (CPU.regs st) ->
  CPU.read_reg r (CPU.write_reg r v st) = v.
Proof.
  intros st r v Hr.
  unfold CPU.read_reg, CPU.write_reg.
  apply nth_update_firstn_skipn_same.
  exact Hr.
Qed.

Lemma read_reg_write_reg_other : forall st r1 r2 v,
  r1 < length (CPU.regs st) ->
  r2 < length (CPU.regs st) ->
  r1 <> r2 ->
  CPU.read_reg r2 (CPU.write_reg r1 v st) = CPU.read_reg r2 st.
Proof.
  intros st r1 r2 v Hr1 Hr2 Hneq.
  unfold CPU.read_reg, CPU.write_reg.
  apply nth_update_firstn_skipn_other.
  - exact Hr1.
  - exact Hr2.
  - exact Hneq.
Qed.

Lemma read_reg_write_reg_commute : forall st a b va vb r,
  a <> b -> r <> a -> r <> b ->
  a < length (CPU.regs st) -> b < length (CPU.regs st) -> r < length (CPU.regs st) ->
  CPU.read_reg r (CPU.write_reg a va (CPU.write_reg b vb st)) = CPU.read_reg r (CPU.write_reg b vb (CPU.write_reg a va st)).
Proof.
  intros st a b va vb r Hab Hra Hrb Ha Hb Hr.
  set (st_b := CPU.write_reg b vb st).
  assert (Hlen_b : length (CPU.regs st_b) = length (CPU.regs st))
    by (unfold st_b; apply length_regs_write_reg; exact Hb).
  assert (Ha_st_b : a < length (CPU.regs st_b)) by (rewrite Hlen_b; exact Ha).
  assert (Hr_st_b : r < length (CPU.regs st_b)) by (rewrite Hlen_b; exact Hr).
  assert (Hab_comm :
            CPU.read_reg r (CPU.write_reg a va st_b) = CPU.read_reg r st_b).
  { unfold st_b.
    apply (read_reg_write_reg_other st_b a r va);
      [ exact Ha_st_b | exact Hr_st_b | exact (not_eq_sym Hra) ].
  }
  assert (Hrb_comm : CPU.read_reg r st_b = CPU.read_reg r st).
  { unfold st_b.
    apply (read_reg_write_reg_other st b r vb);
      [ exact Hb | exact Hr | exact (not_eq_sym Hrb) ].
  }
  assert (Hlen_a : length (CPU.regs (CPU.write_reg a va st)) = length (CPU.regs st))
    by (apply length_regs_write_reg; exact Ha).
  assert (Hb_st_a : b < length (CPU.regs (CPU.write_reg a va st))) by (rewrite Hlen_a; exact Hb).
  assert (Hr_st_a : r < length (CPU.regs (CPU.write_reg a va st))) by (rewrite Hlen_a; exact Hr).
  assert (Hba_comm :
            CPU.read_reg r (CPU.write_reg b vb (CPU.write_reg a va st)) =
            CPU.read_reg r (CPU.write_reg a va st)).
  { apply (read_reg_write_reg_other (CPU.write_reg a va st) b r vb);
    [ exact Hb_st_a | exact Hr_st_a | exact (not_eq_sym Hrb) ]. }
  assert (Hra_comm : CPU.read_reg r (CPU.write_reg a va st) = CPU.read_reg r st).
  { apply (read_reg_write_reg_other st a r va);
    [ exact Ha | exact Hr | exact (not_eq_sym Hra) ]. }
  rewrite Hab_comm, Hrb_comm, Hba_comm, Hra_comm.
  reflexivity.
Qed.

Lemma read_reg_ge_length : forall st r,
  r >= length (CPU.regs st) -> CPU.read_reg r st = 0.
Proof.
  intros st r Hge.
  unfold CPU.read_reg.
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
  CPU.read_reg r st <> 0 -> r < length (CPU.regs st).
Proof.
  intros st r Hnz.
  destruct (le_lt_dec (length (CPU.regs st)) r) as [Hle|Hlt].
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

Lemma TM_find_rule_some_split :
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

Lemma TM_find_rule_skipn_index :
  forall rules i q sym q' w m,
    TM.find_rule (skipn i rules) q sym = Some (q', w, m) ->
    exists j,
      i <= j /\ j < length rules /\
      nth j rules (0,0,0,0,0%Z) = (q, sym, q', w, m).
Proof.
  intros rules i q sym q' w m Hfind.
  pose proof (TM_find_rule_some_split (skipn i rules) q sym q' w m Hfind)
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

(* Helper lemma for memory consistency in rule table suffixes *)
Lemma encode_rules_skipn_consistent :
  forall rules i j,
    i < length rules ->
    j < length (skipn i rules) ->
    nth (i + j) rules (0,0,0,0,0%Z) = nth j (skipn i rules) (0,0,0,0,0%Z).
Proof.
  intros rules i j Hi Hj.
  rewrite length_skipn_general in Hj.
  assert (Hbound : i + j < length rules) by lia.
  rewrite (@nth_add_skipn _ rules i j (0,0,0,0,0%Z)).
  reflexivity.
Qed.
