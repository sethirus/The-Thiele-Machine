Require Import List.
Require Import Lia.
Require Import ThieleUniversal.

Import ListNotations.
Import CPU.

(* Basic properties of register and memory operations. *)

Lemma read_reg_write_same :
  forall r v st,
    r <= length (regs st) ->
    read_reg r (write_reg r v st) = v.
Proof.
  intros r v st Hlen.
  unfold read_reg, write_reg.
  generalize (regs st) as l.
  intros l.
  revert r Hlen.
  induction l as [|x l IH]; intros [|r] Hlen; simpl in *; try lia; auto.
  - apply IH. lia.
Qed.

Lemma read_reg_write_other :
  forall r1 r2 v st,
    r1 <> r2 ->
    read_reg r2 (write_reg r1 v st) = read_reg r2 st.
Proof.
  intros r1 r2 v st Hneq.
  unfold read_reg, write_reg.
  generalize (regs st) as l.
  intros l.
  revert r1 r2 Hneq.
  induction l as [|x l IH]; intros [|r1] [|r2] Hneq; simpl; auto;
    try (apply IH; congruence).
Qed.

Lemma read_mem_write_mem_same :
  forall addr v st,
    read_mem addr (write_mem addr v st) = v.
Proof.
  intros addr v st.
  unfold read_mem, write_mem.
  generalize (mem st) as m.
  intros m.
  revert addr.
  induction m as [|x m IH]; intros [|addr]; simpl; auto.
Qed.

Lemma read_mem_write_mem_other :
  forall a1 a2 v st,
    a1 <> a2 ->
    read_mem a2 (write_mem a1 v st) = read_mem a2 st.
Proof.
  intros a1 a2 v st Hneq.
  unfold read_mem, write_mem.
  generalize (mem st) as m.
  intros m.
  revert a1 a2 Hneq.
  induction m as [|x m IH]; intros [|a1] [|a2] Hneq; simpl; auto;
    try (apply IH; congruence).
Qed.

Lemma read_mem_write_reg :
  forall addr r v st,
    read_mem addr (write_reg r v st) = read_mem addr st.
Proof.
  intros addr r v st. unfold read_mem, write_reg. reflexivity.
Qed.

Lemma run1_preserves_memory :
  forall st addr,
    let pc := read_reg REG_PC st in
    let instr := decode_instr (read_mem pc st) in
    is_not_StoreIndirect instr ->
    read_mem addr (run1 st) = read_mem addr st.
Proof.
  intros st addr pc instr Hns.
  unfold run1.
  unfold CPU.step.
  remember (read_reg REG_PC st) as pc0.
  remember (write_reg REG_PC (S pc0) st) as st'.
  destruct instr; simpl in Hns; try contradiction;
    try (rewrite read_mem_write_reg; reflexivity);
    try (rewrite read_mem_write_reg; rewrite read_mem_write_reg; reflexivity).
  - (* Jz case *)
    destruct (Nat.eqb (read_reg rc st) 0);
      rewrite read_mem_write_reg; reflexivity.
  - (* Jnz case *)
    destruct (Nat.eqb (read_reg rc st) 0);
      repeat rewrite read_mem_write_reg; reflexivity.
  - (* Halt case *)
    reflexivity.
Qed.

(* Instructions that do not write to memory. *)
Definition is_not_StoreIndirect (i:Instr) : Prop :=
  match i with
  | StoreIndirect _ _ => False
  | _ => True
  end.

(* Running instructions that never store preserves memory outside the program area. *)
Lemma run_n_preserves_memory_outside_range :
  forall st n start_addr end_addr,
    (forall i, i < n ->
       let current_pc := read_reg REG_PC (run_n st i) in
       let instr := decode_instr (read_mem current_pc st) in
       is_not_StoreIndirect instr) ->
    (forall addr, start_addr <= addr -> addr < end_addr ->
       read_mem addr (run_n st n) = read_mem addr st).
Proof.
  induction n as [|n IH]; intros start_addr end_addr Hsafe addr Hge Hlt; simpl.
  - reflexivity.
  - assert (Hns :
        let pc := read_reg REG_PC st in
        let instr := decode_instr (read_mem pc st) in
        is_not_StoreIndirect instr).
    { specialize (Hsafe 0). apply Hsafe. lia. }
    assert (Hmem1 : forall a, read_mem a (run1 st) = read_mem a st).
    { intro a. apply run1_preserves_memory with (st:=st) (addr:=a).
      unfold is_not_StoreIndirect in Hns. exact Hns. }
    assert (Hsafe' : forall i, i < n ->
        let current_pc := read_reg REG_PC (run_n (run1 st) i) in
        let instr := decode_instr (read_mem current_pc (run1 st)) in
        is_not_StoreIndirect instr).
    { intros i Hi.
      specialize (Hsafe (S i)). assert (S i < S n) by lia. specialize (Hsafe H0).
      rewrite run_n_succ in Hsafe.
      set (pc := read_reg REG_PC (run_n (run1 st) i)) in *.
      rewrite <- (Hmem1 pc) in Hsafe. exact Hsafe. }
    rewrite run_n_succ.
    specialize (IH start_addr end_addr Hsafe' addr Hge Hlt).
    rewrite IH.
    apply Hmem1.
Qed.

(* Encoding rules occupy five consecutive cells per TM rule. *)
Lemma length_encode_rule : forall r,
  length (encode_rule r) = 5.
Proof.
  intros [q [s [q' [w m]]]]. simpl. reflexivity.
Qed.

Lemma length_encode_rules : forall rs,
  length (encode_rules rs) = 5 * length rs.
Proof.
  induction rs as [|r rs IH]; simpl; auto.
  rewrite app_length, length_encode_rule, IH. lia.
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
  - destruct r as [q_rule [sym_rule [q_next [w_next m_next]]]].
    destruct j; simpl in *; try lia; try reflexivity.
    destruct j; simpl in *; try lia; try reflexivity.
    destruct j; simpl in *; try lia; try reflexivity.
    destruct j; simpl in *; try lia; try reflexivity.
    destruct j; simpl in *; try lia; try reflexivity.
  - replace (S i * 5 + j) with (5 + (i * 5 + j)) by lia.
    rewrite flat_map_cons, nth_app.
    rewrite length_encode_rule.
    destruct (lt_dec (i * 5 + j) (length (encode_rules rs))).
    + rewrite IH; try lia.
      destruct (nth i rs (0,0,0,0,0%Z)) as [[[[q1 s1] q1'] w1'] m1'].
      simpl. destruct j; simpl in *; try lia; reflexivity.
    + assert (i * 5 + j < 5 + length (encode_rules rs)) by (rewrite length_encode_rule; lia).
      exfalso. apply n. lia.
Qed.

(* Bridge between abstract rule list and concrete memory layout. *)
Lemma read_mem_rule_component :
  forall tm conf st i component_offset,
    inv st tm conf ->
    i < length (tm_rules tm) ->
    let rule_addr := RULES_START_ADDR + i * 5 + component_offset in
    let rule_list := tm_rules tm in
    let '(q_rule, sym_rule, q_next, w_next, m_next) :=
        nth i rule_list (0,0,0,0,0%Z) in
    (component_offset = 0 -> read_mem rule_addr st = q_rule) /\
    (component_offset = 1 -> read_mem rule_addr st = sym_rule) /\
    (component_offset = 2 -> read_mem rule_addr st = q_next) /\
    (component_offset = 3 -> read_mem rule_addr st = w_next) /\
    (component_offset = 4 -> read_mem rule_addr st = encode_z m_next).
Proof.
  intros tm conf st i component_offset Hinv Hi.
  unfold rule_addr, rule_list.
  destruct Hinv as [HQ [HHEAD [HPC [Htape [Hprog Hr]]]]].
  set (rules := tm_rules tm) in *.
  assert (Hr_mem : forall k,
            k < length (encode_rules rules) ->
            read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
  {
    intros k Hk.
    pose proof (f_equal (fun l => nth k l 0) Hr) as Hnth.
    rewrite nth_firstn in Hnth by lia.
    rewrite nth_skipn in Hnth.
    exact Hnth.
  }
  repeat split; intros Hc; subst component_offset;
    rewrite Hr_mem; try (rewrite length_encode_rules; lia);
    rewrite nth_encode_rules with (rs:=rules) (i:=i);
    try lia; reflexivity.
Qed.
