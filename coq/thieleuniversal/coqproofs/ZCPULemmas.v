Require Import List.
Require Import Lia.
Require Import UTM_CoreLemmas.

Import ListNotations.
Import CPU.

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
