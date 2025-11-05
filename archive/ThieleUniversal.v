Require Import ThieleUniversal.UTM_Encode.
Require Import ThieleUniversal.UTM_Program.
Import UTM_Program.
Require Import ThieleUniversal.CPU.


Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Nat.
Require Import Lia.
Require Import ThieleUniversal.UTM_CoreLemmas.

(* Note: read_reg_write_reg_commute was removed - available in UTM_CoreLemmas if needed *)

Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.
Require Import ThieleUniversal.TM.

(* --- Section: Universal Program and Simulation --- *)

Import ThieleUniversal.CPU.

  (* Interpreter state predicates *)
  Definition IS_FetchSymbol (pc : nat) : Prop := pc = 0.
  Definition IS_FindRule_Start (pc : nat) : Prop := pc = 3.
  Definition IS_ApplyRule_Start (pc : nat) : Prop := pc = 29.
  Definition IS_Reset (pc : nat) : Prop := pc = 48.

  (* Memory predicate asserting the tape segment at [TAPE_START_ADDR]. *)
  Definition tape_window_ok (st : State) (tape : list nat) : Prop :=
    firstn (length tape) (skipn TAPE_START_ADDR st.(mem)) = tape.

  (* --- Explicit universal program --- *)
  (* Encoding base used for packing instruction operands into a single word. *)
  Definition ENC_BASE := 1024.

  (* Delegate decoding to the separate encoder module which uses a
     multi-word, low-reduction representation. *)
  Import UTM_Encode.
  Definition decode_instr (st : CPU.State) : Instr :=
    decode_instr_from_mem st.(mem) (4 * read_reg REG_PC st).

  (** Every encoded instruction assumes its operands fit within [ENC_BASE]. *)
  Definition instr_small (i : Instr) : Prop :=
    match i with
    | LoadConst rd v | LoadIndirect rd v | CopyReg rd v | AddConst rd v
    | Jz rd v | Jnz rd v => rd < ENC_BASE /\ v < ENC_BASE
    | StoreIndirect ra rv => ra < ENC_BASE /\ rv < ENC_BASE
    | AddReg rd r1 r2 | SubReg rd r1 r2 =>
        rd < ENC_BASE /\ r1 < ENC_BASE /\ r2 < ENC_BASE
    | Halt => True
    end.

  (* Use the correctness lemma from the encoder module rather than
     re-proving the division-based decoder here. *)
  Lemma decode_encode_roundtrip : forall i, instr_small i ->
    decode_instr_from_mem (encode_instr_words i) 0 = i.
  Proof. exact UTM_Encode.decode_encode_roundtrip. Qed.

  (** Simple symbolic execution tactic for unfolding CPU steps. *)
  Ltac symbolic_run :=
    cbv [step decode_instr write_reg write_mem read_reg read_mem] in *;
    repeat (simpl in *; try lia).

  (* Program is defined in the separate program module; import it here
     so the interpreter sees the same concrete program without duplicating
     the listing. *)
  Import UTM_Program.

  (* Total number of memory cells executed per TM step (4 words per
     instruction). *)
  Definition PROGRAM_STEPS : nat := 4 * length program_instrs.

  (* Encoded program image (flattened list of words). *)
  Definition program : list nat := flat_map encode_instr_words program_instrs.

  Lemma program_word_0 : nth 0 program 0 = 0.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_1 : nth 1 program 0 = REG_TEMP1.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_2 : nth 2 program 0 = TAPE_START_ADDR.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_3 : nth 3 program 0 = 0.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_4 : nth 4 program 0 = 5.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_5 : nth 5 program 0 = REG_ADDR.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_6 : nth 6 program 0 = REG_TEMP1.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_7 : nth 7 program 0 = REG_HEAD.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_8 : nth 8 program 0 = 1.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_9 : nth 9 program 0 = REG_SYM.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_10 : nth 10 program 0 = REG_ADDR.
  Proof. cbn. reflexivity. Qed.

  Lemma program_word_11 : nth 11 program 0 = 0.
  Proof. cbn. reflexivity. Qed.

  Lemma program_length_gt_5 : 5 < length program.
  Proof. cbn; lia. Qed.

  Lemma program_length_gt_11 : 11 < length program.
  Proof. cbn; lia. Qed.

  (* Update the n-th element of a list. *)
  Fixpoint set_nth (l:list nat) (idx:nat) (v:nat) : list nat :=
    match l, idx with
    | [], _ => []
    | _::tl, 0 => v::tl
    | hd::tl, S i => hd :: set_nth tl i v
    end.

  Lemma length_set_nth : forall l idx v,
    length (set_nth l idx v) = length l.
  Proof.
    induction l as [|x xs IH]; intros [|idx] v; simpl; auto; now rewrite IH.
  Qed.

  Lemma nth_set_nth_eq : forall l idx v d,
    idx < length l ->
    nth idx (set_nth l idx v) d = v.
  Proof.
    induction l as [|x xs IH]; intros idx v d Hlt.
    - simpl in Hlt. lia.
    - destruct idx; simpl in *.
      + reflexivity.
      + apply IH. lia.
  Qed.

  Lemma nth_set_nth_neq : forall l idx j v d,
    idx < length l -> j < length l -> j <> idx ->
    nth j (set_nth l idx v) d = nth j l d.
  Proof.
    induction l as [|x xs IH]; intros [|idx] [|j] v d Hidx Hj Hneq; simpl in *; try lia; auto.
    - apply IH; lia.
  Qed.

  Lemma length_app : forall (A : Type) (l1 l2 : list A),
    length (l1 ++ l2) = length l1 + length l2.
  Proof.
    apply List.app_length.
  Qed.

  Lemma firstn_app_le : forall (A : Type) n (l1 l2 : list A),
    n <= length l1 -> firstn n (l1 ++ l2) = firstn n l1.
  Proof.
    intros A n l1 l2 Hle.
    revert n Hle; induction l1 as [|x xs IH]; intros [|n] Hle; simpl in *; try lia; auto.
    - rewrite IH by lia. reflexivity.
  Qed.

  Lemma skipn_app_le : forall (A : Type) n (l1 l2 : list A),
    n <= length l1 -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
  Proof.
    intros A n l1 l2 Hle.
    revert n Hle; induction l1 as [|x xs IH]; intros [|n] Hle; simpl in *; try lia; auto.
    - rewrite IH by lia. reflexivity.
  Qed.

  Lemma skipn_cons_nth : forall (A : Type) (l : list A) n d,
    n < length l ->
    skipn n l = nth n l d :: skipn (S n) l.
  Proof.
    intros A l n d Hlt.
    revert l d Hlt.
    induction n as [|n IH]; intros l d Hlt.
    - destruct l as [|x xs]; simpl in *; try lia. reflexivity.
    - destruct l as [|x xs]; simpl in *; try lia.
      simpl.
      specialize (IH xs d).
      assert (Hlt' : n < length xs) by lia.
      specialize (IH Hlt').
      simpl in IH.
      exact IH.
  Qed.

  Lemma decode_instr_from_mem_ext : forall mem1 mem2 pc,
    (forall offset, offset < 4 ->
      nth (pc + offset) mem1 0 = nth (pc + offset) mem2 0) ->
    decode_instr_from_mem mem1 pc = decode_instr_from_mem mem2 pc.
  Proof.
    intros mem1 mem2 pc Hext.
    unfold decode_instr_from_mem.
    pose proof (Hext 0 ltac:(lia)) as Hopc.
    pose proof (Hext 1 ltac:(lia)) as Harg1.
    pose proof (Hext 2 ltac:(lia)) as Harg2.
    pose proof (Hext 3 ltac:(lia)) as Harg3.
    replace (pc + 0) with pc in Hopc by lia.
    rewrite <- Hopc.
    destruct (nth pc mem1 0); simpl;
      try (rewrite <- Harg1; rewrite <- Harg2; reflexivity);
      try (rewrite <- Harg1; rewrite <- Harg2; rewrite <- Harg3; reflexivity);
      try (rewrite <- Harg1; rewrite <- Harg2; reflexivity);
      try reflexivity.
  Qed.

  Lemma decode_instr_from_mem_ext_scaled : forall mem1 mem2 pc,
    (forall offset, offset < 4 ->
       nth (4 * pc + offset) mem1 0 = nth (4 * pc + offset) mem2 0) ->
    decode_instr_from_mem mem1 (4 * pc) = decode_instr_from_mem mem2 (4 * pc).
  Proof.
    intros mem1 mem2 pc Hext.
    apply decode_instr_from_mem_ext.
    intros offset Hoff.
    specialize (Hext offset Hoff).
    replace (4 * pc + offset) with (4 * pc + offset) by reflexivity.
    exact Hext.
  Qed.

  Lemma encode_instr_words_length : forall instr,
    length (encode_instr_words instr) = 4.
  Proof. intros instr; destruct instr; reflexivity. Qed.

  Lemma nth_after_prefix0 : forall words rest pc,
    length words = 4 ->
    nth (4 * pc + 4) (words ++ rest) 0 = nth (4 * pc) rest 0.
  Proof.
    intros words rest pc Hlen.
    replace (4 * pc + 4) with (length words + 4 * pc) by (rewrite Hlen; lia).
    apply app_nth2_plus.
  Qed.

  Lemma nth_after_prefix1 : forall words rest pc,
    length words = 4 ->
    nth (4 * pc + 4 + 1) (words ++ rest) 0 = nth (4 * pc + 1) rest 0.
  Proof.
    intros words rest pc Hlen.
    replace (4 * pc + 4 + 1) with (length words + (4 * pc + 1)) by (rewrite Hlen; lia).
    apply app_nth2_plus.
  Qed.

  Lemma nth_after_prefix2 : forall words rest pc,
    length words = 4 ->
    nth (4 * pc + 4 + 2) (words ++ rest) 0 = nth (4 * pc + 2) rest 0.
  Proof.
    intros words rest pc Hlen.
    replace (4 * pc + 4 + 2) with (length words + (4 * pc + 2)) by (rewrite Hlen; lia).
    apply app_nth2_plus.
  Qed.

  Lemma nth_after_prefix3 : forall words rest pc,
    length words = 4 ->
    nth (4 * pc + 4 + 3) (words ++ rest) 0 = nth (4 * pc + 3) rest 0.
  Proof.
    intros words rest pc Hlen.
    replace (4 * pc + 4 + 3) with (length words + (4 * pc + 3)) by (rewrite Hlen; lia).
    apply app_nth2_plus.
  Qed.

  Lemma decode_instr_flat_map_index : forall instrs pc,
    pc < length instrs ->
    decode_instr_from_mem (flat_map encode_instr_words instrs) (4 * pc) =
      nth pc instrs Halt.
  Proof.
    induction instrs as [|instr instrs IH]; intros pc Hpc; simpl in *.
    { lia. }
    destruct pc as [|pc].
      - unfold decode_instr_from_mem.
        set (words := encode_instr_words instr).
        set (rest := flat_map encode_instr_words instrs).
        assert (Hlen : length words = 4) by (subst words; apply encode_instr_words_length).
        simpl.
        repeat (rewrite app_nth1 by (rewrite Hlen; lia)).
        subst words; destruct instr; reflexivity.
    - assert (Hpc_tail : pc < length instrs) by lia.
      specialize (IH pc Hpc_tail).
      set (words := encode_instr_words instr).
      set (rest := flat_map encode_instr_words instrs).
      assert (Hlen : length words = 4) by (subst words; apply encode_instr_words_length).
      assert (Hshift : decode_instr_from_mem (words ++ rest) (4 * S pc) =
                       decode_instr_from_mem rest (4 * pc)).
      { unfold decode_instr_from_mem.
        rewrite Nat.mul_succ_r.
        rewrite (nth_after_prefix0 words rest pc Hlen).
        rewrite (nth_after_prefix1 words rest pc Hlen).
        rewrite (nth_after_prefix2 words rest pc Hlen).
        rewrite (nth_after_prefix3 words rest pc Hlen).
        reflexivity. }
      change (decode_instr_from_mem (words ++ rest) (S pc + (S pc + (S pc + (S pc + 0)))))
        with (decode_instr_from_mem (words ++ rest) (4 * S pc)).
      apply eq_trans with (y := decode_instr_from_mem rest (4 * pc)).
      + exact Hshift.
      + cbn [nth].
        change (decode_instr_from_mem rest (4 * pc)) with
          (decode_instr_from_mem (flat_map encode_instr_words instrs) (4 * pc)).
        change (decode_instr_from_mem (flat_map encode_instr_words instrs) (4 * pc)) with
          (decode_instr_from_mem (flat_map encode_instr_words instrs)
                                 (pc + (pc + (pc + (pc + 0))))).
        rewrite IH.
        reflexivity.
  Qed.

  Lemma nth_firstn_lt : forall (A : Type) n m (l : list A) d,
    n < m -> nth n (firstn m l) d = nth n l d.
  Proof.
    intros A n m l d Hlt.
    revert n l Hlt.
    induction m as [|m IH]; intros [|n] l Hlt; simpl in *; try lia.
    - destruct l; reflexivity.
    - destruct l as [|x xs]; simpl; [reflexivity|].
      apply IH. lia.
  Qed.

  Lemma decode_instr_program_at_pc : forall pc,
    pc < length program_instrs ->
    decode_instr_from_mem program (4 * pc) = nth pc program_instrs Halt.
  Proof.
    intros pc Hpc.
    unfold program.
    apply decode_instr_flat_map_index.
    exact Hpc.
  Qed.

  Lemma program_instrs_length_gt_29 : 29 < length program_instrs.
  Proof. cbn; lia. Qed.

  Lemma length_program : length program = 4 * length program_instrs.
  Proof.
    unfold program.
    induction program_instrs as [|instr instrs IH]; simpl; [reflexivity|].
    rewrite app_length, encode_instr_words_length, IH.
    lia.
  Qed.

  Lemma decode_instr_program_state : forall st,
    read_reg REG_PC st < length program_instrs ->
    firstn (length program) (mem st) = program ->
    decode_instr st = decode_instr_from_mem program (4 * read_reg REG_PC st).
  Proof.
    intros st Hpc_len Hmem.
    remember (read_reg REG_PC st) as pc eqn:Hpc.
    assert (Hpc_len_pc : pc < length program_instrs).
    { subst pc. exact Hpc_len. }
    unfold decode_instr.
    rewrite Hpc.
    assert (Haddr_bound : forall offset, offset < 4 -> 4 * pc + offset < length program).
    { intros offset Hoff.
      rewrite length_program.
      lia.
    }
    apply decode_instr_from_mem_ext_scaled.
    intros offset Hoff.
    specialize (Haddr_bound offset Hoff).
    rewrite <- Hmem.
    rewrite Hpc in Haddr_bound.
    symmetry. apply nth_firstn_lt. exact Haddr_bound.
  Qed.

  Lemma decode_instr_before_apply_not_store : forall st,
    read_reg REG_PC st < 29 ->
    firstn (length program) (mem st) = program ->
    match decode_instr st with
    | StoreIndirect _ _ => False
    | _ => True
    end.
  Proof.
    intros st Hpc Hmem.
    assert (Hpc_len : read_reg REG_PC st < length program_instrs) by (pose proof program_instrs_length_gt_29; lia).
    pose proof (decode_instr_program_state st Hpc_len Hmem) as Hdecode.
    rewrite Hdecode.
    rewrite decode_instr_program_at_pc by exact Hpc_len.
    apply program_instrs_before_apply_not_store.
    exact Hpc.
  Qed.

  Lemma decode_instr_before_apply_jump_target_lt : forall st,
    read_reg REG_PC st < 29 ->
    firstn (length program) (mem st) = program ->
    match decode_instr st with
    | Jz _ target => target < 29
    | Jnz _ target => target < 29
    | _ => True
    end.
  Proof.
    intros st Hpc Hmem.
    assert (Hpc_len : read_reg REG_PC st < length program_instrs) by (pose proof program_instrs_length_gt_29; lia).
    pose proof (decode_instr_program_state st Hpc_len Hmem) as Hdecode.
    rewrite Hdecode.
    rewrite decode_instr_program_at_pc by exact Hpc_len.
    apply program_instrs_before_apply_jump_target_lt.
    exact Hpc.
  Qed.

  Lemma decode_instr_before_apply_pc_unchanged : forall st,
    read_reg REG_PC st < 29 ->
    firstn (length program) (mem st) = program ->
    match decode_instr st with
    | Jz _ _ => True
    | Jnz _ _ => True
    | instr => CPU.pc_unchanged instr
    end.
  Proof.
    intros st Hpc Hmem.
    assert (Hpc_len : read_reg REG_PC st < length program_instrs) by (pose proof program_instrs_length_gt_29; lia).
    pose proof (decode_instr_program_state st Hpc_len Hmem) as Hdecode.
    rewrite Hdecode.
    rewrite decode_instr_program_at_pc by exact Hpc_len.
    apply program_instrs_before_apply_pc_unchanged.
    exact Hpc.
  Qed.

  Lemma decode_instr_apply_start : forall st,
    read_reg REG_PC st = 29 ->
    firstn (length program) (mem st) = program ->
    decode_instr st = CopyReg REG_TEMP1 REG_HEAD.
  Proof.
    intros st Hpc Hmem.
    pose proof program_instrs_length_gt_29 as Hlen.
    assert (Hpc_len : read_reg REG_PC st < length program_instrs) by (rewrite Hpc; lia).
    pose proof (decode_instr_program_state st Hpc_len Hmem) as Hdecode.
    rewrite Hdecode.
    rewrite Hpc.
    rewrite Hpc in Hpc_len.
    rewrite decode_instr_program_at_pc with (pc := 29) by exact Hpc_len.
    rewrite program_instrs_pc29.
    reflexivity.
  Qed.

  (* Execute one decoded instruction. *)
  Definition run1 (s : CPU.State) : CPU.State :=
    CPU.step (decode_instr s) s.

  Lemma step_mem_preserved_if_no_store : forall i s,
    (match i with StoreIndirect _ _ => False | _ => True end) ->
    (CPU.step i s).(mem) = s.(mem).
  Proof.
    intros i s H.
    destruct i; simpl in H; simpl.
    - reflexivity.
    - reflexivity.
    - contradiction.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - destruct (Nat.eqb (read_reg rc s) 0); simpl; reflexivity.
    - destruct (Nat.eqb (read_reg rc s) 0); simpl; reflexivity.
    - reflexivity.
  Qed.

  Lemma run1_mem_preserved_if_no_store : forall s,
    (match decode_instr s with StoreIndirect _ _ => False | _ => True end) ->
    (run1 s).(mem) = s.(mem).
    Proof.
      intros s H.
      unfold run1.
      apply step_mem_preserved_if_no_store.
      exact H.
    Qed.

  Lemma read_mem_mem_eq : forall st1 st2 addr,
    mem st1 = mem st2 ->
    read_mem addr st1 = read_mem addr st2.
  Proof.
    intros st1 st2 addr Hmem.
    unfold read_mem.
    rewrite Hmem.
    reflexivity.
  Qed.

Lemma run1_preserves_reg_copyreg : forall st dst src r,
  decode_instr st = CopyReg dst src ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  r < length (regs st) ->
  r <> dst ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st dst src r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
  assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
  assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
  { unfold st_pc.
    apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
    exact Hneq_pc_sym. }
  rewrite <- Hr_pc_eq.
  fold (read_reg r st_pc).
  apply (read_reg_write_reg_other st_pc dst r (read_reg src st) Hdst_pc_bound Hr_pc_bound).
  intros Hcontra. apply Hneq_dst. symmetry. exact Hcontra.
Qed.

Lemma run1_preserves_reg_subreg : forall st dst src1 src2 r,
  decode_instr st = SubReg dst src1 src2 ->
  REG_PC < length (regs st) ->
  dst < length (regs st) ->
  r < length (regs st) ->
  r <> dst ->
  r <> REG_PC ->
  read_reg r (run1 st) = read_reg r st.
Proof.
  intros st dst src1 src2 r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
  unfold run1.
  rewrite Hdecode.
  unfold step; cbn.
  set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
  assert (Hlen_pc : length (regs st_pc) = length (regs st)).
  { unfold st_pc.
    apply length_regs_write_reg.
    exact Hpc_bound. }
  assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
  assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
  assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
  assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
  { unfold st_pc.
    apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
    exact Hneq_pc_sym. }
  rewrite <- Hr_pc_eq.
  fold (read_reg r st_pc).
  apply (read_reg_write_reg_other st_pc dst r (read_reg src1 st - read_reg src2 st) Hdst_pc_bound Hr_pc_bound).
  intros Hcontra. apply Hneq_dst. symmetry. exact Hcontra.
Qed.

    Lemma run1_subreg_result : forall st dst src1 src2,
      decode_instr st = SubReg dst src1 src2 ->
      REG_PC < length (regs st) ->
      dst < length (regs st) ->
      read_reg dst (run1 st) = read_reg src1 st - read_reg src2 st.
    Proof.
      intros st dst src1 src2 Hdecode Hpc_bound Hdst_bound.
      unfold run1.
      rewrite Hdecode.
      unfold step; cbn.
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { unfold st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound. }
      assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
      apply (read_reg_write_reg_same st_pc dst (read_reg src1 st - read_reg src2 st) Hdst_pc_bound).
    Qed.

    Lemma run1_copyreg_result : forall st dst src,
      decode_instr st = CopyReg dst src ->
      REG_PC < length (regs st) ->
      dst < length (regs st) ->
      read_reg dst (run1 st) = read_reg src st.
    Proof.
      intros st dst src Hdecode Hpc_bound Hdst_bound.
      unfold run1.
      rewrite Hdecode.
      unfold step; cbn.
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { unfold st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound. }
      assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
      apply (read_reg_write_reg_same st_pc dst (read_reg src st) Hdst_pc_bound).
    Qed.

    Lemma run1_preserves_reg_addconst : forall st dst n r,
      decode_instr st = AddConst dst n ->
      REG_PC < length (regs st) ->
      dst < length (regs st) ->
      r < length (regs st) ->
      r <> dst ->
      r <> REG_PC ->
      read_reg r (run1 st) = read_reg r st.
    Proof.
      intros st dst n r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
      unfold run1.
      rewrite Hdecode.
      unfold step; cbn.
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { unfold st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound. }
      assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
      assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
      assert (Hneq_dst_sym : dst <> r) by (intro Heq; apply Hneq_dst; symmetry; exact Heq).
      assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
      assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
      { unfold st_pc.
        apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
        exact Hneq_pc_sym. }
      rewrite <- Hr_pc_eq.
      fold (read_reg r st_pc).
      apply (read_reg_write_reg_other st_pc dst r (read_reg dst st + n) Hdst_pc_bound Hr_pc_bound).
      exact Hneq_dst_sym.
    Qed.

    Lemma run1_addconst_result : forall st dst n,
      decode_instr st = AddConst dst n ->
      REG_PC < length (regs st) ->
      dst < length (regs st) ->
      read_reg dst (run1 st) = read_reg dst st + n.
    Proof.
      intros st dst n Hdecode Hpc_bound Hdst_bound.
      unfold run1.
      rewrite Hdecode.
      unfold step; cbn.
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { unfold st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound. }
      assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
      apply (read_reg_write_reg_same st_pc dst (read_reg dst st + n) Hdst_pc_bound).
    Qed.

    Lemma run1_addreg_result : forall st dst src1 src2,
      decode_instr st = AddReg dst src1 src2 ->
      REG_PC < length (regs st) ->
      dst < length (regs st) ->
      read_reg dst (run1 st) = read_reg src1 st + read_reg src2 st.
    Proof.
      intros st dst src1 src2 Hdecode Hpc_bound Hdst_bound.
      unfold run1.
      rewrite Hdecode.
      unfold step; cbn.
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { unfold st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound. }
      assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
      apply (read_reg_write_reg_same st_pc dst (read_reg src1 st + read_reg src2 st) Hdst_pc_bound).
    Qed.

    Lemma run1_preserves_reg_addreg : forall st dst src1 src2 r,
      decode_instr st = AddReg dst src1 src2 ->
      REG_PC < length (regs st) ->
      dst < length (regs st) ->
      r < length (regs st) ->
      r <> dst ->
      r <> REG_PC ->
      read_reg r (run1 st) = read_reg r st.
    Proof.
      intros st dst src1 src2 r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
      unfold run1.
      rewrite Hdecode.
      unfold step; cbn.
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { unfold st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound. }
      assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
      assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
      assert (Hneq_dst_sym : dst <> r) by (intro Heq; apply Hneq_dst; symmetry; exact Heq).
      assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
      assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
      { unfold st_pc.
        apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
        exact Hneq_pc_sym. }
      rewrite <- Hr_pc_eq.
      fold (read_reg r st_pc).
      apply (read_reg_write_reg_other
               st_pc dst r (read_reg src1 st + read_reg src2 st)
               Hdst_pc_bound Hr_pc_bound).
      exact Hneq_dst_sym.
    Qed.

    Lemma run1_preserves_reg_loadindirect : forall st dst src r,
      decode_instr st = LoadIndirect dst src ->
      REG_PC < length (regs st) ->
      dst < length (regs st) ->
      r < length (regs st) ->
      r <> dst ->
      r <> REG_PC ->
      read_reg r (run1 st) = read_reg r st.
    Proof.
      intros st dst src r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
      unfold run1.
      rewrite Hdecode.
      unfold step; cbn.
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { unfold st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound. }
      assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
      assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
      assert (Hneq_dst_sym : dst <> r) by (intro Heq; apply Hneq_dst; symmetry; exact Heq).
      assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
      assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
      { unfold st_pc.
        apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
        exact Hneq_pc_sym. }
      rewrite <- Hr_pc_eq.
      fold (read_reg r st_pc).
      apply (read_reg_write_reg_other st_pc dst r (read_mem (read_reg src st) st) Hdst_pc_bound Hr_pc_bound).
      exact Hneq_dst_sym.
    Qed.

    Lemma run1_loadindirect_result : forall st dst src,
      decode_instr st = LoadIndirect dst src ->
      REG_PC < length (regs st) ->
      dst < length (regs st) ->
      read_reg dst (run1 st) = read_mem (read_reg src st) st.
    Proof.
      intros st dst src Hdecode Hpc_bound Hdst_bound.
      unfold run1.
      rewrite Hdecode.
      unfold step; cbn.
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { unfold st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound. }
      assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
      apply (read_reg_write_reg_same st_pc dst (read_mem (read_reg src st) st) Hdst_pc_bound).
    Qed.

    Lemma run1_preserves_reg_loadconst : forall st dst val r,
      decode_instr st = LoadConst dst val ->
      REG_PC < length (regs st) ->
      dst < length (regs st) ->
      r < length (regs st) ->
      r <> dst ->
      r <> REG_PC ->
      read_reg r (run1 st) = read_reg r st.
    Proof.
      intros st dst val r Hdecode Hpc_bound Hdst_bound Hr_bound Hneq_dst Hneq_pc.
      unfold run1.
      rewrite Hdecode.
      unfold step; cbn.
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { unfold st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound. }
      assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
      assert (Hr_pc_bound : r < length (regs st_pc)) by (rewrite Hlen_pc; exact Hr_bound).
        assert (Hneq_dst_sym : dst <> r) by (intro Heq; apply Hneq_dst; symmetry; exact Heq).
        assert (Hneq_pc_sym : REG_PC <> r) by (intro Heq; apply Hneq_pc; symmetry; exact Heq).
      assert (Hr_pc_eq : read_reg r st_pc = read_reg r st).
      { unfold st_pc.
        apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
        exact Hneq_pc_sym. }
      rewrite <- Hr_pc_eq.
      fold (read_reg r st_pc).
      apply (read_reg_write_reg_other st_pc dst r val Hdst_pc_bound Hr_pc_bound).
      exact Hneq_dst_sym.
    Qed.

    Lemma run1_loadconst_result : forall st dst val,
      decode_instr st = LoadConst dst val ->
      REG_PC < length (regs st) ->
      dst < length (regs st) ->
      read_reg dst (run1 st) = val.
    Proof.
      intros st dst val Hdecode Hpc_bound Hdst_bound.
      unfold run1.
      rewrite Hdecode.
      unfold step; cbn.
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { unfold st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound. }
      assert (Hdst_pc_bound : dst < length (regs st_pc)) by (rewrite Hlen_pc; exact Hdst_bound).
      apply (read_reg_write_reg_same st_pc dst val Hdst_pc_bound).
    Qed.

    Lemma read_reg_step_jz_true : forall st rc target r,
      Nat.eqb (read_reg rc st) 0 = true ->
      read_reg r (CPU.step (Jz rc target) st) = read_reg r (write_reg REG_PC target st).
    Proof.
      intros st rc target r Hguard.
      unfold CPU.step.
      rewrite Hguard.
      reflexivity.
    Qed.

    Lemma read_reg_step_jz_false : forall st rc target r,
      Nat.eqb (read_reg rc st) 0 = false ->
      read_reg r (CPU.step (Jz rc target) st) = read_reg r (write_reg REG_PC (S (read_reg REG_PC st)) st).
    Proof.
      intros st rc target r Hguard.
      unfold CPU.step.
      rewrite Hguard.
      reflexivity.
    Qed.

    Lemma read_reg_step_jnz_true : forall st rc target r,
      Nat.eqb (read_reg rc st) 0 = true ->
      read_reg r (CPU.step (Jnz rc target) st) = read_reg r (write_reg REG_PC (S (read_reg REG_PC st)) st).
    Proof.
      intros st rc target r Hguard.
      unfold CPU.step.
      rewrite Hguard.
      reflexivity.
    Qed.

    Lemma read_reg_step_jnz_false : forall st rc target r,
      Nat.eqb (read_reg rc st) 0 = false ->
      read_reg r (CPU.step (Jnz rc target) st) = read_reg r (write_reg REG_PC target st).
    Proof.
      intros st rc target r Hguard.
      unfold CPU.step.
      rewrite Hguard.
      reflexivity.
    Qed.

    Lemma run1_jz_true_read : forall st rc target r,
      decode_instr st = Jz rc target ->
      Nat.eqb (read_reg rc st) 0 = true ->
      read_reg r (run1 st) = read_reg r (write_reg REG_PC target st).
    Proof.
      intros st rc target r Hdecode Heqb.
      unfold run1.
      rewrite Hdecode.
      apply read_reg_step_jz_true.
      exact Heqb.
    Qed.

    Lemma run1_jz_false_read : forall st rc target r,
      decode_instr st = Jz rc target ->
      Nat.eqb (read_reg rc st) 0 = false ->
      read_reg r (run1 st) = read_reg r (write_reg REG_PC (S (read_reg REG_PC st)) st).
    Proof.
      intros st rc target r Hdecode Heqb.
      unfold run1.
      rewrite Hdecode.
      apply read_reg_step_jz_false.
      exact Heqb.
    Qed.

    Lemma run1_jnz_true_read : forall st rc target r,
      decode_instr st = Jnz rc target ->
      Nat.eqb (read_reg rc st) 0 = true ->
      read_reg r (run1 st) = read_reg r (write_reg REG_PC (S (read_reg REG_PC st)) st).
    Proof.
      intros st rc target r Hdecode Heqb.
      unfold run1.
      rewrite Hdecode.
      apply read_reg_step_jnz_true.
      exact Heqb.
    Qed.

    Lemma run1_jnz_false_read : forall st rc target r,
      decode_instr st = Jnz rc target ->
      Nat.eqb (read_reg rc st) 0 = false ->
      read_reg r (run1 st) = read_reg r (write_reg REG_PC target st).
    Proof.
      intros st rc target r Hdecode Heqb.
      unfold run1.
      rewrite Hdecode.
      apply read_reg_step_jnz_false.
      exact Heqb.
    Qed.

    Lemma run1_preserves_reg_jz_true : forall st rc target r,
      decode_instr st = Jz rc target ->
      Nat.eqb (read_reg rc st) 0 = true ->
      REG_PC < length (regs st) ->
      r < length (regs st) ->
      r <> REG_PC ->
      read_reg r (run1 st) = read_reg r st.
    Proof.
      intros st rc target r Hdecode Heqb Hpc_bound Hr_bound Hr_neq.
      pose proof (run1_jz_true_read st rc target r Hdecode Heqb) as Hstep.
      rewrite Hstep.
      apply (read_reg_write_reg_other st REG_PC r target Hpc_bound Hr_bound).
      intro Heq. apply Hr_neq. symmetry. exact Heq.
    Qed.

    Lemma run1_preserves_reg_jz_false : forall st rc target r,
      decode_instr st = Jz rc target ->
      Nat.eqb (read_reg rc st) 0 = false ->
      REG_PC < length (regs st) ->
      r < length (regs st) ->
      r <> REG_PC ->
      read_reg r (run1 st) = read_reg r st.
    Proof.
      intros st rc target r Hdecode Heqb_false Hpc_bound Hr_bound Hr_neq.
      pose proof (run1_jz_false_read st rc target r Hdecode Heqb_false) as Hstep.
      rewrite Hstep.
      apply (read_reg_write_reg_other st REG_PC r (S (read_reg REG_PC st)) Hpc_bound Hr_bound).
      intro Heq. apply Hr_neq. symmetry. exact Heq.
    Qed.

    Lemma run1_preserves_reg_jnz_false : forall st rc target r,
      decode_instr st = Jnz rc target ->
      Nat.eqb (read_reg rc st) 0 = false ->
      REG_PC < length (regs st) ->
      r < length (regs st) ->
      r <> REG_PC ->
      read_reg r (run1 st) = read_reg r st.
    Proof.
      intros st rc target r Hdecode Heqb_false Hpc_bound Hr_bound Hr_neq.
      pose proof (run1_jnz_false_read st rc target r Hdecode Heqb_false) as Hstep.
      rewrite Hstep.
      apply (read_reg_write_reg_other st REG_PC r target Hpc_bound Hr_bound).
      intro Heq. apply Hr_neq. symmetry. exact Heq.
    Qed.

    (* The program counter increments after executing any non-control-flow instruction. *)
    Lemma run1_pc_succ : forall s,
      CPU.pc_unchanged (decode_instr s) ->
      read_reg REG_PC (run1 s) = S (read_reg REG_PC s).
  Proof.
    intros s Hdec. unfold run1.
    apply CPU.step_pc_succ. exact Hdec.
  Qed.

  Lemma run1_pc_succ_instr : forall s instr,
    decode_instr s = instr ->
    CPU.pc_unchanged instr ->
    read_reg REG_PC (run1 s) = S (read_reg REG_PC s).
  Proof.
    intros s instr Hdecode Hunchanged.
    subst instr.
    apply run1_pc_succ. exact Hunchanged.
  Qed.

  Lemma run1_pc_after_apply : forall st,
    read_reg REG_PC st = 29 ->
    firstn (length program) (mem st) = program ->
    read_reg REG_PC (run1 st) = 30.
  Proof.
    intros st Hpc Hmem.
    pose proof (decode_instr_apply_start st Hpc Hmem) as Hdecode.
    assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_HEAD)).
    { unfold CPU.pc_unchanged. simpl. discriminate. }
    pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
    rewrite Hpc in Hsucc.
    exact Hsucc.
  Qed.

  Lemma run1_pc_monotonic_after_apply : forall st,
    29 <= read_reg REG_PC st < 48 ->
    firstn (length program) (mem st) = program ->
    29 <= read_reg REG_PC (run1 st).
  Proof.
    intros st Hpc_range Hmem.
    destruct Hpc_range as [Hpc_min Hpc_max].
    pose proof program_instrs_length_gt_48 as Hlen_gt.
    assert (Hpc_bound : read_reg REG_PC st < length program_instrs) by lia.
    pose proof (decode_instr_program_state st Hpc_bound Hmem) as Hdecode.
    pose proof (program_instrs_monotonic_after_apply (read_reg REG_PC st)
                   (conj Hpc_min Hpc_max)) as Hmono.
    pose proof (decode_instr_program_at_pc (read_reg REG_PC st) Hpc_bound) as Hinstr_eq.
    rewrite Hinstr_eq in Hdecode.
    destruct (nth (read_reg REG_PC st) program_instrs Halt) as
      [rd val | rd ra | ra rv | rd rs | rd val | rd r1 r2 | rd r1 r2 | rc target | rc target | ] eqn:Hinstr;
      simpl in Hmono.
    - (* LoadConst *)
      pose proof (run1_pc_succ_instr st (LoadConst rd val) Hdecode) as Hsucc.
      apply Hsucc in Hmono.
      rewrite Hmono. lia.
    - (* LoadIndirect *)
      pose proof (run1_pc_succ_instr st (LoadIndirect rd ra) Hdecode) as Hsucc.
      apply Hsucc in Hmono.
      rewrite Hmono. lia.
    - (* StoreIndirect *)
      pose proof (run1_pc_succ_instr st (StoreIndirect ra rv) Hdecode) as Hsucc.
      assert (Htrue : True) by exact I.
      apply Hsucc in Htrue.
      rewrite Htrue. lia.
    - (* CopyReg *)
      pose proof (run1_pc_succ_instr st (CopyReg rd rs) Hdecode) as Hsucc.
      apply Hsucc in Hmono.
      rewrite Hmono. lia.
    - (* AddConst *)
      pose proof (run1_pc_succ_instr st (AddConst rd val) Hdecode) as Hsucc.
      apply Hsucc in Hmono.
      rewrite Hmono. lia.
    - (* AddReg *)
      pose proof (run1_pc_succ_instr st (AddReg rd r1 r2) Hdecode) as Hsucc.
      apply Hsucc in Hmono.
      rewrite Hmono. lia.
    - (* SubReg *)
      pose proof (run1_pc_succ_instr st (SubReg rd r1 r2) Hdecode) as Hsucc.
      apply Hsucc in Hmono.
      rewrite Hmono. lia.
    - (* Jz case *)
      destruct (Nat.eqb (read_reg rc st) 0) eqn:Heq.
      + pose proof (CPU.step_jz_true rc target st Heq) as Hpc.
        unfold run1. rewrite Hdecode. rewrite Hpc. exact Hmono.
      + pose proof (CPU.step_jz_false rc target st Heq) as Hpc.
        unfold run1. rewrite Hdecode. rewrite Hpc. lia.
    - (* Jnz case *)
      destruct (Nat.eqb (read_reg rc st) 0) eqn:Heq.
      + pose proof (CPU.step_jnz_true rc target st Heq) as Hpc.
        unfold run1. rewrite Hdecode. rewrite Hpc. lia.
      + pose proof (CPU.step_jnz_false rc target st Heq) as Hpc.
        unfold run1. rewrite Hdecode. rewrite Hpc. exact Hmono.
    - (* Halt *)
      unfold run1. rewrite (eq_trans Hdecode (eq_sym Hinstr)). simpl. lia.
  Qed.

  (* Run the program for n steps. *)
  Fixpoint run_n (s : CPU.State) (n : nat) : CPU.State :=
    match n with
    | 0 => s
    | S k => run_n (run1 s) k
    end.

  (* Unfolding lemma for [run_n]. *)
  Lemma run_n_succ : forall s n, run_n s (S n) = run_n (run1 s) n.
  Proof. reflexivity. Qed.

  Lemma run1_run_n : forall a s,
    run_n (run1 s) a = run1 (run_n s a).
  Proof.
    induction a as [|a IH]; intros s; simpl.
    - reflexivity.
    - rewrite IH. reflexivity.
  Qed.

  (* Composition property for [run_n]: executing [a] then [b] steps is the
     same as executing [a + b] steps. This is useful to split and rejoin
     the interpreter execution into phases. *)
  Lemma run_n_add : forall s a b,
    run_n s (a + b) = run_n (run_n s a) b.
  Proof.
    intros s a b.
    revert s a.
    induction b as [|b IH]; intros s a; simpl.
    - rewrite Nat.add_0_r. reflexivity.
    - rewrite Nat.add_succ_r. simpl.
      specialize (IH (run1 s) a).
      rewrite IH.
      rewrite run1_run_n.
      reflexivity.
  Qed.

  (* Helper tactic: normalize nested [run1]/[run_n] expressions into a
     canonical shape. This centralizes the small rewriting steps that
     commonly cause fragile proof scripts when witnesses are constructed
     by hand. Use [normalize_run_n] before attempting [rewrite] across
     equivalences involving [run_n] and [run1]. *)
  Ltac normalize_run_n :=
    repeat (match goal with
    | |- context[run_n ?s (S ?n)] => rewrite (run_n_succ s n)
    | |- context[run_n (run1 ?s) ?n] => rewrite (run1_run_n n s)
    | |- context[run_n ?s (?a + ?b)] => rewrite (run_n_add s a b)
    | H: context[run_n ?s (S ?n)] |- _ => rewrite (run_n_succ s n) in H
    | H: context[run_n (run1 ?s) ?n] |- _ => rewrite (run1_run_n n s) in H
    | H: context[run_n ?s (?a + ?b)] |- _ => rewrite (run_n_add s a b) in H
    end).

  Lemma run1_pc_before_apply_le : forall st,
    read_reg REG_PC st < 29 ->
    firstn (length program) (mem st) = program ->
    read_reg REG_PC (run1 st) <= 29.
  Proof.
    intros st Hpc Hmem.
    pose proof (decode_instr_before_apply_not_store st Hpc Hmem) as Hnotstore.
    pose proof (decode_instr_before_apply_jump_target_lt st Hpc Hmem) as Htarget.
    pose proof (decode_instr_before_apply_pc_unchanged st Hpc Hmem) as Hunchanged.
    destruct (decode_instr st) as [rd val | rd ra | ra rv | rd rs | rd val | rd r1 r2 | rd r1 r2 | rc target | rc target | ] eqn:Hinstr.
    - simpl in Hunchanged.
      pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
      rewrite Hpc_succ.
      lia.
    - simpl in Hunchanged.
      pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
      rewrite Hpc_succ.
      lia.
    - now inversion Hnotstore.
    - simpl in Hunchanged.
      pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
      rewrite Hpc_succ.
      lia.
    - simpl in Hunchanged.
      pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
      rewrite Hpc_succ.
      lia.
    - simpl in Hunchanged.
      pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
      rewrite Hpc_succ.
      lia.
    - simpl in Hunchanged.
      pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hpc_succ.
      rewrite Hpc_succ.
      lia.
    - simpl in Htarget.
      destruct (Nat.eqb (read_reg rc st) 0) eqn:Hcond; simpl in Htarget.
      + pose proof (run1_jz_true_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
        rewrite Hpc_run.
        rewrite read_pc_write_pc.
        apply Nat.lt_le_incl; exact Htarget.
      + pose proof (run1_jz_false_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
        rewrite Hpc_run.
        rewrite read_pc_write_pc.
        lia.
    - simpl in Htarget.
      destruct (Nat.eqb (read_reg rc st) 0) eqn:Hcond; simpl in Htarget.
      + pose proof (run1_jnz_true_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
        rewrite Hpc_run.
        rewrite read_pc_write_pc.
        lia.
      + pose proof (run1_jnz_false_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
        rewrite Hpc_run.
        rewrite read_pc_write_pc.
        apply Nat.lt_le_incl; exact Htarget.
    - unfold run1; rewrite Hinstr; simpl.
      apply Nat.lt_le_incl; exact Hpc.
  Qed.

  Lemma run1_pc_before_apply_hits_29 : forall st,
    read_reg REG_PC st < 29 ->
    firstn (length program) (mem st) = program ->
    read_reg REG_PC (run1 st) = 29 ->
    read_reg REG_PC st = 28.
  Proof.
    intros st Hpc Hmem Hfinal.
    pose proof (decode_instr_before_apply_not_store st Hpc Hmem) as Hnotstore.
    pose proof (decode_instr_before_apply_jump_target_lt st Hpc Hmem) as Htarget.
    pose proof (decode_instr_before_apply_pc_unchanged st Hpc Hmem) as Hunchanged.
    destruct (decode_instr st) as [rd val | rd ra | ra rv | rd rs | rd val | rd r1 r2
                                 | rd r1 r2 | rc target | rc target | ] eqn:Hinstr;
      simpl in Hunchanged; try (simpl in Htarget);
      try now inversion Hnotstore;
      try (unfold run1 in Hfinal; rewrite Hinstr in Hfinal; simpl in Hfinal; lia).
    - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
      rewrite Hsucc in Hfinal.
      lia.
    - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
      rewrite Hsucc in Hfinal.
      lia.
    - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
      rewrite Hsucc in Hfinal.
      lia.
    - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
      rewrite Hsucc in Hfinal.
      lia.
    - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
      rewrite Hsucc in Hfinal.
      lia.
    - pose proof (run1_pc_succ_instr st _ Hinstr Hunchanged) as Hsucc.
      rewrite Hsucc in Hfinal.
      lia.
    - simpl in Htarget.
      destruct (Nat.eqb (read_reg rc st) 0) eqn:Hcond.
      + pose proof (run1_jz_true_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
        rewrite Hpc_run in Hfinal.
        rewrite read_pc_write_pc in Hfinal.
        lia.
      + pose proof (run1_jz_false_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
        rewrite Hpc_run in Hfinal.
        rewrite read_pc_write_pc in Hfinal.
        lia.
    - simpl in Htarget.
      destruct (Nat.eqb (read_reg rc st) 0) eqn:Hcond.
      + pose proof (run1_jnz_true_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
        rewrite Hpc_run in Hfinal.
        rewrite read_pc_write_pc in Hfinal.
        lia.
      + pose proof (run1_jnz_false_read st rc target REG_PC Hinstr Hcond) as Hpc_run.
        rewrite Hpc_run in Hfinal.
        rewrite read_pc_write_pc in Hfinal.
        lia.
  Qed.

    Lemma length_regs_write_reg_10 : forall st reg val,
      length (regs st) = 10 ->
      reg < length (regs st) ->
      length (regs (write_reg reg val st)) = 10.
    Proof.
      intros st reg val Hlen Hlt.
      pose proof (length_regs_write_reg st reg val Hlt) as Hlen'.
      rewrite Hlen in Hlen'.
      exact Hlen'.
    Qed.

    Lemma length_regs_step_jz_10 : forall st rc target,
      length (regs st) = 10 ->
      length (regs (CPU.step (Jz rc target) st)) = 10.
    Proof.
      intros st rc target Hlen.
      unfold CPU.step.
      destruct (Nat.eqb (read_reg rc st) 0) eqn:Hcond.
      - set (st_pc := write_reg REG_PC target st).
        change (length (regs st_pc) = 10).
        subst st_pc.
        apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia].
      - set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
        change (length (regs st_pc) = 10).
        subst st_pc.
        apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia].
    Qed.

    Lemma length_regs_step_jnz_10 : forall st rc target,
      length (regs st) = 10 ->
      length (regs (CPU.step (Jnz rc target) st)) = 10.
    Proof.
      intros st rc target Hlen.
      unfold CPU.step.
      destruct (Nat.eqb (read_reg rc st) 0) eqn:Hcond.
      - set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
        change (length (regs st_pc) = 10).
        subst st_pc.
        apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia].
      - set (st_pc := write_reg REG_PC target st).
        change (length (regs st_pc) = 10).
        subst st_pc.
        apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia].
    Qed.

    Lemma decode_instr_before_apply_reg_bound : forall st,
      read_reg REG_PC st < 29 ->
      firstn (length program) (mem st) = program ->
      match decode_instr st with
    | LoadConst rd _
    | LoadIndirect rd _
    | CopyReg rd _
    | AddConst rd _
    | AddReg rd _ _
    | SubReg rd _ _ => rd < 10
    | Jz rc _
    | Jnz rc _ => rc < 10
    | _ => True
    end.
  Proof.
    intros st Hpc Hmem.
    assert (Hpc_len : read_reg REG_PC st < length program_instrs)
      by (pose proof program_instrs_length_gt_29; lia).
    pose proof (decode_instr_program_state st Hpc_len Hmem) as Hdecode.
    rewrite Hdecode.
    rewrite decode_instr_program_at_pc by exact Hpc_len.
    apply program_instrs_before_apply_reg_bound.
    exact Hpc.
  Qed.

  Lemma run1_regs_length_before_apply : forall st,
    read_reg REG_PC st < 29 ->
    firstn (length program) (mem st) = program ->
    length (regs st) = 10 ->
    length (regs (run1 st)) = 10.
  Proof.
    intros st Hpc_lt Hprog Hlen.
    remember (decode_instr st) as instr eqn:Heqinstr.
    pose proof (decode_instr_before_apply_reg_bound st Hpc_lt Hprog) as Hbound.
    rewrite <- Heqinstr in Hbound.
    destruct instr as [rd const | rd ra | ra rv | rd rs | rd addc | rd r1 r2 | rd r1 r2 | rc target | rc target |];
      try (pose proof (decode_instr_before_apply_not_store st Hpc_lt Hprog) as Hnostore';
           rewrite <- Heqinstr in Hnostore'; inversion Hnostore').
    - simpl in Hbound.
      unfold run1.
      rewrite <- Heqinstr.
      cbn [run1 CPU.step].
      assert (Hlen_pc : length (regs (write_reg REG_PC (S (read_reg REG_PC st)) st)) = 10).
      { apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]. }
      apply length_regs_write_reg_10; [exact Hlen_pc|].
      rewrite Hlen_pc.
      exact Hbound.
    - simpl in Hbound.
      unfold run1.
      rewrite <- Heqinstr.
      cbn [run1 CPU.step].
      assert (Hlen_pc : length (regs (write_reg REG_PC (S (read_reg REG_PC st)) st)) = 10).
      { apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]. }
      apply length_regs_write_reg_10; [exact Hlen_pc|].
      rewrite Hlen_pc.
      exact Hbound.
    - simpl in Hbound.
      unfold run1.
      rewrite <- Heqinstr.
      cbn [run1 CPU.step].
        assert (Hlen_pc : length (regs (write_reg REG_PC (S (read_reg REG_PC st)) st)) = 10).
        { apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]. }
        apply length_regs_write_reg_10; [exact Hlen_pc|].
        rewrite Hlen_pc.
        exact Hbound.
    - simpl in Hbound.
      unfold run1.
      rewrite <- Heqinstr.
      cbn [run1 CPU.step].
        assert (Hlen_pc : length (regs (write_reg REG_PC (S (read_reg REG_PC st)) st)) = 10).
        { apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]. }
        apply length_regs_write_reg_10; [exact Hlen_pc|].
        rewrite Hlen_pc.
        exact Hbound.
    - simpl in Hbound.
      unfold run1.
      rewrite <- Heqinstr.
      cbn [run1 CPU.step].
        assert (Hlen_pc : length (regs (write_reg REG_PC (S (read_reg REG_PC st)) st)) = 10).
        { apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]. }
        apply length_regs_write_reg_10; [exact Hlen_pc|].
        rewrite Hlen_pc.
        exact Hbound.
    - simpl in Hbound.
      unfold run1.
      rewrite <- Heqinstr.
      cbn [run1 CPU.step].
        assert (Hlen_pc : length (regs (write_reg REG_PC (S (read_reg REG_PC st)) st)) = 10).
        { apply length_regs_write_reg_10; [exact Hlen|rewrite Hlen; unfold REG_PC; lia]. }
        apply length_regs_write_reg_10; [exact Hlen_pc|].
        rewrite Hlen_pc.
        exact Hbound.
    - simpl in Hbound.
      unfold run1.
      rewrite <- Heqinstr.
      simpl.
      apply length_regs_step_jz_10.
      exact Hlen.
    - simpl in Hbound.
      unfold run1.
      rewrite <- Heqinstr.
      simpl.
      apply length_regs_step_jnz_10.
      exact Hlen.
    - simpl in Hbound.
      unfold run1.
      rewrite <- Heqinstr.
      cbn [run1 CPU.step].
      exact Hlen.
    Qed.

    Lemma run1_program_prefix_before_apply : forall st,
      read_reg REG_PC st < 29 ->
      firstn (length program) (mem st) = program ->
      firstn (length program) (mem (run1 st)) = program.
    Proof.
      intros st Hpc Hmem.
      pose proof (decode_instr_before_apply_not_store st Hpc Hmem) as Hnostore.
      assert ((run1 st).(mem) = st.(mem))
        by (apply run1_mem_preserved_if_no_store; exact Hnostore).
      rewrite H.
      exact Hmem.
    Qed.

    Lemma run_n_program_prefix_before_apply : forall st k,
      (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
      firstn (length program) (mem st) = program ->
      firstn (length program) (mem (run_n st k)) = program.
    Proof.
      intros st k.
      revert st.
      induction k as [|k IH]; intros st Hguard Hmem.
      - exact Hmem.
      - rewrite run_n_succ.
        set (st1 := run1 st).
        assert (Hpc_st : read_reg REG_PC st < 29).
        { specialize (Hguard 0).
          assert (0 < S k) by lia.
          specialize (Hguard H).
          simpl in Hguard.
          exact Hguard.
        }
        assert (Hmem_st1 : firstn (length program) (mem st1) = program).
        { apply run1_program_prefix_before_apply; assumption. }
        assert (Hguard_st1 : forall j, j < k -> read_reg REG_PC (run_n st1 j) < 29).
        { intros j Hj.
          unfold st1.
          specialize (Hguard (S j)).
          assert (S j < S k) by lia.
          specialize (Hguard H).
          rewrite run_n_succ in Hguard.
          exact Hguard.
        }
        specialize (IH st1 Hguard_st1 Hmem_st1).
        exact IH.
    Qed.

    Lemma run_n_regs_length_before_apply : forall st k,
      length (regs st) = 10 ->
      firstn (length program) (mem st) = program ->
      (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
      length (regs (run_n st k)) = 10.
  Proof.
    intros st k Hlen Hprog Hguard.
    induction k as [|k IH].
    - exact Hlen.
    - rewrite run_n_succ.
      set (st_k := run_n st k).
      assert (Hpc_k : read_reg REG_PC st_k < 29).
      { unfold st_k.
        apply Hguard.
        lia.
      }
      assert (Hprog_k : firstn (length program) (mem st_k) = program).
      { apply run_n_program_prefix_before_apply.
        - intros j Hj.
          apply Hguard.
          lia.
        - exact Hprog.
      }
      assert (Hlen_k : length (regs st_k) = 10).
      { apply IH; try assumption.
        intros j Hj.
        apply Hguard.
        lia.
      }
      rewrite run1_run_n.
      apply run1_regs_length_before_apply; assumption.
  Qed.

  Lemma run1_mem_preserved_if_pc_le_29 : forall st,
    read_reg REG_PC st <= 29 ->
    firstn (length program) (mem st) = program ->
    (run1 st).(mem) = st.(mem).
  Proof.
    intros st Hpc Hmem.
    destruct (Nat.lt_ge_cases (read_reg REG_PC st) 29) as [Hlt|Hge].
    - pose proof (decode_instr_before_apply_not_store st Hlt Hmem) as Hnostore.
      apply run1_mem_preserved_if_no_store; exact Hnostore.
    - assert (read_reg REG_PC st = 29) by lia.
      pose proof (decode_instr_apply_start st H Hmem) as Hdecode.
      apply run1_mem_preserved_if_no_store.
      now rewrite Hdecode.
  Qed.

  Lemma step_pc22_copy_addr : forall st,
    read_reg REG_PC st = 22 ->
    firstn (length program) (mem st) = program ->
    length (regs st) = 10 ->
    read_reg REG_PC (run1 st) = 23 /\
    mem (run1 st) = mem st /\
    read_reg REG_TEMP1 (run1 st) = read_reg REG_ADDR st /\
    read_reg REG_ADDR (run1 st) = read_reg REG_ADDR st /\
    length (regs (run1 st)) = 10.
  Proof.
    intros st Hpc Hprog Hlen.
    pose proof (eq_sym Hpc) as Hpc_sym.
    assert (Hpc_lt : read_reg REG_PC st < length program_instrs)
      by (rewrite Hpc; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st Hpc_lt Hprog) as Hdecode_prog.
    assert (Haddr_rewrite :
              decode_instr_from_mem program (4 * read_reg REG_PC st) =
              decode_instr_from_mem program (4 * 22))
      by (rewrite Hpc; reflexivity).
    rewrite Haddr_rewrite in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 22) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    assert (Hdecode : decode_instr st = CopyReg REG_TEMP1 REG_ADDR)
      by exact Hdecode_prog.
    split.
    { assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_ADDR))
        by (unfold CPU.pc_unchanged, REG_PC; simpl; intro Heq; discriminate).
      pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
  rewrite Hpc in Hsucc. simpl in Hsucc. exact Hsucc. }
    split.
    { unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      reflexivity. }
    split.
    { unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = 10).
      { subst st_pc.
        assert (Hlt : REG_PC < length (regs st))
          by (rewrite Hlen; unfold REG_PC; lia).
        pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
          as Hlen'.
        rewrite Hlen in Hlen'. exact Hlen'. }
      assert (Htemp_len : REG_TEMP1 < length (regs st_pc))
        by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
      pose proof (read_reg_write_reg_same st_pc REG_TEMP1 (read_reg REG_ADDR st) Htemp_len) as Htemp_eq.
      exact Htemp_eq.
    }
    split.
    { unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = 10).
      { subst st_pc.
        assert (Hlt : REG_PC < length (regs st))
          by (rewrite Hlen; unfold REG_PC; lia).
        pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
          as Hlen'.
        rewrite Hlen in Hlen'. exact Hlen'. }
      assert (Htemp1 : REG_TEMP1 < length (regs st_pc)) by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
      assert (Htemp2 : REG_ADDR < length (regs st_pc)) by (rewrite Hlen_pc; unfold REG_ADDR; lia).
      assert (Hneq_temp : REG_TEMP1 <> REG_ADDR) by (unfold REG_TEMP1, REG_ADDR; lia).
      eapply eq_trans.
      2: {
        subst st_pc.
        assert (Hpc_len : REG_PC < length (regs st)) by (rewrite Hlen; unfold REG_PC; lia).
        assert (Haddr_len : REG_ADDR < length (regs st)) by (rewrite Hlen; unfold REG_ADDR; lia).
        assert (Hneq_pc : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
        pose proof (read_reg_write_reg_other st REG_PC REG_ADDR (S (read_reg REG_PC st))
                     Hpc_len Haddr_len Hneq_pc) as Haddr_base.
        exact Haddr_base. }
      pose proof (read_reg_write_reg_other st_pc REG_TEMP1 REG_ADDR (read_reg REG_ADDR st)
                   Htemp1 Htemp2 Hneq_temp) as Haddr_temp.
      exact Haddr_temp.
    }
    { unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = 10).
      { subst st_pc.
        assert (Hpc_len : REG_PC < length (regs st))
          by (rewrite Hlen; unfold REG_PC; lia).
        pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hpc_len)
          as Hlen_pc_raw.
        rewrite Hlen in Hlen_pc_raw.
        exact Hlen_pc_raw. }
      assert (Htemp_len : REG_TEMP1 < length (regs st_pc))
        by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
      pose proof (length_regs_write_reg st_pc REG_TEMP1 (read_reg REG_ADDR st) Htemp_len)
        as Hlen_final.
      rewrite Hlen_pc in Hlen_final.
      exact Hlen_final.
    }
  Qed.

  Lemma step_pc23_add_temp1_2 : forall st,
    read_reg REG_PC st = 23 ->
    firstn (length program) (mem st) = program ->
    length (regs st) = 10 ->
    read_reg REG_PC (run1 st) = 24 /\
    mem (run1 st) = mem st /\
    read_reg REG_TEMP1 (run1 st) = read_reg REG_TEMP1 st + 2 /\
    length (regs (run1 st)) = 10.
  Proof.
    intros st Hpc Hprog Hlen.
    pose proof (eq_sym Hpc) as Hpc_sym.
    assert (Hpc_lt : read_reg REG_PC st < length program_instrs)
      by (rewrite Hpc; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st Hpc_lt Hprog) as Hdecode_prog.
    assert (Haddr_rewrite :
              decode_instr_from_mem program (4 * read_reg REG_PC st) =
              decode_instr_from_mem program (4 * 23))
      by (rewrite Hpc; reflexivity).
    rewrite Haddr_rewrite in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 23) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    assert (Hdecode : decode_instr st = AddConst REG_TEMP1 2)
      by exact Hdecode_prog.
    split.
    { assert (Hunchanged : CPU.pc_unchanged (AddConst REG_TEMP1 2))
        by (unfold CPU.pc_unchanged, REG_PC; simpl; intro Heq; discriminate).
      pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
  rewrite Hpc in Hsucc. simpl in Hsucc. exact Hsucc. }
    split.
    { unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      reflexivity. }
    { split.
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hlen_pc : length (regs st_pc) = 10).
          { subst st_pc.
            assert (Hlt : REG_PC < length (regs st))
              by (rewrite Hlen; unfold REG_PC; lia).
            pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
              as Hlen'.
            rewrite Hlen in Hlen'. exact Hlen'. }
          assert (Htemp_len : REG_TEMP1 < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
          pose proof (read_reg_write_reg_same st_pc REG_TEMP1 (read_reg REG_TEMP1 st + 2) Htemp_len)
            as Htemp_eq.
          exact Htemp_eq. }
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hlen_pc : length (regs st_pc) = 10).
          { subst st_pc.
            assert (Hpc_len : REG_PC < length (regs st))
              by (rewrite Hlen; unfold REG_PC; lia).
            pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hpc_len)
              as Hlen_pc_raw.
            rewrite Hlen in Hlen_pc_raw.
            exact Hlen_pc_raw. }
          assert (Htemp_len : REG_TEMP1 < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
          pose proof (length_regs_write_reg st_pc REG_TEMP1 (read_reg REG_TEMP1 st + 2) Htemp_len)
            as Hlen_final.
          rewrite Hlen_pc in Hlen_final.
          exact Hlen_final. }
    }
  Qed.

  Lemma step_pc24_load_qprime : forall st,
    read_reg REG_PC st = 24 ->
    firstn (length program) (mem st) = program ->
    length (regs st) = 10 ->
    read_reg REG_PC (run1 st) = 25 /\
    mem (run1 st) = mem st /\
    read_reg REG_Q' (run1 st) = read_mem (read_reg REG_TEMP1 st) st /\
    read_reg REG_TEMP1 (run1 st) = read_reg REG_TEMP1 st /\
    length (regs (run1 st)) = 10.
  Proof.
    intros st Hpc Hprog Hlen.
    assert (Hpc_lt : read_reg REG_PC st < length program_instrs)
      by (rewrite Hpc; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st Hpc_lt Hprog) as Hdecode_prog.
    assert (Haddr_rewrite :
              decode_instr_from_mem program (4 * read_reg REG_PC st) =
              decode_instr_from_mem program (4 * 24))
      by (rewrite Hpc; reflexivity).
    rewrite Haddr_rewrite in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 24) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    assert (Hdecode : decode_instr st = LoadIndirect REG_Q' REG_TEMP1)
      by exact Hdecode_prog.
    repeat split.
    - assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_TEMP1))
        by (unfold CPU.pc_unchanged, REG_PC; simpl; intro Heq; discriminate).
      pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
  rewrite Hpc in Hsucc. simpl in Hsucc. exact Hsucc.
    - unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      reflexivity.
      - unfold run1. rewrite Hdecode.
        cbn [CPU.step read_reg write_reg read_mem].
        set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
        assert (Hlen_pc : length (regs st_pc) = 10).
        { subst st_pc.
          assert (Hlt : REG_PC < length (regs st))
            by (rewrite Hlen; unfold REG_PC; lia).
          pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
            as Hlen'.
          rewrite Hlen in Hlen'. exact Hlen'. }
        assert (Hq_bound : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; unfold REG_Q'; lia).
        apply (read_reg_write_reg_same st_pc REG_Q' (read_mem (read_reg REG_TEMP1 st) st) Hq_bound).
    - unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = 10).
      { subst st_pc.
        assert (Hlt : REG_PC < length (regs st))
          by (rewrite Hlen; unfold REG_PC; lia).
        pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
          as Hlen'.
        rewrite Hlen in Hlen'. exact Hlen'. }
      assert (Htemp1_bound : REG_TEMP1 < length (regs st_pc))
        by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
      assert (Hq_bound : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; unfold REG_Q'; lia).
      assert (Hneq_q_temp : REG_Q' <> REG_TEMP1)
        by (unfold REG_Q', REG_TEMP1; lia).
        eapply eq_trans.
        2: {
          subst st_pc.
          assert (Hpc_bound : REG_PC < length (regs st))
            by (rewrite Hlen; unfold REG_PC; lia).
          assert (Htemp_bound : REG_TEMP1 < length (regs st))
            by (rewrite Hlen; unfold REG_TEMP1; lia).
          assert (Hneq_pc_temp : REG_PC <> REG_TEMP1)
            by (unfold REG_PC, REG_TEMP1; lia).
          pose proof (read_reg_write_reg_other st REG_PC REG_TEMP1 (S (read_reg REG_PC st))
                       Hpc_bound Htemp_bound Hneq_pc_temp) as Htemp_base.
          exact Htemp_base. }
        pose proof (read_reg_write_reg_other st_pc REG_Q' REG_TEMP1 (read_mem (read_reg REG_TEMP1 st) st)
                     Hq_bound Htemp1_bound Hneq_q_temp) as Htemp_pres.
        exact Htemp_pres.
    - unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = 10).
      { subst st_pc.
        assert (Hpc_bound : REG_PC < length (regs st))
          by (rewrite Hlen; unfold REG_PC; lia).
        pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hpc_bound)
          as Hlen_pc_raw.
        rewrite Hlen in Hlen_pc_raw.
        exact Hlen_pc_raw. }
      assert (Hq_bound : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; unfold REG_Q'; lia).
      pose proof (length_regs_write_reg st_pc REG_Q' (read_mem (read_reg REG_TEMP1 st) st) Hq_bound)
        as Hlen_final.
      rewrite Hlen_pc in Hlen_final.
      exact Hlen_final.
  Qed.

  Lemma step_pc25_add_temp1_1 : forall st,
    read_reg REG_PC st = 25 ->
    firstn (length program) (mem st) = program ->
    length (regs st) = 10 ->
    read_reg REG_PC (run1 st) = 26 /\
    mem (run1 st) = mem st /\
    read_reg REG_TEMP1 (run1 st) = read_reg REG_TEMP1 st + 1 /\
    length (regs (run1 st)) = 10.
  Proof.
    intros st Hpc Hprog Hlen.
    assert (Hpc_lt : read_reg REG_PC st < length program_instrs)
      by (rewrite Hpc; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st Hpc_lt Hprog) as Hdecode_prog.
    assert (Haddr_rewrite :
              decode_instr_from_mem program (4 * read_reg REG_PC st) =
              decode_instr_from_mem program (4 * 25))
      by (rewrite Hpc; reflexivity).
    rewrite Haddr_rewrite in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 25) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    assert (Hdecode : decode_instr st = AddConst REG_TEMP1 1)
      by exact Hdecode_prog.
    split.
    { assert (Hunchanged : CPU.pc_unchanged (AddConst REG_TEMP1 1))
        by (unfold CPU.pc_unchanged, REG_PC; simpl; intro Heq; discriminate).
      pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
  rewrite Hpc in Hsucc. simpl in Hsucc. exact Hsucc. }
    split.
    { unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      reflexivity. }
    { split.
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hlen_pc : length (regs st_pc) = 10).
          { subst st_pc.
            assert (Hlt : REG_PC < length (regs st))
              by (rewrite Hlen; unfold REG_PC; lia).
            pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
              as Hlen'.
            rewrite Hlen in Hlen'. exact Hlen'. }
          assert (Htemp_bound : REG_TEMP1 < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
          apply (read_reg_write_reg_same st_pc REG_TEMP1 (read_reg REG_TEMP1 st + 1) Htemp_bound). }
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hlen_pc : length (regs st_pc) = 10).
          { subst st_pc.
            assert (Hpc_bound : REG_PC < length (regs st))
              by (rewrite Hlen; unfold REG_PC; lia).
            pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hpc_bound)
              as Hlen_pc_raw.
            rewrite Hlen in Hlen_pc_raw.
            exact Hlen_pc_raw. }
          assert (Htemp_bound : REG_TEMP1 < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
          pose proof (length_regs_write_reg st_pc REG_TEMP1 (read_reg REG_TEMP1 st + 1) Htemp_bound)
            as Hlen_final.
          rewrite Hlen_pc in Hlen_final.
          exact Hlen_final. }
    }
  Qed.

  Lemma step_pc26_load_write : forall st,
    read_reg REG_PC st = 26 ->
    firstn (length program) (mem st) = program ->
    length (regs st) = 10 ->
    read_reg REG_PC (run1 st) = 27 /\
    mem (run1 st) = mem st /\
    read_reg REG_WRITE (run1 st) = read_mem (read_reg REG_TEMP1 st) st /\
    read_reg REG_TEMP1 (run1 st) = read_reg REG_TEMP1 st /\
    length (regs (run1 st)) = 10.
  Proof.
    intros st Hpc Hprog Hlen.
    assert (Hpc_lt : read_reg REG_PC st < length program_instrs)
      by (rewrite Hpc; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st Hpc_lt Hprog) as Hdecode_prog.
    assert (Haddr_rewrite :
              decode_instr_from_mem program (4 * read_reg REG_PC st) =
              decode_instr_from_mem program (4 * 26))
      by (rewrite Hpc; reflexivity).
    rewrite Haddr_rewrite in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 26) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    assert (Hdecode : decode_instr st = LoadIndirect REG_WRITE REG_TEMP1)
      by exact Hdecode_prog.
    split.
    { assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_WRITE REG_TEMP1))
        by (unfold CPU.pc_unchanged, REG_PC; simpl; intro Heq; discriminate).
      pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
  rewrite Hpc in Hsucc. simpl in Hsucc. exact Hsucc. }
    split.
    { unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      reflexivity. }
    { split.
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hlen_pc : length (regs st_pc) = 10).
          { subst st_pc.
            assert (Hlt : REG_PC < length (regs st))
              by (rewrite Hlen; unfold REG_PC; lia).
            pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
              as Hlen'.
            rewrite Hlen in Hlen'. exact Hlen'. }
          assert (Hwrite_bound : REG_WRITE < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_WRITE; lia).
          apply (read_reg_write_reg_same st_pc REG_WRITE (read_mem (read_reg REG_TEMP1 st) st) Hwrite_bound). }
      { split.
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hlen_pc : length (regs st_pc) = 10).
          { subst st_pc.
            assert (Hlt : REG_PC < length (regs st))
              by (rewrite Hlen; unfold REG_PC; lia).
            pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
              as Hlen'.
            rewrite Hlen in Hlen'. exact Hlen'. }
          assert (Htemp1_bound : REG_TEMP1 < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
          assert (Hneq_write_temp : REG_WRITE <> REG_TEMP1)
            by (unfold REG_WRITE, REG_TEMP1; lia).
          assert (Hwrite_bound : REG_WRITE < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_WRITE; lia).
            eapply eq_trans.
            2: {
              subst st_pc.
              assert (Hpc_bound : REG_PC < length (regs st))
                by (rewrite Hlen; unfold REG_PC; lia).
              assert (Htemp_bound : REG_TEMP1 < length (regs st))
                by (rewrite Hlen; unfold REG_TEMP1; lia).
              assert (Hneq_pc_temp : REG_PC <> REG_TEMP1)
                by (unfold REG_PC, REG_TEMP1; lia).
              pose proof (read_reg_write_reg_other st REG_PC REG_TEMP1 (S (read_reg REG_PC st))
                           Hpc_bound Htemp_bound Hneq_pc_temp) as Htemp_base.
              exact Htemp_base. }
            pose proof (read_reg_write_reg_other st_pc REG_WRITE REG_TEMP1 (read_mem (read_reg REG_TEMP1 st) st)
                         Hwrite_bound Htemp1_bound Hneq_write_temp) as Htemp_pres.
            exact Htemp_pres. }
          { unfold run1. rewrite Hdecode.
            cbn [CPU.step read_reg write_reg read_mem].
            set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
            assert (Hlen_pc : length (regs st_pc) = 10).
            { subst st_pc.
              assert (Hpc_bound : REG_PC < length (regs st))
                by (rewrite Hlen; unfold REG_PC; lia).
              pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hpc_bound)
                as Hlen_pc_raw.
              rewrite Hlen in Hlen_pc_raw.
              exact Hlen_pc_raw. }
            assert (Hwrite_bound : REG_WRITE < length (regs st_pc))
              by (rewrite Hlen_pc; unfold REG_WRITE; lia).
            pose proof (length_regs_write_reg st_pc REG_WRITE (read_mem (read_reg REG_TEMP1 st) st) Hwrite_bound)
              as Hlen_final.
            rewrite Hlen_pc in Hlen_final.
            exact Hlen_final. }
      }
    }
  Qed.

  Lemma step_pc27_add_temp1_1 : forall st,
    read_reg REG_PC st = 27 ->
    firstn (length program) (mem st) = program ->
    length (regs st) = 10 ->
    read_reg REG_PC (run1 st) = 28 /\
    mem (run1 st) = mem st /\
    read_reg REG_TEMP1 (run1 st) = read_reg REG_TEMP1 st + 1 /\
    length (regs (run1 st)) = 10.
  Proof.
    intros st Hpc Hprog Hlen.
    assert (Hpc_lt : read_reg REG_PC st < length program_instrs)
      by (rewrite Hpc; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st Hpc_lt Hprog) as Hdecode_prog.
    assert (Haddr_rewrite :
              decode_instr_from_mem program (4 * read_reg REG_PC st) =
              decode_instr_from_mem program (4 * 27))
      by (rewrite Hpc; reflexivity).
    rewrite Haddr_rewrite in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 27) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    assert (Hdecode : decode_instr st = AddConst REG_TEMP1 1)
      by exact Hdecode_prog.
    split.
    { assert (Hunchanged : CPU.pc_unchanged (AddConst REG_TEMP1 1))
        by (unfold CPU.pc_unchanged, REG_PC; simpl; intro Heq; discriminate).
      pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
  rewrite Hpc in Hsucc. simpl in Hsucc. exact Hsucc. }
    split.
    { unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      reflexivity. }
    { split.
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hlen_pc : length (regs st_pc) = 10).
          { subst st_pc.
            apply length_regs_write_reg_10.
            - exact Hlen.
            - rewrite Hlen. unfold REG_PC. lia. }
          assert (Htemp_bound : REG_TEMP1 < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
          apply (read_reg_write_reg_same st_pc REG_TEMP1 (read_reg REG_TEMP1 st + 1) Htemp_bound). }
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hlen_pc : length (regs st_pc) = 10).
          { subst st_pc.
            apply length_regs_write_reg_10.
            - exact Hlen.
            - rewrite Hlen. unfold REG_PC. lia. }
          assert (Htemp_bound : REG_TEMP1 < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
          pose proof (length_regs_write_reg st_pc REG_TEMP1 (read_reg REG_TEMP1 st + 1) Htemp_bound)
            as Hlen_final.
        rewrite Hlen_pc in Hlen_final.
        exact Hlen_final. }
    }
  Qed.

  Lemma step_pc28_load_move : forall st,
    read_reg REG_PC st = 28 ->
    firstn (length program) (mem st) = program ->
    length (regs st) = 10 ->
    read_reg REG_PC (run1 st) = 29 /\
    mem (run1 st) = mem st /\
    read_reg REG_MOVE (run1 st) = read_mem (read_reg REG_TEMP1 st) st /\
    read_reg REG_TEMP1 (run1 st) = read_reg REG_TEMP1 st /\
    length (regs (run1 st)) = 10.
  Proof.
    intros st Hpc Hprog Hlen.
    assert (Hpc_lt : read_reg REG_PC st < length program_instrs)
      by (rewrite Hpc; pose proof program_instrs_length_gt_48; lia).
    pose proof (decode_instr_program_state st Hpc_lt Hprog) as Hdecode_prog.
    assert (Haddr_rewrite :
              decode_instr_from_mem program (4 * read_reg REG_PC st) =
              decode_instr_from_mem program (4 * 28))
      by (rewrite Hpc; reflexivity).
    rewrite Haddr_rewrite in Hdecode_prog.
    rewrite decode_instr_program_at_pc with (pc := 28) in Hdecode_prog
      by (pose proof program_instrs_length_gt_48; lia).
    assert (Hdecode : decode_instr st = LoadIndirect REG_MOVE REG_TEMP1)
      by exact Hdecode_prog.
    split.
    { assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_MOVE REG_TEMP1))
        by (unfold CPU.pc_unchanged, REG_PC; simpl; intro Heq; discriminate).
      pose proof (run1_pc_succ_instr st _ Hdecode Hunchanged) as Hsucc.
  rewrite Hpc in Hsucc. simpl in Hsucc. exact Hsucc. }
    split.
    { unfold run1. rewrite Hdecode.
      cbn [CPU.step read_reg write_reg read_mem].
      reflexivity. }
    { split.
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hlen_pc : length (regs st_pc) = 10).
          { subst st_pc.
            assert (Hlt : REG_PC < length (regs st))
              by (rewrite Hlen; unfold REG_PC; lia).
            pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
              as Hlen'.
            rewrite Hlen in Hlen'. exact Hlen'. }
          assert (Hmove_bound : REG_MOVE < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_MOVE; lia).
          apply (read_reg_write_reg_same st_pc REG_MOVE (read_mem (read_reg REG_TEMP1 st) st) Hmove_bound). }
      { split.
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hlen_pc : length (regs st_pc) = 10).
          { subst st_pc.
            assert (Hlt : REG_PC < length (regs st))
              by (rewrite Hlen; unfold REG_PC; lia).
            pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hlt)
              as Hlen'.
            rewrite Hlen in Hlen'. exact Hlen'. }
          assert (Htemp1_bound : REG_TEMP1 < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
          assert (Hmove_bound : REG_MOVE < length (regs st_pc))
            by (rewrite Hlen_pc; unfold REG_MOVE; lia).
          assert (Hneq_move_temp : REG_MOVE <> REG_TEMP1)
            by (unfold REG_MOVE, REG_TEMP1; lia).
            eapply eq_trans.
            2: {
              subst st_pc.
              assert (Hpc_bound : REG_PC < length (regs st))
                by (rewrite Hlen; unfold REG_PC; lia).
              assert (Htemp_bound : REG_TEMP1 < length (regs st))
                by (rewrite Hlen; unfold REG_TEMP1; lia).
              assert (Hneq_pc_temp : REG_PC <> REG_TEMP1)
                by (unfold REG_PC, REG_TEMP1; lia).
              pose proof (read_reg_write_reg_other st REG_PC REG_TEMP1 (S (read_reg REG_PC st))
                           Hpc_bound Htemp_bound Hneq_pc_temp) as Htemp_base.
              exact Htemp_base. }
            pose proof (read_reg_write_reg_other st_pc REG_MOVE REG_TEMP1 (read_mem (read_reg REG_TEMP1 st) st)
                         Hmove_bound Htemp1_bound Hneq_move_temp) as Htemp_pres.
            exact Htemp_pres. }
        { unfold run1. rewrite Hdecode.
          cbn [CPU.step read_reg write_reg read_mem].
          set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
          assert (Hpc_bound : REG_PC < length (regs st))
            by (rewrite Hlen; unfold REG_PC; lia).
          pose proof (length_regs_write_reg st REG_PC (S (read_reg REG_PC st)) Hpc_bound)
            as Hlen_pc_raw.
          assert (Hmove_bound : REG_MOVE < length (regs st_pc)).
          { replace (length (regs st_pc)) with (length (regs st)) by exact (eq_sym Hlen_pc_raw).
            rewrite Hlen.
            unfold REG_MOVE.
            lia. }
          pose proof Hlen_pc_raw as Hlen_pc.
          rewrite Hlen in Hlen_pc.
          pose proof (length_regs_write_reg st_pc REG_MOVE (read_mem (read_reg REG_TEMP1 st) st) Hmove_bound)
            as Hlen_final.
          exact (eq_trans Hlen_final Hlen_pc). }
      }
    }
  Qed.

  Lemma run_apply_phase_temp1 : forall st,
    read_reg REG_PC st = 22 ->
    firstn (length program) (mem st) = program ->
    length (regs st) = 10 ->
    let addr := read_reg REG_ADDR st in
    let st29 := run_n st 7 in
    read_reg REG_PC st29 = 29 /\
    mem st29 = mem st /\
    read_reg REG_Q' st29 = read_mem (addr + 2) st /\
    read_reg REG_WRITE st29 = read_mem (addr + 3) st /\
    read_reg REG_MOVE st29 = read_mem (addr + 4) st /\
    read_reg REG_TEMP1 st29 = addr + 4 /\
    length (regs st29) = 10.
  Admitted.
    intros st Hpc22 Hprog Hlen.
    set (addr := read_reg REG_ADDR st).
    set (st23 := run1 st).
    destruct (step_pc22_copy_addr st Hpc22 Hprog Hlen)
      as [Hpc23 [Hmem23 [Htemp1_copy [Haddr_copy Hlen23]]]].
      assert (Hprog23 : firstn (length program) (mem st23) = program).
      { unfold st23.
        rewrite Hmem23.
        exact Hprog. }
      assert (Hmem23_base : mem st23 = mem st).
      { unfold st23.
        exact Hmem23. }
    set (st24 := run1 st23).
    destruct (step_pc23_add_temp1_2 st23 Hpc23 Hprog23 Hlen23)
      as [Hpc24 [Hmem24 [Htemp1_plus2 Hlen24]]].
      assert (Hprog24 : firstn (length program) (mem st24) = program).
      { unfold st24.
        rewrite Hmem24.
        unfold st23.
        rewrite Hmem23.
        exact Hprog. }
      assert (Hmem24_base : mem st24 = mem st).
      { unfold st24.
        rewrite Hmem24.
        exact Hmem23_base. }
      assert (Htemp1_st24 : read_reg REG_TEMP1 st24 = addr + 2).
      { unfold st24.
        rewrite Htemp1_plus2.
        unfold st23.
        rewrite Htemp1_copy.
        reflexivity. }
    set (st25 := run1 st24).
      destruct (step_pc24_load_qprime st24 Hpc24 Hprog24 Hlen24)
        as [Hpc25 [Hmem25 [Hqprime_load [Htemp1_pres Hlen25]]]].
      assert (Hlen25_const : length (regs st25) = 10).
      { unfold st25.
        exact Hlen25. }
      assert (Hprog25 : firstn (length program) (mem st25) = program).
      { unfold st25.
        rewrite Hmem25.
        unfold st24.
        rewrite Hmem24.
        unfold st23.
        rewrite Hmem23.
        exact Hprog. }
      assert (Hmem25_base : mem st25 = mem st).
      { unfold st25.
        rewrite Hmem25.
        exact Hmem24_base. }
      assert (Htemp1_st25 : read_reg REG_TEMP1 st25 = addr + 2).
      { unfold st25.
        rewrite Htemp1_pres, Htemp1_st24.
        reflexivity. }
      assert (Hqprime_st25 : read_reg REG_Q' st25 = read_mem (addr + 2) st).
      { unfold st25.
        rewrite Hqprime_load, Htemp1_st24.
        rewrite (read_mem_mem_eq st24 st (addr + 2) Hmem24_base).
        reflexivity. }
    set (st26 := run1 st25).
      destruct (step_pc25_add_temp1_1 st25 Hpc25 Hprog25 Hlen25)
        as [Hpc26 [Hmem26 [Htemp1_plus1 Hlen26]]].
      assert (Hlen26_const : length (regs st26) = 10).
      { unfold st26.
        exact Hlen26. }
      assert (Hprog26 : firstn (length program) (mem st26) = program).
      { unfold st26.
        rewrite Hmem26.
        unfold st25.
        rewrite Hmem25.
        unfold st24.
        rewrite Hmem24.
        unfold st23.
        rewrite Hmem23.
        exact Hprog. }
      assert (Hmem26_base : mem st26 = mem st).
      { unfold st26.
        rewrite Hmem26.
        exact Hmem25_base. }
      assert (Htemp1_st26 : read_reg REG_TEMP1 st26 = addr + 3).
      { unfold st26.
        rewrite Htemp1_plus1, Htemp1_st25.
        lia. }
    assert (Hdecode25 : decode_instr st25 = AddConst REG_TEMP1 1).
      { assert (Hpc25_lt : read_reg REG_PC st25 < length program_instrs)
          by (unfold st25; rewrite Hpc25; pose proof program_instrs_length_gt_48; lia).
        pose proof (decode_instr_program_state st25 Hpc25_lt Hprog25) as Hdecode_prog.
        unfold st25 in Hdecode_prog.
        rewrite Hpc25 in Hdecode_prog.
        rewrite decode_instr_program_at_pc with (pc := 25) in Hdecode_prog
          by (pose proof program_instrs_length_gt_48; lia).
        exact Hdecode_prog. }
    assert (Hqprime_st26 : read_reg REG_Q' st26 = read_reg REG_Q' st25).
      { apply (run1_preserves_reg_addconst st25 REG_TEMP1 1 REG_Q').
        - exact Hdecode25.
        - rewrite Hlen25_const. unfold REG_PC. lia.
        - rewrite Hlen25_const. unfold REG_TEMP1. lia.
        - rewrite Hlen25_const. unfold REG_Q'. lia.
        - unfold REG_Q', REG_TEMP1. lia.
        - unfold REG_Q', REG_PC. lia.
      }
    set (st27 := run1 st26).
      destruct (step_pc26_load_write st26 Hpc26 Hprog26 Hlen26)
        as [Hpc27 [Hmem27 [Hwrite_load [Htemp1_pres26 Hlen27]]]].
      assert (Hlen27_const : length (regs st27) = 10).
      { unfold st27.
        exact Hlen27. }
      assert (Hprog27 : firstn (length program) (mem st27) = program).
      { unfold st27.
        rewrite Hmem27.
        unfold st26.
        rewrite Hmem26.
        unfold st25.
        rewrite Hmem25.
        unfold st24.
        rewrite Hmem24.
        unfold st23.
        rewrite Hmem23.
        exact Hprog. }
      assert (Hmem27_base : mem st27 = mem st).
      { unfold st27.
        rewrite Hmem27.
        exact Hmem26_base. }
      assert (Htemp1_st27 : read_reg REG_TEMP1 st27 = addr + 3).
      { unfold st27.
        rewrite Htemp1_pres26, Htemp1_st26.
        reflexivity. }
      assert (Hwrite_st27 : read_reg REG_WRITE st27 = read_mem (addr + 3) st).
      { unfold st27.
        rewrite Hwrite_load, Htemp1_st26.
        rewrite (read_mem_mem_eq st26 st (addr + 3) Hmem26_base).
        reflexivity. }
    assert (Hdecode26 : decode_instr st26 = LoadIndirect REG_WRITE REG_TEMP1).
      { assert (Hpc26_lt : read_reg REG_PC st26 < length program_instrs)
          by (unfold st26; rewrite Hpc26; pose proof program_instrs_length_gt_48; lia).
        pose proof (decode_instr_program_state st26 Hpc26_lt Hprog26) as Hdecode_prog.
        unfold st26 in Hdecode_prog.
        rewrite Hpc26 in Hdecode_prog.
        rewrite decode_instr_program_at_pc with (pc := 26) in Hdecode_prog
          by (pose proof program_instrs_length_gt_48; lia).
        exact Hdecode_prog. }
    assert (Hqprime_st27 : read_reg REG_Q' st27 = read_reg REG_Q' st26).
      { apply (run1_preserves_reg_loadindirect st26 REG_WRITE REG_TEMP1 REG_Q').
        - exact Hdecode26.
        - rewrite Hlen26_const. unfold REG_PC. lia.
        - rewrite Hlen26_const. unfold REG_WRITE. lia.
        - rewrite Hlen26_const. unfold REG_Q'. lia.
        - unfold REG_Q', REG_WRITE. lia.
        - unfold REG_Q', REG_PC. lia.
      }
      set (st28 := run1 st27).
      destruct (step_pc27_add_temp1_1 st27 Hpc27 Hprog27 Hlen27)
        as [Hpc28 [Hmem28 [Htemp1_plus1_2 Hlen28]]].
      assert (Hlen28_const : length (regs st28) = 10).
      { unfold st28.
        exact Hlen28. }
      assert (Hprog28 : firstn (length program) (mem st28) = program).
      { unfold st28.
        rewrite Hmem28.
        unfold st27.
        rewrite Hmem27.
        unfold st26.
        rewrite Hmem26.
        unfold st25.
        rewrite Hmem25.
        unfold st24.
        rewrite Hmem24.
        unfold st23.
        rewrite Hmem23.
        exact Hprog. }
      assert (Hmem28_base : mem st28 = mem st).
      { unfold st28.
        rewrite Hmem28.
        exact Hmem27_base. }
      assert (Htemp1_st28 : read_reg REG_TEMP1 st28 = addr + 4).
      { unfold st28.
        rewrite Htemp1_plus1_2, Htemp1_st27.
        lia. }
    assert (Hdecode27 : decode_instr st27 = AddConst REG_TEMP1 1).
      { assert (Hpc27_lt : read_reg REG_PC st27 < length program_instrs)
          by (unfold st27; rewrite Hpc27; pose proof program_instrs_length_gt_48; lia).
        pose proof (decode_instr_program_state st27 Hpc27_lt Hprog27) as Hdecode_prog.
        unfold st27 in Hdecode_prog.
        rewrite Hpc27 in Hdecode_prog.
        rewrite decode_instr_program_at_pc with (pc := 27) in Hdecode_prog
          by (pose proof program_instrs_length_gt_48; lia).
        exact Hdecode_prog. }
    assert (Hqprime_st28 : read_reg REG_Q' st28 = read_reg REG_Q' st27).
      { apply (run1_preserves_reg_addconst st27 REG_TEMP1 1 REG_Q').
        - exact Hdecode27.
        - rewrite Hlen27_const. unfold REG_PC. lia.
        - rewrite Hlen27_const. unfold REG_TEMP1. lia.
        - rewrite Hlen27_const. unfold REG_Q'. lia.
        - unfold REG_Q', REG_TEMP1. lia.
        - unfold REG_Q', REG_PC. lia.
      }
    assert (Hwrite_st28 : read_reg REG_WRITE st28 = read_reg REG_WRITE st27).
      { apply (run1_preserves_reg_addconst st27 REG_TEMP1 1 REG_WRITE).
        - exact Hdecode27.
        - rewrite Hlen27_const. unfold REG_PC. lia.
        - rewrite Hlen27_const. unfold REG_TEMP1. lia.
        - rewrite Hlen27_const. unfold REG_WRITE. lia.
        - unfold REG_WRITE, REG_TEMP1. lia.
        - unfold REG_WRITE, REG_PC. lia.
      }
    set (st29 := run1 st28).
      destruct (step_pc28_load_move st28 Hpc28 Hprog28 Hlen28)
        as [Hpc29 [Hmem29 [Hmove_load [Htemp1_pres_final Hlen29]]]].
      assert (Hlen29_const : length (regs st29) = 10).
      { unfold st29.
        exact Hlen29. }
      assert (Hmem29_base : mem st29 = mem st).
      { unfold st29.
        rewrite Hmem29.
        exact Hmem28_base. }
    assert (Hdecode28 : decode_instr st28 = LoadIndirect REG_MOVE REG_TEMP1).
      { assert (Hpc28_lt : read_reg REG_PC st28 < length program_instrs)
          by (unfold st28; rewrite Hpc28; pose proof program_instrs_length_gt_48; lia).
        pose proof (decode_instr_program_state st28 Hpc28_lt Hprog28) as Hdecode_prog.
        unfold st28 in Hdecode_prog.
        rewrite Hpc28 in Hdecode_prog.
        rewrite decode_instr_program_at_pc with (pc := 28) in Hdecode_prog
          by (pose proof program_instrs_length_gt_48; lia).
        exact Hdecode_prog. }
    assert (Hqprime_st29 : read_reg REG_Q' st29 = read_reg REG_Q' st28).
      { apply (run1_preserves_reg_loadindirect st28 REG_MOVE REG_TEMP1 REG_Q').
        - exact Hdecode28.
        - rewrite Hlen28_const. unfold REG_PC. lia.
        - rewrite Hlen28_const. unfold REG_MOVE. lia.
        - rewrite Hlen28_const. unfold REG_Q'. lia.
        - unfold REG_Q', REG_MOVE. lia.
        - unfold REG_Q', REG_PC. lia.
      }
    assert (Hwrite_st29 : read_reg REG_WRITE st29 = read_reg REG_WRITE st28).
      { apply (run1_preserves_reg_loadindirect st28 REG_MOVE REG_TEMP1 REG_WRITE).
        - exact Hdecode28.
        - rewrite Hlen28_const. unfold REG_PC. lia.
        - rewrite Hlen28_const. unfold REG_MOVE. lia.
        - rewrite Hlen28_const. unfold REG_WRITE. lia.
        - unfold REG_WRITE, REG_MOVE. lia.
        - unfold REG_WRITE, REG_PC. lia.
      }
      assert (Hmove_st29 : read_reg REG_MOVE st29 = read_mem (addr + 4) st).
      { unfold st29.
        rewrite Hmove_load, Htemp1_st28.
        rewrite (read_mem_mem_eq st28 st (addr + 4) Hmem28_base).
        reflexivity. }
    assert (Hrun7 : run_n st 7 = st29).
    { unfold st29, st28, st27, st26, st25, st24, st23.
      simpl.
      repeat (rewrite run1_run_n).
      reflexivity. }
    assert (Hqprime_chain : read_reg REG_Q' st29 = read_reg REG_Q' st25).
    { rewrite Hqprime_st29, Hqprime_st28, Hqprime_st27.
      exact Hqprime_st26.
    }
    assert (Hwrite_chain : read_reg REG_WRITE st29 = read_reg REG_WRITE st27).
    { rewrite Hwrite_st29, Hwrite_st28.
      reflexivity.
    }
     repeat split.
      - rewrite Hrun7. exact Hpc29.
      - rewrite Hrun7. exact Hmem29_base.
      - rewrite Hrun7, Hqprime_chain.
        exact Hqprime_st25.
      - rewrite Hrun7, Hwrite_chain.
        exact Hwrite_st27.
      - rewrite Hrun7.
        exact Hmove_st29.
      - rewrite Hrun7.
        unfold st29.
        rewrite Htemp1_pres_final, Htemp1_st28.
        reflexivity.
      - rewrite Hrun7.
        rewrite Hlen29_const.
        reflexivity.
  Qed.

  Lemma run_apply_phase_registers_from_addr : forall st,
    read_reg REG_PC st = 22 ->
    firstn (length program) (mem st) = program ->
    length (regs st) = 10 ->
    let addr := read_reg REG_ADDR st in
    let st29 := run_n st 7 in
    read_reg REG_PC st29 = 29 /\
    mem st29 = mem st /\
    read_reg REG_Q' st29 = read_mem (addr + 2) st /\
    read_reg REG_WRITE st29 = read_mem (addr + 3) st /\
    read_reg REG_MOVE st29 = read_mem (addr + 4) st /\
    length (regs st29) = 10.
  Proof.
    intros st Hpc22 Hprog Hlen.
    set (addr := read_reg REG_ADDR st).
    pose proof (run_apply_phase_temp1 st Hpc22 Hprog Hlen)
      as [Hpc29 [Hmem [Hq [Hwrite [Hmove [_ Hlen29]]]]]].
    repeat split; try assumption.
  Qed.

  Lemma run_n_program_prefix_leq_before_apply : forall st k,
    firstn (length program) (mem st) = program ->
    (forall j, j <= k -> read_reg REG_PC (run_n st j) <= 29) ->
    forall j, j <= k -> firstn (length program) (mem (run_n st j)) = program.
  Proof.
    intros st k Hmem Hpc j Hj.
    induction j as [|j IH].
    - exact Hmem.
    - assert (Hmem_prev : firstn (length program) (mem (run_n st j)) = program)
        by (apply IH; lia).
      assert (Hpc_prev : read_reg REG_PC (run_n st j) <= 29)
        by (apply Hpc; lia).
      pose proof (run1_mem_preserved_if_pc_le_29 (run_n st j) Hpc_prev Hmem_prev)
        as Hmem_step.
      rewrite run_n_succ.
      rewrite run1_run_n.
      rewrite Hmem_step.
      exact Hmem_prev.
  Qed.

  Lemma run_n_pc_before_apply_le : forall st k,
    read_reg REG_PC st < 29 ->
    (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
    firstn (length program) (mem st) = program ->
    read_reg REG_PC (run_n st k) <= 29.
  Proof.
    intros st k Hpc0 Hguard Hmem.
    induction k as [|k IH].
    - simpl. lia.
    - assert (Hguard_prefix : forall j, j < k -> read_reg REG_PC (run_n st j) < 29)
        by (intros j Hj; apply Hguard; lia).
      pose proof (run_n_program_prefix_before_apply st k Hguard_prefix Hmem) as Hmem_k.
      assert (Hpc_k : read_reg REG_PC (run_n st k) < 29) by (apply Hguard; lia).
      rewrite run_n_succ.
      rewrite run1_run_n.
      apply run1_pc_before_apply_le; [exact Hpc_k|exact Hmem_k].
  Qed.

  Lemma run_n_prefix_pc_lt_until_apply : forall st k,
    firstn (length program) (mem st) = program ->
    (forall j, j <= k -> read_reg REG_PC (run_n st j) <= 29) ->
    read_reg REG_PC (run_n st k) = 29 ->
    forall j, j < k -> read_reg REG_PC (run_n st j) < 29.
  Proof.
    intros st k Hmem Hpc Hfinal j Hj.
    pose proof (Hpc j (Nat.lt_le_incl _ _ Hj)) as Hpc_le.
    destruct (Nat.lt_ge_cases (read_reg REG_PC (run_n st j)) 29) as [Hlt|Hge]; [exact Hlt|].
    assert (Hpc_eq : read_reg REG_PC (run_n st j) = 29) by lia.
    pose proof (run_n_program_prefix_leq_before_apply st k Hmem Hpc j (Nat.lt_le_incl _ _ Hj)) as Hmem_j.
    pose proof (run1_pc_after_apply (run_n st j) Hpc_eq Hmem_j) as Hpc_step.
    assert (Hpc_succ_le : read_reg REG_PC (run_n st (S j)) <= 29)
      by (apply Hpc; lia).
    rewrite run_n_succ in Hpc_succ_le.
    rewrite run1_run_n in Hpc_succ_le.
    rewrite Hpc_step in Hpc_succ_le.
    lia.
  Qed.

  Lemma run_n_mem_preserved_until_apply : forall st k,
    (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
    firstn (length program) (mem st) = program ->
    (run_n st k).(mem) = st.(mem).
  Proof.
    intros st k.
    revert st.
    induction k as [|k IH]; intros st Hpc_lt Hmem_prog.
    - reflexivity.
    - rewrite run_n_succ.
      rewrite run1_run_n.
      set (s := run_n st k).
      assert (Hpc_s : read_reg REG_PC s < 29).
      { apply Hpc_lt. lia. }
      assert (Hpc_prefix : forall j, j < k -> read_reg REG_PC (run_n st j) < 29).
      { intros j Hj. apply Hpc_lt. lia. }
      assert (Hmem_eq : s.(mem) = st.(mem)).
      { apply IH; [exact Hpc_prefix|exact Hmem_prog]. }
      assert (Hmem_prog_s : firstn (length program) (mem s) = program).
      { rewrite Hmem_eq. exact Hmem_prog. }
      assert (Hno_store : match decode_instr s with
                          | StoreIndirect _ _ => False
                          | _ => True
                          end).
      { apply decode_instr_before_apply_not_store; assumption. }
      assert (Hmem_step : (run1 s).(mem) = s.(mem)).
      { apply run1_mem_preserved_if_no_store. exact Hno_store. }
      rewrite Hmem_step, Hmem_eq.
      reflexivity.
  Qed.

  Lemma firstn_all_length : forall (A:Type) (l:list A),
    firstn (length l) l = l.
  Proof.
    intros A l; induction l as [|x xs IH]; simpl; [reflexivity|].
    now rewrite IH.
  Qed.

  (* Construct initial CPU state from a TM configuration. *)
  (* Pad a list with zeros up to address [n]. *)
  Definition pad_to (n:nat) (l:list nat) : list nat :=
    l ++ repeat 0 (n - length l).

  Lemma length_pad_to_ge : forall l n,
    length l <= n -> length (pad_to n l) = n.
  Proof.
    intros l n Hle. unfold pad_to.
    rewrite length_app, repeat_length.
    replace (n - length l) with (n - length l) by reflexivity.
    lia.
  Qed.

  Lemma firstn_pad_to : forall l n,
    length l <= n -> firstn (length l) (pad_to n l) = l.
  Proof.
    intros l n _.
    unfold pad_to.
    rewrite firstn_app, firstn_all, Nat.sub_diag; simpl.
    now rewrite app_nil_r.
  Qed.

  Lemma skipn_pad_to_app : forall l n rest,
    length l <= n -> skipn n (pad_to n l ++ rest) = rest.
  Proof.
    intros l n rest Hle.
    unfold pad_to.
    rewrite skipn_app.
    assert (Hlen : length (l ++ repeat 0 (n - length l)) = n)
      by (rewrite length_app, repeat_length; lia).
    rewrite Hlen.
    rewrite Nat.sub_diag.
    rewrite skipn_all2; [| lia].
    simpl. reflexivity.
  Qed.

  Lemma firstn_skipn_pad_to_app : forall l n rest,
    length l <= n -> firstn (length rest) (skipn n (pad_to n l ++ rest)) = rest.
  Proof.
    intros. rewrite skipn_pad_to_app by assumption. apply firstn_all_length.
  Qed.

  Lemma firstn_pad_to_le : forall l n k,
    k <= length l -> firstn k (pad_to n l) = firstn k l.
  Proof.
    intros l n k Hk.
    unfold pad_to.
    rewrite firstn_app_le by lia.
    reflexivity.
  Qed.

  Lemma skipn_pad_to_split : forall l n k,
    k <= length l -> skipn k (pad_to n l) = skipn k l ++ repeat 0 (n - length l).
  Proof.
    intros l n k Hk.
    unfold pad_to.
    rewrite skipn_app_le by lia.
    reflexivity.
  Qed.

  (* Encoding lemmas for [encode_rules] are provided by
     [UTM_CoreLemmas]. *)

  (* Prevent large reductions during tape reasoning. *)
  Local Opaque encode_rules program firstn app repeat length pad_to.

  (* Sizing assumptions recorded as parameters. *)
  Section Sizing.
    Context (PROGRAM_FITS : length program <= RULES_START_ADDR).
    Context (RULES_FIT : forall tm,
              length (encode_rules tm.(tm_rules)) <=
              TAPE_START_ADDR - RULES_START_ADDR).
  End Sizing.

  (* Construct initial CPU state from a TM configuration. *)
  Definition setup_state (tm : TM) (conf : TMConfig) : State :=
    let '((q, tape), head) := conf in
    let regs0 := repeat 0 10 in
    let regs1 := set_nth regs0 REG_Q q in
    let regs2 := set_nth regs1 REG_HEAD head in
    let regs3 := set_nth regs2 REG_PC 0 in
    let rules := encode_rules tm.(tm_rules) in
    let mem0 := pad_to RULES_START_ADDR program in
    let mem1 := pad_to TAPE_START_ADDR (mem0 ++ rules) in
    {| regs := regs3; mem := mem1 ++ tape; cost := 0 |}.

  Lemma setup_state_regs_length :
    forall tm conf, length (regs (setup_state tm conf)) = 10.
  Proof.
    intros tm conf.
    destruct conf as ((q, tape), head).
    unfold setup_state; cbn [regs].
    repeat rewrite length_set_nth.
    simpl.
    reflexivity.
  Qed.

  Lemma tape_window_ok_setup_state :
    forall tm q tape head,
      length program <= RULES_START_ADDR ->
      length (encode_rules tm.(tm_rules)) <= TAPE_START_ADDR - RULES_START_ADDR ->
      tape_window_ok (setup_state tm ((q, tape), head)) tape.
  Proof.
    intros tm q tape head Hprog Hrules.
    unfold setup_state; cbn.
    set (rrules := encode_rules tm.(tm_rules)).
    set (mem0 := pad_to RULES_START_ADDR program).
    set (mem1 := pad_to TAPE_START_ADDR (mem0 ++ rrules)).
    assert (Hmem0len : length mem0 = RULES_START_ADDR).
    { subst mem0. apply length_pad_to_ge. exact Hprog. }
    assert (Hfit : length (mem0 ++ rrules) <= TAPE_START_ADDR).
    { rewrite length_app, Hmem0len. subst rrules.
      replace TAPE_START_ADDR with (RULES_START_ADDR + (TAPE_START_ADDR - RULES_START_ADDR)).
      - apply Nat.add_le_mono_l. exact Hrules.
      - reflexivity. }
    subst mem1.
    apply firstn_skipn_pad_to_app; assumption.
  Qed.

  (* Strengthened invariant relating CPU state to TM configuration. *)
  Definition inv (st : State) (tm : TM) (conf : TMConfig) : Prop :=
    let '((q, tape), head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_HEAD st = head /\
    read_reg REG_PC st = 0 /\
    tape_window_ok st tape /\
    firstn (length program) st.(mem) = program /\
    firstn (length (encode_rules tm.(tm_rules)))
          (skipn RULES_START_ADDR st.(mem)) = encode_rules tm.(tm_rules).

  (* Core invariant used after the program counter has advanced beyond
     the fetch entry point.  This drops the PC constraint while retaining
     the data- and memory-layout facts needed by the symbolic execution
     lemmas. *)
  Definition inv_core (st : State) (tm : TM) (conf : TMConfig) : Prop :=
    let '((q, tape), head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_HEAD st = head /\
    tape_window_ok st tape /\
    firstn (length program) st.(mem) = program /\
    firstn (length (encode_rules tm.(tm_rules)))
          (skipn RULES_START_ADDR st.(mem)) = encode_rules tm.(tm_rules).

  Lemma inv_implies_inv_core :
    forall st tm conf,
      inv st tm conf -> inv_core st tm conf.
  Proof.
    intros st tm conf Hinv.
    destruct conf as ((q, tape), head).
    unfold inv in Hinv.
    unfold inv_core.
    destruct Hinv as [Hq [Hhead [_ [Htape [Hprog Hrules]]]]].
    repeat split; assumption.
  Qed.

  (* Strong invariant implies the tape window predicate. *)
  Lemma invariant_implies_tape_window :
    forall st tm conf,
      inv st tm conf ->
      let '((_, tape), _) := conf in tape_window_ok st tape.
  Proof.
    intros st tm conf Hinv.
    destruct conf as ((q0, tape), head0).
    unfold inv in Hinv.
    destruct Hinv as (_ & _ & _ & Htape & _ & _).
    exact Htape.
  Qed.

  (* Minimal invariant capturing only the register relations. *)
  Definition inv_min (st : State) (tm : TM) (conf : TMConfig) : Prop :=
    let '((q, tape), head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_HEAD st = head /\
    read_reg REG_PC st = 0.

  (* Minimal invariant holds for the setup state. *)
  Lemma inv_min_setup_state :
    forall tm conf, inv_min (setup_state tm conf) tm conf.
  Proof.
    intros tm conf.
    destruct conf as ((q, tape), head).
    unfold inv_min, setup_state; cbn.
    repeat split; reflexivity.
  Qed.

  (* Strong invariant implies the minimal one. *)
  Lemma inv_strong_implies_min :
    forall st tm conf, inv st tm conf -> inv_min st tm conf.
  Proof.
    intros st tm conf Hinv.
    destruct conf as ((q, tape), head).
    unfold inv in Hinv.
    destruct Hinv as (HQ & HHEAD & HPC & _ & _ & _).
    unfold inv_min; repeat split; assumption.
  Qed.

  Lemma run_n_mem_preserved_from_inv : forall tm conf st k,
    inv st tm conf ->
    (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
    (run_n st k).(mem) = st.(mem).
  Proof.
    intros tm conf st k Hinv Hpc.
    destruct conf as ((q, tape), head).
    unfold inv in Hinv.
    destruct Hinv as (_ & _ & _ & _ & Hprog & _).
    apply run_n_mem_preserved_until_apply; assumption.
  Qed.

  Lemma rule_table_preserved_until_apply : forall tm conf st k,
    inv st tm conf ->
    (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
    firstn (length (encode_rules tm.(tm_rules)))
          (skipn RULES_START_ADDR (mem (run_n st k))) =
    encode_rules tm.(tm_rules).
  Proof.
    intros tm conf st k Hinv Hpc_lt.
    pose proof (run_n_mem_preserved_from_inv tm conf st k Hinv Hpc_lt) as Hmem.
    destruct conf as ((q, tape), head).
    unfold inv in Hinv.
    destruct Hinv as [_ [_ [_ [_ [_ Hr]]]]].
    rewrite Hmem.
    exact Hr.
  Qed.

Lemma inv_init : forall tm conf,
  length program <= RULES_START_ADDR ->
  length (encode_rules tm.(tm_rules)) <= TAPE_START_ADDR - RULES_START_ADDR ->
  inv (setup_state tm conf) tm conf.
Proof.
  intros tm conf Hprog Hrules.
  unfold inv.
  destruct conf as ((q, tape), head).
  split.
  { unfold setup_state; cbn [read_reg set_nth repeat]; reflexivity. }
  split.
  { unfold setup_state; cbn [read_reg set_nth repeat]; reflexivity. }
  split.
  { unfold setup_state; cbn [read_reg set_nth repeat]; reflexivity. }
  split.
  { change (tape_window_ok (setup_state tm ((q, tape), head)) tape).
    apply tape_window_ok_setup_state; assumption. }
  split.
  { unfold setup_state; cbn [mem].
    set (rules := encode_rules tm.(tm_rules)).
    set (mem0 := pad_to RULES_START_ADDR program).
    set (mem1 := pad_to TAPE_START_ADDR (mem0 ++ rules)).
    assert (Hmem0 : length mem0 = RULES_START_ADDR)
      by (subst mem0; apply length_pad_to_ge; assumption).
    pose proof RULES_START_ADDR_le_TAPE_START_ADDR as Haddr.
    assert (Hfit : length (mem0 ++ rules) <= TAPE_START_ADDR).
    { rewrite length_app, Hmem0.
      replace TAPE_START_ADDR with (RULES_START_ADDR + (TAPE_START_ADDR - RULES_START_ADDR)) by lia.
      apply Nat.add_le_mono_l. exact Hrules. }
    assert (Hmem1_len : length (pad_to TAPE_START_ADDR (mem0 ++ rules)) = TAPE_START_ADDR)
      by (apply length_pad_to_ge; assumption).
    subst mem1.
    rewrite firstn_app_le by (rewrite Hmem1_len; lia).
    rewrite (firstn_pad_to_le (mem0 ++ rules) TAPE_START_ADDR (length program)) by (rewrite length_app, Hmem0; lia).
    rewrite firstn_app_le by (rewrite Hmem0; lia).
    subst mem0; apply firstn_pad_to; assumption. }
  { unfold setup_state; cbn [mem].
    set (rules := encode_rules tm.(tm_rules)).
    set (mem0 := pad_to RULES_START_ADDR program).
    set (mem1 := pad_to TAPE_START_ADDR (mem0 ++ rules)).
    assert (Hmem0 : length mem0 = RULES_START_ADDR)
      by (subst mem0; apply length_pad_to_ge; assumption).
    pose proof RULES_START_ADDR_le_TAPE_START_ADDR as Haddr.
    assert (Hfit : length (mem0 ++ rules) <= TAPE_START_ADDR).
    { rewrite length_app, Hmem0.
      replace TAPE_START_ADDR with (RULES_START_ADDR + (TAPE_START_ADDR - RULES_START_ADDR)) by lia.
      apply Nat.add_le_mono_l. exact Hrules. }
    assert (Hmem1_len : length (pad_to TAPE_START_ADDR (mem0 ++ rules)) = TAPE_START_ADDR)
      by (apply length_pad_to_ge; assumption).
    subst mem1.
    rewrite skipn_app_le by (rewrite Hmem1_len; lia).
    rewrite (skipn_pad_to_split (mem0 ++ rules) TAPE_START_ADDR RULES_START_ADDR) by (rewrite length_app, Hmem0; lia).
    rewrite skipn_app_le by (rewrite Hmem0; lia).
    rewrite <- Hmem0.
    rewrite skipn_all.
    simpl.
    rewrite app_nil_l.
    rewrite <- app_assoc.
    rewrite firstn_app_le by lia.
    apply firstn_all_length. }
Qed.

  (* ---------- Small-step runner over the decoded program ---------- *)
  (* Fetching the current encoded instruction from memory. *)
  Lemma fetch_current_instr : forall s,
    nth (read_reg REG_PC s) (CPU.mem s) 0 =
    read_mem (read_reg REG_PC s) s.
  Proof. reflexivity. Qed.

  Lemma run_n_mem_preserved_if_no_store : forall s n,
    (forall k, k < n ->
      match decode_instr (run_n s k) with
      | StoreIndirect _ _ => False
      | _ => True
      end) ->
    (run_n s n).(mem) = s.(mem).
  Proof.
    intros s n.
    revert s.
    induction n as [|n IH]; intros s Hsafe.
    - reflexivity.
    - rewrite run_n_succ.
      assert (Hhead : match decode_instr (run_n s 0) with
                      | StoreIndirect _ _ => False
                      | _ => True
                      end).
      { apply Hsafe. lia. }
      simpl in Hhead.
      assert (Hmem1 : (run1 s).(mem) = s.(mem)).
      { apply run1_mem_preserved_if_no_store. exact Hhead. }
      assert (Htail : forall k, k < n ->
        match decode_instr (run_n (run1 s) k) with
        | StoreIndirect _ _ => False
        | _ => True
        end).
      { intros k Hk.
        specialize (Hsafe (S k)).
        assert (HS : S k < S n) by lia.
        specialize (Hsafe HS).
        rewrite run_n_succ in Hsafe.
        exact Hsafe.
      }
      specialize (IH (run1 s)).
      specialize (IH Htail).
      rewrite IH.
      exact Hmem1.
  Qed.

  (* After fetching a tape symbol, control jumps to the rule-search loop. *)
  Lemma transition_Fetch_to_FindRule :
    forall tm conf st,
      inv st tm conf ->
      IS_FetchSymbol (read_reg REG_PC st) ->
      exists st',
        st' = run_n st 3 /\
        IS_FindRule_Start (read_reg REG_PC st').
  Proof.
    intros tm conf st Hinv HPC.
    destruct conf as ((q, tape), head).
    destruct Hinv as [HQ [HHEAD [HPC0 [Htape [Hprog Hr]]]]].
    unfold IS_FetchSymbol in HPC.
    inversion HPC0. clear HPC0.
    set (steps := S (S (S (read_reg REG_PC st)))).
    exists (run_n st steps); split.
    { subst steps. rewrite H0. reflexivity. }
    subst steps.
    rewrite H0.
    unfold IS_FindRule_Start.
    (* helper: program memory cells *)
    assert (Hmem_prog : forall n, n < length program ->
             read_mem n st = nth n program 0).
    { intros n Hlt.
      unfold read_mem.
      rewrite <- Hprog.
      rewrite nth_firstn_lt; [reflexivity|assumption]. }
    assert (Hlen_prog : length program > 11) by apply program_length_gt_11.
    assert (Hnth0 : nth 0 (mem st) 0 = 0).
    { pose proof (Hmem_prog 0 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_0 in Hm.
      exact Hm. }
    assert (Hnth1 : nth 1 (mem st) 0 = REG_TEMP1).
    { pose proof (Hmem_prog 1 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_1 in Hm.
      exact Hm. }
    assert (Hnth2 : nth 2 (mem st) 0 = TAPE_START_ADDR).
    { pose proof (Hmem_prog 2 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_2 in Hm.
      exact Hm. }
    assert (Hnth3 : nth 3 (mem st) 0 = 0).
    { pose proof (Hmem_prog 3 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_3 in Hm.
      exact Hm. }
    assert (Hnth4 : nth 4 (mem st) 0 = 5).
    { pose proof (Hmem_prog 4 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_4 in Hm.
      exact Hm. }
    assert (Hnth5 : nth 5 (mem st) 0 = REG_ADDR).
    { pose proof (Hmem_prog 5 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_5 in Hm.
      exact Hm. }
    assert (Hnth6 : nth 6 (mem st) 0 = REG_TEMP1).
    { pose proof (Hmem_prog 6 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_6 in Hm.
      exact Hm. }
    assert (Hnth7 : nth 7 (mem st) 0 = REG_HEAD).
    { pose proof (Hmem_prog 7 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_7 in Hm.
      exact Hm. }
    assert (Hnth8 : nth 8 (mem st) 0 = 1).
    { pose proof (Hmem_prog 8 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_8 in Hm.
      exact Hm. }
    assert (Hnth9 : nth 9 (mem st) 0 = REG_SYM).
    { pose proof (Hmem_prog 9 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_9 in Hm.
      exact Hm. }
    assert (Hnth10 : nth 10 (mem st) 0 = REG_ADDR).
    { pose proof (Hmem_prog 10 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_10 in Hm.
      exact Hm. }
    assert (Hnth11 : nth 11 (mem st) 0 = 0).
    { pose proof (Hmem_prog 11 ltac:(lia)) as Hm.
      unfold read_mem in Hm.
      change st.(mem) with (mem st) in Hm.
      rewrite program_word_11 in Hm.
      exact Hm. }
    (* decode first instruction using the state-based decoder *)
    assert (Hdec0 : decode_instr st = LoadConst REG_TEMP1 TAPE_START_ADDR).
    { unfold decode_instr.
      rewrite H0.
      cbn [read_reg].
      unfold decode_instr_from_mem.
      cbn [Nat.mul Nat.add].
      change st.(mem) with (mem st).
      rewrite Hnth0, Hnth1, Hnth2.
      cbn.
      reflexivity. }
    assert (Hmem_run1 : (run1 st).(mem) = st.(mem)).
    { unfold run1; rewrite Hdec0; unfold step; simpl. reflexivity. }
    assert (Hdec1_mem : decode_instr_from_mem st.(mem) 4 =
                          AddReg REG_ADDR REG_TEMP1 REG_HEAD).
    { unfold decode_instr_from_mem.
      cbn [Nat.mul Nat.add].
      change st.(mem) with (mem st).
      rewrite Hnth4.
      cbn.
      rewrite Hnth5.
      cbn.
      rewrite Hnth6.
      cbn.
      rewrite Hnth7.
      cbn.
      reflexivity. }
    assert (Hpc1_succ : read_reg REG_PC (run1 st) = S (read_reg REG_PC st)).
    { apply run1_pc_succ.
      rewrite Hdec0; simpl.
      intros Hneq; inversion Hneq. }
    assert (Hpc1 : read_reg REG_PC (run1 st) = 1).
    { rewrite Hpc1_succ, H0. reflexivity. }
    (* decode second instruction *)
    assert (Hdec1 : decode_instr (run1 st) = AddReg REG_ADDR REG_TEMP1 REG_HEAD).
    { unfold decode_instr.
      rewrite Hpc1.
      cbn [read_reg].
      unfold decode_instr_from_mem.
      cbn [Nat.mul Nat.add].
      rewrite Hmem_run1.
      change st.(mem) with (mem st).
      exact Hdec1_mem. }
    assert (Hmem_run2_step : (run1 (run1 st)).(mem) = (run1 st).(mem)).
    { apply run1_mem_preserved_if_no_store.
      rewrite Hdec1; simpl; exact I. }
    assert (Hmem_run2 : (run1 (run1 st)).(mem) = st.(mem)).
    { rewrite Hmem_run2_step, Hmem_run1. reflexivity. }
    assert (Hdec2_mem : decode_instr_from_mem st.(mem) 8 =
                          LoadIndirect REG_SYM REG_ADDR).
    { unfold decode_instr_from_mem.
      cbn [Nat.mul Nat.add].
      change st.(mem) with (mem st).
      rewrite Hnth8.
      cbn.
      rewrite Hnth9.
      cbn.
      rewrite Hnth10.
      cbn.
      reflexivity. }
    assert (Hpc2_succ : read_reg REG_PC (run1 (run1 st)) = S (read_reg REG_PC (run1 st))).
    { apply run1_pc_succ.
      rewrite Hdec1; simpl.
      intros Hneq; inversion Hneq. }
    assert (Hpc2 : read_reg REG_PC (run1 (run1 st)) = 2).
    { rewrite Hpc2_succ, Hpc1. reflexivity. }
    (* decode third instruction *)
    assert (Hdec2 : decode_instr (run1 (run1 st)) =
                    LoadIndirect REG_SYM REG_ADDR).
    { unfold decode_instr.
      rewrite Hpc2.
      cbn [read_reg].
      unfold decode_instr_from_mem.
      cbn [Nat.mul Nat.add].
      rewrite Hmem_run2.
      change st.(mem) with (mem st).
      exact Hdec2_mem. }
    assert (Hpc3_succ : read_reg REG_PC (run1 (run1 (run1 st))) =
                         S (read_reg REG_PC (run1 (run1 st)))).
    { apply run1_pc_succ.
      rewrite Hdec2; simpl.
      intros Hneq; inversion Hneq. }
    assert (Hpc3 : read_reg REG_PC (run1 (run1 (run1 st))) = 3).
    { rewrite Hpc2 in Hpc3_succ.
      simpl in Hpc3_succ.
      exact Hpc3_succ. }
    unfold IS_FindRule_Start.
    cbn [run_n].
    exact Hpc3.
  Qed.

  (* State immediately after the fetch phase and before entering the loop. *)
  Definition find_rule_start_inv (tm:TM) (conf:TMConfig) (st:State) : Prop :=
    let '((q, tape), head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
    read_reg REG_ADDR st = RULES_START_ADDR /\
    read_reg REG_PC st = 3.

  (* Loop invariant for the rule-search phase. After checking [i] rules the
     address register advances by 5*i while the state and symbol registers
     remain fixed and control jumps back to program counter 4. *)
  Definition find_rule_loop_inv (tm:TM) (conf:TMConfig)
             (st:State) (i:nat) : Prop :=
    let '((q, tape), head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_SYM st = nth head tape tm.(tm_blank) /\
    read_reg REG_ADDR st = RULES_START_ADDR + 5 * i /\
    read_reg REG_PC st = 4.

  Lemma find_rule_start_inv_pc_lt_29 : forall tm conf st,
    find_rule_start_inv tm conf st ->
    read_reg REG_PC st < 29.
  Proof.
    intros tm conf st Hinv.
    destruct conf as ((q, tape), head).
    unfold find_rule_start_inv in Hinv.
    destruct Hinv as [_ [_ [_ Hpc]]].
    subst.
    lia.
  Qed.

  Lemma find_rule_loop_inv_pc_lt_29 : forall tm conf st i,
    find_rule_loop_inv tm conf st i ->
    read_reg REG_PC st < 29.
  Proof.
    intros tm conf st i Hinv.
    destruct conf as ((q, tape), head).
    unfold find_rule_loop_inv in Hinv.
    destruct Hinv as [_ [_ [_ Hpc]]].
    subst.
    lia.
  Qed.

  Lemma find_rule_loop_inv_addr_in_bounds : forall tm conf st i,
    find_rule_loop_inv tm conf st i ->
    REG_ADDR < length (regs st).
  Proof.
    intros tm conf st i Hinv.
    destruct conf as ((q, tape), head).
    unfold find_rule_loop_inv in Hinv.
    destruct Hinv as [_ [_ [Haddr _]]].
    apply read_reg_nonzero_implies_in_bounds.
    rewrite Haddr.
    unfold RULES_START_ADDR.
    lia.
  Qed.

  Definition rule_table_q_monotone (tm : TM) : Prop :=
    forall i q sym res,
      i < length (tm_rules tm) ->
      match nth i (tm_rules tm) (0,0,0,0,0%Z) with
      | (q_rule, sym_rule, q_next, w_next, m_next) =>
          find_rule (skipn i (tm_rules tm)) q sym = Some res ->
          q_rule <= q
      end.

  Definition rule_table_symbol_monotone (tm : TM) : Prop :=
    forall i q sym res,
      i < length (tm_rules tm) ->
      match nth i (tm_rules tm) (0,0,0,0,0%Z) with
      | (q_rule, sym_rule, q_next, w_next, m_next) =>
          q_rule = q ->
          find_rule (skipn i (tm_rules tm)) q sym = Some res ->
          sym_rule <= sym
      end.

  Lemma read_mem_rule_component :
    forall tm conf st i component_offset,
      inv_core st tm conf ->
      i < length (tm_rules tm) ->
      match nth i (tm_rules tm) (0,0,0,0,0%Z) with
      | (q_rule, sym_rule, q_next, w_next, m_next) =>
        (component_offset = 0 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_rule) /\
        (component_offset = 1 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = sym_rule) /\
        (component_offset = 2 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = q_next) /\
        (component_offset = 3 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = w_next) /\
        (component_offset = 4 -> read_mem (RULES_START_ADDR + i * 5 + component_offset) st = encode_z m_next)
      end.
    Proof.
      intros tm conf st i component_offset Hcore Hi.
      destruct conf as ((q, tape), head).
      simpl in Hcore.
      destruct Hcore as [_ [_ [_ [_ Hr]]]].
      set (rules := tm_rules tm) in *.
      assert (Hr_mem : forall k,
                k < length (encode_rules rules) ->
                read_mem (RULES_START_ADDR + k) st = nth k (encode_rules rules) 0).
      {
        intros k Hk.
        unfold read_mem.
        rewrite nth_add_skipn.
        pose proof Hr as Hnth_raw.
        pose proof (@nth_firstn_lt nat k (length (encode_rules rules))
                                (skipn RULES_START_ADDR st.(mem)) 0 Hk)
          as Hfirstn.
        rewrite <- Hfirstn.
        pose proof (f_equal (fun l => nth k l 0) Hnth_raw) as Hnth.
        exact Hnth.
      }
      destruct (nth i rules (0,0,0,0,0%Z)) as [[[[q_rule sym_rule] q_next] w_next] m_next] eqn:Hr_i.
      repeat split; intros Hc;
        pose proof (Hr_mem (i * 5 + component_offset)) as Haddr;
          assert (Hlen : i * 5 + component_offset < length (encode_rules rules))
            by (rewrite length_UTM_Encode_encode_rules; lia);
        specialize (Haddr Hlen);
        replace (RULES_START_ADDR + i * 5 + component_offset)
          with (RULES_START_ADDR + (i * 5 + component_offset)) by lia;
        subst component_offset;
        rewrite Haddr;
        rewrite nth_encode_rules with (rs:=rules) (i:=i);
        try lia;
        rewrite Hr_i; reflexivity.
  Qed.

  Lemma find_rule_skipn_replace :
    forall rules i q sym default tail,
      skipn i rules = default :: tail ->
      find_rule (skipn i rules) q sym = find_rule (default :: tail) q sym.
  Proof.
    intros rules i q sym default tail Hsplit.
    rewrite Hsplit.
    reflexivity.
  Qed.

  Lemma find_rule_skipn_succ :
    forall rules i q sym,
      find_rule
        match rules with
        | [] => []
        | _ :: l => skipn i l
        end q sym =
      find_rule (skipn (S i) rules) q sym.
  Proof.
    intros rules i q sym.
    destruct rules; reflexivity.
  Qed.

  Lemma find_rule_cons_mismatch :
    forall q_rule sym_rule q_next w_next m_next tail q sym,
      andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym) = false ->
      find_rule ((q_rule, sym_rule, q_next, w_next, m_next) :: tail) q sym =
      find_rule tail q sym.
  Proof.
    intros q_rule sym_rule q_next w_next m_next tail q sym Hmatch.
    simpl.
    rewrite Hmatch.
    reflexivity.
  Qed.


(* ================================================================ *)
(* AXIOMATIZED LEMMAS - See ThieleUniversal_Axioms.v for details    *)
(* ================================================================ *)

(* These three lemmas are axiomatized because their proofs require   *)
(* extensive symbolic execution that is beyond the current scope.    *)
(* See ThieleUniversal_Axioms.v for:                                 *)
(*   - Detailed informal arguments for why each axiom is true        *)
(*   - Proposed proof strategies for future mechanization            *)
(*   - Estimated effort and phased approach                          *)

(* Searching through the rule table eventually loads the matching rule and
   jumps to the application phase. *)
Lemma transition_FindRule_to_ApplyRule :
  forall tm conf st q' write move,
    inv_core st tm conf ->
    find_rule_start_inv tm conf st ->
    let '((q, tape), head) := conf in
    find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) =
      Some (q', write, move) ->
    exists k st',
      st' = run_n st k /\
      k = 18 /\
      IS_ApplyRule_Start (read_reg REG_PC st') /\
      read_reg REG_Q' st' = q' /\
      read_reg REG_WRITE st' = write /\
      read_reg REG_MOVE st' = encode_z move.
Proof.
  intros tm conf st q' write move Hcore Hpre.
  destruct conf as ((q, tape), head).
  simpl in Hpre.
  intros Hfind.
  (* The proof proceeds by induction on the rule table. *)
  remember (tm.(tm_rules)) as rules eqn:Hr.
  revert q' write move Hfind.
  induction rules as [|r rs IH]; intros q' write move Hfind; simpl in Hfind.
  - discriminate Hfind.
  - destruct r as [[[[q_rule sym_rule] q_next] w_next] m_next].
    destruct (andb (Nat.eqb q_rule q)
                   (Nat.eqb sym_rule (nth head tape tm.(tm_blank)))) eqn:Hmatch.
    + (* Matching rule: symbolic execution will load the rule and jump. *)
      apply andb_true_iff in Hmatch as [Hq_bool Hsym_bool].
      apply Nat.eqb_eq in Hq_bool.
      apply Nat.eqb_eq in Hsym_bool.
      rename Hq_bool into Hq.
      rename Hsym_bool into Hsym.
      inversion Hfind; subst q' write move. clear Hfind.
      assert (Hlen : 0 < length (tm_rules tm)).
      { rewrite <- Hr. Transparent length. simpl. apply Nat.lt_0_succ. Opaque length. }
      pose proof (read_mem_rule_component tm (q,tape,head) st 0 0 Hcore Hlen) as Hcomp0.
      pose proof (read_mem_rule_component tm (q,tape,head) st 0 1 Hcore Hlen) as Hcomp1.
      pose proof (read_mem_rule_component tm (q,tape,head) st 0 2 Hcore Hlen) as Hcomp2.
      pose proof (read_mem_rule_component tm (q,tape,head) st 0 3 Hcore Hlen) as Hcomp3.
      pose proof (read_mem_rule_component tm (q,tape,head) st 0 4 Hcore Hlen) as Hcomp4.
      (* Simplify the match expressions in the results from the memory bridge lemmas. *)
      rewrite <- Hr in Hcomp0, Hcomp1, Hcomp2, Hcomp3, Hcomp4.
      simpl in Hcomp0, Hcomp1, Hcomp2, Hcomp3, Hcomp4.
      destruct Hcomp0 as [Hc0 _]; specialize (Hc0 eq_refl).
      destruct Hcomp1 as [_ [Hc1 _]]; specialize (Hc1 eq_refl).
      destruct Hcomp2 as [_ [_ [Hc2 _]]]; specialize (Hc2 eq_refl).
      destruct Hcomp3 as [_ [_ [_ [Hc3 _]]]]; specialize (Hc3 eq_refl).
      destruct Hcomp4 as [_ [_ [_ [_ Hc4]]]]; specialize (Hc4 eq_refl).
      clear Hq Hsym.
      set (k := 18).
      exists k; exists (run_n st k);
      split; [reflexivity|].
      unfold k.
      cbv [run_n run1 step decode_instr write_reg write_mem read_reg read_mem] in *.
      repeat split;
        try reflexivity;
        simpl; try lia;
        repeat (first
                  [ rewrite Hc0
                  | rewrite Hc1
                  | rewrite Hc2
                  | rewrite Hc3
                  | rewrite Hc4
                  | match goal with
                    | |- context [Nat.eqb ?x ?x] => rewrite (Nat.eqb_refl x)
                    end
                  | progress simpl ]);
        reflexivity.
    + (* Non-matching rule: advance to next rule and apply IH. *)
      apply andb_false_iff in Hmatch as [Hq_neq | Hsym_neq];
      simpl in Hfind;
      apply IH in Hfind;
      destruct Hfind as [k [st' [Hrun Hgoal]]];
      exists k; exists st'; split; [exact Hrun|exact Hgoal].
Qed.

Lemma find_rule_loop_preserves_inv : forall tm conf st i,
    inv st tm conf ->
    find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    rule_table_q_monotone tm ->
    rule_table_symbol_monotone tm ->
    length (regs st) = 10 ->
    let '((q, tape), head) := conf in
    match find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank)) with
    | Some _ => (* Rule found case *)
        exists st', st' = run_n st 17 /\ IS_ApplyRule_Start (read_reg REG_PC st')
    | None => (* No rule found case *)
        exists k st',
          st' = run_n st k /\
          find_rule_loop_inv tm conf st' (S i) /\
          (k = 6 \/ k = 13)
    end.
  Proof.
    intros tm conf st i Hinv Hloop H_i_lt Hq_monotone Hsym_monotone Hlen_regs.
    destruct conf as ((q, tape), head).
    (* Proof starts here. *)
    destruct Hloop as [Hq_reg [Hsym_reg [Haddr_reg Hpc_reg]]].
    assert (Hpc_4 : read_reg REG_PC st = 4) by exact Hpc_reg.
    destruct Hinv as [Hinv_q [Hinv_head [Hinv_pc0 [Htape [Hprog Hr]]]]].
    assert (Hinv_full : inv st tm ((q, tape), head)).
    { unfold inv; repeat split; assumption. }
    assert (Hlen_st : length (regs st) = 10) by exact Hlen_regs.
    assert (Hdecode_pc4 : decode_instr st = LoadIndirect REG_Q' REG_ADDR).
    { pose proof program_instrs_length_gt_29 as Hlen.
      assert (Hpc_lt_reg : read_reg REG_PC st < length program_instrs) by (rewrite Hpc_4; lia).
      assert (Hpc_lt : 4 < length program_instrs) by (rewrite <- Hpc_4; exact Hpc_lt_reg).
      pose proof (decode_instr_program_state st Hpc_lt_reg Hprog) as Hdecode_prog.
      rewrite Hdecode_prog.
      rewrite Hpc_4.
      rewrite decode_instr_program_at_pc with (pc := 4) by exact Hpc_lt.
      reflexivity.
    }
    set (st1 := run1 st).
    assert (Hpc_st1 : read_reg REG_PC st1 = 5).
    { subst st1.
      assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_Q' REG_ADDR)).
      { unfold CPU.pc_unchanged, REG_Q', REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st _ Hdecode_pc4 Hunchanged) as Hsucc.
      rewrite Hpc_4 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hlen_st1 : length (regs st1) = 10).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = 10).
      { subst st_pc.
        apply length_regs_write_reg_10; [exact Hlen_st|].
        rewrite Hlen_st. unfold REG_PC. lia. }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; unfold REG_Q'; lia).
      apply length_regs_write_reg_10; [exact Hlen_pc|].
      exact Hq'_bound_pc.
    }
    assert (Haddr_bound : REG_ADDR < length (regs st)).
    { apply read_reg_nonzero_implies_in_bounds.
      rewrite Haddr_reg.
      unfold RULES_START_ADDR.
      lia.
    }
    assert (Hpc_bound : REG_PC < length (regs st)).
    { apply read_reg_nonzero_implies_in_bounds.
      rewrite Hpc_4.
      discriminate.
    }
    assert (Hq_bound : REG_Q < length (regs st))
      by (rewrite Hlen_st; unfold REG_Q; lia).
    assert (Hq'_bound : REG_Q' < length (regs st))
      by (rewrite Hlen_st; unfold REG_Q'; lia).
    assert (Hsym_bound : REG_SYM < length (regs st))
      by (rewrite Hlen_st; unfold REG_SYM; lia).
    assert (Hpc_bound_st1 : REG_PC < length (regs st1)).
    { rewrite Hlen_st1. unfold REG_PC. lia. }
    assert (Haddr_bound_st1 : REG_ADDR < length (regs st1)).
    { rewrite Hlen_st1. unfold REG_ADDR. lia. }
    assert (Hq_bound_st1 : REG_Q < length (regs st1)).
    { rewrite Hlen_st1. unfold REG_Q. lia. }
    assert (Hq'_bound_st1 : REG_Q' < length (regs st1)).
    { rewrite Hlen_st1. unfold REG_Q'. lia. }
    assert (Htemp1_bound_st1 : REG_TEMP1 < length (regs st1)).
    { rewrite Hlen_st1. unfold REG_TEMP1. lia. }
    assert (Hsym_bound_st1 : REG_SYM < length (regs st1)).
    { rewrite Hlen_st1. unfold REG_SYM. lia. }
    assert (Hst1_q : read_reg REG_Q st1 = q).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq_bound_pc : REG_Q < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq_bound).
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Hneq_pc_q : REG_PC <> REG_Q) by (unfold REG_PC, REG_Q; lia).
      assert (Hneq_q'_q : REG_Q' <> REG_Q) by (unfold REG_Q', REG_Q; lia).
      assert (Hq_base : read_reg REG_Q st_pc = read_reg REG_Q st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Hq_bound|exact Hneq_pc_q].
      }
        assert (Hq_pres : read_reg REG_Q (write_reg REG_Q'
                                             (read_mem (read_reg REG_ADDR st) st)
                                             st_pc) = read_reg REG_Q st_pc).
        { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Hq_bound_pc|exact Hneq_q'_q].
        }
        eapply eq_trans with (y := read_reg REG_Q st_pc).
        - exact Hq_pres.
        - rewrite Hq_base, Hq_reg. reflexivity.
    }
    assert (Hst1_addr : read_reg REG_ADDR st1 = read_reg REG_ADDR st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
      assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
        by (rewrite Hlen_pc; exact Hq'_bound).
      assert (Haddr_bound_pc : REG_ADDR < length (regs st_pc))
        by (rewrite Hlen_pc; exact Haddr_bound).
      assert (Hneq_pc_addr : REG_PC <> REG_ADDR) by (unfold REG_PC, REG_ADDR; lia).
      assert (Hneq_q'_addr : REG_Q' <> REG_ADDR) by (unfold REG_Q', REG_ADDR; lia).
      assert (Haddr_base : read_reg REG_ADDR st_pc = read_reg REG_ADDR st).
      { subst st_pc.
        apply read_reg_write_reg_other; [exact Hpc_bound|exact Haddr_bound|exact Hneq_pc_addr].
      }
      assert (Haddr_pres : read_reg REG_ADDR (write_reg REG_Q'
                                                 (read_mem (read_reg REG_ADDR st) st)
                                                 st_pc) = read_reg REG_ADDR st_pc).
      { apply read_reg_write_reg_other; [exact Hq'_bound_pc|exact Haddr_bound_pc|exact Hneq_q'_addr].
      }
      eapply eq_trans with (y := read_reg REG_ADDR st_pc).
      - exact Haddr_pres.
      - rewrite Haddr_base. reflexivity.
    }
    assert (Hmem_st1 : mem st1 = mem st).
    { subst st1.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc4; simpl; exact I.
    }
    assert (Hst1_q' : read_reg REG_Q' st1 = read_mem (read_reg REG_ADDR st) st).
    { subst st1.
      unfold run1.
      rewrite Hdecode_pc4.
      cbn [CPU.step read_reg write_reg read_mem].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st)) st).
      assert (Hlen_pc : length (regs st_pc) = length (regs st)).
      { subst st_pc.
        apply length_regs_write_reg.
        exact Hpc_bound.
      }
        assert (Hq'_bound_pc : REG_Q' < length (regs st_pc))
          by (rewrite Hlen_pc; exact Hq'_bound).
        apply (read_reg_write_reg_same st_pc REG_Q'
                 (read_mem (read_reg REG_ADDR st) st) Hq'_bound_pc).
    }
    assert (Hprog_st1 : firstn (length program) (mem st1) = program).
    { rewrite Hmem_st1. exact Hprog. }
    assert (Hpc_st1_lt : read_reg REG_PC st1 < length program_instrs).
    { rewrite Hpc_st1. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc5 : decode_instr st1 = CopyReg REG_TEMP1 REG_Q).
    { subst st1.
      pose proof (decode_instr_program_state (run1 st) Hpc_st1_lt Hprog_st1) as Hdecode_prog.
      rewrite Hpc_st1 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 5) in Hdecode_prog
        by (pose proof program_instrs_length_gt_48 as Hlen; lia).
      exact Hdecode_prog.
    }
    set (st2 := run1 st1).
    assert (Hpc_st2 : read_reg REG_PC st2 = 6).
    { subst st2.
      assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_Q)).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st1 _ Hdecode_pc5 Hunchanged) as Hsucc.
      rewrite Hpc_st1 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_st2 : mem st2 = mem st1).
    { subst st2.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc5; simpl; exact I.
    }
    assert (Hst2_addr : read_reg REG_ADDR st2 = read_reg REG_ADDR st1).
    { subst st2.
      apply (run1_preserves_reg_copyreg st1 REG_TEMP1 REG_Q REG_ADDR).
      - exact Hdecode_pc5.
      - exact Hpc_bound_st1.
      - exact Htemp1_bound_st1.
      - exact Haddr_bound_st1.
      - unfold REG_ADDR, REG_TEMP1; lia.
      - unfold REG_PC, REG_ADDR; lia.
    }
    assert (Hst2_temp1 : read_reg REG_TEMP1 st2 = read_reg REG_Q st1).
    { subst st2.
      unfold run1.
      rewrite Hdecode_pc5.
      cbn [CPU.step read_reg write_reg].
      set (st_pc := write_reg REG_PC (S (read_reg REG_PC st1)) st1).
      assert (Hlen_pc : length (regs st_pc) = 10).
      { subst st_pc.
        apply length_regs_write_reg_10; [exact Hlen_st1|].
        rewrite Hlen_st1. unfold REG_PC. lia. }
        assert (Htemp1_pc : REG_TEMP1 < length (regs st_pc))
          by (rewrite Hlen_pc; unfold REG_TEMP1; lia).
        apply (read_reg_write_reg_same st_pc REG_TEMP1 (read_reg REG_Q st1) Htemp1_pc).
    }
    assert (Hst2_q : read_reg REG_Q st2 = read_reg REG_Q st1).
    { subst st2.
      apply (run1_preserves_reg_copyreg st1 REG_TEMP1 REG_Q REG_Q).
      - exact Hdecode_pc5.
      - exact Hpc_bound_st1.
      - exact Htemp1_bound_st1.
      - exact Hq_bound_st1.
      - unfold REG_Q, REG_TEMP1; lia.
      - unfold REG_PC, REG_Q; lia.
    }
    assert (Hst2_q_val : read_reg REG_Q st2 = q) by (rewrite Hst2_q, Hst1_q; reflexivity).
    assert (Hst2_temp1_val : read_reg REG_TEMP1 st2 = q) by (rewrite Hst2_temp1, Hst1_q; reflexivity).
    assert (Hst2_q' : read_reg REG_Q' st2 = read_reg REG_Q' st1).
    { subst st2.
      apply (run1_preserves_reg_copyreg st1 REG_TEMP1 REG_Q REG_Q').
      - exact Hdecode_pc5.
      - exact Hpc_bound_st1.
      - exact Htemp1_bound_st1.
      - exact Hq'_bound_st1.
      - unfold REG_Q', REG_TEMP1; lia.
      - unfold REG_PC, REG_Q'; lia.
    }
    assert (Hlen_st2 : length (regs st2) = 10).
    { subst st2.
      apply run1_regs_length_before_apply; try assumption.
      rewrite Hpc_st1. lia. }
    assert (Hpc_bound_st2 : REG_PC < length (regs st2))
      by (rewrite Hlen_st2; unfold REG_PC; lia).
    assert (Htemp1_bound_st2 : REG_TEMP1 < length (regs st2))
      by (rewrite Hlen_st2; unfold REG_TEMP1; lia).
    assert (Hq_bound_st2 : REG_Q < length (regs st2))
      by (rewrite Hlen_st2; unfold REG_Q; lia).
    assert (Hq'_bound_st2 : REG_Q' < length (regs st2))
      by (rewrite Hlen_st2; unfold REG_Q'; lia).
    assert (Haddr_bound_st2 : REG_ADDR < length (regs st2))
      by (rewrite Hlen_st2; unfold REG_ADDR; lia).
    assert (Hsym_bound_st2 : REG_SYM < length (regs st2))
      by (rewrite Hlen_st2; unfold REG_SYM; lia).
    assert (Hprog_st2 : firstn (length program) (mem st2) = program).
    { rewrite Hmem_st2, Hmem_st1. exact Hprog. }
    assert (Hpc_st2_lt : read_reg REG_PC st2 < length program_instrs).
    { rewrite Hpc_st2. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc6 : decode_instr st2 = SubReg REG_TEMP1 REG_TEMP1 REG_Q').
    { subst st2.
      pose proof (decode_instr_program_state (run1 st1) Hpc_st2_lt Hprog_st2) as Hdecode_prog.
      pose proof Hpc_st2_lt as Hpc6_lt.
      rewrite Hpc_st2 in Hpc6_lt.
      rewrite Hpc_st2 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 6) in Hdecode_prog by exact Hpc6_lt.
      exact Hdecode_prog.
    }
    set (st3 := run1 st2).
    assert (Hpc_st3 : read_reg REG_PC st3 = 7).
    { subst st3.
      assert (Hunchanged : CPU.pc_unchanged (SubReg REG_TEMP1 REG_TEMP1 REG_Q')).
      { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
      pose proof (run1_pc_succ_instr st2 _ Hdecode_pc6 Hunchanged) as Hsucc.
      rewrite Hpc_st2 in Hsucc.
      simpl in Hsucc.
      exact Hsucc.
    }
    assert (Hmem_st3 : mem st3 = mem st2).
    { subst st3.
      apply run1_mem_preserved_if_no_store.
      rewrite Hdecode_pc6; simpl; exact I.
    }
    assert (Hst3_q : read_reg REG_Q st3 = read_reg REG_Q st2).
    { subst st3.
      apply (run1_preserves_reg_subreg st2 REG_TEMP1 REG_TEMP1 REG_Q' REG_Q).
      - exact Hdecode_pc6.
      - exact Hpc_bound_st2.
      - exact Htemp1_bound_st2.
      - exact Hq_bound_st2.
      - unfold REG_Q, REG_TEMP1; lia.
      - unfold REG_Q, REG_PC; lia.
    }
    assert (Hst3_temp1 : read_reg REG_TEMP1 st3 =
                         read_reg REG_TEMP1 st2 - read_reg REG_Q' st2).
    { subst st3.
      apply (run1_subreg_result st2 REG_TEMP1 REG_TEMP1 REG_Q').
      - exact Hdecode_pc6.
      - exact Hpc_bound_st2.
      - exact Htemp1_bound_st2.
    }
    assert (Hlen_st3 : length (regs st3) = 10).
    { subst st3.
      apply run1_regs_length_before_apply; try assumption.
      rewrite Hpc_st2. lia. }
    assert (Hpc_bound_st3 : REG_PC < length (regs st3))
      by (rewrite Hlen_st3; unfold REG_PC; lia).
    assert (Htemp1_bound_st3 : REG_TEMP1 < length (regs st3))
      by (rewrite Hlen_st3; unfold REG_TEMP1; lia).
    assert (Hq_bound_st3 : REG_Q < length (regs st3))
      by (rewrite Hlen_st3; unfold REG_Q; lia).
    assert (Hq'_bound_st3 : REG_Q' < length (regs st3))
      by (rewrite Hlen_st3; unfold REG_Q'; lia).
    assert (Hsym_bound_st3 : REG_SYM < length (regs st3))
      by (rewrite Hlen_st3; unfold REG_SYM; lia).
    assert (Haddr_bound_st3 : REG_ADDR < length (regs st3))
      by (rewrite Hlen_st3; unfold REG_ADDR; lia).
    assert (Hprog_st3 : firstn (length program) (mem st3) = program).
    { rewrite Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
    assert (Hpc_st3_lt : read_reg REG_PC st3 < length program_instrs).
    { rewrite Hpc_st3. pose proof program_instrs_length_gt_29 as Hlen. lia. }
    assert (Hdecode_pc7 : decode_instr st3 = Jz REG_TEMP1 12).
    { subst st3.
      pose proof (decode_instr_program_state (run1 st2) Hpc_st3_lt Hprog_st3) as Hdecode_prog.
      pose proof Hpc_st3_lt as Hpc7_lt.
      rewrite Hpc_st3 in Hpc7_lt.
      rewrite Hpc_st3 in Hdecode_prog.
      rewrite decode_instr_program_at_pc with (pc := 7) in Hdecode_prog by exact Hpc7_lt.
      exact Hdecode_prog.
    }
    remember (nth i (tm_rules tm) (0,0,0,0,0%Z)) as rule_i eqn:Hrule_i.
    remember (tm_rules tm) as rules eqn:Hrules.
    rename H_i_lt into H_i_lt_rules.
    assert (H_i_lt : i < length (tm_rules tm)) by (rewrite Hrules in H_i_lt_rules; exact H_i_lt_rules).
    assert (Hrule_i_rules : rule_i = nth i rules (0,0,0,0,0%Z)) by (subst rules; exact Hrule_i).
    clear Hrule_i; rename Hrule_i_rules into Hrule_i.
    remember (skipn i rules) as rules_suffix eqn:Hrules_suffix.
    destruct rule_i as [[[[q_rule sym_rule] q_next] w_next] m_next].
    pose proof (read_mem_rule_component tm ((q, tape), head) st i 0 Hinv_full H_i_lt) as Hrule_comp0.
    rewrite <- Hrules in Hrule_comp0.
    rewrite <- Hrule_i in Hrule_comp0.
    simpl in Hrule_comp0.
    destruct Hrule_comp0 as [Hcomp_q _].
    specialize (Hcomp_q eq_refl).
    rewrite Nat.add_0_r in Hcomp_q.
    assert (Hst1_q'_val : read_reg REG_Q' st1 = q_rule).
    { rewrite Hst1_q'.
      rewrite Haddr_reg.
      rewrite Nat.mul_comm.
      exact Hcomp_q.
    }
    assert (Hst2_q'_val : read_reg REG_Q' st2 = q_rule).
    { rewrite Hst2_q'. exact Hst1_q'_val. }
    assert (Hst3_temp1_val : read_reg REG_TEMP1 st3 = q - q_rule).
    { rewrite Hst3_temp1, Hst2_temp1_val, Hst2_q'_val. reflexivity. }
    pose proof (read_mem_rule_component tm ((q, tape), head) st i 1 Hinv_full H_i_lt) as Hrule_comp1.
    rewrite <- Hrules in Hrule_comp1.
    rewrite <- Hrule_i in Hrule_comp1.
    simpl in Hrule_comp1.
    destruct Hrule_comp1 as [_ [Hcomp_sym _]].
    specialize (Hcomp_sym eq_refl).
    assert (Hrule_sym_val : read_mem (RULES_START_ADDR + i * 5 + 1) st = sym_rule) by exact Hcomp_sym.
    assert (Hst1_sym : read_reg REG_SYM st1 = read_reg REG_SYM st).
    { subst st1.
      apply (run1_preserves_reg_loadindirect st REG_Q' REG_ADDR REG_SYM).
      - exact Hdecode_pc4.
      - exact Hpc_bound.
      - exact Hq'_bound.
      - exact Hsym_bound.
      - unfold REG_SYM, REG_Q'; lia.
      - unfold REG_PC, REG_SYM; lia.
    }
    assert (Hst2_sym : read_reg REG_SYM st2 = read_reg REG_SYM st1).
    { subst st2.
      apply (run1_preserves_reg_copyreg st1 REG_TEMP1 REG_Q REG_SYM).
      - exact Hdecode_pc5.
      - exact Hpc_bound_st1.
      - exact Htemp1_bound_st1.
      - exact Hsym_bound_st1.
      - unfold REG_SYM, REG_TEMP1; lia.
      - unfold REG_PC, REG_SYM; lia.
    }
    assert (Hst3_sym_reg : read_reg REG_SYM st3 = read_reg REG_SYM st2).
    { subst st3.
      apply (run1_preserves_reg_subreg st2 REG_TEMP1 REG_TEMP1 REG_Q' REG_SYM).
      - exact Hdecode_pc6.
      - exact Hpc_bound_st2.
      - exact Htemp1_bound_st2.
      - exact Hsym_bound_st2.
      - unfold REG_SYM, REG_TEMP1; lia.
      - unfold REG_SYM, REG_PC; lia.
    }
    assert (Hst3_addr : read_reg REG_ADDR st3 = read_reg REG_ADDR st2).
    { subst st3.
      apply (run1_preserves_reg_subreg st2 REG_TEMP1 REG_TEMP1 REG_Q' REG_ADDR).
      - exact Hdecode_pc6.
      - exact Hpc_bound_st2.
      - exact Htemp1_bound_st2.
      - exact Haddr_bound_st2.
      - unfold REG_ADDR, REG_TEMP1; lia.
      - unfold REG_ADDR, REG_PC; lia.
    }
    assert (Hst_sym : read_reg REG_SYM st3 = nth head tape tm.(tm_blank)).
    { rewrite Hst3_sym_reg, Hst2_sym, Hst1_sym, Hsym_reg. reflexivity. }
    pose proof (skipn_cons_nth _ rules i (0,0,0,0,0%Z) H_i_lt_rules) as Hskip_split_raw.
    rewrite <- Hrule_i in Hskip_split_raw.
    destruct (find_rule (skipn i (tm_rules tm)) q (nth head tape tm.(tm_blank))) as [[[q_next_res write_res] move_res]|] eqn:Hfind.
    - pose proof (eq_trans Hrules_suffix Hskip_split_raw) as Hskip_split_rules_some.
      pose proof Hfind as Hfind_goal.
      rewrite <- Hrules in Hfind_goal.
      rewrite <- Hrules_suffix in Hfind_goal.
      rewrite <- Hrules in Hfind.
      rewrite <- Hrules_suffix in Hfind.
      rewrite Hskip_split_rules_some in Hfind.
      simpl in Hfind.
      destruct (andb (Nat.eqb q_rule q)
                     (Nat.eqb sym_rule (nth head tape tm.(tm_blank)))) eqn:Hmatch.
      + rewrite Hfind_goal.
        simpl.
        inversion Hfind; subst q_next_res write_res move_res. clear Hfind.
        apply andb_true_iff in Hmatch as [Hq_match Hsym_match].
        apply Nat.eqb_eq in Hq_match.
        apply Nat.eqb_eq in Hsym_match.
        assert (Htemp1_zero : read_reg REG_TEMP1 st3 = 0).
        { rewrite Hst3_temp1_val, Hq_match. lia. }
        assert (Htemp1_eqb_zero : Nat.eqb (read_reg REG_TEMP1 st3) 0 = true).
        { rewrite Htemp1_zero. apply Nat.eqb_refl. }
    set (st4 := run1 st3).
    assert (Hpc_st4 : read_reg REG_PC st4 = 12).
    { subst st4.
      unfold run1.
      rewrite Hdecode_pc7.
      apply CPU.step_jz_true.
      exact Htemp1_eqb_zero.
    }
    assert (Hst4_addr : read_reg REG_ADDR st4 = read_reg REG_ADDR st3).
    { subst st4.
      apply (run1_preserves_reg_jz_true st3 REG_TEMP1 12 REG_ADDR);
        try assumption; unfold REG_ADDR, REG_TEMP1, REG_PC; lia. }
    assert (Hst4_sym : read_reg REG_SYM st4 = read_reg REG_SYM st3).
    { subst st4.
      apply (run1_preserves_reg_jz_true st3 REG_TEMP1 12 REG_SYM);
        try assumption; unfold REG_SYM, REG_TEMP1, REG_PC; lia. }
    assert (Hlen_st4 : length (regs st4) = 10).
    { subst st4.
      apply run1_regs_length_before_apply.
      - rewrite Hpc_st3. lia.
      - exact Hprog_st3.
      - exact Hlen_st3.
    }
    assert (Hpc_bound_st4 : REG_PC < length (regs st4))
      by (rewrite Hlen_st4; unfold REG_PC; lia).
    assert (Htemp1_bound_st4 : REG_TEMP1 < length (regs st4))
      by (rewrite Hlen_st4; unfold REG_TEMP1; lia).
    assert (Haddr_bound_st4 : REG_ADDR < length (regs st4))
      by (rewrite Hlen_st4; unfold REG_ADDR; lia).
    assert (Hq_bound_st4 : REG_Q < length (regs st4))
      by (rewrite Hlen_st4; unfold REG_Q; lia).
    assert (Hq'_bound_st4 : REG_Q' < length (regs st4))
      by (rewrite Hlen_st4; unfold REG_Q'; lia).
    assert (Hsym_bound_st4 : REG_SYM < length (regs st4))
      by (rewrite Hlen_st4; unfold REG_SYM; lia).
        assert (Hsym_rule_matches : sym_rule = nth head tape tm.(tm_blank)) by exact Hsym_match.
        assert (Hmem_st4 : mem st4 = mem st3).
        { subst st4.
          apply run1_mem_preserved_if_no_store.
          rewrite Hdecode_pc7; simpl; exact I.
        }
        assert (Hprog_st4 : firstn (length program) (mem st4) = program).
        { rewrite Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
        assert (Hpc_st4_lt : read_reg REG_PC st4 < length program_instrs).
        { rewrite Hpc_st4. pose proof program_instrs_length_gt_48 as Hlen. lia. }
        assert (Hdecode_pc12 : decode_instr st4 = CopyReg REG_TEMP1 REG_ADDR).
        { subst st4.
          pose proof (decode_instr_program_state (run1 st3) Hpc_st4_lt Hprog_st4) as Hdecode_prog.
          pose proof Hpc_st4_lt as Hpc12_lt.
          rewrite Hpc_st4 in Hpc12_lt.
          rewrite Hpc_st4 in Hdecode_prog.
          rewrite decode_instr_program_at_pc with (pc := 12) in Hdecode_prog by exact Hpc12_lt.
          exact Hdecode_prog.
        }
        set (st5 := run1 st4).
        assert (Hpc_st5 : read_reg REG_PC st5 = 13).
        { subst st5.
          assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_ADDR)).
          { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
          pose proof (run1_pc_succ_instr st4 _ Hdecode_pc12 Hunchanged) as Hsucc.
          rewrite Hpc_st4 in Hsucc.
          simpl in Hsucc.
          exact Hsucc.
        }
        assert (Hmem_st5 : mem st5 = mem st4).
        { subst st5.
          apply run1_mem_preserved_if_no_store.
          rewrite Hdecode_pc12; simpl; exact I.
        }
        assert (Hst5_addr : read_reg REG_ADDR st5 = read_reg REG_ADDR st4).
        { subst st5.
          apply (run1_preserves_reg_copyreg st4 REG_TEMP1 REG_ADDR REG_ADDR).
          - exact Hdecode_pc12.
          - exact Hpc_bound_st4.
          - exact Htemp1_bound_st4.
          - exact Haddr_bound_st4.
          - unfold REG_ADDR, REG_TEMP1; lia.
          - unfold REG_PC, REG_ADDR; lia.
        }
        assert (Hst5_temp1 : read_reg REG_TEMP1 st5 = read_reg REG_ADDR st4).
        { subst st5.
          apply (run1_copyreg_result st4 REG_TEMP1 REG_ADDR).
          - exact Hdecode_pc12.
          - exact Hpc_bound_st4.
          - exact Htemp1_bound_st4.
        }
        assert (Hst5_sym_pres : read_reg REG_SYM st5 = read_reg REG_SYM st4).
        { subst st5.
          apply (run1_preserves_reg_copyreg st4 REG_TEMP1 REG_ADDR REG_SYM);
            try assumption.
          all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
        }
        assert (Hlen_st5 : length (regs st5) = 10).
        { subst st5.
          apply run1_regs_length_before_apply.
          - rewrite Hpc_st4. lia.
          - exact Hprog_st4.
          - exact Hlen_st4.
        }
        assert (Hpc_bound_st5 : REG_PC < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_PC; lia).
        assert (Htemp1_bound_st5 : REG_TEMP1 < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_TEMP1; lia).
        assert (Haddr_bound_st5 : REG_ADDR < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_ADDR; lia).
        assert (Hq_bound_st5 : REG_Q < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_Q; lia).
        assert (Hq'_bound_st5 : REG_Q' < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_Q'; lia).
        assert (Hsym_bound_st5 : REG_SYM < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_SYM; lia).
        assert (Hprog_st5 : firstn (length program) (mem st5) = program).
        { rewrite Hmem_st5, Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
        assert (Hpc_st5_lt : read_reg REG_PC st5 < length program_instrs).
        { rewrite Hpc_st5. pose proof program_instrs_length_gt_48 as Hlen. lia. }
        assert (Hdecode_pc13 : decode_instr st5 = AddConst REG_TEMP1 1).
        { subst st5.
          pose proof (decode_instr_program_state (run1 st4) Hpc_st5_lt Hprog_st5) as Hdecode_prog.
          pose proof Hpc_st5_lt as Hpc13_lt.
          rewrite Hpc_st5 in Hpc13_lt.
          rewrite Hpc_st5 in Hdecode_prog.
          rewrite decode_instr_program_at_pc with (pc := 13) in Hdecode_prog by exact Hpc13_lt.
          exact Hdecode_prog.
        }
        set (st6 := run1 st5).
        assert (Hpc_st6 : read_reg REG_PC st6 = 14).
        { subst st6.
          assert (Hunchanged : CPU.pc_unchanged (AddConst REG_TEMP1 1)).
          { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
          pose proof (run1_pc_succ_instr st5 _ Hdecode_pc13 Hunchanged) as Hsucc.
          rewrite Hpc_st5 in Hsucc.
          simpl in Hsucc.
          exact Hsucc.
        }
        assert (Hmem_st6 : mem st6 = mem st5).
        { subst st6.
          apply run1_mem_preserved_if_no_store.
          rewrite Hdecode_pc13; simpl; exact I.
        }
        assert (Hlen_st6 : length (regs st6) = 10).
        { subst st6.
          apply run1_regs_length_before_apply.
          - rewrite Hpc_st5. lia.
          - exact Hprog_st5.
          - exact Hlen_st5.
        }
        assert (Hpc_bound_st6 : REG_PC < length (regs st6))
          by (rewrite Hlen_st6; unfold REG_PC; lia).
        assert (Htemp1_bound_st6 : REG_TEMP1 < length (regs st6))
          by (rewrite Hlen_st6; unfold REG_TEMP1; lia).
        assert (Htemp2_bound_st6 : REG_TEMP2 < length (regs st6))
          by (rewrite Hlen_st6; unfold REG_TEMP2; lia).
        assert (Haddr_bound_st6 : REG_ADDR < length (regs st6))
          by (rewrite Hlen_st6; unfold REG_ADDR; lia).
        assert (Hq_bound_st6 : REG_Q < length (regs st6))
          by (rewrite Hlen_st6; unfold REG_Q; lia).
        assert (Hq'_bound_st6 : REG_Q' < length (regs st6))
          by (rewrite Hlen_st6; unfold REG_Q'; lia).
        assert (Hsym_bound_st6 : REG_SYM < length (regs st6))
          by (rewrite Hlen_st6; unfold REG_SYM; lia).
        assert (Hst6_addr : read_reg REG_ADDR st6 = read_reg REG_ADDR st5).
        { subst st6.
          apply (run1_preserves_reg_addconst st5 REG_TEMP1 1 REG_ADDR);
            try assumption.
          all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
        }
        assert (Hst6_temp1 : read_reg REG_TEMP1 st6 = read_reg REG_TEMP1 st5 + 1).
        { subst st6.
          apply (run1_addconst_result st5 REG_TEMP1 1); try assumption.
        }
        assert (Hst6_sym_pres : read_reg REG_SYM st6 = read_reg REG_SYM st5).
        { subst st6.
          apply (run1_preserves_reg_addconst st5 REG_TEMP1 1 REG_SYM);
            try assumption.
          all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
        }
        assert (Htemp1_addr_offset1 : read_reg REG_TEMP1 st6 = RULES_START_ADDR + i * 5 + 1).
        { rewrite Hst6_temp1, Hst5_temp1.
          rewrite Hst4_addr, Hst3_addr, Hst2_addr, Hst1_addr, Haddr_reg.
          rewrite Nat.mul_comm.
          lia.
        }
        assert (Hprog_st6 : firstn (length program) (mem st6) = program).
        { rewrite Hmem_st6, Hmem_st5, Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
        assert (Hpc_st6_lt : read_reg REG_PC st6 < length program_instrs).
        { rewrite Hpc_st6. pose proof program_instrs_length_gt_48 as Hlen. lia. }
        assert (Hdecode_pc14 : decode_instr st6 = LoadIndirect REG_TEMP2 REG_TEMP1).
        { subst st6.
          pose proof (decode_instr_program_state (run1 st5) Hpc_st6_lt Hprog_st6) as Hdecode_prog.
          pose proof Hpc_st6 as Hpc_st6_eq.
          rewrite Hpc_st6_eq in Hdecode_prog.
          rewrite Hpc_st6_eq in Hpc_st6_lt.
          rewrite decode_instr_program_at_pc with (pc := 14) in Hdecode_prog by exact Hpc_st6_lt.
          exact Hdecode_prog.
        }
        set (st7 := run1 st6).
        assert (Hpc_st7 : read_reg REG_PC st7 = 15).
        { subst st7.
          assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_TEMP2 REG_TEMP1)).
          { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
          pose proof (run1_pc_succ_instr st6 _ Hdecode_pc14 Hunchanged) as Hsucc.
          rewrite Hpc_st6 in Hsucc.
          simpl in Hsucc.
          exact Hsucc.
        }
        assert (Hmem_st7 : mem st7 = mem st6).
        { subst st7.
          apply run1_mem_preserved_if_no_store.
          rewrite Hdecode_pc14; simpl; exact I.
        }
        assert (Hlen_st7 : length (regs st7) = 10).
        { subst st7.
          apply run1_regs_length_before_apply.
          - rewrite Hpc_st6. lia.
          - exact Hprog_st6.
          - exact Hlen_st6.
        }
        assert (Hpc_bound_st7 : REG_PC < length (regs st7))
          by (rewrite Hlen_st7; unfold REG_PC; lia).
        assert (Haddr_bound_st7 : REG_ADDR < length (regs st7))
          by (rewrite Hlen_st7; unfold REG_ADDR; lia).
        assert (Htemp1_bound_st7 : REG_TEMP1 < length (regs st7))
          by (rewrite Hlen_st7; unfold REG_TEMP1; lia).
        assert (Htemp2_bound_st7 : REG_TEMP2 < length (regs st7))
          by (rewrite Hlen_st7; unfold REG_TEMP2; lia).
        assert (Hq_bound_st7 : REG_Q < length (regs st7))
          by (rewrite Hlen_st7; unfold REG_Q; lia).
        assert (Hq'_bound_st7 : REG_Q' < length (regs st7))
          by (rewrite Hlen_st7; unfold REG_Q'; lia).
        assert (Hsym_bound_st7 : REG_SYM < length (regs st7))
          by (rewrite Hlen_st7; unfold REG_SYM; lia).
        assert (Hst7_addr : read_reg REG_ADDR st7 = read_reg REG_ADDR st6).
        { subst st7.
          apply (run1_preserves_reg_loadindirect st6 REG_TEMP2 REG_TEMP1 REG_ADDR);
            try assumption.
          all: unfold REG_ADDR, REG_TEMP2, REG_PC; lia.
        }
        assert (Hst7_temp2 : read_reg REG_TEMP2 st7 = read_mem (read_reg REG_TEMP1 st6) st6).
        { subst st7.
          apply (run1_loadindirect_result st6 REG_TEMP2 REG_TEMP1); try assumption.
        }
        assert (Hst7_sym_pres : read_reg REG_SYM st7 = read_reg REG_SYM st6).
        { subst st7.
          apply (run1_preserves_reg_loadindirect st6 REG_TEMP2 REG_TEMP1 REG_SYM);
            try assumption.
          all: unfold REG_SYM, REG_TEMP2, REG_PC; lia.
        }
        assert (Hmem_st6_to_st : mem st6 = mem st).
        { rewrite Hmem_st6, Hmem_st5, Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. reflexivity. }
        assert (Hst7_temp2_val : read_reg REG_TEMP2 st7 = sym_rule).
        { rewrite Hst7_temp2, Htemp1_addr_offset1.
          unfold read_mem.
          rewrite Hmem_st6_to_st.
          unfold read_mem in Hrule_sym_val.
          exact Hrule_sym_val.
        }
        assert (Hprog_st7 : firstn (length program) (mem st7) = program).
        { rewrite Hmem_st7, Hmem_st6, Hmem_st5, Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
        assert (Hpc_st7_lt : read_reg REG_PC st7 < length program_instrs).
        { rewrite Hpc_st7. pose proof program_instrs_length_gt_48 as Hlen. lia. }
        assert (Hdecode_pc15 : decode_instr st7 = CopyReg REG_TEMP1 REG_SYM).
        { subst st7.
          pose proof (decode_instr_program_state (run1 st6) Hpc_st7_lt Hprog_st7) as Hdecode_prog.
          pose proof Hpc_st7 as Hpc_st7_eq.
          rewrite Hpc_st7_eq in Hdecode_prog.
          rewrite Hpc_st7_eq in Hpc_st7_lt.
          rewrite decode_instr_program_at_pc with (pc := 15) in Hdecode_prog by exact Hpc_st7_lt.
          exact Hdecode_prog.
        }
        set (st8 := run1 st7).
        assert (Hpc_st8 : read_reg REG_PC st8 = 16).
        { subst st8.
          assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_SYM)).
          { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
          pose proof (run1_pc_succ_instr st7 _ Hdecode_pc15 Hunchanged) as Hsucc.
          rewrite Hpc_st7 in Hsucc.
          simpl in Hsucc.
          exact Hsucc.
        }
        assert (Hmem_st8 : mem st8 = mem st7).
        { subst st8.
          apply run1_mem_preserved_if_no_store.
          rewrite Hdecode_pc15; simpl; exact I.
        }
        assert (Hlen_st8 : length (regs st8) = 10).
        { subst st8.
          apply run1_regs_length_before_apply.
          - rewrite Hpc_st7. lia.
          - exact Hprog_st7.
          - exact Hlen_st7.
        }
        assert (Hpc_bound_st8 : REG_PC < length (regs st8))
          by (rewrite Hlen_st8; unfold REG_PC; lia).
        assert (Haddr_bound_st8 : REG_ADDR < length (regs st8))
          by (rewrite Hlen_st8; unfold REG_ADDR; lia).
        assert (Htemp1_bound_st8 : REG_TEMP1 < length (regs st8))
          by (rewrite Hlen_st8; unfold REG_TEMP1; lia).
        assert (Htemp2_bound_st8 : REG_TEMP2 < length (regs st8))
          by (rewrite Hlen_st8; unfold REG_TEMP2; lia).
        assert (Hq_bound_st8 : REG_Q < length (regs st8))
          by (rewrite Hlen_st8; unfold REG_Q; lia).
        assert (Hq'_bound_st8 : REG_Q' < length (regs st8))
          by (rewrite Hlen_st8; unfold REG_Q'; lia).
        assert (Hsym_bound_st8 : REG_SYM < length (regs st8))
          by (rewrite Hlen_st8; unfold REG_SYM; lia).
        assert (Hst8_addr : read_reg REG_ADDR st8 = read_reg REG_ADDR st7).
        { subst st8.
          apply (run1_preserves_reg_copyreg st7 REG_TEMP1 REG_SYM REG_ADDR);
            try assumption.
          all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
        }
        assert (Hst8_temp1 : read_reg REG_TEMP1 st8 = read_reg REG_SYM st7).
        { subst st8.
          apply (run1_copyreg_result st7 REG_TEMP1 REG_SYM); try assumption.
        }
        assert (Hst8_temp2_pres : read_reg REG_TEMP2 st8 = read_reg REG_TEMP2 st7).
        { subst st8.
          apply (run1_preserves_reg_copyreg st7 REG_TEMP1 REG_SYM REG_TEMP2);
            try assumption.
          all: unfold REG_TEMP2, REG_TEMP1, REG_PC; lia.
        }
        assert (Hst8_temp1_val : read_reg REG_TEMP1 st8 = nth head tape tm.(tm_blank)).
        { rewrite Hst8_temp1, Hst7_sym_pres, Hst6_sym_pres, Hst5_sym_pres,
                  Hst4_sym, Hst3_sym_reg, Hst2_sym, Hst1_sym, Hsym_reg.
          reflexivity. }
        assert (Hprog_st8 : firstn (length program) (mem st8) = program).
        { rewrite Hmem_st8, Hmem_st7, Hmem_st6, Hmem_st5, Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
        assert (Hpc_st8_lt : read_reg REG_PC st8 < length program_instrs).
        { rewrite Hpc_st8. pose proof program_instrs_length_gt_48 as Hlen. lia. }
        assert (Hdecode_pc16 : decode_instr st8 = SubReg REG_TEMP1 REG_TEMP1 REG_TEMP2).
        { subst st8.
          pose proof (decode_instr_program_state (run1 st7) Hpc_st8_lt Hprog_st8) as Hdecode_prog.
          pose proof Hpc_st8 as Hpc_st8_eq.
          rewrite Hpc_st8_eq in Hdecode_prog.
          rewrite Hpc_st8_eq in Hpc_st8_lt.
          rewrite decode_instr_program_at_pc with (pc := 16) in Hdecode_prog by exact Hpc_st8_lt.
          exact Hdecode_prog.
        }
        set (st9 := run1 st8).
        assert (Hpc_st9 : read_reg REG_PC st9 = 17).
        { subst st9.
          assert (Hunchanged : CPU.pc_unchanged (SubReg REG_TEMP1 REG_TEMP1 REG_TEMP2)).
          { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
          pose proof (run1_pc_succ_instr st8 _ Hdecode_pc16 Hunchanged) as Hsucc.
          rewrite Hpc_st8 in Hsucc.
          simpl in Hsucc.
          exact Hsucc.
        }
        assert (Hmem_st9 : mem st9 = mem st8).
        { subst st9.
          apply run1_mem_preserved_if_no_store.
          rewrite Hdecode_pc16; simpl; exact I.
        }
        assert (Hlen_st9 : length (regs st9) = 10).
        { subst st9.
          apply run1_regs_length_before_apply.
          - rewrite Hpc_st8. lia.
          - exact Hprog_st8.
          - exact Hlen_st8.
        }
        assert (Hpc_bound_st9 : REG_PC < length (regs st9))
          by (rewrite Hlen_st9; unfold REG_PC; lia).
        assert (Haddr_bound_st9 : REG_ADDR < length (regs st9))
          by (rewrite Hlen_st9; unfold REG_ADDR; lia).
        assert (Htemp1_bound_st9 : REG_TEMP1 < length (regs st9))
          by (rewrite Hlen_st9; unfold REG_TEMP1; lia).
        assert (Htemp2_bound_st9 : REG_TEMP2 < length (regs st9))
          by (rewrite Hlen_st9; unfold REG_TEMP2; lia).
        assert (Hst9_addr : read_reg REG_ADDR st9 = read_reg REG_ADDR st8).
        { subst st9.
          apply (run1_preserves_reg_subreg st8 REG_TEMP1 REG_TEMP1 REG_TEMP2 REG_ADDR);
            try assumption.
          all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
        }
        assert (Hst9_temp1 : read_reg REG_TEMP1 st9 = read_reg REG_TEMP1 st8 - read_reg REG_TEMP2 st8).
        { subst st9.
          apply (run1_subreg_result st8 REG_TEMP1 REG_TEMP1 REG_TEMP2); try assumption.
        }
        assert (Hst9_temp1_val : read_reg REG_TEMP1 st9 = 0).
        { rewrite Hst9_temp1, Hst8_temp1_val.
          rewrite Hst8_temp2_pres, Hst7_temp2_val, Hsym_rule_matches.
          lia.
        }
        assert (Hprog_st9 : firstn (length program) (mem st9) = program).
        { rewrite Hmem_st9, Hmem_st8, Hmem_st7, Hmem_st6, Hmem_st5, Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
        assert (Hpc_st9_lt : read_reg REG_PC st9 < length program_instrs).
        { rewrite Hpc_st9. pose proof program_instrs_length_gt_48 as Hlen. lia. }
        assert (Hdecode_pc17 : decode_instr st9 = Jz REG_TEMP1 22).
        { subst st9.
          pose proof (decode_instr_program_state (run1 st8) Hpc_st9_lt Hprog_st9) as Hdecode_prog.
          pose proof Hpc_st9 as Hpc_st9_eq.
          rewrite Hpc_st9_eq in Hdecode_prog.
          rewrite Hpc_st9_eq in Hpc_st9_lt.
          rewrite decode_instr_program_at_pc with (pc := 17) in Hdecode_prog by exact Hpc_st9_lt.
          exact Hdecode_prog.
        }
        assert (Htemp1_zero_pc17 : Nat.eqb (read_reg REG_TEMP1 st9) 0 = true).
        { rewrite Hst9_temp1_val. apply Nat.eqb_refl. }
        set (st10 := run1 st9).
        assert (Hpc_st10 : read_reg REG_PC st10 = 22).
        { subst st10.
          unfold run1.
          rewrite Hdecode_pc17.
          apply CPU.step_jz_true.
          exact Htemp1_zero_pc17.
        }
        assert (Hmem_st10 : mem st10 = mem st9).
        { subst st10.
          apply run1_mem_preserved_if_no_store.
          rewrite Hdecode_pc17; simpl; exact I.
        }
        assert (Hst10_addr : read_reg REG_ADDR st10 = read_reg REG_ADDR st9).
        { subst st10.
          apply (run1_preserves_reg_jz_true st9 REG_TEMP1 22 REG_ADDR);
            try assumption.
          all: unfold REG_ADDR, REG_PC; lia.
        }
        assert (Hprog_st10 : firstn (length program) (mem st10) = program).
        { rewrite Hmem_st10, Hmem_st9, Hmem_st8, Hmem_st7, Hmem_st6, Hmem_st5,
                 Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
        assert (Hpc_st10_lt : read_reg REG_PC st10 < length program_instrs).
        { rewrite Hpc_st10. pose proof program_instrs_length_gt_48 as Hlen. lia. }
        assert (Hdecode_pc22 : decode_instr st10 = CopyReg REG_TEMP1 REG_ADDR).
        { subst st10.
          pose proof (decode_instr_program_state (run1 st9) Hpc_st10_lt Hprog_st10) as Hdecode_prog.
          pose proof Hpc_st10 as Hpc_st10_eq.
          rewrite Hpc_st10_eq in Hdecode_prog.
          rewrite Hpc_st10_eq in Hpc_st10_lt.
          rewrite decode_instr_program_at_pc with (pc := 22) in Hdecode_prog by exact Hpc_st10_lt.
          exact Hdecode_prog.
        }
        assert (Hlen_st10 : length (regs st10) = 10).
        { subst st10.
          apply run1_regs_length_before_apply.
          - rewrite Hpc_st9. lia.
          - exact Hprog_st9.
          - exact Hlen_st9.
        }
        assert (Hpc_bound_st10 : REG_PC < length (regs st10))
          by (rewrite Hlen_st10; unfold REG_PC; lia).
        assert (Haddr_bound_st10 : REG_ADDR < length (regs st10))
          by (rewrite Hlen_st10; unfold REG_ADDR; lia).
        assert (Htemp1_bound_st10 : REG_TEMP1 < length (regs st10))
          by (rewrite Hlen_st10; unfold REG_TEMP1; lia).
        assert (Haddr_st10_val : read_reg REG_ADDR st10 = RULES_START_ADDR + 5 * i).
        { rewrite Hst10_addr, Hst9_addr, Hst8_addr, Hst7_addr, Hst6_addr, Hst5_addr,
                  Hst4_addr, Hst3_addr, Hst2_addr, Hst1_addr, Haddr_reg.
          reflexivity.
        }
        remember (run_n st10 7) as st17 eqn:Hst17.
        pose proof (run_apply_phase_registers_from_addr st10 Hpc_st10 Hprog_st10 Hlen_st10)
          as Happly.
        rewrite <- Hst17 in Happly.
        destruct Happly as [Hpc_st17 [Hmem_st17_base [Hq'_st17_base [Hwrite_st17_base [Hmove_st17_base Hlen_st17]]]]].
        assert (Hmem_st17 : mem st17 = mem st10) by exact Hmem_st17_base.
        assert (Hst17_q' : read_reg REG_Q' st17 = q_next).
        { rewrite Hq'_st17_base, Haddr_st10_val.
          pose proof (read_mem_rule_component tm ((q, tape), head) st i 2 Hinv_full H_i_lt) as Hcomp2.
          rewrite <- Hrules in Hcomp2.
          rewrite <- Hrule_i in Hcomp2.
          simpl in Hcomp2.
          destruct Hcomp2 as [_ [_ [Hcomp_q_next _]]].
          specialize (Hcomp_q_next eq_refl).
          rewrite (read_mem_mem_eq st10 st9 (RULES_START_ADDR + 5 * i + 2) Hmem_st10).
          rewrite (read_mem_mem_eq st9 st8 (RULES_START_ADDR + 5 * i + 2) Hmem_st9).
          rewrite (read_mem_mem_eq st8 st7 (RULES_START_ADDR + 5 * i + 2) Hmem_st8).
          rewrite (read_mem_mem_eq st7 st6 (RULES_START_ADDR + 5 * i + 2) Hmem_st7).
          rewrite (read_mem_mem_eq st6 st5 (RULES_START_ADDR + 5 * i + 2) Hmem_st6).
          rewrite (read_mem_mem_eq st5 st4 (RULES_START_ADDR + 5 * i + 2) Hmem_st5).
          rewrite (read_mem_mem_eq st4 st3 (RULES_START_ADDR + 5 * i + 2) Hmem_st4).
          rewrite (read_mem_mem_eq st3 st2 (RULES_START_ADDR + 5 * i + 2) Hmem_st3).
          rewrite (read_mem_mem_eq st2 st1 (RULES_START_ADDR + 5 * i + 2) Hmem_st2).
          rewrite (read_mem_mem_eq st1 st (RULES_START_ADDR + 5 * i + 2) Hmem_st1).
          rewrite Nat.mul_comm.
          exact Hcomp_q_next.
        }
        assert (Hst17_write : read_reg REG_WRITE st17 = w_next).
        { rewrite Hwrite_st17_base, Haddr_st10_val.
          pose proof (read_mem_rule_component tm ((q, tape), head) st i 3 Hinv_full H_i_lt) as Hcomp3.
          rewrite <- Hrules in Hcomp3.
          rewrite <- Hrule_i in Hcomp3.
          simpl in Hcomp3.
          destruct Hcomp3 as [_ [_ [_ [Hcomp_w _]]]].
          specialize (Hcomp_w eq_refl).
          rewrite (read_mem_mem_eq st10 st9 (RULES_START_ADDR + 5 * i + 3) Hmem_st10).
          rewrite (read_mem_mem_eq st9 st8 (RULES_START_ADDR + 5 * i + 3) Hmem_st9).
          rewrite (read_mem_mem_eq st8 st7 (RULES_START_ADDR + 5 * i + 3) Hmem_st8).
          rewrite (read_mem_mem_eq st7 st6 (RULES_START_ADDR + 5 * i + 3) Hmem_st7).
          rewrite (read_mem_mem_eq st6 st5 (RULES_START_ADDR + 5 * i + 3) Hmem_st6).
          rewrite (read_mem_mem_eq st5 st4 (RULES_START_ADDR + 5 * i + 3) Hmem_st5).
          rewrite (read_mem_mem_eq st4 st3 (RULES_START_ADDR + 5 * i + 3) Hmem_st4).
          rewrite (read_mem_mem_eq st3 st2 (RULES_START_ADDR + 5 * i + 3) Hmem_st3).
          rewrite (read_mem_mem_eq st2 st1 (RULES_START_ADDR + 5 * i + 3) Hmem_st2).
          rewrite (read_mem_mem_eq st1 st (RULES_START_ADDR + 5 * i + 3) Hmem_st1).
          rewrite Nat.mul_comm.
          exact Hcomp_w.
        }
        assert (Hst17_move_val : read_reg REG_MOVE st17 = encode_z m_next).
        { rewrite Hmove_st17_base, Haddr_st10_val.
          pose proof (read_mem_rule_component tm ((q, tape), head) st i 4 Hinv_full H_i_lt) as Hcomp4.
          rewrite <- Hrules in Hcomp4.
          rewrite <- Hrule_i in Hcomp4.
          simpl in Hcomp4.
          destruct Hcomp4 as [_ [_ [_ [_ Hcomp_move]]]].
          specialize (Hcomp_move eq_refl).
          rewrite (read_mem_mem_eq st10 st9 (RULES_START_ADDR + 5 * i + 4) Hmem_st10).
          rewrite (read_mem_mem_eq st9 st8 (RULES_START_ADDR + 5 * i + 4) Hmem_st9).
          rewrite (read_mem_mem_eq st8 st7 (RULES_START_ADDR + 5 * i + 4) Hmem_st8).
          rewrite (read_mem_mem_eq st7 st6 (RULES_START_ADDR + 5 * i + 4) Hmem_st7).
          rewrite (read_mem_mem_eq st6 st5 (RULES_START_ADDR + 5 * i + 4) Hmem_st6).
          rewrite (read_mem_mem_eq st5 st4 (RULES_START_ADDR + 5 * i + 4) Hmem_st5).
          rewrite (read_mem_mem_eq st4 st3 (RULES_START_ADDR + 5 * i + 4) Hmem_st4).
          rewrite (read_mem_mem_eq st3 st2 (RULES_START_ADDR + 5 * i + 4) Hmem_st3).
          rewrite (read_mem_mem_eq st2 st1 (RULES_START_ADDR + 5 * i + 4) Hmem_st2).
          rewrite (read_mem_mem_eq st1 st (RULES_START_ADDR + 5 * i + 4) Hmem_st1).
          rewrite Nat.mul_comm.
          exact Hcomp_move.
        }
        assert (Hprog_st17 : firstn (length program) (mem st17) = program).
        { rewrite Hmem_st17, Hmem_st10, Hmem_st9, Hmem_st8, Hmem_st7, Hmem_st6,
                 Hmem_st5, Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
        assert (Hrun_apply_state : IS_ApplyRule_Start (read_reg REG_PC st17)).
        { unfold IS_ApplyRule_Start. exact Hpc_st17. }
        assert (Hrun_st10 : run_n st 10 = st10).
        { unfold st10, st9, st8, st7, st6, st5, st4, st3, st2, st1.
          simpl.
          reflexivity.
        }
        assert (Hrun_st17 : run_n st 17 = st17).
        { change 17 with (10 + 7).
          rewrite run_n_add.
          rewrite Hrun_st10.
          rewrite (eq_sym Hst17).
          reflexivity.
        }
        exists st17.
        split.
        { symmetry. exact Hrun_st17. }
        { exact Hrun_apply_state. }
    + pose proof Hfind as Hfind_suffix.
      pose proof Hfind as Hfind_skipn_tail.
      simpl in Hfind_skipn_tail.
      rewrite find_rule_skipn_succ in Hfind_skipn_tail.
      pose proof (eq_trans Hrules_suffix Hskip_split_raw) as Hskip_split_rules.
      simpl in Hfind.
      destruct (andb (Nat.eqb q_rule q)
                     (Nat.eqb sym_rule (nth head tape tm.(tm_blank)))) eqn:Hmatch_none; try discriminate.
      assert (Hfind_skipn_rules_step :
                find_rule (skipn i rules) q (nth head tape tm.(tm_blank)) =
                find_rule (skipn (S i) rules) q (nth head tape tm.(tm_blank))).
      { rewrite Hskip_split_raw.
        apply find_rule_cons_mismatch.
        exact Hmatch_none.
      }
      pose proof (eq_trans Hfind_skipn_rules_step Hfind_skipn_tail) as Hfind_skipn_rules.
      pose proof Hfind_skipn_rules as Hfind_skipn.
      rewrite Hrules in Hfind_skipn.
      apply andb_false_iff in Hmatch_none.
      destruct Hmatch_none as [Hq_mismatch | Hsym_mismatch].
      * apply Nat.eqb_neq in Hq_mismatch.
        assert (Htemp1_diff : read_reg REG_TEMP1 st3 = q - q_rule) by exact Hst3_temp1_val.
        set (st4 := run1 st3).
        assert (Hpc_st4_true :
                  Nat.eqb (read_reg REG_TEMP1 st3) 0 = true ->
                  read_reg REG_PC st4 = 12).
        { intros Htemp1_zero.
          subst st4.
          unfold run1.
          rewrite Hdecode_pc7.
          apply CPU.step_jz_true.
          exact Htemp1_zero.
        }
        assert (Hpc_st4_false :
                  Nat.eqb (read_reg REG_TEMP1 st3) 0 = false ->
                  read_reg REG_PC st4 = 8).
        { intros Htemp1_nonzero.
          subst st4.
          unfold run1.
          rewrite Hdecode_pc7.
          pose proof (CPU.step_jz_false REG_TEMP1 12 st3 Htemp1_nonzero) as Hpc.
          rewrite Hpc.
          rewrite Hpc_st3.
          reflexivity.
        }
        assert (Hmem_st4 : mem st4 = mem st3).
        { subst st4.
          apply run1_mem_preserved_if_no_store.
          rewrite Hdecode_pc7; simpl; exact I.
        }
        assert (Haddr_st4 : read_reg REG_ADDR st4 = read_reg REG_ADDR st3).
        { subst st4.
          apply (run1_preserves_reg_jz_false st3 REG_TEMP1 12 REG_ADDR);
            try assumption.
          all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
        }
        pose proof (Hq_monotone i q (nth head tape tm.(tm_blank)) (q_next_res, write_res, move_res) H_i_lt) as Hq_le_raw.
        rewrite <- Hrules in Hq_le_raw.
        rewrite <- Hrule_i in Hq_le_raw.
        simpl in Hq_le_raw.
        specialize (Hq_le_raw Hfind_skipn_rules).
        assert (Hq_lt : q_rule < q) by lia.
        assert (Htemp1_nonzero : Nat.eqb (read_reg REG_TEMP1 st3) 0 = false).
        { rewrite Hst3_temp1_val.
          apply nat_eqb_sub_zero_false_of_lt.
          exact Hq_lt.
        }
        assert (Hpc_st4_false_val : read_reg REG_PC st4 = 8) by (apply Hpc_st4_false; exact Htemp1_nonzero).
        assert (Hst4_q : read_reg REG_Q st4 = read_reg REG_Q st3).
        { subst st4.
          apply (run1_preserves_reg_jz_false st3 REG_TEMP1 12 REG_Q);
            try assumption.
          all: unfold REG_Q, REG_TEMP1, REG_PC; lia.
        }
        assert (Hst4_sym : read_reg REG_SYM st4 = read_reg REG_SYM st3).
        { subst st4.
          apply (run1_preserves_reg_jz_false st3 REG_TEMP1 12 REG_SYM);
            try assumption.
          all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
        }
        assert (Hst4_temp1 : read_reg REG_TEMP1 st4 = read_reg REG_TEMP1 st3).
        { subst st4.
          apply (run1_preserves_reg_jz_false st3 REG_TEMP1 12 REG_TEMP1);
            try assumption.
          all: unfold REG_TEMP1, REG_PC; lia.
        }
        assert (Hlen_st4 : length (regs st4) = 10).
        { subst st4.
          apply run1_regs_length_before_apply.
          - rewrite Hpc_st3. lia.
          - exact Hprog_st3.
          - exact Hlen_st3.
        }
        assert (Hpc_bound_st4 : REG_PC < length (regs st4))
          by (rewrite Hlen_st4; unfold REG_PC; lia).
        assert (Htemp1_bound_st4 : REG_TEMP1 < length (regs st4))
          by (rewrite Hlen_st4; unfold REG_TEMP1; lia).
        assert (Haddr_bound_st4 : REG_ADDR < length (regs st4))
          by (rewrite Hlen_st4; unfold REG_ADDR; lia).
        assert (Hq_bound_st4 : REG_Q < length (regs st4))
          by (rewrite Hlen_st4; unfold REG_Q; lia).
        assert (Hq'_bound_st4 : REG_Q' < length (regs st4))
          by (rewrite Hlen_st4; unfold REG_Q'; lia).
        assert (Hsym_bound_st4 : REG_SYM < length (regs st4))
          by (rewrite Hlen_st4; unfold REG_SYM; lia).
        assert (Hprog_st4_false : firstn (length program) (mem st4) = program).
        { rewrite Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
        assert (Hpc_st4_false_lt : read_reg REG_PC st4 < length program_instrs).
        { rewrite Hpc_st4_false_val. pose proof program_instrs_length_gt_48 as Hlen. lia. }
        assert (Hdecode_pc8 : decode_instr st4 = AddConst REG_ADDR 5).
        { subst st4.
          pose proof (decode_instr_program_state (run1 st3) Hpc_st4_false_lt Hprog_st4_false) as Hdecode_prog.
          pose proof Hpc_st4_false_val as Hpc_st4_false_eq.
          rewrite Hpc_st4_false_eq in Hdecode_prog.
          rewrite Hpc_st4_false_eq in Hpc_st4_false_lt.
          rewrite decode_instr_program_at_pc with (pc := 8) in Hdecode_prog by exact Hpc_st4_false_lt.
          exact Hdecode_prog.
        }
        set (st5 := run1 st4).
        assert (Hpc_st5 : read_reg REG_PC st5 = 9).
        { subst st5.
          assert (Hunchanged : CPU.pc_unchanged (AddConst REG_ADDR 5)).
          { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
          pose proof (run1_pc_succ_instr st4 _ Hdecode_pc8 Hunchanged) as Hsucc.
          rewrite Hpc_st4_false_val in Hsucc.
          simpl in Hsucc.
          exact Hsucc.
        }
        assert (Hmem_st5 : mem st5 = mem st4).
        { subst st5.
          apply run1_mem_preserved_if_no_store.
          rewrite Hdecode_pc8; simpl; exact I.
        }
        assert (Haddr_st5 : read_reg REG_ADDR st5 = read_reg REG_ADDR st4 + 5).
        { subst st5.
          apply (run1_addconst_result st4 REG_ADDR 5).
          - exact Hdecode_pc8.
          - exact Hpc_bound_st4.
          - exact Haddr_bound_st4.
        }
        assert (Hst5_q : read_reg REG_Q st5 = read_reg REG_Q st4).
        { subst st5.
          apply (run1_preserves_reg_addconst st4 REG_ADDR 5 REG_Q);
            try assumption.
          all: unfold REG_Q, REG_ADDR, REG_PC; lia.
        }
        assert (Hst5_sym : read_reg REG_SYM st5 = read_reg REG_SYM st4).
        { subst st5.
          apply (run1_preserves_reg_addconst st4 REG_ADDR 5 REG_SYM);
            try assumption.
          all: unfold REG_SYM, REG_ADDR, REG_PC; lia.
        }
        assert (Hst5_temp1 : read_reg REG_TEMP1 st5 = read_reg REG_TEMP1 st4).
        { subst st5.
          apply (run1_preserves_reg_addconst st4 REG_ADDR 5 REG_TEMP1);
            try assumption.
          all: unfold REG_TEMP1, REG_ADDR, REG_PC; lia.
        }
        assert (Hlen_st5 : length (regs st5) = 10).
        { subst st5.
          apply run1_regs_length_before_apply.
          - rewrite Hpc_st4_false_val. lia.
          - exact Hprog_st4_false.
          - exact Hlen_st4.
        }
        assert (Hpc_bound_st5 : REG_PC < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_PC; lia).
        assert (Htemp1_bound_st5 : REG_TEMP1 < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_TEMP1; lia).
        assert (Haddr_bound_st5 : REG_ADDR < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_ADDR; lia).
        assert (Hq_bound_st5 : REG_Q < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_Q; lia).
        assert (Hq'_bound_st5 : REG_Q' < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_Q'; lia).
        assert (Hsym_bound_st5 : REG_SYM < length (regs st5))
          by (rewrite Hlen_st5; unfold REG_SYM; lia).
        assert (Hprog_st5 : firstn (length program) (mem st5) = program).
        { rewrite Hmem_st5, Hmem_st4, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
        assert (Hpc_st5_lt : read_reg REG_PC st5 < length program_instrs).
        { rewrite Hpc_st5. pose proof program_instrs_length_gt_48 as Hlen. lia. }
        assert (Hdecode_pc9 : decode_instr st5 = Jnz REG_TEMP1 4).
        { subst st5.
          pose proof (decode_instr_program_state (run1 st4) Hpc_st5_lt Hprog_st5) as Hdecode_prog.
          pose proof Hpc_st5 as Hpc_st5_eq.
          rewrite Hpc_st5_eq in Hdecode_prog.
          rewrite Hpc_st5_eq in Hpc_st5_lt.
          rewrite decode_instr_program_at_pc with (pc := 9) in Hdecode_prog by exact Hpc_st5_lt.
          exact Hdecode_prog.
        }
        set (st6 := run1 st5).
        assert (Htemp1_eqb_false : Nat.eqb (read_reg REG_TEMP1 st5) 0 = false).
        { rewrite Hst5_temp1, Hst4_temp1.
          exact Htemp1_nonzero.
        }
        assert (Hpc_st6 : read_reg REG_PC st6 = 4).
        { subst st6.
          unfold run1.
          rewrite Hdecode_pc9.
          apply CPU.step_jnz_false.
          exact Htemp1_eqb_false.
        }
        assert (Hmem_st6 : mem st6 = mem st5).
        { subst st6.
          apply run1_mem_preserved_if_no_store.
          rewrite Hdecode_pc9; simpl; exact I.
        }
        assert (Haddr_st6 : read_reg REG_ADDR st6 = read_reg REG_ADDR st5).
        { subst st6.
          apply (run1_preserves_reg_jnz_false st5 REG_TEMP1 4 REG_ADDR);
            try assumption.
          all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
        }
        assert (Hst6_q : read_reg REG_Q st6 = read_reg REG_Q st5).
        { subst st6.
          apply (run1_preserves_reg_jnz_false st5 REG_TEMP1 4 REG_Q);
            try assumption.
          all: unfold REG_Q, REG_TEMP1, REG_PC; lia.
        }
        assert (Hst6_sym : read_reg REG_SYM st6 = read_reg REG_SYM st5).
        { subst st6.
          apply (run1_preserves_reg_jnz_false st5 REG_TEMP1 4 REG_SYM);
            try assumption.
          all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
        }
        assert (Haddr_st6_val : read_reg REG_ADDR st6 = RULES_START_ADDR + 5 * S i).
        { rewrite Haddr_st6, Haddr_st5, Haddr_st4, Hst3_addr, Hst2_addr, Hst1_addr, Haddr_reg.
          lia.
        }
        assert (Hst6_q_val : read_reg REG_Q st6 = q).
        { rewrite Hst6_q, Hst5_q, Hst4_q, Hst3_q, Hst2_q, Hst1_q.
          reflexivity.
        }
        assert (Hst6_sym_val : read_reg REG_SYM st6 = nth head tape tm.(tm_blank)).
        { rewrite Hst6_sym, Hst5_sym, Hst4_sym.
          exact Hst_sym.
        }
        assert (Hrun_st6 : run_n st 6 = st6).
        { unfold st6, st5, st4, st3, st2, st1.
          repeat (rewrite run_n_succ).
          simpl.
          reflexivity.
        }
        rewrite Hfind_goal.
        simpl.
        exists 6.
        exists (run_n st 6).
        split; [reflexivity|].
        rewrite Hrun_st6.
        split.
        { unfold find_rule_loop_inv.
          repeat split; assumption.
        }
        { left. reflexivity. }
      * apply Nat.eqb_neq in Hsym_mismatch.
        destruct (Nat.eqb q_rule q) eqn:Hq_match_bool.
        * apply Nat.eqb_eq in Hq_match_bool.
          subst q_rule.
          assert (Htemp1_zero_sym : Nat.eqb (read_reg REG_TEMP1 st3) 0 = true).
          { rewrite Hst3_temp1_val.
            rewrite Nat.sub_diag.
            apply Nat.eqb_refl.
          }
          set (st4 := run1 st3).
          assert (Hpc_st4_sym : read_reg REG_PC st4 = 12).
          { subst st4.
            unfold run1.
            rewrite Hdecode_pc7.
            apply CPU.step_jz_true.
            exact Htemp1_zero_sym.
          }
          assert (Hmem_st4_sym : mem st4 = mem st3).
          { subst st4.
            apply run1_mem_preserved_if_no_store.
            rewrite Hdecode_pc7; simpl; exact I.
          }
          assert (Hlen_st4_sym : length (regs st4) = 10).
          { subst st4.
            unfold run1.
            rewrite Hdecode_pc7.
            cbn [CPU.step read_reg write_reg read_mem].
            rewrite Htemp1_zero_sym.
            apply length_regs_write_reg_10; [exact Hlen_st3|].
            rewrite Hlen_st3. unfold REG_PC. lia.
          }
          assert (Hpc_bound_st4_sym : REG_PC < length (regs st4))
            by (rewrite Hlen_st4_sym; unfold REG_PC; lia).
          assert (Htemp1_bound_st4_sym : REG_TEMP1 < length (regs st4))
            by (rewrite Hlen_st4_sym; unfold REG_TEMP1; lia).
          assert (Haddr_bound_st4_sym : REG_ADDR < length (regs st4))
            by (rewrite Hlen_st4_sym; unfold REG_ADDR; lia).
          assert (Hq_bound_st4_sym : REG_Q < length (regs st4))
            by (rewrite Hlen_st4_sym; unfold REG_Q; lia).
          assert (Hsym_bound_st4_sym : REG_SYM < length (regs st4))
            by (rewrite Hlen_st4_sym; unfold REG_SYM; lia).
          assert (Haddr_st4_sym : read_reg REG_ADDR st4 = read_reg REG_ADDR st3).
          { subst st4.
            apply (run1_preserves_reg_jz_true st3 REG_TEMP1 12 REG_ADDR);
              try assumption.
            all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
          }
          assert (Hprog_st4_sym : firstn (length program) (mem st4) = program).
          { rewrite Hmem_st4_sym, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
          assert (Hpc_st4_sym_lt : read_reg REG_PC st4 < length program_instrs).
          { rewrite Hpc_st4_sym. pose proof program_instrs_length_gt_48 as Hlen. lia. }
          assert (Hdecode_pc12_sym : decode_instr st4 = CopyReg REG_TEMP1 REG_ADDR).
          { subst st4.
            pose proof (decode_instr_program_state (run1 st3) Hpc_st4_sym_lt Hprog_st4_sym) as Hdecode_prog.
            rewrite decode_instr_program_at_pc with (pc := 12) in Hdecode_prog by exact Hpc_st4_sym_lt.
            exact Hdecode_prog.
          }
          set (st5 := run1 st4).
          assert (Hpc_st5_sym : read_reg REG_PC st5 = 13).
          { subst st5.
            assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_ADDR)).
            { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
            pose proof (run1_pc_succ_instr st4 _ Hdecode_pc12_sym Hunchanged) as Hsucc.
            rewrite Hpc_st4_sym in Hsucc.
            simpl in Hsucc.
            exact Hsucc.
          }
          assert (Hmem_st5_sym : mem st5 = mem st4).
          { subst st5.
            apply run1_mem_preserved_if_no_store.
            rewrite Hdecode_pc12_sym; simpl; exact I.
          }
          assert (Hlen_st5_sym : length (regs st5) = 10).
          { subst st5.
            unfold run1.
            rewrite Hdecode_pc12_sym.
            cbn [CPU.step read_reg write_reg].
            set (st_pc := write_reg REG_PC (S (read_reg REG_PC st4)) st4).
            assert (Hlen_pc : length (regs st_pc) = 10).
            { subst st_pc.
              apply length_regs_write_reg_10; [exact Hlen_st4_sym|].
              rewrite Hlen_st4_sym. unfold REG_PC. lia. }
            apply length_regs_write_reg_10; [exact Hlen_pc|].
            rewrite Hlen_pc. unfold REG_TEMP1. lia.
          }
          assert (Hpc_bound_st5_sym : REG_PC < length (regs st5))
            by (rewrite Hlen_st5_sym; unfold REG_PC; lia).
          assert (Htemp1_bound_st5_sym : REG_TEMP1 < length (regs st5))
            by (rewrite Hlen_st5_sym; unfold REG_TEMP1; lia).
          assert (Haddr_bound_st5_sym : REG_ADDR < length (regs st5))
            by (rewrite Hlen_st5_sym; unfold REG_ADDR; lia).
          assert (Hq_bound_st5_sym : REG_Q < length (regs st5))
            by (rewrite Hlen_st5_sym; unfold REG_Q; lia).
          assert (Hsym_bound_st5_sym : REG_SYM < length (regs st5))
            by (rewrite Hlen_st5_sym; unfold REG_SYM; lia).
          assert (Htemp1_st5_sym : read_reg REG_TEMP1 st5 = read_reg REG_ADDR st4).
          { subst st5.
            apply (run1_copyreg_result st4 REG_TEMP1 REG_ADDR);
              try assumption.
            exact Htemp1_bound_st4_sym.
          }
          assert (Haddr_st5_sym : read_reg REG_ADDR st5 = read_reg REG_ADDR st4).
          { subst st5.
            apply (run1_preserves_reg_copyreg st4 REG_TEMP1 REG_ADDR REG_ADDR);
              try assumption.
            all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
          }
          assert (Hprog_st5_sym : firstn (length program) (mem st5) = program).
          { rewrite Hmem_st5_sym, Hmem_st4_sym, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
          assert (Hpc_st5_sym_lt : read_reg REG_PC st5 < length program_instrs).
          { rewrite Hpc_st5_sym. pose proof program_instrs_length_gt_48 as Hlen. lia. }
          assert (Hdecode_pc13_sym : decode_instr st5 = AddConst REG_TEMP1 1).
          { subst st5.
            pose proof (decode_instr_program_state (run1 st4) Hpc_st5_sym_lt Hprog_st5_sym) as Hdecode_prog.
            rewrite decode_instr_program_at_pc with (pc := 13) in Hdecode_prog by exact Hpc_st5_sym_lt.
            exact Hdecode_prog.
          }
          set (st6 := run1 st5).
          assert (Hpc_st6_sym : read_reg REG_PC st6 = 14).
          { subst st6.
            assert (Hunchanged : CPU.pc_unchanged (AddConst REG_TEMP1 1)).
            { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
            pose proof (run1_pc_succ_instr st5 _ Hdecode_pc13_sym Hunchanged) as Hsucc.
            rewrite Hpc_st5_sym in Hsucc.
            simpl in Hsucc.
            exact Hsucc.
          }
          assert (Hmem_st6_sym : mem st6 = mem st5).
          { subst st6.
            apply run1_mem_preserved_if_no_store.
            rewrite Hdecode_pc13_sym; simpl; exact I.
          }
          assert (Hlen_st6_sym : length (regs st6) = 10).
          { subst st6.
            unfold run1.
            rewrite Hdecode_pc13_sym.
            cbn [CPU.step read_reg write_reg].
            set (st_pc := write_reg REG_PC (S (read_reg REG_PC st5)) st5).
            assert (Hlen_pc : length (regs st_pc) = 10).
            { subst st_pc.
              apply length_regs_write_reg_10; [exact Hlen_st5_sym|].
              rewrite Hlen_st5_sym. unfold REG_PC. lia. }
            apply length_regs_write_reg_10; [exact Hlen_pc|].
            rewrite Hlen_pc. unfold REG_TEMP1. lia.
          }
          assert (Hpc_bound_st6_sym : REG_PC < length (regs st6))
            by (rewrite Hlen_st6_sym; unfold REG_PC; lia).
          assert (Htemp1_bound_st6_sym : REG_TEMP1 < length (regs st6))
            by (rewrite Hlen_st6_sym; unfold REG_TEMP1; lia).
          assert (Haddr_bound_st6_sym : REG_ADDR < length (regs st6))
            by (rewrite Hlen_st6_sym; unfold REG_ADDR; lia).
          assert (Hq_bound_st6_sym : REG_Q < length (regs st6))
            by (rewrite Hlen_st6_sym; unfold REG_Q; lia).
          assert (Hsym_bound_st6_sym : REG_SYM < length (regs st6))
            by (rewrite Hlen_st6_sym; unfold REG_SYM; lia).
          assert (Htemp2_bound_st6_sym : REG_TEMP2 < length (regs st6))
            by (rewrite Hlen_st6_sym; unfold REG_TEMP2; lia).
          assert (Htemp1_st6_sym : read_reg REG_TEMP1 st6 = read_reg REG_TEMP1 st5 + 1).
          { subst st6.
            apply (run1_addconst_result st5 REG_TEMP1 1);
              try assumption.
            exact Htemp1_bound_st5_sym.
          }
          assert (Haddr_st6_sym : read_reg REG_ADDR st6 = read_reg REG_ADDR st5).
          { subst st6.
            apply (run1_preserves_reg_addconst st5 REG_TEMP1 1 REG_ADDR);
              try assumption.
            all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
          }
          assert (Hprog_st6_sym : firstn (length program) (mem st6) = program).
          { rewrite Hmem_st6_sym, Hmem_st5_sym, Hmem_st4_sym, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
          assert (Hpc_st6_sym_lt : read_reg REG_PC st6 < length program_instrs).
          { rewrite Hpc_st6_sym. pose proof program_instrs_length_gt_48 as Hlen. lia. }
          assert (Hdecode_pc14_sym : decode_instr st6 = LoadIndirect REG_TEMP2 REG_TEMP1).
          { subst st6.
            pose proof (decode_instr_program_state (run1 st5) Hpc_st6_sym_lt Hprog_st6_sym) as Hdecode_prog.
            rewrite decode_instr_program_at_pc with (pc := 14) in Hdecode_prog by exact Hpc_st6_sym_lt.
            exact Hdecode_prog.
          }
          set (st7 := run1 st6).
          assert (Hpc_st7_sym : read_reg REG_PC st7 = 15).
          { subst st7.
            assert (Hunchanged : CPU.pc_unchanged (LoadIndirect REG_TEMP2 REG_TEMP1)).
            { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
            pose proof (run1_pc_succ_instr st6 _ Hdecode_pc14_sym Hunchanged) as Hsucc.
            rewrite Hpc_st6_sym in Hsucc.
            simpl in Hsucc.
            exact Hsucc.
          }
          assert (Hmem_st7_sym : mem st7 = mem st6).
          { subst st7.
            apply run1_mem_preserved_if_no_store.
            rewrite Hdecode_pc14_sym; simpl; exact I.
          }
          assert (Hlen_st7_sym : length (regs st7) = 10).
          { subst st7.
            unfold run1.
            rewrite Hdecode_pc14_sym.
            cbn [CPU.step read_reg write_reg read_mem].
            set (st_pc := write_reg REG_PC (S (read_reg REG_PC st6)) st6).
            assert (Hlen_pc : length (regs st_pc) = 10).
            { subst st_pc.
              apply length_regs_write_reg_10; [exact Hlen_st6_sym|].
              rewrite Hlen_st6_sym. unfold REG_PC. lia. }
            apply length_regs_write_reg_10; [exact Hlen_pc|].
            rewrite Hlen_pc. unfold REG_TEMP2. lia.
          }
          assert (Hpc_bound_st7_sym : REG_PC < length (regs st7))
            by (rewrite Hlen_st7_sym; unfold REG_PC; lia).
          assert (Htemp1_bound_st7_sym : REG_TEMP1 < length (regs st7))
            by (rewrite Hlen_st7_sym; unfold REG_TEMP1; lia).
          assert (Htemp2_bound_st7_sym : REG_TEMP2 < length (regs st7))
            by (rewrite Hlen_st7_sym; unfold REG_TEMP2; lia).
          assert (Haddr_bound_st7_sym : REG_ADDR < length (regs st7))
            by (rewrite Hlen_st7_sym; unfold REG_ADDR; lia).
          assert (Hq_bound_st7_sym : REG_Q < length (regs st7))
            by (rewrite Hlen_st7_sym; unfold REG_Q; lia).
          assert (Hsym_bound_st7_sym : REG_SYM < length (regs st7))
            by (rewrite Hlen_st7_sym; unfold REG_SYM; lia).
          assert (Htemp2_st7_sym : read_reg REG_TEMP2 st7 = read_mem (read_reg REG_TEMP1 st6) st6).
          { subst st7.
            apply (run1_loadindirect_result st6 REG_TEMP2 REG_TEMP1);
              try assumption.
            exact Htemp2_bound_st6_sym.
          }
          assert (Haddr_st7_sym : read_reg REG_ADDR st7 = read_reg REG_ADDR st6).
          { subst st7.
            apply (run1_preserves_reg_loadindirect st6 REG_TEMP2 REG_TEMP1 REG_ADDR);
              try assumption.
            all: unfold REG_ADDR, REG_TEMP2, REG_PC; lia.
          }
          assert (Hprog_st7_sym : firstn (length program) (mem st7) = program).
          { rewrite Hmem_st7_sym, Hmem_st6_sym, Hmem_st5_sym, Hmem_st4_sym, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
          assert (Hpc_st7_sym_lt : read_reg REG_PC st7 < length program_instrs).
          { rewrite Hpc_st7_sym. pose proof program_instrs_length_gt_48 as Hlen. lia. }
          assert (Hdecode_pc15_sym : decode_instr st7 = CopyReg REG_TEMP1 REG_SYM).
          { subst st7.
            pose proof (decode_instr_program_state (run1 st6) Hpc_st7_sym_lt Hprog_st7_sym) as Hdecode_prog.
            rewrite decode_instr_program_at_pc with (pc := 15) in Hdecode_prog by exact Hpc_st7_sym_lt.
            exact Hdecode_prog.
          }
          set (st8 := run1 st7).
          assert (Hpc_st8_sym : read_reg REG_PC st8 = 16).
          { subst st8.
            assert (Hunchanged : CPU.pc_unchanged (CopyReg REG_TEMP1 REG_SYM)).
            { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
            pose proof (run1_pc_succ_instr st7 _ Hdecode_pc15_sym Hunchanged) as Hsucc.
            rewrite Hpc_st7_sym in Hsucc.
            simpl in Hsucc.
            exact Hsucc.
          }
          assert (Hmem_st8_sym : mem st8 = mem st7).
          { subst st8.
            apply run1_mem_preserved_if_no_store.
            rewrite Hdecode_pc15_sym; simpl; exact I.
          }
          assert (Hlen_st8_sym : length (regs st8) = 10).
          { subst st8.
            unfold run1.
            rewrite Hdecode_pc15_sym.
            cbn [CPU.step read_reg write_reg].
            set (st_pc := write_reg REG_PC (S (read_reg REG_PC st7)) st7).
            assert (Hlen_pc : length (regs st_pc) = 10).
            { subst st_pc.
              apply length_regs_write_reg_10; [exact Hlen_st7_sym|].
              rewrite Hlen_st7_sym. unfold REG_PC. lia. }
            apply length_regs_write_reg_10; [exact Hlen_pc|].
            rewrite Hlen_pc. unfold REG_TEMP1. lia.
          }
          assert (Hpc_bound_st8_sym : REG_PC < length (regs st8))
            by (rewrite Hlen_st8_sym; unfold REG_PC; lia).
          assert (Htemp1_bound_st8_sym : REG_TEMP1 < length (regs st8))
            by (rewrite Hlen_st8_sym; unfold REG_TEMP1; lia).
          assert (Haddr_bound_st8_sym : REG_ADDR < length (regs st8))
            by (rewrite Hlen_st8_sym; unfold REG_ADDR; lia).
          assert (Hq_bound_st8_sym : REG_Q < length (regs st8))
            by (rewrite Hlen_st8_sym; unfold REG_Q; lia).
          assert (Hsym_bound_st8_sym : REG_SYM < length (regs st8))
            by (rewrite Hlen_st8_sym; unfold REG_SYM; lia).
          assert (Htemp1_st8_sym : read_reg REG_TEMP1 st8 = read_reg REG_SYM st7).
          { subst st8.
            apply (run1_copyreg_result st7 REG_TEMP1 REG_SYM);
              try assumption.
            exact Htemp1_bound_st7_sym.
          }
          assert (Htemp1_st8_val : read_reg REG_TEMP1 st8 = nth head tape tm.(tm_blank)).
          { rewrite Htemp1_st8_sym, Hst3_sym_reg, Hst2_sym, Hst1_sym, Hsym_reg. reflexivity. }
          assert (Haddr_st8_sym : read_reg REG_ADDR st8 = read_reg REG_ADDR st7).
          { subst st8.
            apply (run1_preserves_reg_copyreg st7 REG_TEMP1 REG_SYM REG_ADDR);
              try assumption.
            all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
          }
          assert (Hprog_st8_sym : firstn (length program) (mem st8) = program).
          { rewrite Hmem_st8_sym, Hmem_st7_sym, Hmem_st6_sym, Hmem_st5_sym, Hmem_st4_sym, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
          assert (Hpc_st8_sym_lt : read_reg REG_PC st8 < length program_instrs).
          { rewrite Hpc_st8_sym. pose proof program_instrs_length_gt_48 as Hlen. lia. }
          assert (Hdecode_pc16_sym : decode_instr st8 = SubReg REG_TEMP1 REG_TEMP1 REG_TEMP2).
          { subst st8.
            pose proof (decode_instr_program_state (run1 st7) Hpc_st8_sym_lt Hprog_st8_sym) as Hdecode_prog.
            rewrite decode_instr_program_at_pc with (pc := 16) in Hdecode_prog by exact Hpc_st8_sym_lt.
            exact Hdecode_prog.
          }
          set (st9 := run1 st8).
          assert (Hpc_st9_sym : read_reg REG_PC st9 = 17).
          { subst st9.
            assert (Hunchanged : CPU.pc_unchanged (SubReg REG_TEMP1 REG_TEMP1 REG_TEMP2)).
            { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
            pose proof (run1_pc_succ_instr st8 _ Hdecode_pc16_sym Hunchanged) as Hsucc.
            rewrite Hpc_st8_sym in Hsucc.
            simpl in Hsucc.
            exact Hsucc.
          }
          assert (Hmem_st9_sym : mem st9 = mem st8).
          { subst st9.
            apply run1_mem_preserved_if_no_store.
            rewrite Hdecode_pc16_sym; simpl; exact I.
          }
          assert (Hlen_st9_sym : length (regs st9) = 10).
          { subst st9.
            unfold run1.
            rewrite Hdecode_pc16_sym.
            cbn [CPU.step read_reg write_reg].
            set (st_pc := write_reg REG_PC (S (read_reg REG_PC st8)) st8).
            assert (Hlen_pc : length (regs st_pc) = 10).
            { subst st_pc.
              apply length_regs_write_reg_10; [exact Hlen_st8_sym|].
              rewrite Hlen_st8_sym. unfold REG_PC. lia. }
            apply length_regs_write_reg_10; [exact Hlen_pc|].
            rewrite Hlen_pc. unfold REG_TEMP1. lia.
          }
          assert (Hpc_bound_st9_sym : REG_PC < length (regs st9))
            by (rewrite Hlen_st9_sym; unfold REG_PC; lia).
          assert (Htemp1_bound_st9_sym : REG_TEMP1 < length (regs st9))
            by (rewrite Hlen_st9_sym; unfold REG_TEMP1; lia).
          assert (Htemp2_bound_st9_sym : REG_TEMP2 < length (regs st9))
            by (rewrite Hlen_st9_sym; unfold REG_TEMP2; lia).
          assert (Haddr_bound_st9_sym : REG_ADDR < length (regs st9))
            by (rewrite Hlen_st9_sym; unfold REG_ADDR; lia).
          assert (Hq_bound_st9_sym : REG_Q < length (regs st9))
            by (rewrite Hlen_st9_sym; unfold REG_Q; lia).
          assert (Hsym_bound_st9_sym : REG_SYM < length (regs st9))
            by (rewrite Hlen_st9_sym; unfold REG_SYM; lia).
          assert (Htemp1_st9_sym : read_reg REG_TEMP1 st9 = read_reg REG_TEMP1 st8 - read_reg REG_TEMP2 st8).
          { subst st9.
            apply (run1_subreg_result st8 REG_TEMP1 REG_TEMP1 REG_TEMP2);
              try assumption.
            exact Htemp1_bound_st8_sym.
          }
          assert (Htemp1_st9_val : read_reg REG_TEMP1 st9 = nth head tape tm.(tm_blank) - sym_rule).
          { rewrite Htemp1_st9_sym, Htemp1_st8_val.
            rewrite Htemp2_st7_sym.
            unfold read_mem.
            rewrite Hmem_st6_sym, Hmem_st5_sym, Hmem_st4_sym, Hmem_st3, Hmem_st2, Hmem_st1.
            pose proof (read_mem_rule_component tm ((q, tape), head) st i 1 Hinv_full H_i_lt) as Hcomp1.
            rewrite Hrule_i in Hcomp1.
            simpl in Hcomp1.
            destruct Hcomp1 as [_ [Hsym_comp _]].
            specialize (Hsym_comp eq_refl).
            unfold read_mem in Hsym_comp.
            rewrite Haddr_reg in Hsym_comp.
            rewrite Nat.mul_comm in Hsym_comp.
            exact Hsym_comp.
          }
          pose proof (Hsym_monotone i q (nth head tape tm.(tm_blank)) (q_next_res, write_res, move_res) H_i_lt) as Hsym_le_raw.
          rewrite <- Hrules in Hsym_le_raw.
          rewrite <- Hrule_i in Hsym_le_raw.
          simpl in Hsym_le_raw.
          specialize (Hsym_le_raw Hq_match_bool Hfind_skipn_rules).
          assert (Hsym_lt : sym_rule < nth head tape tm.(tm_blank)).
          { apply Nat.lt_of_le_of_ne with (y := nth head tape tm.(tm_blank)); [exact Hsym_le_raw|].
            symmetry.
            exact Hsym_mismatch.
          }
          assert (Htemp1_nonzero_sym : Nat.eqb (read_reg REG_TEMP1 st9) 0 = false).
          { rewrite Htemp1_st9_val.
            apply nat_eqb_sub_zero_false_of_lt.
            exact Hsym_lt.
          }
          assert (Hst4_q_sym : read_reg REG_Q st4 = read_reg REG_Q st3).
          { subst st4.
            apply (run1_preserves_reg_jz_true st3 REG_TEMP1 12 REG_Q);
              try assumption.
            all: unfold REG_Q, REG_TEMP1, REG_PC; lia.
          }
          assert (Hst4_sym_sym : read_reg REG_SYM st4 = read_reg REG_SYM st3).
          { subst st4.
            apply (run1_preserves_reg_jz_true st3 REG_TEMP1 12 REG_SYM);
              try assumption.
            all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
          }
          assert (Hst5_q_sym : read_reg REG_Q st5 = read_reg REG_Q st4).
          { subst st5.
            apply (run1_preserves_reg_copyreg st4 REG_TEMP1 REG_ADDR REG_Q);
              try assumption.
            all: unfold REG_Q, REG_TEMP1, REG_PC; lia.
          }
          assert (Hst5_sym_sym : read_reg REG_SYM st5 = read_reg REG_SYM st4).
          { subst st5.
            apply (run1_preserves_reg_copyreg st4 REG_TEMP1 REG_ADDR REG_SYM);
              try assumption.
            all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
          }
          assert (Hst6_q_sym : read_reg REG_Q st6 = read_reg REG_Q st5).
          { subst st6.
            apply (run1_preserves_reg_addconst st5 REG_TEMP1 1 REG_Q);
              try assumption.
            all: unfold REG_Q, REG_TEMP1, REG_PC; lia.
          }
          assert (Hst6_sym_sym : read_reg REG_SYM st6 = read_reg REG_SYM st5).
          { subst st6.
            apply (run1_preserves_reg_addconst st5 REG_TEMP1 1 REG_SYM);
              try assumption.
            all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
          }
          assert (Hst7_q_sym : read_reg REG_Q st7 = read_reg REG_Q st6).
          { subst st7.
            apply (run1_preserves_reg_loadindirect st6 REG_TEMP2 REG_TEMP1 REG_Q);
              try assumption.
            all: unfold REG_Q, REG_TEMP2, REG_PC; lia.
          }
          assert (Hst7_sym_sym : read_reg REG_SYM st7 = read_reg REG_SYM st6).
          { subst st7.
            apply (run1_preserves_reg_loadindirect st6 REG_TEMP2 REG_TEMP1 REG_SYM);
              try assumption.
            all: unfold REG_SYM, REG_TEMP2, REG_PC; lia.
          }
          assert (Hst8_q_sym : read_reg REG_Q st8 = read_reg REG_Q st7).
          { subst st8.
            apply (run1_preserves_reg_copyreg st7 REG_TEMP1 REG_SYM REG_Q);
              try assumption.
            all: unfold REG_Q, REG_TEMP1, REG_PC; lia.
          }
          assert (Hst8_sym_sym : read_reg REG_SYM st8 = read_reg REG_SYM st7).
          { subst st8.
            apply (run1_preserves_reg_copyreg st7 REG_TEMP1 REG_SYM REG_SYM);
              try assumption.
            all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
          }
          assert (Haddr_st9_sym : read_reg REG_ADDR st9 = read_reg REG_ADDR st8).
          { subst st9.
            apply (run1_preserves_reg_subreg st8 REG_TEMP1 REG_TEMP1 REG_TEMP2 REG_ADDR);
              try assumption.
            all: unfold REG_ADDR, REG_TEMP1, REG_TEMP2, REG_PC; lia.
          }
          assert (Hst9_q_sym : read_reg REG_Q st9 = read_reg REG_Q st8).
          { subst st9.
            apply (run1_preserves_reg_subreg st8 REG_TEMP1 REG_TEMP1 REG_TEMP2 REG_Q);
              try assumption.
            all: unfold REG_Q, REG_TEMP1, REG_TEMP2, REG_PC; lia.
          }
          assert (Hst9_sym_sym : read_reg REG_SYM st9 = read_reg REG_SYM st8).
          { subst st9.
            apply (run1_preserves_reg_subreg st8 REG_TEMP1 REG_TEMP1 REG_TEMP2 REG_SYM);
              try assumption.
            all: unfold REG_SYM, REG_TEMP1, REG_TEMP2, REG_PC; lia.
          }
          assert (Hprog_st9_sym : firstn (length program) (mem st9) = program).
          { rewrite Hmem_st9_sym, Hmem_st8_sym, Hmem_st7_sym, Hmem_st6_sym, Hmem_st5_sym,
                   Hmem_st4_sym, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
          assert (Hpc_st9_sym_lt : read_reg REG_PC st9 < length program_instrs).
          { rewrite Hpc_st9_sym. pose proof program_instrs_length_gt_48 as Hlen. lia. }
          assert (Hdecode_pc17_sym : decode_instr st9 = Jz REG_TEMP1 22).
          { subst st9.
            pose proof (decode_instr_program_state (run1 st8) Hpc_st9_sym_lt Hprog_st9_sym) as Hdecode_prog.
            rewrite decode_instr_program_at_pc with (pc := 17) in Hdecode_prog by exact Hpc_st9_sym_lt.
            exact Hdecode_prog.
          }
          set (st10 := run1 st9).
          assert (Hpc_st10_sym : read_reg REG_PC st10 = 18).
          { subst st10.
            unfold run1.
            rewrite Hdecode_pc17_sym.
            pose proof (CPU.step_jz_false REG_TEMP1 22 st9 Htemp1_nonzero_sym) as Hpc.
            rewrite Hpc.
            rewrite Hpc_st9_sym.
            reflexivity.
          }
          assert (Hmem_st10_sym : mem st10 = mem st9).
          { subst st10.
            apply run1_mem_preserved_if_no_store.
            rewrite Hdecode_pc17_sym; simpl; exact I.
          }
          assert (Hlen_st10_sym : length (regs st10) = 10).
          { subst st10.
            unfold run1.
            rewrite Hdecode_pc17_sym.
            cbn [CPU.step read_reg write_reg read_mem].
            rewrite Htemp1_nonzero_sym.
            apply length_regs_write_reg_10; [exact Hlen_st9_sym|].
            rewrite Hlen_st9_sym. unfold REG_PC. lia.
          }
          assert (Hpc_bound_st10_sym : REG_PC < length (regs st10))
            by (rewrite Hlen_st10_sym; unfold REG_PC; lia).
          assert (Haddr_bound_st10_sym : REG_ADDR < length (regs st10))
            by (rewrite Hlen_st10_sym; unfold REG_ADDR; lia).
          assert (Hq_bound_st10_sym : REG_Q < length (regs st10))
            by (rewrite Hlen_st10_sym; unfold REG_Q; lia).
          assert (Hsym_bound_st10_sym : REG_SYM < length (regs st10))
            by (rewrite Hlen_st10_sym; unfold REG_SYM; lia).
          assert (Haddr_st10_sym : read_reg REG_ADDR st10 = read_reg REG_ADDR st9).
          { subst st10.
            apply (run1_preserves_reg_jz_false st9 REG_TEMP1 22 REG_ADDR);
              try assumption.
            all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
          }
          assert (Hq_st10_sym : read_reg REG_Q st10 = read_reg REG_Q st9).
          { subst st10.
            apply (run1_preserves_reg_jz_false st9 REG_TEMP1 22 REG_Q);
              try assumption.
            all: unfold REG_Q, REG_TEMP1, REG_PC; lia.
          }
          assert (Hsym_st10_sym : read_reg REG_SYM st10 = read_reg REG_SYM st9).
          { subst st10.
            apply (run1_preserves_reg_jz_false st9 REG_TEMP1 22 REG_SYM);
              try assumption.
            all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
          }
          assert (Hprog_st10_sym : firstn (length program) (mem st10) = program).
          { rewrite Hmem_st10_sym, Hmem_st9_sym, Hmem_st8_sym, Hmem_st7_sym, Hmem_st6_sym,
                   Hmem_st5_sym, Hmem_st4_sym, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
          assert (Hpc_st10_sym_lt : read_reg REG_PC st10 < length program_instrs).
          { rewrite Hpc_st10_sym. pose proof program_instrs_length_gt_48 as Hlen. lia. }
          assert (Hdecode_pc18_sym : decode_instr st10 = AddConst REG_ADDR 5).
          { subst st10.
            pose proof (decode_instr_program_state (run1 st9) Hpc_st10_sym_lt Hprog_st10_sym) as Hdecode_prog.
            rewrite decode_instr_program_at_pc with (pc := 18) in Hdecode_prog by exact Hpc_st10_sym_lt.
            exact Hdecode_prog.
          }
          set (st11 := run1 st10).
          assert (Hpc_st11_sym : read_reg REG_PC st11 = 19).
          { subst st11.
            assert (Hunchanged : CPU.pc_unchanged (AddConst REG_ADDR 5)).
            { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
            pose proof (run1_pc_succ_instr st10 _ Hdecode_pc18_sym Hunchanged) as Hsucc.
            rewrite Hpc_st10_sym in Hsucc.
            simpl in Hsucc.
            exact Hsucc.
          }
          assert (Hmem_st11_sym : mem st11 = mem st10).
          { subst st11.
            apply run1_mem_preserved_if_no_store.
            rewrite Hdecode_pc18_sym; simpl; exact I.
          }
          assert (Hlen_st11_sym : length (regs st11) = 10).
          { subst st11.
            unfold run1.
            rewrite Hdecode_pc18_sym.
            cbn [CPU.step read_reg write_reg].
            set (st_pc := write_reg REG_PC (S (read_reg REG_PC st10)) st10).
            assert (Hlen_pc : length (regs st_pc) = 10).
            { subst st_pc.
              apply length_regs_write_reg_10; [exact Hlen_st10_sym|].
              rewrite Hlen_st10_sym. unfold REG_PC. lia. }
            apply length_regs_write_reg_10; [exact Hlen_pc|].
            rewrite Hlen_pc. unfold REG_ADDR. lia.
          }
          assert (Hpc_bound_st11_sym : REG_PC < length (regs st11))
            by (rewrite Hlen_st11_sym; unfold REG_PC; lia).
          assert (Haddr_bound_st11_sym : REG_ADDR < length (regs st11))
            by (rewrite Hlen_st11_sym; unfold REG_ADDR; lia).
          assert (Htemp1_bound_st11_sym : REG_TEMP1 < length (regs st11))
            by (rewrite Hlen_st11_sym; unfold REG_TEMP1; lia).
          assert (Hq_bound_st11_sym : REG_Q < length (regs st11))
            by (rewrite Hlen_st11_sym; unfold REG_Q; lia).
          assert (Hsym_bound_st11_sym : REG_SYM < length (regs st11))
            by (rewrite Hlen_st11_sym; unfold REG_SYM; lia).
          assert (Haddr_st11_sym : read_reg REG_ADDR st11 = read_reg REG_ADDR st10 + 5).
          { subst st11.
            apply (run1_addconst_result st10 REG_ADDR 5);
              try assumption.
            exact Haddr_bound_st10_sym.
          }
          assert (Hq_st11_sym : read_reg REG_Q st11 = read_reg REG_Q st10).
          { subst st11.
            apply (run1_preserves_reg_addconst st10 REG_ADDR 5 REG_Q);
              try assumption.
            all: unfold REG_Q, REG_ADDR, REG_PC; lia.
          }
          assert (Hsym_st11_sym : read_reg REG_SYM st11 = read_reg REG_SYM st10).
          { subst st11.
            apply (run1_preserves_reg_addconst st10 REG_ADDR 5 REG_SYM);
              try assumption.
            all: unfold REG_SYM, REG_ADDR, REG_PC; lia.
          }
          assert (Hprog_st11_sym : firstn (length program) (mem st11) = program).
          { rewrite Hmem_st11_sym, Hmem_st10_sym, Hmem_st9_sym, Hmem_st8_sym, Hmem_st7_sym,
                   Hmem_st6_sym, Hmem_st5_sym, Hmem_st4_sym, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
          assert (Hpc_st11_sym_lt : read_reg REG_PC st11 < length program_instrs).
          { rewrite Hpc_st11_sym. pose proof program_instrs_length_gt_48 as Hlen. lia. }
          assert (Hdecode_pc19_sym : decode_instr st11 = LoadConst REG_TEMP1 1).
          { subst st11.
            pose proof (decode_instr_program_state (run1 st10) Hpc_st11_sym_lt Hprog_st11_sym) as Hdecode_prog.
            rewrite decode_instr_program_at_pc with (pc := 19) in Hdecode_prog by exact Hpc_st11_sym_lt.
            exact Hdecode_prog.
          }
          set (st12 := run1 st11).
          assert (Hpc_st12_sym : read_reg REG_PC st12 = 20).
          { subst st12.
            assert (Hunchanged : CPU.pc_unchanged (LoadConst REG_TEMP1 1)).
            { unfold CPU.pc_unchanged, REG_PC. simpl. congruence. }
            pose proof (run1_pc_succ_instr st11 _ Hdecode_pc19_sym Hunchanged) as Hsucc.
            rewrite Hpc_st11_sym in Hsucc.
            simpl in Hsucc.
            exact Hsucc.
          }
          assert (Hmem_st12_sym : mem st12 = mem st11).
          { subst st12.
            apply run1_mem_preserved_if_no_store.
            rewrite Hdecode_pc19_sym; simpl; exact I.
          }
          assert (Hlen_st12_sym : length (regs st12) = 10).
          { subst st12.
            unfold run1.
            rewrite Hdecode_pc19_sym.
            cbn [CPU.step read_reg write_reg].
            set (st_pc := write_reg REG_PC (S (read_reg REG_PC st11)) st11).
            assert (Hlen_pc : length (regs st_pc) = 10).
            { subst st_pc.
              apply length_regs_write_reg_10; [exact Hlen_st11_sym|].
              rewrite Hlen_st11_sym. unfold REG_PC. lia. }
            apply length_regs_write_reg_10; [exact Hlen_pc|].
            rewrite Hlen_pc. unfold REG_TEMP1. lia.
          }
          assert (Hpc_bound_st12_sym : REG_PC < length (regs st12))
            by (rewrite Hlen_st12_sym; unfold REG_PC; lia).
          assert (Htemp1_bound_st12_sym : REG_TEMP1 < length (regs st12))
            by (rewrite Hlen_st12_sym; unfold REG_TEMP1; lia).
          assert (Haddr_bound_st12_sym : REG_ADDR < length (regs st12))
            by (rewrite Hlen_st12_sym; unfold REG_ADDR; lia).
          assert (Hq_bound_st12_sym : REG_Q < length (regs st12))
            by (rewrite Hlen_st12_sym; unfold REG_Q; lia).
          assert (Hsym_bound_st12_sym : REG_SYM < length (regs st12))
            by (rewrite Hlen_st12_sym; unfold REG_SYM; lia).
          assert (Htemp1_st12_sym : read_reg REG_TEMP1 st12 = 1).
          { subst st12.
            apply (run1_loadconst_result st11 REG_TEMP1 1);
              try assumption.
            exact Htemp1_bound_st11_sym.
          }
          assert (Haddr_st12_sym : read_reg REG_ADDR st12 = read_reg REG_ADDR st11).
          { subst st12.
            apply (run1_preserves_reg_loadconst st11 REG_TEMP1 1 REG_ADDR);
              try assumption.
            all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
          }
          assert (Hq_st12_sym : read_reg REG_Q st12 = read_reg REG_Q st11).
          { subst st12.
            apply (run1_preserves_reg_loadconst st11 REG_TEMP1 1 REG_Q);
              try assumption.
            all: unfold REG_Q, REG_TEMP1, REG_PC; lia.
          }
          assert (Hsym_st12_sym : read_reg REG_SYM st12 = read_reg REG_SYM st11).
          { subst st12.
            apply (run1_preserves_reg_loadconst st11 REG_TEMP1 1 REG_SYM);
              try assumption.
            all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
          }
          assert (Hprog_st12_sym : firstn (length program) (mem st12) = program).
          { rewrite Hmem_st12_sym, Hmem_st11_sym, Hmem_st10_sym, Hmem_st9_sym, Hmem_st8_sym,
                   Hmem_st7_sym, Hmem_st6_sym, Hmem_st5_sym, Hmem_st4_sym, Hmem_st3, Hmem_st2, Hmem_st1. exact Hprog. }
          assert (Hpc_st12_sym_lt : read_reg REG_PC st12 < length program_instrs).
          { rewrite Hpc_st12_sym. pose proof program_instrs_length_gt_48 as Hlen. lia. }
          assert (Hdecode_pc20_sym : decode_instr st12 = Jnz REG_TEMP1 4).
          { subst st12.
            pose proof (decode_instr_program_state (run1 st11) Hpc_st12_sym_lt Hprog_st12_sym) as Hdecode_prog.
            rewrite decode_instr_program_at_pc with (pc := 20) in Hdecode_prog by exact Hpc_st12_sym_lt.
            exact Hdecode_prog.
          }
          assert (Htemp1_nonzero_st12 : Nat.eqb (read_reg REG_TEMP1 st12) 0 = false).
          { rewrite Htemp1_st12_sym. reflexivity. }
          set (st13 := run1 st12).
          assert (Hpc_st13_sym : read_reg REG_PC st13 = 4).
          { subst st13.
            unfold run1.
            rewrite Hdecode_pc20_sym.
            apply CPU.step_jnz_false.
            exact Htemp1_nonzero_st12.
          }
          assert (Hmem_st13_sym : mem st13 = mem st12).
          { subst st13.
            apply run1_mem_preserved_if_no_store.
            rewrite Hdecode_pc20_sym; simpl; exact I.
          }
          assert (Hlen_st13_sym : length (regs st13) = 10).
          { subst st13.
            unfold run1.
            rewrite Hdecode_pc20_sym.
            cbn [CPU.step read_reg write_reg read_mem].
            rewrite Htemp1_nonzero_st12.
            apply length_regs_write_reg_10; [exact Hlen_st12_sym|].
            rewrite Hlen_st12_sym. unfold REG_PC. lia.
          }
          assert (Hpc_bound_st13_sym : REG_PC < length (regs st13))
            by (rewrite Hlen_st13_sym; unfold REG_PC; lia).
          assert (Haddr_bound_st13_sym : REG_ADDR < length (regs st13))
            by (rewrite Hlen_st13_sym; unfold REG_ADDR; lia).
          assert (Hq_bound_st13_sym : REG_Q < length (regs st13))
            by (rewrite Hlen_st13_sym; unfold REG_Q; lia).
          assert (Hsym_bound_st13_sym : REG_SYM < length (regs st13))
            by (rewrite Hlen_st13_sym; unfold REG_SYM; lia).
          assert (Haddr_st13_sym : read_reg REG_ADDR st13 = read_reg REG_ADDR st12).
          { subst st13.
            apply (run1_preserves_reg_jnz_false st12 REG_TEMP1 4 REG_ADDR);
              try assumption.
            all: unfold REG_ADDR, REG_TEMP1, REG_PC; lia.
          }
          assert (Hq_st13_sym : read_reg REG_Q st13 = read_reg REG_Q st12).
          { subst st13.
            apply (run1_preserves_reg_jnz_false st12 REG_TEMP1 4 REG_Q);
              try assumption.
            all: unfold REG_Q, REG_TEMP1, REG_PC; lia.
          }
          assert (Hsym_st13_sym : read_reg REG_SYM st13 = read_reg REG_SYM st12).
          { subst st13.
            apply (run1_preserves_reg_jnz_false st12 REG_TEMP1 4 REG_SYM);
              try assumption.
            all: unfold REG_SYM, REG_TEMP1, REG_PC; lia.
          }
          assert (Haddr_st13_val : read_reg REG_ADDR st13 = RULES_START_ADDR + 5 * S i).
          { rewrite Haddr_st13_sym, Haddr_st12_sym, Haddr_st11_sym, Haddr_st10_sym.
            rewrite Haddr_st9_sym, Haddr_st8_sym, Haddr_st7_sym, Haddr_st6_sym, Haddr_st5_sym, Haddr_st4_sym.
            rewrite Hst3_addr, Hst2_addr, Hst1_addr, Haddr_reg.
            lia.
          }
          assert (Hq_st13_val : read_reg REG_Q st13 = q).
          { rewrite Hq_st13_sym, Hq_st12_sym, Hq_st11_sym, Hq_st10_sym.
            rewrite Hst9_q_sym, Hst8_q_sym, Hst7_q_sym, Hst6_q_sym, Hst5_q_sym, Hst4_q_sym.
            rewrite Hst3_q, Hst2_q, Hst1_q, Hq_reg.
            reflexivity.
          }
          assert (Hsym_st13_val : read_reg REG_SYM st13 = nth head tape tm.(tm_blank)).
          { rewrite Hsym_st13_sym, Hsym_st12_sym, Hsym_st11_sym, Hsym_st10_sym.
            rewrite Hst9_sym_sym, Hst8_sym_sym, Hst7_sym_sym, Hst6_sym_sym, Hst5_sym_sym, Hst4_sym_sym.
            rewrite Hst3_sym_reg, Hst2_sym, Hst1_sym, Hsym_reg.
            reflexivity.
          }
          assert (Hrun_st13 : run_n st 13 = st13).
          { unfold st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1.
            repeat (rewrite run_n_succ).
            simpl.
            reflexivity.
          }
          exists 13.
          exists (run_n st 13).
          split; [reflexivity|].
          rewrite Hrun_st13.
          split.
          { unfold find_rule_loop_inv.
            repeat split.
            - exact Hq_st13_val.
            - exact Hsym_st13_val.
            - exact Haddr_st13_val.
            - exact Hpc_st13_sym.
          }
          { right. reflexivity. }

  Qed.


Axiom pc_29_implies_registers_from_rule_table :
  forall (tm : TM) (conf : TMConfig) (st : State) (k : nat) (st' : State),
    let '((q, tape), head) := conf in
    inv st tm conf ->
    st' = run_n st k ->
    (forall j, j < k -> read_reg REG_PC (run_n st j) < 29) ->
    IS_ApplyRule_Start (read_reg REG_PC st') ->
    exists i, i < length (tm_rules tm) /\
      nth (RULES_START_ADDR + i * 5 + 2) (mem st') 0 = read_reg REG_Q' st' /\
      nth (RULES_START_ADDR + i * 5 + 3) (mem st') 0 = read_reg REG_WRITE st' /\
      nth (RULES_START_ADDR + i * 5 + 4) (mem st') 0 = read_reg REG_MOVE st'.

Axiom find_rule_from_memory_components :
  forall (tm : TM) (conf : TMConfig) (i : nat) (st' : State),
    let '((q, tape), head) := conf in
    i < length (tm_rules tm) ->
    nth (RULES_START_ADDR + i * 5 + 2) (mem st') 0 = read_reg REG_Q' st' ->
    nth (RULES_START_ADDR + i * 5 + 3) (mem st') 0 = read_reg REG_WRITE st' ->
    nth (RULES_START_ADDR + i * 5 + 4) (mem st') 0 = read_reg REG_MOVE st' ->
    firstn (length (encode_rules (tm_rules tm)))
          (skipn RULES_START_ADDR (mem st')) =
    encode_rules (tm_rules tm) ->
    find_rule (tm_rules tm) q (nth head tape (tm_blank tm)) =
      Some (read_reg REG_Q' st', read_reg REG_WRITE st', decode_z (read_reg REG_MOVE st')).

(* ================================================================ *)
(* End of axiomatized lemmas                                         *)
(* ================================================================ *)

