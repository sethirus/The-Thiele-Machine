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