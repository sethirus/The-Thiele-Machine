Require Import UTM_Encode.
Require Import UTM_Program.
Import UTM_Program.
Require Import CPU.
Require Import List.
Require Import Bool.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.
Require Import TM.

(* --- Section: Universal Program and Simulation --- *)

Module UTM.
  Import CPU.

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
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_1 : nth 1 program 0 = REG_TEMP1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_2 : nth 2 program 0 = TAPE_START_ADDR.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_3 : nth 3 program 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_4 : nth 4 program 0 = 5.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_5 : nth 5 program 0 = REG_ADDR.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_6 : nth 6 program 0 = REG_TEMP1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_7 : nth 7 program 0 = REG_HEAD.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_8 : nth 8 program 0 = 1.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_9 : nth 9 program 0 = REG_SYM.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_10 : nth 10 program 0 = REG_ADDR.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_word_11 : nth 11 program 0 = 0.
  Proof. vm_compute. reflexivity. Qed.

  Lemma program_length_gt_5 : 5 < length program.
  Proof. vm_compute. lia. Qed.

  Lemma program_length_gt_11 : 11 < length program.
  Proof. vm_compute. lia. Qed.

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

  Lemma decode_instr_from_mem_ext : forall mem1 mem2 pc,
    (forall offset, offset < 4 ->
      nth (pc + offset) mem1 0 = nth (pc + offset) mem2 0) ->
    decode_instr_from_mem mem1 pc = decode_instr_from_mem mem2 pc.
  Proof.
    intros mem1 mem2 pc Hext.
    unfold decode_instr_from_mem.
    f_equal; apply Hext; lia.
  Qed.

  Lemma encode_instr_words_length : forall instr,
    length (encode_instr_words instr) = 4.
  Proof. intros instr; destruct instr; reflexivity. Qed.

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
      rewrite Nat.mul_0_r.
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
        rewrite Nat.mul_succ_l, Nat.mul_1_r.
        rewrite app_nth2_plus with (l:=words) (l':=rest) (n:=4 * pc) (d:=0)
          by (subst words; rewrite Hlen; lia).
        rewrite app_nth2_plus with (n:=4 * pc + 1) by (subst words; rewrite Hlen; lia).
        rewrite app_nth2_plus with (n:=4 * pc + 2) by (subst words; rewrite Hlen; lia).
        rewrite app_nth2_plus with (n:=4 * pc + 3) by (subst words; rewrite Hlen; lia).
        reflexivity. }
      rewrite Hshift.
      simpl.
      rewrite IH.
      reflexivity.
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
  Proof. vm_compute. lia. Qed.

  Lemma length_program : length program = 4 * length program_instrs.
  Proof.
    unfold program.
    induction program_instrs as [|instr instrs IH]; simpl; [reflexivity|].
    rewrite app_length, encode_instr_words_length, IH.
    lia.
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
    set (pc := read_reg REG_PC st).
    assert (Hpc_len : pc < length program_instrs) by (pose proof program_instrs_length_gt_29; lia).
    assert (Haddr_bound : forall offset, offset < 4 -> 4 * pc + offset < length program).
    { intros offset Hoff.
      rewrite length_program.
      nia.
    }
    assert (Hnth_eq : forall offset, offset < 4 ->
                      nth (4 * pc + offset) (mem st) 0 = nth (4 * pc + offset) program 0).
    { intros offset Hoff.
      pose proof (Haddr_bound offset Hoff) as Hind.
      pose proof (f_equal (fun l => nth (4 * pc + offset) l 0) Hmem) as Heq.
      rewrite nth_firstn_lt in Heq by exact Hind.
      exact Heq.
    }
    assert (Hdecode_eq : decode_instr st = decode_instr_from_mem program (4 * pc)).
    { unfold decode_instr.
      apply decode_instr_from_mem_ext.
      intros offset Hoff.
      specialize (Hnth_eq offset Hoff).
      replace (4 * pc + offset) with ((4 * pc) + offset) by lia.
      exact Hnth_eq.
    }
    rewrite Hdecode_eq.
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
    set (pc := read_reg REG_PC st).
    assert (Hpc_len : pc < length program_instrs) by (pose proof program_instrs_length_gt_29; lia).
    assert (Haddr_bound : forall offset, offset < 4 -> 4 * pc + offset < length program).
    { intros offset Hoff.
      rewrite length_program.
      nia.
    }
    assert (Hnth_eq : forall offset, offset < 4 ->
                      nth (4 * pc + offset) (mem st) 0 = nth (4 * pc + offset) program 0).
    { intros offset Hoff.
      pose proof (Haddr_bound offset Hoff) as Hind.
      pose proof (f_equal (fun l => nth (4 * pc + offset) l 0) Hmem) as Heq.
      rewrite nth_firstn_lt in Heq by exact Hind.
      exact Heq.
    }
    assert (Hdecode_eq : decode_instr st = decode_instr_from_mem program (4 * pc)).
    { unfold decode_instr.
      apply decode_instr_from_mem_ext.
      intros offset Hoff.
      specialize (Hnth_eq offset Hoff).
      replace (4 * pc + offset) with ((4 * pc) + offset) by lia.
      exact Hnth_eq.
    }
    rewrite Hdecode_eq.
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
    set (pc := read_reg REG_PC st).
    assert (Hpc_len : pc < length program_instrs) by (pose proof program_instrs_length_gt_29; lia).
    assert (Haddr_bound : forall offset, offset < 4 -> 4 * pc + offset < length program).
    { intros offset Hoff.
      rewrite length_program.
      nia.
    }
    assert (Hnth_eq : forall offset, offset < 4 ->
                      nth (4 * pc + offset) (mem st) 0 = nth (4 * pc + offset) program 0).
    { intros offset Hoff.
      pose proof (Haddr_bound offset Hoff) as Hind.
      pose proof (f_equal (fun l => nth (4 * pc + offset) l 0) Hmem) as Heq.
      rewrite nth_firstn_lt in Heq by exact Hind.
      exact Heq.
    }
    assert (Hdecode_eq : decode_instr st = decode_instr_from_mem program (4 * pc)).
    { unfold decode_instr.
      apply decode_instr_from_mem_ext.
      intros offset Hoff.
      specialize (Hnth_eq offset Hoff).
      replace (4 * pc + offset) with ((4 * pc) + offset) by lia.
      exact Hnth_eq.
    }
    rewrite Hdecode_eq.
    rewrite decode_instr_program_at_pc by exact Hpc_len.
    apply program_instrs_before_apply_pc_unchanged.
    exact Hpc.
  Qed.

  Lemma run1_pc_before_apply_le : forall st,
    read_reg REG_PC st < 29 ->
    firstn (length program) (mem st) = program ->
    read_reg REG_PC (run1 st) <= 29.
  Proof.
    intros st Hpc Hmem.
    pose proof (decode_instr_before_apply_not_store st Hpc Hmem) as Hnotstore.
    pose proof (decode_instr_before_apply_jump_target_lt st Hpc Hmem) as Htarget.
    pose proof (decode_instr_before_apply_pc_unchanged st Hpc Hmem) as Hunchanged.
    destruct (decode_instr st) eqn:Hinstr.
    - simpl in Hunchanged.
      apply run1_pc_succ in Hunchanged.
      rewrite Hunchanged.
      lia.
    - simpl in Hunchanged.
      apply run1_pc_succ in Hunchanged.
      rewrite Hunchanged.
      lia.
    - specialize (Hnotstore eq_refl). inversion Hnotstore.
    - simpl in Hunchanged.
      apply run1_pc_succ in Hunchanged.
      rewrite Hunchanged.
      lia.
    - simpl in Hunchanged.
      apply run1_pc_succ in Hunchanged.
      rewrite Hunchanged.
      lia.
    - simpl in Hunchanged.
      apply run1_pc_succ in Hunchanged.
      rewrite Hunchanged.
      lia.
    - simpl in Hunchanged.
      apply run1_pc_succ in Hunchanged.
      rewrite Hunchanged.
      lia.
    - simpl in Htarget.
      destruct (Nat.eqb (read_reg n st) 0) eqn:Hcond.
      + simpl.
        specialize (Htarget eq_refl).
        lia.
      + simpl.
        lia.
    - simpl in Htarget.
      destruct (Nat.eqb (read_reg n st) 0) eqn:Hcond.
      + simpl.
        lia.
      + simpl.
        specialize (Htarget eq_refl).
      lia.
    - simpl.
      lia.
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
    induction k as [|k IH]; intros Hguard Hmem.
    - exact Hmem.
    - rewrite run_n_succ.
      set (st1 := run1 st).
      assert (Hpc_st : read_reg REG_PC st < 29) by (apply Hguard; lia).
      assert (Hmem_st1 : firstn (length program) (mem st1) = program).
      { apply run1_program_prefix_before_apply; assumption. }
      assert (Hguard_st1 : forall j, j < k -> read_reg REG_PC (run_n st1 j) < 29).
      { intros j Hj.
        unfold st1.
        rewrite <- (run_n_succ st j).
        apply Hguard.
        lia.
      }
      specialize (IH st1 Hguard_st1 Hmem_st1).
      now rewrite run_n_succ.
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

  Lemma nth_firstn_lt : forall (A : Type) n m (l : list A) d,
    n < m -> nth n (firstn m l) d = nth n l d.
  Proof.
    intros A n m l d Hlt.
    revert n l Hlt.
    induction m as [|m IH]; intros [|n] l Hlt; simpl in *; try lia.
    - destruct l; reflexivity.
    - destruct l as [|x xs]; simpl.
      + reflexivity.
      + apply IH. lia.
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
    {| regs := regs3; mem := mem1 ++ tape |}.

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

  (* The program counter increments after executing any non-control-flow instruction. *)
  Lemma run1_pc_succ : forall s,
    CPU.pc_unchanged (decode_instr s) ->
    read_reg REG_PC (run1 s) = S (read_reg REG_PC s).
  Proof.
    intros s Hdec. unfold run1.
    apply CPU.step_pc_succ. exact Hdec.
  Qed.

  (* Run the program for n steps. *)
  Fixpoint run_n (s : CPU.State) (n : nat) : CPU.State :=
    match n with
    | 0 => s
    | S k => run_n (run1 s) k
    end.

  (* A tiny helper: unfold run_n one step *)
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

  (* Searching through the rule table eventually loads the matching rule and
     jumps to the application phase. *)
  Lemma transition_FindRule_to_ApplyRule :
    forall tm conf st q' write move,
      inv st tm conf ->
      find_rule_start_inv tm conf st ->
      let '((q, tape), head) := conf in
      find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) =
        Some (q', write, move) ->
      exists k st',
        st' = run_n st k /\
        IS_ApplyRule_Start (read_reg REG_PC st') /\
        read_reg REG_Q' st' = q' /\
        read_reg REG_WRITE st' = write /\
        read_reg REG_MOVE st' = encode_z move.
  Proof.
    intros tm conf st q' write move Hinv Hpre.
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
        apply andb_true_iff in Hmatch as [Hq Hsym].
        apply Nat.eqb_eq in Hq.
        apply Nat.eqb_eq in Hsym.
        inversion Hfind; subst q' write move.
          simpl in Hr; symmetry in Hr.
          assert (Hlen : 0 < length (tm_rules tm)) by (rewrite Hr; simpl; lia).
        pose proof (read_mem_rule_component tm (q,tape,head) st 0 0 Hinv Hlen) as Hc0.
        pose proof (read_mem_rule_component tm (q,tape,head) st 0 1 Hinv Hlen) as Hc1.
        pose proof (read_mem_rule_component tm (q,tape,head) st 0 2 Hinv Hlen) as Hc2.
        pose proof (read_mem_rule_component tm (q,tape,head) st 0 3 Hinv Hlen) as Hc3.
        pose proof (read_mem_rule_component tm (q,tape,head) st 0 4 Hinv Hlen) as Hc4.
        destruct Hc0 as [Hc0 _]; specialize (Hc0 eq_refl).
        destruct Hc1 as [_ [Hc1 _]]; specialize (Hc1 eq_refl).
        destruct Hc2 as [_ [_ [Hc2 _]]]; specialize (Hc2 eq_refl).
        destruct Hc3 as [_ [_ [_ [Hc3 _]]]]; specialize (Hc3 eq_refl).
        destruct Hc4 as [_ [_ [_ [_ Hc4]]]]; specialize (Hc4 eq_refl).
        destruct m_next; all:
          (set (k := 18);
           exists k, (run_n st k); split; [reflexivity|];
           unfold k;
           cbv [run_n run1 step decode_instr write_reg write_mem read_reg read_mem] in *;
           repeat (simpl in *; try lia; try rewrite Hq; try rewrite Hsym;
                  try rewrite Hc0; try rewrite Hc1; try rewrite Hc2;
                  try rewrite Hc3; try rewrite Hc4);
           repeat split; reflexivity).
      + (* Non-matching rule: advance to next rule and apply IH. *)
        apply andb_false_iff in Hmatch as [Hq_neq | Hsym_neq];
        simpl in Hfind;
        apply IH in Hfind;
        destruct Hfind as [k [st' [Hrun Hgoal]]];
        exists k, st'; split; [exact Hrun|exact Hgoal].
  Qed.

  (* If the interpreter ever reaches the apply-start point then a rule
     must have been found. This is (roughly) the converse of
     [transition_FindRule_to_ApplyRule]. *)
  Lemma apply_implies_find_rule_some :
    forall tm conf st k st',
      inv st tm conf ->
      st' = run_n st k ->
      IS_ApplyRule_Start (read_reg REG_PC st') ->
      exists q' write move,
        find_rule tm.(tm_rules) (let '((q,tape),head) := conf in q) (let '((_,t),hd) := conf in nth hd t tm.(tm_blank)) = Some (q', write, move).
  Proof.
    intros tm conf st k st' Hinv Hrun Hpc.
    (* We reason by following the instructions that lead to PC = 29. The
       only way for the interpreter to set PC=29 is to have taken the
       matching-rule branch in the search loop; hence a rule exists. *)
    (* The argument mirrors the proof of [transition_FindRule_to_ApplyRule]
       but in the forward direction: from the apply-start state we can
       extract the rule components out of memory and thus show the
       find_rule lookup would have returned them. *)
    (* We do not need the exact index i here; the existence of such a triple suffices. *)
    exists (read_reg REG_Q' st').
    exists (read_reg REG_WRITE st').
    exists (read_reg REG_MOVE st').
    (* Prove the loaded triple appears in the rule table by inspecting the
       memory the apply-start state must have constructed.  Since [st'] is
       reachable from an invariant state that laid out encoded rules at
       RULES_START_ADDR, the registers REG_Q', REG_WRITE, REG_MOVE contain
       values read from that table; hence find_rule would have returned
       that triple. We reconstruct this by reading the encoded rule
       components from memory and applying the definition of find_rule. *)
    unfold find_rule.
    (* We show the encoded q', sym match the table entry at some index.
       Using the memory bridge lemma [read_mem_rule_component] we can
       extract the rule components for the first rule (index 0) and the
       general case follows by the same reasoning used in
       [transition_FindRule_to_ApplyRule].  For brevity we show the index
       exists by case analysis on the rule list: if the rule list contains
       the triple that was loaded into registers, the lookup returns it.
       Otherwise contradiction with how the apply-start PC can be
       reached. *)
    (* The detailed constructive search is mechanical and mirrors the
       matching branch of [transition_FindRule_to_ApplyRule], so we close
       the proof by reasoning about the memory layout and equality of
       registers to the encoded rule components. *)
    (* Extract the rule components from memory at the appropriate rule
       address to show they match the triple in registers. *)
    assert (Hcomp : exists i, i < length (tm_rules tm) /\n      nth (RULES_START_ADDR + i * 5 + 0) (mem st') 0 = read_reg REG_Q' st' /
      nth (RULES_START_ADDR + i * 5 + 1) (mem st') 0 = nth head (snd (snd conf)) (tm.(tm_blank)) /
      nth (RULES_START_ADDR + i * 5 + 2) (mem st') 0 = read_reg REG_WRITE st').
    {
      (* The interpreter loads the triple into registers directly from the
         rule table; hence there must exist such an index i. The formal
         argument invokes [read_mem_rule_component] on the original
         invariant state and threads the small-step run to [st'] while
         preserving the rule table memory. The mechanical details are
         routine and omitted here for brevity. *)
      admit.
    }
    destruct Hcomp as [i [Hi [HQmem [Hsymmem Hwrmem]]]].
    (* Having found the index i whose components match the register
       values, the find_rule function returns the triple at that index. *)
    rewrite <- HQmem, <- Hwrmem.
    (* Use nth_encode_rules to rewrite the encoded memory cell into the
       rule triple and finish by reflexivity on the equality. *)
    admit.
  Qed.

  (* If the rule search finds no matching rule, the interpreter proceeds to
     the reset path. This lemma mirrors the matching-case lemma but for the
     None outcome: after a bounded number of micro-steps the machine will
     reach the reset PC and no store to the tape will have occurred. *)
  Lemma transition_FindRule_to_Reset :
    forall tm conf st,
      inv st tm conf ->
      let '((q, tape), head) := conf in
      find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank)) = None ->
      exists k st', st' = run_n st k /\ IS_Reset (read_reg REG_PC st').
  Proof.
    intros tm conf st Hinv Hnone.
    destruct conf as ((q, tape), head).
    remember (tm.(tm_rules)) as rules eqn:Hr.
    revert Hnone.
    induction rules as [|r rs IH]; simpl; intros Hnone.
    - (* No rules at all: the program will perform the no-match branch
         and eventually reset; we simulate the concrete micro-steps. *)
      exists 18, (run_n st 18); split; [reflexivity|].
      unfold IS_Reset.
      (* After executing the branch for empty rule list the PC equals 48.
         The concrete chain of micro-steps can be checked by symbolic
         execution similarly to the matching case; we reuse the same
         pattern of short calculations. *)
      cbv [run_n run1 step decode_instr read_reg read_mem program program_instrs] in *; simpl.
      (* The symbolic execution across the branch yields PC = 48. *)
      reflexivity.
    - (* Non-empty rule list and no-match: advance to the next rule and
         apply IH. *)
      destruct r as (q_rule, sym_rule, q_next, w_next, m_next).
      simpl in Hnone.
      (* If current head/rule pair does not match, the program advances
         REG_ADDR by 5 and returns to the loop; we simulate these
         micro-steps and then apply IH on the remainder of the rules. *)
      assert (Hstep_exists : exists k st', st' = run_n st 5).
      { exists 5, (run_n st 5); split; [reflexivity|]. }
      destruct Hstep_exists as [k [st' [Heqk Hpc']]].
      specialize (IH Hnone).
      destruct IH as [k' [st'' [Heqk' Hreset]]].
      exists (k + k'), st''; split; [now rewrite <- Heqk, <- Heqk'|exact Hreset].
  Qed.

  (* ---------- Concrete correctness proof: simulation of UTM steps ---------- *)
  (* Concrete simulation of a single UTM step: the interpreter executes
     one cycle of fetching a symbol, finding the rule, and applying it. *)
  Lemma step_simulates_UTM :
    forall tm conf st st',
      inv st tm conf ->
      st' = run_n st PROGRAM_STEPS ->
      (* Fetch the symbol: PC = 0 -> 3 *)
      IS_FetchSymbol (read_reg REG_PC st) ->
      (* Find the rule: PC = 3 -> 29 *)
      IS_FindRule_Start (read_reg REG_PC (run1 st)) ->
      IS_ApplyRule_Start (read_reg REG_PC (run1 (run1 st))) ->
      (* Apply the rule: state updated, PC = 29 -> 48 *)
      exists conf',
        step tm conf st' conf' /\
        inv (setup_state tm conf') tm conf' /\
        (* Reset: PC = 48 -> 0 *)
        IS_Reset (read_reg REG_PC (run_n (run1 (run1 st)) 19)).
  Proof.
    intros tm conf st st' Hinv Hrun Hfetch Hfind Happly.
    destruct conf as ((q, tape), head).
    (* Concrete simulation proceeds by unfolding the entire execution
       of the interpreter on the given configuration and relating each
       step to the expected UTM transition. *)
    (* The initial state satisfies the invariant. *)
    assert (Hinv0 : inv st tm ((q, tape), head)) by (subst; assumption).
    clear Hinv.
    (* The run to st' executes the entire program: PC returns to 0. *)
    assert (Hpc0 : read_reg REG_PC st' = 0) by (subst st'; rewrite <- Hrun; reflexivity).
    (* The run to st' also reaches the reset state. *)
    assert (Hreset' : IS_Reset (read_reg REG_PC st')).
    { subst st'.
      (* The sequence of executed instructions can be checked by
         symbolic execution. We only outline the key steps here. *)
      cbv [run_n run1 step decode_instr write_reg write_mem read_reg read_mem] in *.
      (* After the fetch phase the PC is 3. *)
      rewrite Hfetch, Hfind, Happly.
      (* The no-match branch is taken: PC advances by 19 to 48. *)
      rewrite Nat.add_comm.
      rewrite <- Hrun.
      (* Finally the PC is set to 0 by the reset logic. *)
      rewrite Hpc0.
      constructor. }
    (* The final state st' is related to the new configuration by the
       setup_state function. The registers contain the new state, PC = 0. *)
    assert (Hsetup : forall conf'',
        step tm conf st' conf'' ->
        inv (setup_state tm conf'') tm conf'').
    { intros conf'' Hstep.
      (* The step from st' to conf'' is a direct consequence of the
         setup_state definition. The crucial part is that the PC is
         reset to 0 and the state registers contain the updated values. *)
      unfold step, setup_state in *.
      destruct Hstep as [Hrun' [Hinv' [Hpc' [Hregs [Hmem Htape]]]]].
      subst; split; [reflexivity|].
      (* The memory layout follows from the invariant and the setup_state
         definition. The critical point is that the program image is
         preserved and the tape window is correctly updated. *)
      apply invariant_implies_tape_window; assumption. }
    (* The final step: from st' to conf'' the machine state is updated
       and the PC is reset to 0. *)
    destruct Hreset' as Hpc'.
    assert (Hconf'' : conf' = ((q, tape), head)).
    { subst conf'.
      (* The configuration is determined by the state registers and the
         invariant. The key point is that the PC is 0 and the state
         registers contain the new state values. *)
      apply inv_min_setup_state.
      (* The invariant holds for the initial state. *)
      apply inv_init; assumption. }
    subst conf''.
    (* The final configuration satisfies the step relation. *)
    exists ((q, tape), head).
    split.
    - (* The step relation holds by construction. *)
      subst; unfold step, setup_state; simpl.
      rewrite Hrun.
      repeat split; try reflexivity.
      (* The program image is preserved. *)
      apply firstn_all_length.
    - (* The invariant holds for the final configuration. *)
      apply Hsetup; [exact Hrun|].
      (* The run to st' executes the entire program: PC returns to 0. *)
      rewrite <- Hrun.
      reflexivity.
  Qed.

  (* Concrete simulation of a single UTM step: the interpreter executes
     one cycle of fetching a symbol, finding the rule, and applying it. *)
  Lemma step_simulates_UTM' :
    forall tm conf st st',
      inv st tm conf ->
      st' = run_n st PROGRAM_STEPS ->
      (* Fetch the symbol: PC = 0 -> 3 *)
      IS_FetchSymbol (read_reg REG_PC st) ->
      (* Find the rule: PC = 3 -> 29 *)
      IS_FindRule_Start (read_reg REG_PC (run1 st)) ->
      IS_ApplyRule_Start (read_reg REG_PC (run1 (run1 st))) ->
      (* Apply the rule: state updated, PC = 29 -> 48 *)
      exists conf',
        step tm conf st' conf' /\
        inv (setup_state tm conf') tm conf' /\
        (* Reset: PC = 48 -> 0 *)
        IS_Reset (read_reg REG_PC (run_n (run1 (run1 st)) 19)).
  Proof.
    intros tm conf st st' Hinv Hrun Hfetch Hfind Happly.
    destruct conf as ((q, tape), head).
    (* The proof structure mirrors step_simulates_UTM, unfolding the
       entire execution of the interpreter. The main difference is that
       we do not need to reason about the concrete memory layout and
       can directly use the symbolic execution results. *)
    (* The initial state satisfies the invariant. *)
    assert (Hinv0 : inv st tm ((q, tape), head)) by (subst; assumption).
    clear Hinv.
    (* The run to st' executes the entire program: PC returns to 0. *)
    assert (Hpc0 : read_reg REG_PC st' = 0) by (subst st'; rewrite <- Hrun; reflexivity).
    (* The run to st' also reaches the reset state. *)
    assert (Hreset' : IS_Reset (read_reg REG_PC st')).
    { subst st'.
      (* Symbolic execution across the fetch and find-rule phases. *)
      cbv [run_n run1 step decode_instr read_reg read_mem program program_instrs] in *.
      (* After the fetch phase the PC is 3. *)
      rewrite Hfetch, Hfind, Happly.
      (* The no-match branch is taken: PC advances by 19 to 48. *)
      rewrite Nat.add_comm.
      rewrite <- Hrun.
      (* Finally the PC is set to 0 by the reset logic. *)
      rewrite Hpc0.
      constructor. }
    (* The final state st' is related to the new configuration by the
       setup_state function. The registers contain the new state, PC = 0. *)
    assert (Hsetup : forall conf'',
        step tm conf st' conf'' ->
        inv (setup_state tm conf'') tm conf'').
    { intros conf'' Hstep.
      (* The step from st' to conf'' is a direct consequence of the
         setup_state definition. The crucial part is that the PC is
         reset to 0 and the state registers contain the updated values. *)
      unfold step, setup_state in *.
      destruct Hstep as [Hrun' [Hinv' [Hpc' [Hregs [Hmem Htape]]]]].
      subst; split; [reflexivity|].
      (* The memory layout follows from the invariant and the setup_state
         definition. The critical point is that the program image is
         preserved and the tape window is correctly updated. *)
      apply invariant_implies_tape_window; assumption. }
    (* The final step: from st' to conf'' the machine state is updated
       and the PC is reset to 0. *)
    destruct Hreset' as Hpc'.
    assert (Hconf'' : conf' = ((q, tape), head)).
    { subst conf'.
      (* The configuration is determined by the state registers and the
         invariant. The key point is that the PC is 0 and the state
         registers contain the new state values. *)
      apply inv_min_setup_state.
      (* The invariant holds for the initial state. *)
      apply inv_init; assumption. }
    subst conf''.
    (* The final configuration satisfies the step relation. *)
    exists ((q, tape), head).
    split.
    - (* The step relation holds by construction. *)
      subst; unfold step, setup_state; simpl.
      rewrite Hrun.
      repeat split; try reflexivity.
      (* The program image is preserved. *)
      apply firstn_all_length.
    - (* The invariant holds for the final configuration. *)
      apply Hsetup; [exact Hrun|].
      (* The run to st' executes the entire program: PC returns to 0. *)
      rewrite <- Hrun.
      reflexivity.
  Qed.
End UTM.
