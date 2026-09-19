(** VMUnboundedOpcodeAdd.v — the ADD opcode block: the first actual
    guest-instruction simulation case for B3, composed from
    get_slot_program/set_slot_program via the embedding infrastructure in
    VMUnboundedInterpreterCompose.v, and proved against the guest's actual
    list-based register file via VMUnboundedGuestEncoding.v.

    Register convention: R14 is the persistent packed-registers cell
    across the whole block (loaded at the start of each get_slot/set_slot
    call into R0, since those subroutines clobber R0). R11/R12/R13 hold
    the two unpacked operands and their sum, chosen outside get_slot_program
    /set_slot_program's own clobber set (R0-R10) so back-to-back calls
    don't destroy each other's results. R15 stays unused (CALL/RET
    convention, forward compatibility). rs1/rs2/dst are concrete constants
    for this theorem — decoding them from an actual encoded guest
    instruction is the dispatch loop's job, built separately.

    The single 36-step simulation is proved as four phase lemmas (glue1+
    call1, glue2+call2, glue3+call3, glue4), each closed by its own [Qed],
    rather than as one monolithic proof term. A single-Qed version of this
    proof was tried first: every individual tactic completed in well under
    a second, but [Qed] itself then ran past 30 minutes on a 2-core
    machine, because the kernel must convertibility-check the whole chain
    of ~40 [set]/[fold]/[change] steps in one pass. Splitting the same
    tactics into four independently-checked lemmas keeps each [Qed] fast. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep.
From Kernel Require Import VMUnboundedInterpreterSlots VMUnboundedInterpreterCode.
From Kernel Require Import VMUnboundedInterpreterCompose VMUnboundedGuestEncoding.

Definition R11 : nat := 11. Definition R12 : nat := 12. Definition R13 : nat := 13.
Definition R14 : nat := 14.

Definition add_glue1 (rs1 : nat) : list vm_instruction :=
  [ instr_xfer R0 R14 0 ; instr_load_imm R1 rs1 0 ].

Definition add_glue2 (rs2 : nat) : list vm_instruction :=
  [ instr_xfer R11 R8 0 ; instr_xfer R0 R14 0 ; instr_load_imm R1 rs2 0 ].

Definition add_glue3 (dst : nat) : list vm_instruction :=
  [ instr_xfer R12 R8 0 ; instr_add R13 R11 R12 0
  ; instr_xfer R0 R14 0 ; instr_load_imm R1 dst 0 ; instr_xfer R2 R13 0 ].

Definition add_glue4 : list vm_instruction := [ instr_xfer R14 R8 0 ].

Definition add_block (rs1 rs2 dst : nat) : list vm_instruction :=
  add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2 ++ get_slot_program ++
  add_glue3 dst ++ set_slot_program ++ add_glue4.

Lemma add_glue_straightline : forall rs1 rs2 dst,
  Forall straightline_arith (add_glue1 rs1) /\
  Forall straightline_arith (add_glue2 rs2) /\
  Forall straightline_arith (add_glue3 dst) /\
  Forall straightline_arith add_glue4.
Proof.
  intros. repeat split; unfold add_glue1, add_glue2, add_glue3, add_glue4;
    repeat constructor.
Qed.

Lemma add_block_straightline : forall rs1 rs2 dst,
  Forall straightline_arith (add_block rs1 rs2 dst).
Proof.
  intros rs1 rs2 dst. unfold add_block.
  destruct (add_glue_straightline rs1 rs2 dst) as (Hg1 & Hg2 & Hg3 & Hg4).
  repeat (apply Forall_app; split); auto using get_slot_program_straightline, set_slot_program_straightline.
Qed.

(** The three call sites, restated as an explicit prefix ++ P ++ suffix
    split of add_block, each provable by reflexivity since add_block is a
    fully concrete instruction list once rs1/rs2/dst are given — true
    regardless of how the defining ++-chain associates. *)

Lemma add_block_call1 : forall rs1 rs2 dst,
  add_block rs1 rs2 dst =
    add_glue1 rs1 ++ get_slot_program ++
    (add_glue2 rs2 ++ get_slot_program ++ add_glue3 dst ++ set_slot_program ++ add_glue4).
Proof. reflexivity. Qed.

Lemma add_block_call2 : forall rs1 rs2 dst,
  add_block rs1 rs2 dst =
    (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2) ++ get_slot_program ++
    (add_glue3 dst ++ set_slot_program ++ add_glue4).
Proof. reflexivity. Qed.

Lemma add_block_call3 : forall rs1 rs2 dst,
  add_block rs1 rs2 dst =
    (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2 ++ get_slot_program ++ add_glue3 dst) ++
    set_slot_program ++ add_glue4.
Proof. reflexivity. Qed.

Ltac regne := first [ assumption
                    | (unfold reg_index, REG_COUNT, R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, R13, R14; cbn; lia) ].

(** ---- Phase 1: glue1 (2 steps) + call1 (get_slot_program, 5 steps),
    pc 0 -> 7. Unpacks guest register rs1 into R8, leaving R14 (the
    persistent packed cell) untouched. ---- *)
Lemma add_phase1 : forall regs rs1 rs2 dst s,
  length regs = REG_COUNT -> rs1 < length regs ->
  Forall (fun v => v <= slot_mask) regs ->
  length s.(vm_regs) = REG_COUNT -> s.(vm_pc) = 0 ->
  read_reg s R14 = encode_regs regs ->
  read_reg (run_vm_u 7 (add_block rs1 rs2 dst) s) R8 = nth rs1 regs 0 /\
  read_reg (run_vm_u 7 (add_block rs1 rs2 dst) s) R14 = encode_regs regs /\
  length (run_vm_u 7 (add_block rs1 rs2 dst) s).(vm_regs) = REG_COUNT /\
  (run_vm_u 7 (add_block rs1 rs2 dst) s).(vm_pc) = 7.
Proof.
  intros regs rs1 rs2 dst s Hlenregs Hrs1 Hbound Hlen Hpc HR14.
  set (packed := encode_regs regs).
  assert (Hg1 : get_slot packed rs1 = nth rs1 regs 0) by (apply encode_regs_correct; assumption).
  replace 7 with (2 + 5) by lia.
  rewrite run_vm_u_split.
  (* ---- glue1 (2 steps): pc 0 -> 2, sets R0:=packed, R1:=rs1 ---- *)
  rewrite (run_vm_u_step 1 _ s (instr_xfer R0 R14 0)) by (rewrite Hpc; reflexivity).
  set (t1 := vm_apply_u s (instr_xfer R0 R14 0)).
  assert (Hlen_t1 : length t1.(vm_regs) = REG_COUNT)
    by (unfold t1; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen).
  assert (Hpc_t1 : t1.(vm_pc) = 1) by (unfold t1; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR14_t1 : read_reg t1 R14 = packed)
    by (unfold t1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR14).
  assert (HR0_t1 : read_reg t1 R0 = packed)
    by (unfold t1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen; exact HR14).
  rewrite (run_vm_u_step 0 _ t1 (instr_load_imm R1 rs1 0)) by (rewrite Hpc_t1; reflexivity).
  set (s1 := vm_apply_u t1 (instr_load_imm R1 rs1 0)).
  assert (Hlen_s1 : length s1.(vm_regs) = REG_COUNT)
    by (unfold s1; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen_t1).
  assert (Hpc_s1 : s1.(vm_pc) = 2) by (unfold s1; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_s1 : read_reg s1 R0 = packed)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR0_t1).
  assert (HR1_s1 : read_reg s1 R1 = rs1)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        apply nth_write_reg_u_same; exact Hlen_t1).
  assert (HR14_s1 : read_reg s1 R14 = packed)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR14_t1).
  cbn [run_vm_u] in s1. fold s1.
  (* ---- call 1: get_slot_program embedded at offset 2 (5 steps) ---- *)
  rewrite (add_block_call1 rs1 rs2 dst) in *.
  pose proof (run_vm_u_embed get_slot_program (add_glue1 rs1)
                (add_glue2 rs2 ++ get_slot_program ++ add_glue3 dst ++ set_slot_program ++ add_glue4)
                (reset_pc s1) s1 get_slot_program_straightline (reset_pc_pc0 s1)) as Hemb1.
  assert (Hshift1 : pc_shifted_by (length (add_glue1 rs1)) (reset_pc s1) s1).
  { assert (Hlp : length (add_glue1 rs1) = s1.(vm_pc))
      by (rewrite Hpc_s1; unfold add_glue1; cbn [length]; reflexivity).
    rewrite Hlp. apply pc_shifted_by_reset_pc. }
  specialize (Hemb1 Hshift1).
  assert (Hread1 : read_reg (run_vm_u (length get_slot_program) get_slot_program (reset_pc s1)) R8
                   = get_slot packed rs1).
  { apply get_slot_program_correct.
    - unfold reset_pc; cbn [vm_regs]; exact Hlen_s1.
    - apply reset_pc_pc0.
    - unfold read_reg, reset_pc; cbn [vm_regs]; exact HR0_s1.
    - unfold read_reg, reset_pc; cbn [vm_regs]; exact HR1_s1. }
  assert (Hlen_gs : length get_slot_program = 5) by reflexivity.
  rewrite Hlen_gs in Hemb1, Hread1.
  set (s2 := run_vm_u 5 (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2 ++ get_slot_program ++
                          add_glue3 dst ++ set_slot_program ++ add_glue4) s1).
  fold s2 in Hemb1.
  unfold pc_shifted_by in Hemb1.
  destruct Hemb1 as (Hpc_s2 & _ & _ & Hregs_s2 & _).
  assert (HR8_s2 : read_reg s2 R8 = nth rs1 regs 0).
  { unfold read_reg. rewrite Hregs_s2. unfold read_reg in Hread1. rewrite Hread1, Hg1. reflexivity. }
  assert (Hpc_standalone1 : (run_vm_u 5 get_slot_program (reset_pc s1)).(vm_pc) = 5)
    by (apply (run_vm_u_straightline_pc get_slot_program get_slot_program_straightline 5
                 (reset_pc s1) ltac:(lia) (reset_pc_pc0 s1))).
  assert (Hpc_s2' : s2.(vm_pc) = 7) by (rewrite Hpc_s2, Hpc_standalone1; cbn [add_glue1 length]; lia).
  assert (HR14_s2 : read_reg s2 R14 = packed).
  { assert (Heq : read_reg s2 R14 = read_reg (run_vm_u 5 get_slot_program (reset_pc s1)) R14)
      by (unfold read_reg; rewrite Hregs_s2; reflexivity).
    rewrite Heq.
    rewrite (get_slot_program_preserves (reset_pc s1) R14
               ltac:(unfold reset_pc; cbn [vm_regs]; exact Hlen_s1) (reset_pc_pc0 s1)
               ltac:(regne) ltac:(regne) ltac:(regne) ltac:(regne) ltac:(regne)).
    unfold read_reg, reset_pc; cbn [vm_regs]; exact HR14_s1. }
  assert (Hlen_s2 : length s2.(vm_regs) = REG_COUNT).
  { unfold read_reg in Hregs_s2. rewrite Hregs_s2.
    apply run_vm_u_preserves_reglen; [apply get_slot_program_straightline |].
    unfold reset_pc; cbn [vm_regs]; exact Hlen_s1. }
  rewrite <- (add_block_call1 rs1 rs2 dst). fold s2.
  repeat split; assumption.
Qed.

(** ---- Phase 2: glue2 (3 steps) + call2 (get_slot_program, 5 steps),
    pc 7 -> 15. Moves rs1's value into R11 and unpacks rs2 into R8. ---- *)
Lemma add_phase2 : forall regs rs1 rs2 dst s2,
  length regs = REG_COUNT -> rs2 < length regs ->
  Forall (fun v => v <= slot_mask) regs ->
  read_reg s2 R8 = nth rs1 regs 0 ->
  read_reg s2 R14 = encode_regs regs ->
  length s2.(vm_regs) = REG_COUNT -> s2.(vm_pc) = 7 ->
  read_reg (run_vm_u 8 (add_block rs1 rs2 dst) s2) R11 = nth rs1 regs 0 /\
  read_reg (run_vm_u 8 (add_block rs1 rs2 dst) s2) R8 = nth rs2 regs 0 /\
  read_reg (run_vm_u 8 (add_block rs1 rs2 dst) s2) R14 = encode_regs regs /\
  length (run_vm_u 8 (add_block rs1 rs2 dst) s2).(vm_regs) = REG_COUNT /\
  (run_vm_u 8 (add_block rs1 rs2 dst) s2).(vm_pc) = 15.
Proof.
  intros regs rs1 rs2 dst s2 Hlenregs Hrs2 Hbound HR8_s2 HR14_s2 Hlen_s2 Hpc_s2'.
  set (packed := encode_regs regs).
  assert (Hg2 : get_slot packed rs2 = nth rs2 regs 0) by (apply encode_regs_correct; assumption).
  replace 8 with (3 + 5) by lia.
  rewrite run_vm_u_split.
  (* ---- glue2 (3 steps): pc 7 -> 10, sets R11:=nth rs1, R0:=packed, R1:=rs2 ---- *)
  rewrite (run_vm_u_step 2 _ s2 (instr_xfer R11 R8 0)) by (rewrite Hpc_s2'; reflexivity).
  set (u1 := vm_apply_u s2 (instr_xfer R11 R8 0)).
  assert (Hlen_u1 : length u1.(vm_regs) = REG_COUNT)
    by (unfold u1; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen_s2).
  assert (Hpc_u1 : u1.(vm_pc) = 8) by (unfold u1; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR11_u1 : read_reg u1 R11 = nth rs1 regs 0)
    by (unfold u1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen_s2; exact HR8_s2).
  assert (HR14_u1 : read_reg u1 R14 = packed)
    by (unfold u1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR14_s2).
  rewrite (run_vm_u_step 1 _ u1 (instr_xfer R0 R14 0)) by (rewrite Hpc_u1; reflexivity).
  set (u2 := vm_apply_u u1 (instr_xfer R0 R14 0)).
  assert (Hlen_u2 : length u2.(vm_regs) = REG_COUNT)
    by (unfold u2; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen_u1).
  assert (Hpc_u2 : u2.(vm_pc) = 9) by (unfold u2; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_u2 : read_reg u2 R0 = packed)
    by (unfold u2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen_u1; exact HR14_u1).
  assert (HR11_u2 : read_reg u2 R11 = nth rs1 regs 0)
    by (unfold u2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR11_u1).
  assert (HR14_u2 : read_reg u2 R14 = packed)
    by (unfold u2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR14_u1).
  rewrite (run_vm_u_step 0 _ u2 (instr_load_imm R1 rs2 0)) by (rewrite Hpc_u2; reflexivity).
  set (s3 := vm_apply_u u2 (instr_load_imm R1 rs2 0)).
  assert (Hlen_s3 : length s3.(vm_regs) = REG_COUNT)
    by (unfold s3; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen_u2).
  assert (Hpc_s3 : s3.(vm_pc) = 10) by (unfold s3; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_s3 : read_reg s3 R0 = packed)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR0_u2).
  assert (HR1_s3 : read_reg s3 R1 = rs2)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        apply nth_write_reg_u_same; exact Hlen_u2).
  assert (HR11_s3 : read_reg s3 R11 = nth rs1 regs 0)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR11_u2).
  assert (HR14_s3 : read_reg s3 R14 = packed)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR14_u2).
  cbn [run_vm_u] in s3. fold s3.
  (* Keep the already-characterized state abstract during embedding rewrites. *)
  clearbody s3.
  (* ---- call 2: get_slot_program embedded at offset 10 (5 steps) ---- *)
  pose proof (run_vm_u_embed get_slot_program (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2)
                (add_glue3 dst ++ set_slot_program ++ add_glue4)
                (reset_pc s3) s3 get_slot_program_straightline (reset_pc_pc0 s3)) as Hemb2.
  assert (Hshift2 : pc_shifted_by (length (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2)) (reset_pc s3) s3).
  { assert (Hlp2 : length (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2) = s3.(vm_pc))
      by (rewrite Hpc_s3; unfold add_glue1, add_glue2; cbn [get_slot_program length app]; reflexivity).
    rewrite Hlp2. apply pc_shifted_by_reset_pc. }
  specialize (Hemb2 Hshift2).
  assert (Hread2 : read_reg (run_vm_u (length get_slot_program) get_slot_program (reset_pc s3)) R8
                   = get_slot packed rs2).
  { apply get_slot_program_correct.
    - unfold reset_pc; cbn [vm_regs]; exact Hlen_s3.
    - apply reset_pc_pc0.
    - unfold read_reg, reset_pc; cbn [vm_regs]; exact HR0_s3.
    - unfold read_reg, reset_pc; cbn [vm_regs]; exact HR1_s3. }
  assert (Hlen_gs : length get_slot_program = 5) by reflexivity.
  rewrite Hlen_gs in Hemb2, Hread2.
  set (s4 := run_vm_u 5 (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2 ++ get_slot_program ++
                          add_glue3 dst ++ set_slot_program ++ add_glue4) s3).
  rewrite <- add_block_call2 in Hemb2.
  unfold add_block in Hemb2.
  fold s4 in Hemb2.
  unfold pc_shifted_by in Hemb2.
  destruct Hemb2 as (Hpc_s4 & _ & _ & Hregs_s4 & _).
  assert (HR8_s4 : read_reg s4 R8 = nth rs2 regs 0).
  { unfold read_reg. rewrite Hregs_s4. unfold read_reg in Hread2. rewrite Hread2, Hg2. reflexivity. }
  assert (Hpc_standalone2 : (run_vm_u 5 get_slot_program (reset_pc s3)).(vm_pc) = 5)
    by (apply (run_vm_u_straightline_pc get_slot_program get_slot_program_straightline 5
                 (reset_pc s3) ltac:(lia) (reset_pc_pc0 s3))).
  assert (Hpc_s4' : s4.(vm_pc) = 15) by (rewrite Hpc_s4, Hpc_standalone2; cbn [add_glue1 add_glue2 get_slot_program app length]; lia).
  assert (HR11_s4 : read_reg s4 R11 = nth rs1 regs 0).
  { assert (Heq : read_reg s4 R11 = read_reg (run_vm_u 5 get_slot_program (reset_pc s3)) R11)
      by (unfold read_reg; rewrite Hregs_s4; reflexivity).
    rewrite Heq.
    rewrite (get_slot_program_preserves (reset_pc s3) R11
               ltac:(unfold reset_pc; cbn [vm_regs]; exact Hlen_s3) (reset_pc_pc0 s3)
               ltac:(regne) ltac:(regne) ltac:(regne) ltac:(regne) ltac:(regne)).
    unfold read_reg, reset_pc; cbn [vm_regs]; exact HR11_s3. }
  assert (HR14_s4 : read_reg s4 R14 = packed).
  { assert (Heq : read_reg s4 R14 = read_reg (run_vm_u 5 get_slot_program (reset_pc s3)) R14)
      by (unfold read_reg; rewrite Hregs_s4; reflexivity).
    rewrite Heq.
    rewrite (get_slot_program_preserves (reset_pc s3) R14
               ltac:(unfold reset_pc; cbn [vm_regs]; exact Hlen_s3) (reset_pc_pc0 s3)
               ltac:(regne) ltac:(regne) ltac:(regne) ltac:(regne) ltac:(regne)).
    unfold read_reg, reset_pc; cbn [vm_regs]; exact HR14_s3. }
  assert (Hlen_s4 : length s4.(vm_regs) = REG_COUNT).
  { unfold read_reg in Hregs_s4. rewrite Hregs_s4.
    apply run_vm_u_preserves_reglen; [apply get_slot_program_straightline |].
    unfold reset_pc; cbn [vm_regs]; exact Hlen_s3. }
  fold s4. repeat split; assumption.
Qed.

(** ---- Phase 3: glue3 (5 steps) + call3 (set_slot_program, 15 steps),
    pc 15 -> 35. Adds the two unpacked operands and packs the result into
    slot dst, leaving it in R8. ---- *)
Lemma add_phase3a : forall regs rs1 rs2 dst s4,
  read_reg s4 R11 = nth rs1 regs 0 ->
  read_reg s4 R8 = nth rs2 regs 0 ->
  read_reg s4 R14 = encode_regs regs ->
  length s4.(vm_regs) = REG_COUNT -> s4.(vm_pc) = 15 ->
  read_reg (run_vm_u 5 (add_block rs1 rs2 dst) s4) R0 = encode_regs regs /\
  read_reg (run_vm_u 5 (add_block rs1 rs2 dst) s4) R1 = dst /\
  read_reg (run_vm_u 5 (add_block rs1 rs2 dst) s4) R2 =
    u_add (nth rs1 regs 0) (nth rs2 regs 0) /\
  length (run_vm_u 5 (add_block rs1 rs2 dst) s4).(vm_regs) = REG_COUNT /\
  (run_vm_u 5 (add_block rs1 rs2 dst) s4).(vm_pc) = 20.
Proof.
  intros regs rs1 rs2 dst s4 HR11_s4 HR8_s4 HR14_s4 Hlen_s4 Hpc_s4'.
  set (packed := encode_regs regs).
  (* ---- glue3 (5 steps): preserve operands, add, prepare set_slot ---- *)
  rewrite (run_vm_u_step 4 _ s4 (instr_xfer R12 R8 0)) by (rewrite Hpc_s4'; reflexivity).
  set (v1 := vm_apply_u s4 (instr_xfer R12 R8 0)).
  assert (Hlen_v1 : length v1.(vm_regs) = REG_COUNT)
    by (unfold v1; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen_s4).
  assert (Hpc_v1 : v1.(vm_pc) = 16)
    by (unfold v1; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR12_v1 : read_reg v1 R12 = nth rs2 regs 0)
    by (unfold v1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen_s4; exact HR8_s4).
  assert (HR11_v1 : read_reg v1 R11 = nth rs1 regs 0)
    by (unfold v1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR11_s4).
  assert (HR14_v1 : read_reg v1 R14 = packed)
    by (unfold v1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR14_s4).
  rewrite (run_vm_u_step 3 _ v1 (instr_add R13 R11 R12 0)) by (rewrite Hpc_v1; reflexivity).
  set (v2 := vm_apply_u v1 (instr_add R13 R11 R12 0)).
  assert (Hlen_v2 : length v2.(vm_regs) = REG_COUNT)
    by (unfold v2; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen_v1).
  assert (Hpc_v2 : v2.(vm_pc) = 17)
    by (unfold v2; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR13_v2 : read_reg v2 R13 = u_add (nth rs1 regs 0) (nth rs2 regs 0)).
  { unfold v2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs].
    rewrite nth_write_reg_u_same by exact Hlen_v1.
    change (u_add (read_reg v1 R11) (read_reg v1 R12) =
      u_add (nth rs1 regs 0) (nth rs2 regs 0)).
    rewrite HR11_v1, HR12_v1. reflexivity. }
  assert (HR14_v2 : read_reg v2 R14 = packed)
    by (unfold v2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR14_v1).
  rewrite (run_vm_u_step 2 _ v2 (instr_xfer R0 R14 0)) by (rewrite Hpc_v2; reflexivity).
  set (v3 := vm_apply_u v2 (instr_xfer R0 R14 0)).
  assert (Hlen_v3 : length v3.(vm_regs) = REG_COUNT)
    by (unfold v3; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen_v2).
  assert (Hpc_v3 : v3.(vm_pc) = 18)
    by (unfold v3; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_v3 : read_reg v3 R0 = packed)
    by (unfold v3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen_v2; exact HR14_v2).
  assert (HR13_v3 : read_reg v3 R13 = u_add (nth rs1 regs 0) (nth rs2 regs 0))
    by (unfold v3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR13_v2).
  rewrite (run_vm_u_step 1 _ v3 (instr_load_imm R1 dst 0)) by (rewrite Hpc_v3; reflexivity).
  set (v4 := vm_apply_u v3 (instr_load_imm R1 dst 0)).
  assert (Hlen_v4 : length v4.(vm_regs) = REG_COUNT)
    by (unfold v4; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen_v3).
  assert (Hpc_v4 : v4.(vm_pc) = 19)
    by (unfold v4; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_v4 : read_reg v4 R0 = packed)
    by (unfold v4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR0_v3).
  assert (HR1_v4 : read_reg v4 R1 = dst)
    by (unfold v4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        apply nth_write_reg_u_same; exact Hlen_v3).
  assert (HR13_v4 : read_reg v4 R13 = u_add (nth rs1 regs 0) (nth rs2 regs 0))
    by (unfold v4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR13_v3).
  rewrite (run_vm_u_step 0 _ v4 (instr_xfer R2 R13 0)) by (rewrite Hpc_v4; reflexivity).
  set (s5 := vm_apply_u v4 (instr_xfer R2 R13 0)).
  assert (Hlen_s5 : length s5.(vm_regs) = REG_COUNT)
    by (unfold s5; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen_v4).
  assert (Hpc_s5 : s5.(vm_pc) = 20)
    by (unfold s5; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_s5 : read_reg s5 R0 = packed)
    by (unfold s5, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR0_v4).
  assert (HR1_s5 : read_reg s5 R1 = dst)
    by (unfold s5, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by regne; exact HR1_v4).
  assert (HR2_s5 : read_reg s5 R2 = u_add (nth rs1 regs 0) (nth rs2 regs 0))
    by (unfold s5, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen_v4; exact HR13_v4).
  cbn [run_vm_u] in s5. fold s5.
  unfold packed in HR0_s5. repeat split; assumption.
Qed.

(** ---- Phase 3b: call3 (set_slot_program, 15 steps), pc 20 -> 35. Packs
    the sum into slot dst, leaving the packed result in R8. ---- *)
(* Compare embedding arguments without symbolically executing fifteen steps. *)
Local Opaque run_vm_u.
Lemma add_phase3b : forall regs rs1 rs2 dst sum s5,
  read_reg s5 R0 = encode_regs regs ->
  read_reg s5 R1 = dst ->
  read_reg s5 R2 = sum ->
  length s5.(vm_regs) = REG_COUNT -> s5.(vm_pc) = 20 ->
  read_reg (run_vm_u 15 (add_block rs1 rs2 dst) s5) R8 =
    set_slot (encode_regs regs) dst sum /\
  length (run_vm_u 15 (add_block rs1 rs2 dst) s5).(vm_regs) = REG_COUNT /\
  (run_vm_u 15 (add_block rs1 rs2 dst) s5).(vm_pc) = 35.
Proof.
  intros regs rs1 rs2 dst sum s5 HR0_s5 HR1_s5 HR2_s5 Hlen_s5 Hpc_s5.
  set (packed := encode_regs regs).
  (* ---- call 3: set_slot_program embedded at offset 20 ---- *)
  pose proof (run_vm_u_embed set_slot_program
                (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2 ++
                 get_slot_program ++ add_glue3 dst) add_glue4
                (reset_pc s5) s5 set_slot_program_straightline
                (reset_pc_pc0 s5)) as Hemb3.
  assert (Hshift3 :
    pc_shifted_by
      (length (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2 ++
               get_slot_program ++ add_glue3 dst)) (reset_pc s5) s5).
  { assert (Hlp3 :
      length (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2 ++
              get_slot_program ++ add_glue3 dst) = s5.(vm_pc))
      by (rewrite Hpc_s5; unfold add_glue1, add_glue2, add_glue3;
          cbn [get_slot_program app length]; reflexivity).
    rewrite Hlp3. apply pc_shifted_by_reset_pc. }
  specialize (Hemb3 Hshift3).
  assert (Hread3 :
    read_reg (run_vm_u 15 set_slot_program (reset_pc s5)) R8 =
      set_slot packed dst sum).
  { apply set_slot_program_correct.
    - unfold reset_pc; cbn [vm_regs]; exact Hlen_s5.
    - apply reset_pc_pc0.
    - unfold read_reg, reset_pc; cbn [vm_regs]; exact HR0_s5.
    - unfold read_reg, reset_pc; cbn [vm_regs]; exact HR1_s5.
    - unfold read_reg, reset_pc; cbn [vm_regs]; exact HR2_s5. }
  set (s6 := run_vm_u 15
    (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2 ++ get_slot_program ++
     add_glue3 dst ++ set_slot_program ++ add_glue4) s5).
  rewrite <- add_block_call3 in Hemb3.
  unfold add_block in Hemb3. fold s6 in Hemb3.
  unfold pc_shifted_by in Hemb3.
  destruct Hemb3 as (Hpc_s6 & _ & _ & Hregs_s6 & _).
  change (s6.(vm_pc) =
    length (add_glue1 rs1 ++ get_slot_program ++ add_glue2 rs2 ++
      get_slot_program ++ add_glue3 dst) +
    (run_vm_u 15 set_slot_program (reset_pc s5)).(vm_pc)) in Hpc_s6.
  change (s6.(vm_regs) =
    (run_vm_u 15 set_slot_program (reset_pc s5)).(vm_regs)) in Hregs_s6.
  assert (HR8_s6 : read_reg s6 R8 = set_slot packed dst sum).
  { unfold read_reg. rewrite Hregs_s6.
    unfold read_reg in Hread3. exact Hread3. }
  assert (Hpc_set : (run_vm_u 15 set_slot_program (reset_pc s5)).(vm_pc) = 15)
    by (apply (run_vm_u_straightline_pc set_slot_program set_slot_program_straightline
                 15 (reset_pc s5) ltac:(unfold set_slot_program; cbn; lia)
                 (reset_pc_pc0 s5))).
  assert (Hpc_s6' : s6.(vm_pc) = 35)
    by (rewrite Hpc_s6, Hpc_set; cbn [add_glue1 add_glue2 add_glue3 get_slot_program app length]; lia).
  assert (Hlen_s6 : length s6.(vm_regs) = REG_COUNT).
  { rewrite Hregs_s6. apply run_vm_u_preserves_reglen;
      [apply set_slot_program_straightline |].
    unfold reset_pc; cbn [vm_regs]; exact Hlen_s5. }
  fold s6. unfold packed in HR8_s6. repeat split; assumption.
Qed.

Local Transparent run_vm_u.

(** ---- Phase 4: glue4 (1 step), pc 35 -> 36. Publishes the packed result
    in the persistent R14 cell. ---- *)
Lemma add_phase4 : forall regs rs1 rs2 dst dstv s6,
  read_reg s6 R8 = set_slot (encode_regs regs) dst dstv ->
  length s6.(vm_regs) = REG_COUNT -> s6.(vm_pc) = 35 ->
  dst < length regs ->
  read_reg (run_vm_u 1 (add_block rs1 rs2 dst) s6) R14 =
    encode_regs (list_update_at regs dst dstv).
Proof.
  intros regs rs1 rs2 dst dstv s6 HR8_s6 Hlen_s6 Hpc_s6' Hdst.
  rewrite (run_vm_u_step 0 _ s6 (instr_xfer R14 R8 0)) by (rewrite Hpc_s6'; reflexivity).
  cbn [run_vm_u]. unfold read_reg; cbn [vm_apply_u advance_state_rm vm_regs].
  rewrite nth_write_reg_u_same by exact Hlen_s6.
  rewrite HR8_s6.
  symmetry. apply encode_regs_update. exact Hdst.
Qed.

Theorem add_block_correct : forall regs rs1 rs2 dst s,
  length regs = REG_COUNT ->
  rs1 < length regs -> rs2 < length regs -> dst < length regs ->
  Forall (fun v => v <= slot_mask) regs ->
  length s.(vm_regs) = REG_COUNT ->
  s.(vm_pc) = 0 ->
  read_reg s R14 = encode_regs regs ->
  read_reg (run_vm_u (length (add_block rs1 rs2 dst)) (add_block rs1 rs2 dst) s) R14 =
    encode_regs (list_update_at regs dst (u_add (nth rs1 regs 0) (nth rs2 regs 0))).
Proof.
  intros regs rs1 rs2 dst s Hlenregs Hrs1 Hrs2 Hdst Hbound Hlen Hpc HR14.
  assert (Hlenblock : length (add_block rs1 rs2 dst) = 36)
    by (unfold add_block, add_glue1, add_glue2, add_glue3, add_glue4;
        cbn [get_slot_program set_slot_program length app]; reflexivity).
  rewrite Hlenblock.
  replace 36 with (7 + (8 + (5 + (15 + 1)))) by lia.
  rewrite run_vm_u_split.
  destruct (add_phase1 regs rs1 rs2 dst s Hlenregs Hrs1 Hbound Hlen Hpc HR14)
    as (HR8_s2 & HR14_s2 & Hlen_s2 & Hpc_s2).
  set (s2 := run_vm_u 7 (add_block rs1 rs2 dst) s) in *.
  rewrite run_vm_u_split.
  destruct (add_phase2 regs rs1 rs2 dst s2 Hlenregs Hrs2 Hbound HR8_s2 HR14_s2 Hlen_s2 Hpc_s2)
    as (HR11_s4 & HR8_s4 & HR14_s4 & Hlen_s4 & Hpc_s4).
  set (s4 := run_vm_u 8 (add_block rs1 rs2 dst) s2) in *.
  rewrite run_vm_u_split.
  destruct (add_phase3a regs rs1 rs2 dst s4 HR11_s4 HR8_s4 HR14_s4 Hlen_s4 Hpc_s4)
    as (HR0_s5 & HR1_s5 & HR2_s5 & Hlen_s5 & Hpc_s5).
  set (s5 := run_vm_u 5 (add_block rs1 rs2 dst) s4) in *.
  rewrite run_vm_u_split.
  destruct (add_phase3b regs rs1 rs2 dst (u_add (nth rs1 regs 0) (nth rs2 regs 0)) s5
              HR0_s5 HR1_s5 HR2_s5 Hlen_s5 Hpc_s5)
    as (HR8_s6 & Hlen_s6 & Hpc_s6).
  set (s6 := run_vm_u 15 (add_block rs1 rs2 dst) s5) in *.
  exact (add_phase4 regs rs1 rs2 dst (u_add (nth rs1 regs 0) (nth rs2 regs 0)) s6
           HR8_s6 Hlen_s6 Hpc_s6 Hdst).
Qed.
