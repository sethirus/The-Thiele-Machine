(** VMUnboundedInterpreterCode.v — Phase 2 of B3: the actual host
    instruction sequences that compute get_slot/set_slot
    (VMUnboundedInterpreterSlots.v) under real vm_apply_u execution, and
    their correctness proofs against that spec.

    Register convention (host registers only; no CALL/RET is used by these
    straight-line programs, so register 15, the CALL/RET stack pointer
    convention elsewhere in this codebase, is deliberately left unused
    here for forward compatibility with later phases that might call
    these as subroutines):

      R0 = packed value (input)
      R1 = slot index i (input)
      R2 = value to write (input, set_slot only)
      R3..R10 = scratch/constants
      R8 (get_slot) / R8 (set_slot) = result, on exit

    Every register used is < REG_COUNT = 16. mu_delta costs are all 0 here
    — this phase proves value correctness only; mirroring the mu-ledger
    increment per guest opcode (part of the eventual ADD block) is a
    separate, later addition once this layer is solid. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep VMUnboundedInterpreterSlots.

(** * 1. Register-write helpers: length preservation and read-after-write,
    for write_reg_u specifically (mirrors the write_reg dichotomy lemmas
    already proved for the bounded model in
    VMWord64BoundednessObstruction.v, redone here for the unbounded one). *)

Lemma nth_firstn_lt : forall {A} (l : list A) n k (d : A),
  k < n -> nth k (firstn n l) d = nth k l d.
Proof.
  induction l as [| x l IH]; intros n k d Hk.
  - destruct n; destruct k; reflexivity.
  - destruct n as [| n']; [lia |]. cbn [firstn].
    destruct k as [| k']; cbn; [reflexivity |]. apply IH. lia.
Qed.

Lemma nth_skipn_add : forall {A} n (l : list A) k (d : A),
  nth k (skipn n l) d = nth (n + k) l d.
Proof.
  induction n as [| n' IH]; intros l k d; cbn; [reflexivity |].
  destruct l as [| x l'].
  - cbn. destruct k; reflexivity.
  - apply IH.
Qed.

Lemma write_reg_u_length : forall s r v,
  length s.(vm_regs) = REG_COUNT -> length (write_reg_u s r v) = REG_COUNT.
Proof.
  intros s r v Hlen. unfold write_reg_u.
  rewrite app_length, app_length, firstn_length, skipn_length, Hlen. cbn [length].
  unfold reg_index.
  pose proof (Nat.mod_upper_bound r REG_COUNT ltac:(unfold REG_COUNT; lia)) as Hb.
  lia.
Qed.

Lemma nth_write_reg_u_same : forall s r v,
  length s.(vm_regs) = REG_COUNT ->
  nth (reg_index r) (write_reg_u s r v) 0 = v.
Proof.
  intros s r v Hlen. unfold write_reg_u.
  assert (Hidx : reg_index r < length s.(vm_regs)).
  { rewrite Hlen. unfold reg_index. apply Nat.mod_upper_bound. unfold REG_COUNT; lia. }
  rewrite app_nth2 by (rewrite firstn_length_le by lia; lia).
  rewrite firstn_length_le by lia.
  replace (reg_index r - reg_index r) with 0 by lia.
  reflexivity.
Qed.

Lemma nth_write_reg_u_other : forall s r r' v,
  length s.(vm_regs) = REG_COUNT ->
  reg_index r <> reg_index r' ->
  nth (reg_index r') (write_reg_u s r v) 0 = nth (reg_index r') s.(vm_regs) 0.
Proof.
  intros s r r' v Hlen Hne. unfold write_reg_u.
  assert (Hidx : reg_index r < length s.(vm_regs)).
  { rewrite Hlen. unfold reg_index. apply Nat.mod_upper_bound. unfold REG_COUNT; lia. }
  destruct (lt_eq_lt_dec (reg_index r') (reg_index r)) as [[Hlt | Heq] | Hgt].
  - rewrite app_nth1 by (rewrite firstn_length_le; lia).
    apply nth_firstn_lt. lia.
  - congruence.
  - rewrite app_nth2 by (rewrite firstn_length_le; lia).
    rewrite firstn_length_le by lia.
    cbn [app].
    destruct (reg_index r' - reg_index r) as [| d] eqn:Hd; [lia |].
    cbn [nth].
    rewrite nth_skipn_add.
    f_equal. lia.
Qed.

(** * 2. Register indices used by the programs below (all < REG_COUNT). *)

Definition R0 : nat := 0.  Definition R1 : nat := 1.  Definition R2 : nat := 2.
Definition R3 : nat := 3.  Definition R4 : nat := 4.  Definition R5 : nat := 5.
Definition R6 : nat := 6.  Definition R7 : nat := 7.  Definition R8 : nat := 8.
Definition R9 : nat := 9.  Definition R10 : nat := 10.

(** * 3. get_slot_program: five instructions, reads R0 (packed), R1 (i),
    leaves the result in R8. Matches get_slot_unfold's
    `u_and (u_shr packed (i*Kn)) slot_mask` term for term. *)

Definition get_slot_program : list vm_instruction :=
  [ instr_load_imm R3 Kn 0
  ; instr_mul R4 R1 R3 0
  ; instr_shr R5 R0 R4 0
  ; instr_load_imm R6 slot_mask 0
  ; instr_and R8 R5 R6 0
  ].

(** A single fetch-execute-advance rewrite step, used to unfold run_vm_u
    through one instruction at a time without re-deriving nth_error facts
    by hand at each call site. *)
Lemma run_vm_u_step : forall fuel trace s instr,
  nth_error trace s.(vm_pc) = Some instr ->
  run_vm_u (S fuel) trace s = run_vm_u fuel trace (vm_apply_u s instr).
Proof. intros fuel trace s instr H. cbn [run_vm_u]. rewrite H. reflexivity. Qed.

Theorem get_slot_program_correct : forall s packed i,
  length s.(vm_regs) = REG_COUNT ->
  s.(vm_pc) = 0 ->
  read_reg s R0 = packed ->
  read_reg s R1 = i ->
  read_reg (run_vm_u 5 get_slot_program s) R8 = get_slot packed i.
Proof.
  intros s packed i Hlen Hpc H0 H1.
  rewrite get_slot_unfold.
  unfold get_slot_program.
  rewrite (run_vm_u_step 4 _ s (instr_load_imm R3 Kn 0))
    by (rewrite Hpc; reflexivity).
  set (s1 := vm_apply_u s (instr_load_imm R3 Kn 0)).
  assert (Hlen1 : length s1.(vm_regs) = REG_COUNT)
    by (unfold s1; cbn [vm_apply_u advance_state_rm vm_regs];
        apply write_reg_u_length; exact Hlen).
  assert (Hpc1 : s1.(vm_pc) = 1)
    by (unfold s1; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_1 : read_reg s1 R0 = packed)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (unfold reg_index, R3, R0; try lia; unfold REG_COUNT; discriminate);
        exact H0).
  assert (HR1_1 : read_reg s1 R1 = i)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (unfold reg_index, R3, R1; try lia; unfold REG_COUNT; discriminate);
        exact H1).
  assert (HR3_1 : read_reg s1 R3 = Kn)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        apply nth_write_reg_u_same; exact Hlen).
  rewrite (run_vm_u_step 3 _ s1 (instr_mul R4 R1 R3 0))
    by (rewrite Hpc1; reflexivity).
  set (s2 := vm_apply_u s1 (instr_mul R4 R1 R3 0)).
  assert (Hlen2 : length s2.(vm_regs) = REG_COUNT)
    by (unfold s2; cbn [vm_apply_u advance_state_rm vm_regs];
        apply write_reg_u_length; exact Hlen1).
  assert (Hpc2 : s2.(vm_pc) = 2)
    by (unfold s2; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_2 : read_reg s2 R0 = packed)
    by (unfold s2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (unfold reg_index, R4, R0; try lia; unfold REG_COUNT; discriminate);
        exact HR0_1).
  assert (HR4_2 : read_reg s2 R4 = i * Kn)
    by (unfold s2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen1;
        unfold u_mul; rewrite HR1_1, HR3_1; reflexivity).
  rewrite (run_vm_u_step 2 _ s2 (instr_shr R5 R0 R4 0))
    by (rewrite Hpc2; reflexivity).
  set (s3 := vm_apply_u s2 (instr_shr R5 R0 R4 0)).
  assert (Hlen3 : length s3.(vm_regs) = REG_COUNT)
    by (unfold s3; cbn [vm_apply_u advance_state_rm vm_regs];
        apply write_reg_u_length; exact Hlen2).
  assert (Hpc3 : s3.(vm_pc) = 3)
    by (unfold s3; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR5_3 : read_reg s3 R5 = u_shr packed (i * Kn))
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen2;
        rewrite HR0_2, HR4_2; reflexivity).
  rewrite (run_vm_u_step 1 _ s3 (instr_load_imm R6 slot_mask 0))
    by (rewrite Hpc3; reflexivity).
  set (s4 := vm_apply_u s3 (instr_load_imm R6 slot_mask 0)).
  assert (Hlen4 : length s4.(vm_regs) = REG_COUNT)
    by (unfold s4; cbn [vm_apply_u advance_state_rm vm_regs];
        apply write_reg_u_length; exact Hlen3).
  assert (Hpc4 : s4.(vm_pc) = 4)
    by (unfold s4; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR5_4 : read_reg s4 R5 = u_shr packed (i * Kn))
    by (unfold s4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (unfold reg_index, R6, R5; try lia; unfold REG_COUNT; discriminate);
        exact HR5_3).
  assert (HR6_4 : read_reg s4 R6 = slot_mask)
    by (unfold s4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        apply nth_write_reg_u_same; exact Hlen3).
  rewrite (run_vm_u_step 0 _ s4 (instr_and R8 R5 R6 0))
    by (rewrite Hpc4; reflexivity).
  cbn [run_vm_u].
  unfold read_reg; cbn [vm_apply_u advance_state_rm vm_regs].
  rewrite nth_write_reg_u_same by exact Hlen4.
  unfold u_and. rewrite HR5_4, HR6_4. reflexivity.
Qed.

(** * 5. set_slot_program: fifteen instructions implementing set_slot's
    high/low/shifted-value split (set_slot_unfold), reading R0 (packed),
    R1 (i), R2 (v), leaving the result in R8. The final two instructions
    (R9 := low_part | shifted_v, then R8 := high_part | R9) match
    set_slot_unfold's right-associated OR grouping exactly, so no
    associativity lemma is needed. *)

Definition set_slot_program : list vm_instruction :=
  [ instr_load_imm R3 Kn 0            (* 0: R3 := 64 *)
  ; instr_mul R4 R1 R3 0              (* 1: R4 := i*64 = shift *)
  ; instr_load_imm R5 1 0             (* 2: R5 := 1 *)
  ; instr_add R6 R1 R5 0              (* 3: R6 := i+1 *)
  ; instr_mul R7 R6 R3 0              (* 4: R7 := (i+1)*64 = shift1 *)
  ; instr_shr R8 R0 R7 0              (* 5: R8 := packed >> shift1 *)
  ; instr_shl R8 R8 R7 0              (* 6: R8 := high_part *)
  ; instr_shl R9 R5 R4 0              (* 7: R9 := 1 << shift = pow *)
  ; instr_sub R9 R9 R5 0              (* 8: R9 := pow - 1 = low_mask *)
  ; instr_and R9 R0 R9 0              (* 9: R9 := low_part *)
  ; instr_load_imm R10 slot_mask 0    (* 10: R10 := mask *)
  ; instr_and R10 R2 R10 0            (* 11: R10 := v' *)
  ; instr_shl R10 R10 R4 0            (* 12: R10 := shifted_v *)
  ; instr_or R9 R9 R10 0              (* 13: R9 := low_part | shifted_v *)
  ; instr_or R8 R8 R9 0               (* 14: R8 := high_part | (low_part | shifted_v) *)
  ].

Theorem set_slot_program_correct : forall s packed i v,
  length s.(vm_regs) = REG_COUNT ->
  s.(vm_pc) = 0 ->
  read_reg s R0 = packed ->
  read_reg s R1 = i ->
  read_reg s R2 = v ->
  read_reg (run_vm_u 15 set_slot_program s) R8 = set_slot packed i v.
Proof.
  intros s packed i v Hlen Hpc H0 H1 H2.
  rewrite set_slot_unfold.
  unfold set_slot_program.
  Ltac reg_ne := unfold reg_index; try lia; unfold REG_COUNT; discriminate.
  (* step 0 *)
  rewrite (run_vm_u_step 14 _ s (instr_load_imm R3 Kn 0)) by (rewrite Hpc; reflexivity).
  set (s1 := vm_apply_u s (instr_load_imm R3 Kn 0)).
  assert (Hlen1 : length s1.(vm_regs) = REG_COUNT)
    by (unfold s1; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen).
  assert (Hpc1 : s1.(vm_pc) = 1) by (unfold s1; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_1 : read_reg s1 R0 = packed)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact H0).
  assert (HR1_1 : read_reg s1 R1 = i)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact H1).
  assert (HR2_1 : read_reg s1 R2 = v)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact H2).
  assert (HR3_1 : read_reg s1 R3 = Kn)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        apply nth_write_reg_u_same; exact Hlen).
  (* step 1 *)
  rewrite (run_vm_u_step 13 _ s1 (instr_mul R4 R1 R3 0)) by (rewrite Hpc1; reflexivity).
  set (s2 := vm_apply_u s1 (instr_mul R4 R1 R3 0)).
  assert (Hlen2 : length s2.(vm_regs) = REG_COUNT)
    by (unfold s2; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen1).
  assert (Hpc2 : s2.(vm_pc) = 2) by (unfold s2; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_2 : read_reg s2 R0 = packed)
    by (unfold s2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR0_1).
  assert (HR1_2 : read_reg s2 R1 = i)
    by (unfold s2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR1_1).
  assert (HR2_2 : read_reg s2 R2 = v)
    by (unfold s2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR2_1).
  assert (HR3_2 : read_reg s2 R3 = Kn)
    by (unfold s2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR3_1).
  assert (HR4_2 : read_reg s2 R4 = i * Kn)
    by (unfold s2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen1;
        unfold u_mul; rewrite HR1_1, HR3_1; reflexivity).
  (* step 2 *)
  rewrite (run_vm_u_step 12 _ s2 (instr_load_imm R5 1 0)) by (rewrite Hpc2; reflexivity).
  set (s3 := vm_apply_u s2 (instr_load_imm R5 1 0)).
  assert (Hlen3 : length s3.(vm_regs) = REG_COUNT)
    by (unfold s3; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen2).
  assert (Hpc3 : s3.(vm_pc) = 3) by (unfold s3; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_3 : read_reg s3 R0 = packed)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR0_2).
  assert (HR1_3 : read_reg s3 R1 = i)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR1_2).
  assert (HR2_3 : read_reg s3 R2 = v)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR2_2).
  assert (HR3_3 : read_reg s3 R3 = Kn)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR3_2).
  assert (HR4_3 : read_reg s3 R4 = i * Kn)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR4_2).
  assert (HR5_3 : read_reg s3 R5 = 1)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        apply nth_write_reg_u_same; exact Hlen2).
  (* step 3 *)
  rewrite (run_vm_u_step 11 _ s3 (instr_add R6 R1 R5 0)) by (rewrite Hpc3; reflexivity).
  set (s4 := vm_apply_u s3 (instr_add R6 R1 R5 0)).
  assert (Hlen4 : length s4.(vm_regs) = REG_COUNT)
    by (unfold s4; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen3).
  assert (Hpc4 : s4.(vm_pc) = 4) by (unfold s4; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_4 : read_reg s4 R0 = packed)
    by (unfold s4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR0_3).
  assert (HR2_4 : read_reg s4 R2 = v)
    by (unfold s4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR2_3).
  assert (HR3_4 : read_reg s4 R3 = Kn)
    by (unfold s4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR3_3).
  assert (HR4_4 : read_reg s4 R4 = i * Kn)
    by (unfold s4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR4_3).
  assert (HR5_4 : read_reg s4 R5 = 1)
    by (unfold s4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR5_3).
  assert (HR6_4 : read_reg s4 R6 = i + 1)
    by (unfold s4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen3;
        unfold u_add; rewrite HR1_3, HR5_3; reflexivity).
  (* step 4 *)
  rewrite (run_vm_u_step 10 _ s4 (instr_mul R7 R6 R3 0)) by (rewrite Hpc4; reflexivity).
  set (s5 := vm_apply_u s4 (instr_mul R7 R6 R3 0)).
  assert (Hlen5 : length s5.(vm_regs) = REG_COUNT)
    by (unfold s5; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen4).
  assert (Hpc5 : s5.(vm_pc) = 5) by (unfold s5; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_5 : read_reg s5 R0 = packed)
    by (unfold s5, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR0_4).
  assert (HR2_5 : read_reg s5 R2 = v)
    by (unfold s5, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR2_4).
  assert (HR4_5 : read_reg s5 R4 = i * Kn)
    by (unfold s5, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR4_4).
  assert (HR5_5 : read_reg s5 R5 = 1)
    by (unfold s5, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR5_4).
  assert (HR7_5 : read_reg s5 R7 = (i + 1) * Kn)
    by (unfold s5, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen4;
        unfold u_mul; rewrite HR6_4, HR3_4; reflexivity).
  (* step 5 *)
  rewrite (run_vm_u_step 9 _ s5 (instr_shr R8 R0 R7 0)) by (rewrite Hpc5; reflexivity).
  set (s6 := vm_apply_u s5 (instr_shr R8 R0 R7 0)).
  assert (Hlen6 : length s6.(vm_regs) = REG_COUNT)
    by (unfold s6; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen5).
  assert (Hpc6 : s6.(vm_pc) = 6) by (unfold s6; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_6 : read_reg s6 R0 = packed)
    by (unfold s6, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR0_5).
  assert (HR2_6 : read_reg s6 R2 = v)
    by (unfold s6, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR2_5).
  assert (HR4_6 : read_reg s6 R4 = i * Kn)
    by (unfold s6, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR4_5).
  assert (HR5_6 : read_reg s6 R5 = 1)
    by (unfold s6, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR5_5).
  assert (HR7_6 : read_reg s6 R7 = (i + 1) * Kn)
    by (unfold s6, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR7_5).
  assert (HR8_6 : read_reg s6 R8 = u_shr packed ((i + 1) * Kn))
    by (unfold s6, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen5;
        unfold u_shr; rewrite HR0_5, HR7_5; reflexivity).
  (* step 6 *)
  rewrite (run_vm_u_step 8 _ s6 (instr_shl R8 R8 R7 0)) by (rewrite Hpc6; reflexivity).
  set (s7 := vm_apply_u s6 (instr_shl R8 R8 R7 0)).
  assert (Hlen7 : length s7.(vm_regs) = REG_COUNT)
    by (unfold s7; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen6).
  assert (Hpc7 : s7.(vm_pc) = 7) by (unfold s7; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_7 : read_reg s7 R0 = packed)
    by (unfold s7, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR0_6).
  assert (HR2_7 : read_reg s7 R2 = v)
    by (unfold s7, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR2_6).
  assert (HR4_7 : read_reg s7 R4 = i * Kn)
    by (unfold s7, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR4_6).
  assert (HR5_7 : read_reg s7 R5 = 1)
    by (unfold s7, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR5_6).
  assert (HR8_7 : read_reg s7 R8 = u_shl (u_shr packed ((i + 1) * Kn)) ((i + 1) * Kn))
    by (unfold s7, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen6;
        unfold u_shl; rewrite HR8_6, HR7_6; reflexivity).
  (* step 7 *)
  rewrite (run_vm_u_step 7 _ s7 (instr_shl R9 R5 R4 0)) by (rewrite Hpc7; reflexivity).
  set (s8 := vm_apply_u s7 (instr_shl R9 R5 R4 0)).
  assert (Hlen8 : length s8.(vm_regs) = REG_COUNT)
    by (unfold s8; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen7).
  assert (Hpc8 : s8.(vm_pc) = 8) by (unfold s8; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_8 : read_reg s8 R0 = packed) by (unfold s8, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR0_7).
  assert (HR2_8 : read_reg s8 R2 = v)
    by (unfold s8, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR2_7).
  assert (HR4_8 : read_reg s8 R4 = i * Kn)
    by (unfold s8, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR4_7).
  assert (HR5_8 : read_reg s8 R5 = 1)
    by (unfold s8, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR5_7).
  assert (HR8_8 : read_reg s8 R8 = u_shl (u_shr packed ((i + 1) * Kn)) ((i + 1) * Kn))
    by (unfold s8, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR8_7).
  assert (HR9_8 : read_reg s8 R9 = u_shl 1 (i * Kn))
    by (unfold s8, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen7;
        unfold u_shl; rewrite HR5_7, HR4_7; reflexivity).
  (* step 8 *)
  rewrite (run_vm_u_step 6 _ s8 (instr_sub R9 R9 R5 0)) by (rewrite Hpc8; reflexivity).
  set (s9 := vm_apply_u s8 (instr_sub R9 R9 R5 0)).
  assert (Hlen9 : length s9.(vm_regs) = REG_COUNT)
    by (unfold s9; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen8).
  assert (Hpc9 : s9.(vm_pc) = 9) by (unfold s9; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR0_9 : read_reg s9 R0 = packed)
    by (unfold s9, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR0_8).
  assert (HR2_9 : read_reg s9 R2 = v)
    by (unfold s9, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR2_8).
  assert (HR4_9 : read_reg s9 R4 = i * Kn)
    by (unfold s9, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR4_8).
  assert (HR8_9 : read_reg s9 R8 = u_shl (u_shr packed ((i + 1) * Kn)) ((i + 1) * Kn))
    by (unfold s9, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR8_8).
  assert (HR9_9 : read_reg s9 R9 = u_sub (u_shl 1 (i * Kn)) 1)
    by (unfold s9, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen8;
        unfold u_sub; rewrite HR9_8, HR5_8; reflexivity).
  (* step 9 *)
  rewrite (run_vm_u_step 5 _ s9 (instr_and R9 R0 R9 0)) by (rewrite Hpc9; reflexivity).
  set (s10 := vm_apply_u s9 (instr_and R9 R0 R9 0)).
  assert (Hlen10 : length s10.(vm_regs) = REG_COUNT)
    by (unfold s10; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen9).
  assert (Hpc10 : s10.(vm_pc) = 10) by (unfold s10; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR2_10 : read_reg s10 R2 = v)
    by (unfold s10, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR2_9).
  assert (HR4_10 : read_reg s10 R4 = i * Kn)
    by (unfold s10, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR4_9).
  assert (HR8_10 : read_reg s10 R8 = u_shl (u_shr packed ((i + 1) * Kn)) ((i + 1) * Kn))
    by (unfold s10, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR8_9).
  assert (HR9_10 : read_reg s10 R9 = u_and packed (u_sub (u_shl 1 (i * Kn)) 1))
    by (unfold s10, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen9;
        unfold u_and; rewrite HR0_9, HR9_9; reflexivity).
  (* step 10 *)
  rewrite (run_vm_u_step 4 _ s10 (instr_load_imm R10 slot_mask 0)) by (rewrite Hpc10; reflexivity).
  set (s11 := vm_apply_u s10 (instr_load_imm R10 slot_mask 0)).
  assert (Hlen11 : length s11.(vm_regs) = REG_COUNT)
    by (unfold s11; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen10).
  assert (Hpc11 : s11.(vm_pc) = 11) by (unfold s11; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR2_11 : read_reg s11 R2 = v)
    by (unfold s11, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR2_10).
  assert (HR4_11 : read_reg s11 R4 = i * Kn)
    by (unfold s11, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR4_10).
  assert (HR8_11 : read_reg s11 R8 = u_shl (u_shr packed ((i + 1) * Kn)) ((i + 1) * Kn))
    by (unfold s11, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR8_10).
  assert (HR9_11 : read_reg s11 R9 = u_and packed (u_sub (u_shl 1 (i * Kn)) 1))
    by (unfold s11, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR9_10).
  assert (HR10_11 : read_reg s11 R10 = slot_mask)
    by (unfold s11, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        apply nth_write_reg_u_same; exact Hlen10).
  (* step 11 *)
  rewrite (run_vm_u_step 3 _ s11 (instr_and R10 R2 R10 0)) by (rewrite Hpc11; reflexivity).
  set (s12 := vm_apply_u s11 (instr_and R10 R2 R10 0)).
  assert (Hlen12 : length s12.(vm_regs) = REG_COUNT)
    by (unfold s12; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen11).
  assert (Hpc12 : s12.(vm_pc) = 12) by (unfold s12; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR4_12 : read_reg s12 R4 = i * Kn)
    by (unfold s12, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR4_11).
  assert (HR8_12 : read_reg s12 R8 = u_shl (u_shr packed ((i + 1) * Kn)) ((i + 1) * Kn))
    by (unfold s12, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR8_11).
  assert (HR9_12 : read_reg s12 R9 = u_and packed (u_sub (u_shl 1 (i * Kn)) 1))
    by (unfold s12, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR9_11).
  assert (HR10_12 : read_reg s12 R10 = u_and v slot_mask)
    by (unfold s12, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen11;
        unfold u_and; rewrite HR2_11, HR10_11; reflexivity).
  (* step 12 *)
  rewrite (run_vm_u_step 2 _ s12 (instr_shl R10 R10 R4 0)) by (rewrite Hpc12; reflexivity).
  set (s13 := vm_apply_u s12 (instr_shl R10 R10 R4 0)).
  assert (Hlen13 : length s13.(vm_regs) = REG_COUNT)
    by (unfold s13; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen12).
  assert (Hpc13 : s13.(vm_pc) = 13) by (unfold s13; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR8_13 : read_reg s13 R8 = u_shl (u_shr packed ((i + 1) * Kn)) ((i + 1) * Kn))
    by (unfold s13, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR8_12).
  assert (HR9_13 : read_reg s13 R9 = u_and packed (u_sub (u_shl 1 (i * Kn)) 1))
    by (unfold s13, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR9_12).
  assert (HR10_13 : read_reg s13 R10 = u_shl (u_and v slot_mask) (i * Kn))
    by (unfold s13, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen12;
        unfold u_shl; rewrite HR10_12, HR4_12; reflexivity).
  (* step 13 *)
  rewrite (run_vm_u_step 1 _ s13 (instr_or R9 R9 R10 0)) by (rewrite Hpc13; reflexivity).
  set (s14 := vm_apply_u s13 (instr_or R9 R9 R10 0)).
  assert (Hlen14 : length s14.(vm_regs) = REG_COUNT)
    by (unfold s14; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen13).
  assert (Hpc14 : s14.(vm_pc) = 14) by (unfold s14; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (HR8_14 : read_reg s14 R8 = u_shl (u_shr packed ((i + 1) * Kn)) ((i + 1) * Kn))
    by (unfold s14, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by reg_ne; exact HR8_13).
  assert (HR9_14 : read_reg s14 R9 =
                     u_or (u_and packed (u_sub (u_shl 1 (i * Kn)) 1))
                          (u_shl (u_and v slot_mask) (i * Kn)))
    by (unfold s14, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_same by exact Hlen13;
        unfold u_or; rewrite HR9_13, HR10_13; reflexivity).
  (* step 14 *)
  rewrite (run_vm_u_step 0 _ s14 (instr_or R8 R8 R9 0)) by (rewrite Hpc14; reflexivity).
  cbn [run_vm_u].
  unfold read_reg; cbn [vm_apply_u advance_state_rm vm_regs].
  rewrite nth_write_reg_u_same by exact Hlen14.
  unfold u_or. rewrite HR8_14, HR9_14. reflexivity.
Qed.

(** * 6. Preservation: any register outside the clobber set is left alone
    by get_slot_program (writes only R3,R4,R5,R6,R8) or set_slot_program
    (writes only R3..R10) — needed to track a "long-lived" register like a
    persistent packed-registers cell across back-to-back subroutine calls
    in an opcode block, without re-deriving each call's step-by-step
    effect on that register from scratch. *)

Theorem get_slot_program_preserves : forall s r,
  length s.(vm_regs) = REG_COUNT -> s.(vm_pc) = 0 ->
  reg_index R3 <> reg_index r -> reg_index R4 <> reg_index r ->
  reg_index R5 <> reg_index r -> reg_index R6 <> reg_index r -> reg_index R8 <> reg_index r ->
  read_reg (run_vm_u 5 get_slot_program s) r = read_reg s r.
Proof.
  intros s r Hlen Hpc0 H3 H4 H5 H6 H8.
  unfold get_slot_program.
  rewrite (run_vm_u_step 4 _ s (instr_load_imm R3 Kn 0)) by (rewrite Hpc0; reflexivity).
  set (s1 := vm_apply_u s (instr_load_imm R3 Kn 0)).
  assert (Hlen1 : length s1.(vm_regs) = REG_COUNT)
    by (unfold s1; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen).
  assert (Hpc1 : s1.(vm_pc) = 1) by (unfold s1; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hr1 : read_reg s1 r = read_reg s r)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        apply nth_write_reg_u_other; [exact Hlen | exact H3]).
  rewrite (run_vm_u_step 3 _ s1 (instr_mul R4 R1 R3 0)) by (rewrite Hpc1; reflexivity).
  set (s2 := vm_apply_u s1 (instr_mul R4 R1 R3 0)).
  assert (Hlen2 : length s2.(vm_regs) = REG_COUNT)
    by (unfold s2; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen1).
  assert (Hpc2 : s2.(vm_pc) = 2) by (unfold s2; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hr2 : read_reg s2 r = read_reg s r)
    by (unfold s2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen1 || exact H4); exact Hr1).
  rewrite (run_vm_u_step 2 _ s2 (instr_shr R5 R0 R4 0)) by (rewrite Hpc2; reflexivity).
  set (s3 := vm_apply_u s2 (instr_shr R5 R0 R4 0)).
  assert (Hlen3 : length s3.(vm_regs) = REG_COUNT)
    by (unfold s3; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen2).
  assert (Hpc3 : s3.(vm_pc) = 3) by (unfold s3; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hr3 : read_reg s3 r = read_reg s r)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen2 || exact H5); exact Hr2).
  rewrite (run_vm_u_step 1 _ s3 (instr_load_imm R6 slot_mask 0)) by (rewrite Hpc3; reflexivity).
  set (s4 := vm_apply_u s3 (instr_load_imm R6 slot_mask 0)).
  assert (Hlen4 : length s4.(vm_regs) = REG_COUNT)
    by (unfold s4; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen3).
  assert (Hpc4 : s4.(vm_pc) = 4) by (unfold s4; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hr4 : read_reg s4 r = read_reg s r)
    by (unfold s4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen3 || exact H6); exact Hr3).
  rewrite (run_vm_u_step 0 _ s4 (instr_and R8 R5 R6 0)) by (rewrite Hpc4; reflexivity).
  cbn [run_vm_u].
  unfold read_reg; cbn [vm_apply_u advance_state_rm vm_regs].
  rewrite nth_write_reg_u_other by (exact Hlen4 || exact H8). exact Hr4.
Qed.

Theorem set_slot_program_preserves : forall s r,
  length s.(vm_regs) = REG_COUNT -> s.(vm_pc) = 0 ->
  reg_index R3 <> reg_index r -> reg_index R4 <> reg_index r -> reg_index R5 <> reg_index r ->
  reg_index R6 <> reg_index r -> reg_index R7 <> reg_index r -> reg_index R8 <> reg_index r ->
  reg_index R9 <> reg_index r -> reg_index R10 <> reg_index r ->
  read_reg (run_vm_u 15 set_slot_program s) r = read_reg s r.
Proof.
  intros s r Hlen Hpc0 H3 H4 H5 H6 H7 H8 H9 H10.
  unfold set_slot_program.
  rewrite (run_vm_u_step 14 _ s (instr_load_imm R3 Kn 0)) by (rewrite Hpc0; reflexivity).
  set (s1 := vm_apply_u s (instr_load_imm R3 Kn 0)).
  assert (Hpc1 : s1.(vm_pc) = 1) by (unfold s1; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen1 : length s1.(vm_regs) = REG_COUNT)
    by (unfold s1; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen).
  assert (Hr1 : read_reg s1 r = read_reg s r)
    by (unfold s1, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        apply nth_write_reg_u_other; [exact Hlen | exact H3]).
  rewrite (run_vm_u_step 13 _ s1 (instr_mul R4 R1 R3 0)) by (rewrite Hpc1; reflexivity).
  set (s2 := vm_apply_u s1 (instr_mul R4 R1 R3 0)).
  assert (Hpc2 : s2.(vm_pc) = 2) by (unfold s2; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen2 : length s2.(vm_regs) = REG_COUNT)
    by (unfold s2; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen1).
  assert (Hr2 : read_reg s2 r = read_reg s r)
    by (unfold s2, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen1 || exact H4); exact Hr1).
  rewrite (run_vm_u_step 12 _ s2 (instr_load_imm R5 1 0)) by (rewrite Hpc2; reflexivity).
  set (s3 := vm_apply_u s2 (instr_load_imm R5 1 0)).
  assert (Hpc3 : s3.(vm_pc) = 3) by (unfold s3; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen3 : length s3.(vm_regs) = REG_COUNT)
    by (unfold s3; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen2).
  assert (Hr3 : read_reg s3 r = read_reg s r)
    by (unfold s3, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen2 || exact H5); exact Hr2).
  rewrite (run_vm_u_step 11 _ s3 (instr_add R6 R1 R5 0)) by (rewrite Hpc3; reflexivity).
  set (s4 := vm_apply_u s3 (instr_add R6 R1 R5 0)).
  assert (Hpc4 : s4.(vm_pc) = 4) by (unfold s4; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen4 : length s4.(vm_regs) = REG_COUNT)
    by (unfold s4; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen3).
  assert (Hr4 : read_reg s4 r = read_reg s r)
    by (unfold s4, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen3 || exact H6); exact Hr3).
  rewrite (run_vm_u_step 10 _ s4 (instr_mul R7 R6 R3 0)) by (rewrite Hpc4; reflexivity).
  set (s5 := vm_apply_u s4 (instr_mul R7 R6 R3 0)).
  assert (Hpc5 : s5.(vm_pc) = 5) by (unfold s5; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen5 : length s5.(vm_regs) = REG_COUNT)
    by (unfold s5; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen4).
  assert (Hr5 : read_reg s5 r = read_reg s r)
    by (unfold s5, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen4 || exact H7); exact Hr4).
  rewrite (run_vm_u_step 9 _ s5 (instr_shr R8 R0 R7 0)) by (rewrite Hpc5; reflexivity).
  set (s6 := vm_apply_u s5 (instr_shr R8 R0 R7 0)).
  assert (Hpc6 : s6.(vm_pc) = 6) by (unfold s6; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen6 : length s6.(vm_regs) = REG_COUNT)
    by (unfold s6; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen5).
  assert (Hr6 : read_reg s6 r = read_reg s r)
    by (unfold s6, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen5 || exact H8); exact Hr5).
  rewrite (run_vm_u_step 8 _ s6 (instr_shl R8 R8 R7 0)) by (rewrite Hpc6; reflexivity).
  set (s7 := vm_apply_u s6 (instr_shl R8 R8 R7 0)).
  assert (Hpc7 : s7.(vm_pc) = 7) by (unfold s7; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen7 : length s7.(vm_regs) = REG_COUNT)
    by (unfold s7; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen6).
  assert (Hr7 : read_reg s7 r = read_reg s r)
    by (unfold s7, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen6 || exact H8); exact Hr6).
  rewrite (run_vm_u_step 7 _ s7 (instr_shl R9 R5 R4 0)) by (rewrite Hpc7; reflexivity).
  set (s8 := vm_apply_u s7 (instr_shl R9 R5 R4 0)).
  assert (Hpc8 : s8.(vm_pc) = 8) by (unfold s8; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen8 : length s8.(vm_regs) = REG_COUNT)
    by (unfold s8; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen7).
  assert (Hr8 : read_reg s8 r = read_reg s r)
    by (unfold s8, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen7 || exact H9); exact Hr7).
  rewrite (run_vm_u_step 6 _ s8 (instr_sub R9 R9 R5 0)) by (rewrite Hpc8; reflexivity).
  set (s9 := vm_apply_u s8 (instr_sub R9 R9 R5 0)).
  assert (Hpc9 : s9.(vm_pc) = 9) by (unfold s9; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen9 : length s9.(vm_regs) = REG_COUNT)
    by (unfold s9; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen8).
  assert (Hr9 : read_reg s9 r = read_reg s r)
    by (unfold s9, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen8 || exact H9); exact Hr8).
  rewrite (run_vm_u_step 5 _ s9 (instr_and R9 R0 R9 0)) by (rewrite Hpc9; reflexivity).
  set (s10 := vm_apply_u s9 (instr_and R9 R0 R9 0)).
  assert (Hpc10 : s10.(vm_pc) = 10) by (unfold s10; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen10 : length s10.(vm_regs) = REG_COUNT)
    by (unfold s10; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen9).
  assert (Hr10 : read_reg s10 r = read_reg s r)
    by (unfold s10, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen9 || exact H9); exact Hr9).
  rewrite (run_vm_u_step 4 _ s10 (instr_load_imm R10 slot_mask 0)) by (rewrite Hpc10; reflexivity).
  set (s11 := vm_apply_u s10 (instr_load_imm R10 slot_mask 0)).
  assert (Hpc11 : s11.(vm_pc) = 11) by (unfold s11; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen11 : length s11.(vm_regs) = REG_COUNT)
    by (unfold s11; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen10).
  assert (Hr11 : read_reg s11 r = read_reg s r)
    by (unfold s11, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen10 || exact H10); exact Hr10).
  rewrite (run_vm_u_step 3 _ s11 (instr_and R10 R2 R10 0)) by (rewrite Hpc11; reflexivity).
  set (s12 := vm_apply_u s11 (instr_and R10 R2 R10 0)).
  assert (Hpc12 : s12.(vm_pc) = 12) by (unfold s12; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen12 : length s12.(vm_regs) = REG_COUNT)
    by (unfold s12; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen11).
  assert (Hr12 : read_reg s12 r = read_reg s r)
    by (unfold s12, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen11 || exact H10); exact Hr11).
  rewrite (run_vm_u_step 2 _ s12 (instr_shl R10 R10 R4 0)) by (rewrite Hpc12; reflexivity).
  set (s13 := vm_apply_u s12 (instr_shl R10 R10 R4 0)).
  assert (Hpc13 : s13.(vm_pc) = 13) by (unfold s13; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen13 : length s13.(vm_regs) = REG_COUNT)
    by (unfold s13; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen12).
  assert (Hr13 : read_reg s13 r = read_reg s r)
    by (unfold s13, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen12 || exact H10); exact Hr12).
  rewrite (run_vm_u_step 1 _ s13 (instr_or R9 R9 R10 0)) by (rewrite Hpc13; reflexivity).
  set (s14 := vm_apply_u s13 (instr_or R9 R9 R10 0)).
  assert (Hpc14 : s14.(vm_pc) = 14) by (unfold s14; cbn [vm_apply_u advance_state_rm vm_pc]; lia).
  assert (Hlen14 : length s14.(vm_regs) = REG_COUNT)
    by (unfold s14; cbn [vm_apply_u advance_state_rm vm_regs]; apply write_reg_u_length; exact Hlen13).
  assert (Hr14 : read_reg s14 r = read_reg s r)
    by (unfold s14, read_reg; cbn [vm_apply_u advance_state_rm vm_regs];
        rewrite nth_write_reg_u_other by (exact Hlen13 || exact H9); exact Hr13).
  rewrite (run_vm_u_step 0 _ s14 (instr_or R8 R8 R9 0)) by (rewrite Hpc14; reflexivity).
  cbn [run_vm_u].
  unfold read_reg; cbn [vm_apply_u advance_state_rm vm_regs].
  rewrite nth_write_reg_u_other by (exact Hlen14 || exact H8). exact Hr14.
Qed.
