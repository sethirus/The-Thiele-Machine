(** CM2 variant: jump on successful decrement; zero falls through.
    This is the control convention of Dudenhefner, FSCD 2022, Definition 2.
    The earlier zero-branch Minsky modules are preserved with their own scope.
    https://doi.org/10.4230/LIPIcs.FSCD.2022.16 *)
From Coq Require Import Arith Lia List.
From Coq Require Import NArith.NArith.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep.
From Kernel Require Import VMUnboundedInterpreterCompose.
From Kernel Require Import VMUnboundedInterpreterCode.
From Kernel Require Import VMUnboundedCM2Interpreter.

Lemma u_and_1_7 : u_and 1 7 = 1. Proof. vm_compute. reflexivity. Qed.
Lemma u_sub_1_1 : u_sub 1 1 = 0. Proof. vm_compute. reflexivity. Qed.

Lemma encoded_opcode_low : forall tag target,
  tag < 8 -> u_and (tag + 8 * target) 7 = tag.
Proof.
  intros tag target Htag. unfold u_and.
  rewrite Nat2N.inj_add, Nat2N.inj_mul.
  apply Nat2N.inj. rewrite N2Nat.id.
  change (N.land (N.of_nat tag + 8 * N.of_nat target)%N (N.ones 3%N) = N.of_nat tag).
  rewrite N.land_ones.
  replace (8 * N.of_nat target)%N with (N.of_nat target * 8)%N by lia.
  rewrite N.Div0.mod_add, N.mod_small by lia. reflexivity.
Qed.

Lemma encoded_target_high : forall tag target,
  tag < 8 -> u_shr (tag + 8 * target) 3 = target.
Proof.
  intros tag target Htag. unfold u_shr.
  rewrite Nat2N.inj_add, Nat2N.inj_mul, N.shiftr_div_pow2.
  apply Nat2N.inj. rewrite N2Nat.id.
  replace (2 ^ N.of_nat 3)%N with 8%N by reflexivity.
  symmetry. apply (N.div_unique _ 8 (N.of_nat target) (N.of_nat tag)); lia.
Qed.

Lemma encode_cm2_opcode_valid : forall i,
  u_and (encode_cm2_instr i) 7 <= 4.
Proof.
  intros [| | |target|target]; cbn [encode_cm2_instr].
  - vm_compute. lia.
  - vm_compute. lia.
  - vm_compute. lia.
  - rewrite encoded_opcode_low by lia. lia.
  - rewrite encoded_opcode_low by lia. lia.
Qed.

Definition cm2_decoded (ambient : VMState) (code width : nat)
    (c : CM2ConfigU) : VMState :=
  let w := cm2_word code width c.(cc_pc) in
  {| vm_graph := ambient.(vm_graph);
     vm_csrs := ambient.(vm_csrs);
     vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                 u_sub (u_shl 1 width) 1; 7; w; 0; 0; u_and w 7; 0;
                 c.(cc_c1); c.(cc_c0); c.(cc_pc); width; code; 0];
     vm_mem := ambient.(vm_mem); vm_pc := 9; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Lemma cm2_decode_correct : forall ambient code width c,
  run_vm_u 9 cm2_interpreter_program (cm2_boundary ambient code width c) =
  cm2_decoded ambient code width c.
Proof.
  intros [graph csrs regs mem hpc mu mut err logic status witness certified]
    code width [pc c0 c1].
  vm_compute.
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r.
Qed.

Definition cm2_decoded_s (ambient : VMState) (code width : nat)
    (c : CM2ConfigU) (z : CM2Scratch) : VMState :=
  let w := cm2_word code width c.(cc_pc) in
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                 u_sub (u_shl 1 width) 1; 7; w; z.(ms6); z.(ms7);
                 u_and w 7; 0; c.(cc_c1); c.(cc_c0); c.(cc_pc);
                 width; code; z.(ms15)];
     vm_mem := ambient.(vm_mem); vm_pc := 9; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Lemma cm2_decode_scratch_correct : forall ambient code width c z,
  run_vm_u 9 cm2_interpreter_program (cm2_boundary_s ambient code width c z) =
  cm2_decoded_s ambient code width c z.
Proof.
  intros [graph csrs regs mem hpc mu mut err logic status witness certified]
    code width [pc c0 c1] [a0 a1 a2 a3 a4 a5 a6 a7 a8 a15].
  vm_compute. repeat f_equal; try lia; try now rewrite !Nat.add_0_r.
Qed.

Lemma cm2_rep_inc0 : forall ambient code width c z,
  cm2_word code width c.(cc_pc) = encode_cm2_instr CM2_Inc0 ->
  exists z',
    run_vm_u 16 cm2_interpreter_program (cm2_boundary_s ambient code width c z) =
    cm2_boundary_s ambient code width
      {| cc_pc := S c.(cc_pc); cc_c0 := S c.(cc_c0); cc_c1 := c.(cc_c1) |} z'.
Proof.
  intros ambient code width [pc c0 c1] [a0 a1 a2 a3 a4 a5 a6 a7 a8 a15] Hword.
  cbn [cc_pc] in Hword.
  exists {| ms0 := pc; ms1 := pc * width; ms2 := 1;
            ms3 := u_sub (u_shl 1 width) 1; ms4 := 7; ms5 := 1;
            ms6 := 1; ms7 := 0; ms8 := 1; ms15 := a15 |}.
  replace 16 with (9 + 7) by lia. rewrite run_vm_u_split, cm2_decode_scratch_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded_s.
  cbn [cc_pc cc_c0 cc_c1 ms6 ms7 ms15]. rewrite Hword. vm_compute.
  unfold cm2_boundary_s. cbn [cc_pc cc_c0 cc_c1 ms0 ms1 ms2 ms3 ms4 ms5 ms6 ms7 ms8 ms15].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity.
  all: match goal with
       | |- ?lhs = S ?x => change (x + 1 = S x); apply Nat.add_1_r
       end.
Qed.

Lemma cm2_rep_inc1 : forall ambient code width c z,
  cm2_word code width c.(cc_pc) = encode_cm2_instr CM2_Inc1 ->
  exists z',
    run_vm_u 20 cm2_interpreter_program (cm2_boundary_s ambient code width c z) =
    cm2_boundary_s ambient code width
      {| cc_pc := S c.(cc_pc); cc_c0 := c.(cc_c0); cc_c1 := S c.(cc_c1) |} z'.
Proof.
  intros ambient code width [pc c0 c1] [a0 a1 a2 a3 a4 a5 a6 a7 a8 a15] Hword.
  cbn [cc_pc] in Hword.
  exists {| ms0 := pc; ms1 := pc * width; ms2 := 1;
            ms3 := u_sub (u_shl 1 width) 1; ms4 := 7; ms5 := 2;
            ms6 := 1; ms7 := 0; ms8 := 2; ms15 := a15 |}.
  replace 20 with (9 + 11) by lia. rewrite run_vm_u_split, cm2_decode_scratch_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded_s.
  cbn [cc_pc cc_c0 cc_c1 ms6 ms7 ms15]. rewrite Hword. vm_compute.
  unfold cm2_boundary_s. cbn [cc_pc cc_c0 cc_c1 ms0 ms1 ms2 ms3 ms4 ms5 ms6 ms7 ms8 ms15].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity.
  all: match goal with
       | |- ?lhs = S ?x => change (x + 1 = S x); apply Nat.add_1_r
       end.
Qed.

Lemma cm2_rep_decjump0_zero : forall ambient code width c z target,
  c.(cc_c0) = 0 ->
  cm2_word code width c.(cc_pc) = encode_cm2_instr (CM2_DecJump0 target) ->
  exists z',
    run_vm_u 23 cm2_interpreter_program (cm2_boundary_s ambient code width c z) =
    cm2_boundary_s ambient code width
      {| cc_pc := S c.(cc_pc); cc_c0 := 0; cc_c1 := c.(cc_c1) |} z'.
Proof.
  intros ambient code width [pc c0 c1] [a0 a1 a2 a3 a4 a5 a6 a7 a8 a15] target Hzero Hword.
  cbn [cc_pc cc_c0] in *. subst c0.
  exists {| ms0 := pc; ms1 := pc * width; ms2 := 1;
            ms3 := u_sub (u_shl 1 width) 1; ms4 := 7; ms5 := 3 + 8 * target;
            ms6 := 3; ms7 := target; ms8 := 3; ms15 := a15 |}.
  replace 23 with (9 + 14) by lia. rewrite run_vm_u_split, cm2_decode_scratch_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded_s.
  cbn [cc_pc cc_c0 cc_c1 ms6 ms7 ms15]. rewrite Hword, encoded_opcode_low by lia.
  pose proof (encoded_target_high 3 target ltac:(lia)) as Htarget. vm_compute in Htarget. vm_compute.
  unfold cm2_boundary_s. cbn [cc_pc cc_c0 cc_c1 ms0 ms1 ms2 ms3 ms4 ms5 ms6 ms7 ms8 ms15].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity; try exact Htarget.
  all: try (change (pc + 1 = S pc); apply Nat.add_1_r).
Qed.

Lemma cm2_rep_decjump0_nonzero : forall ambient code width c z target,
  c.(cc_c0) <> 0 ->
  cm2_word code width c.(cc_pc) = encode_cm2_instr (CM2_DecJump0 target) ->
  exists z',
    run_vm_u 25 cm2_interpreter_program (cm2_boundary_s ambient code width c z) =
    cm2_boundary_s ambient code width
      {| cc_pc := target; cc_c0 := pred c.(cc_c0); cc_c1 := c.(cc_c1) |} z'.
Proof.
  intros ambient code width [pc c0 c1] [a0 a1 a2 a3 a4 a5 a6 a7 a8 a15] target Hnz Hword.
  cbn [cc_pc cc_c0] in *. destruct c0 as [|c0]; [contradiction|].
  exists {| ms0 := pc; ms1 := pc * width; ms2 := 1;
            ms3 := u_sub (u_shl 1 width) 1; ms4 := 7; ms5 := 3 + 8 * target;
            ms6 := 1; ms7 := target; ms8 := 3; ms15 := a15 |}.
  replace 25 with (9 + 16) by lia. rewrite run_vm_u_split, cm2_decode_scratch_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded_s.
  cbn [cc_pc cc_c0 cc_c1 ms6 ms7 ms15]. rewrite Hword, encoded_opcode_low by lia.
  pose proof (encoded_target_high 3 target ltac:(lia)) as Htarget. vm_compute in Htarget. vm_compute.
  unfold cm2_boundary_s. cbn [cc_pc cc_c0 cc_c1 ms0 ms1 ms2 ms3 ms4 ms5 ms6 ms7 ms8 ms15 Nat.pred].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity; try exact Htarget.
  all: try (change (pc + 1 = S pc); apply Nat.add_1_r).
  all: try apply Nat.sub_0_r.
  all: match goal with
       | |- ?lhs = S ?x => change (x + 1 = S x); apply Nat.add_1_r
       | |- _ => exact Htarget
       end.
Qed.

Lemma cm2_rep_decjump1_zero : forall ambient code width c z target,
  c.(cc_c1) = 0 ->
  cm2_word code width c.(cc_pc) = encode_cm2_instr (CM2_DecJump1 target) ->
  exists z',
    run_vm_u 27 cm2_interpreter_program (cm2_boundary_s ambient code width c z) =
    cm2_boundary_s ambient code width
      {| cc_pc := S c.(cc_pc); cc_c0 := c.(cc_c0); cc_c1 := 0 |} z'.
Proof.
  intros ambient code width [pc c0 c1] [a0 a1 a2 a3 a4 a5 a6 a7 a8 a15] target Hzero Hword.
  cbn [cc_pc cc_c1] in *. subst c1.
  exists {| ms0 := pc; ms1 := pc * width; ms2 := 1;
            ms3 := u_sub (u_shl 1 width) 1; ms4 := 7; ms5 := 4 + 8 * target;
            ms6 := 3; ms7 := target; ms8 := 4; ms15 := a15 |}.
  replace 27 with (9 + 18) by lia. rewrite run_vm_u_split, cm2_decode_scratch_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded_s.
  cbn [cc_pc cc_c0 cc_c1 ms6 ms7 ms15]. rewrite Hword, encoded_opcode_low by lia.
  pose proof (encoded_target_high 4 target ltac:(lia)) as Htarget. vm_compute in Htarget. vm_compute.
  unfold cm2_boundary_s. cbn [cc_pc cc_c0 cc_c1 ms0 ms1 ms2 ms3 ms4 ms5 ms6 ms7 ms8 ms15].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity; try exact Htarget.
  all: try (change (pc + 1 = S pc); apply Nat.add_1_r).
Qed.

Lemma cm2_rep_decjump1_nonzero : forall ambient code width c z target,
  c.(cc_c1) <> 0 ->
  cm2_word code width c.(cc_pc) = encode_cm2_instr (CM2_DecJump1 target) ->
  exists z',
    run_vm_u 29 cm2_interpreter_program (cm2_boundary_s ambient code width c z) =
    cm2_boundary_s ambient code width
      {| cc_pc := target; cc_c0 := c.(cc_c0); cc_c1 := pred c.(cc_c1) |} z'.
Proof.
  intros ambient code width [pc c0 c1] [a0 a1 a2 a3 a4 a5 a6 a7 a8 a15] target Hnz Hword.
  cbn [cc_pc cc_c1] in *. destruct c1 as [|c1]; [contradiction|].
  exists {| ms0 := pc; ms1 := pc * width; ms2 := 1;
            ms3 := u_sub (u_shl 1 width) 1; ms4 := 7; ms5 := 4 + 8 * target;
            ms6 := 1; ms7 := target; ms8 := 4; ms15 := a15 |}.
  replace 29 with (9 + 20) by lia. rewrite run_vm_u_split, cm2_decode_scratch_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded_s.
  cbn [cc_pc cc_c0 cc_c1 ms6 ms7 ms15]. rewrite Hword, encoded_opcode_low by lia.
  pose proof (encoded_target_high 4 target ltac:(lia)) as Htarget. vm_compute in Htarget. vm_compute.
  unfold cm2_boundary_s. cbn [cc_pc cc_c0 cc_c1 ms0 ms1 ms2 ms3 ms4 ms5 ms6 ms7 ms8 ms15 Nat.pred].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity; try exact Htarget.
  all: try (change (pc + 1 = S pc); apply Nat.add_1_r).
  all: try apply Nat.sub_0_r.
  all: match goal with
       | |- ?lhs = S ?x => change (x + 1 = S x); apply Nat.add_1_r
       | |- _ => exact Htarget
       end.
Qed.

Definition cm2_after_inc1 (ambient : VMState) (code width : nat)
    (c : CM2ConfigU) : VMState :=
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                 u_sub (u_shl 1 width) 1; 7; 2; 1; 0; 2; 0;
                 S c.(cc_c1); c.(cc_c0); S c.(cc_pc); width; code; 0];
     vm_mem := ambient.(vm_mem); vm_pc := 0; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Lemma cm2_interpreter_inc1_exact : forall ambient code width c,
  cm2_word code width c.(cc_pc) = encode_cm2_instr CM2_Inc1 ->
  run_vm_u 20 cm2_interpreter_program (cm2_boundary ambient code width c) =
  cm2_after_inc1 ambient code width c.
Proof.
  intros ambient code width [pc c0 c1] Hword.
  cbn [cc_pc] in Hword.
  replace 20 with (9 + 11) by lia. rewrite run_vm_u_split, cm2_decode_correct.
  unfold encode_cm2_instr in Hword. cbn [cc_pc] in Hword.
  unfold cm2_decoded. cbn [cc_pc cc_c0 cc_c1]. rewrite Hword.
  vm_compute. unfold cm2_after_inc1. cbn [cc_pc cc_c0 cc_c1].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity.
  all: match goal with
       | |- ?lhs = S ?x => change (x + 1 = S x); apply Nat.add_1_r
       end.
Qed.

Definition cm2_after_jz0 (ambient : VMState) (code width target : nat)
    (c : CM2ConfigU) : VMState :=
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                 u_sub (u_shl 1 width) 1; 7; 3 + 8 * target; 3; target; 3; 0;
                 c.(cc_c1); 0; S c.(cc_pc); width; code; 0];
     vm_mem := ambient.(vm_mem); vm_pc := 0; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Definition cm2_after_dec0 (ambient : VMState) (code width target : nat)
    (c : CM2ConfigU) : VMState :=
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                 u_sub (u_shl 1 width) 1; 7; 3 + 8 * target; 1; target; 3; 0;
                 c.(cc_c1); pred c.(cc_c0); target; width; code; 0];
     vm_mem := ambient.(vm_mem); vm_pc := 0; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Lemma cm2_interpreter_decjump0_zero_exact : forall ambient code width c target,
  c.(cc_c0) = 0 ->
  cm2_word code width c.(cc_pc) = encode_cm2_instr (CM2_DecJump0 target) ->
  run_vm_u 23 cm2_interpreter_program (cm2_boundary ambient code width c) =
  cm2_after_jz0 ambient code width target c.
Proof.
  intros ambient code width [pc c0 c1] target Hzero Hword. cbn [cc_c0 cc_pc] in *.
  subst c0. replace 23 with (9 + 14) by lia. rewrite run_vm_u_split, cm2_decode_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded. cbn [cc_pc cc_c0 cc_c1].
  rewrite Hword, (encoded_opcode_low 3 target ltac:(lia)).
  pose proof (encoded_target_high 3 target ltac:(lia)) as Htarget.
  vm_compute in Htarget.
  vm_compute.
  unfold cm2_after_jz0. cbn [cc_pc cc_c0 cc_c1].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity.
  all: try (change (pc + 1 = S pc); apply Nat.add_1_r).
  all: exact Htarget.
Qed.

Lemma cm2_interpreter_decjump0_nonzero_exact : forall ambient code width c target,
  c.(cc_c0) <> 0 ->
  cm2_word code width c.(cc_pc) = encode_cm2_instr (CM2_DecJump0 target) ->
  run_vm_u 25 cm2_interpreter_program (cm2_boundary ambient code width c) =
  cm2_after_dec0 ambient code width target c.
Proof.
  intros ambient code width [pc c0 c1] target Hnz Hword. cbn [cc_c0 cc_pc] in *.
  destruct c0 as [|c0]; [contradiction|].
  replace 25 with (9 + 16) by lia. rewrite run_vm_u_split, cm2_decode_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded. cbn [cc_pc cc_c0 cc_c1].
  rewrite Hword, (encoded_opcode_low 3 target ltac:(lia)).
  pose proof (encoded_target_high 3 target ltac:(lia)) as Htarget.
  vm_compute in Htarget. vm_compute.
  unfold cm2_after_dec0. cbn [cc_pc cc_c0 cc_c1 Nat.pred].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity.
  all: try apply Nat.sub_0_r.
  all: match goal with
       | |- ?lhs = S ?x => change (x + 1 = S x); apply Nat.add_1_r
       | |- _ => exact Htarget
       end.
Qed.

Definition cm2_after_jz1 (ambient : VMState) (code width target : nat)
    (c : CM2ConfigU) : VMState :=
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                 u_sub (u_shl 1 width) 1; 7; 4 + 8 * target; 3; target; 4; 0;
                 0; c.(cc_c0); S c.(cc_pc); width; code; 0];
     vm_mem := ambient.(vm_mem); vm_pc := 0; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Definition cm2_after_dec1 (ambient : VMState) (code width target : nat)
    (c : CM2ConfigU) : VMState :=
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                 u_sub (u_shl 1 width) 1; 7; 4 + 8 * target; 1; target; 4; 0;
                 pred c.(cc_c1); c.(cc_c0); target; width; code; 0];
     vm_mem := ambient.(vm_mem); vm_pc := 0; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Lemma cm2_interpreter_decjump1_zero_exact : forall ambient code width c target,
  c.(cc_c1) = 0 ->
  cm2_word code width c.(cc_pc) = encode_cm2_instr (CM2_DecJump1 target) ->
  run_vm_u 27 cm2_interpreter_program (cm2_boundary ambient code width c) =
  cm2_after_jz1 ambient code width target c.
Proof.
  intros ambient code width [pc c0 c1] target Hzero Hword. cbn [cc_c1 cc_pc] in *.
  subst c1. replace 27 with (9 + 18) by lia. rewrite run_vm_u_split, cm2_decode_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded. cbn [cc_pc cc_c0 cc_c1].
  rewrite Hword, (encoded_opcode_low 4 target ltac:(lia)).
  pose proof (encoded_target_high 4 target ltac:(lia)) as Htarget.
  vm_compute in Htarget. vm_compute.
  unfold cm2_after_jz1. cbn [cc_pc cc_c0 cc_c1].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity.
  all: try (change (pc + 1 = S pc); apply Nat.add_1_r).
  all: exact Htarget.
Qed.

Lemma cm2_interpreter_decjump1_nonzero_exact : forall ambient code width c target,
  c.(cc_c1) <> 0 ->
  cm2_word code width c.(cc_pc) = encode_cm2_instr (CM2_DecJump1 target) ->
  run_vm_u 29 cm2_interpreter_program (cm2_boundary ambient code width c) =
  cm2_after_dec1 ambient code width target c.
Proof.
  intros ambient code width [pc c0 c1] target Hnz Hword. cbn [cc_c1 cc_pc] in *.
  destruct c1 as [|c1]; [contradiction|].
  replace 29 with (9 + 20) by lia. rewrite run_vm_u_split, cm2_decode_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded. cbn [cc_pc cc_c0 cc_c1].
  rewrite Hword, (encoded_opcode_low 4 target ltac:(lia)).
  pose proof (encoded_target_high 4 target ltac:(lia)) as Htarget.
  vm_compute in Htarget. vm_compute.
  unfold cm2_after_dec1. cbn [cc_pc cc_c0 cc_c1 Nat.pred].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity.
  all: try apply Nat.sub_0_r.
  all: match goal with
       | |- ?lhs = S ?x => change (x + 1 = S x); apply Nat.add_1_r
       | |- _ => exact Htarget
       end.
Qed.

Definition cm2_after_halt (ambient : VMState) (code width : nat)
    (c : CM2ConfigU) : VMState :=
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                 u_sub (u_shl 1 width) 1; 7; 0; 0; 0; 0; 1;
                 c.(cc_c1); c.(cc_c0); c.(cc_pc); width; code; 0];
     vm_mem := ambient.(vm_mem); vm_pc := 60; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Lemma cm2_interpreter_halt_exact : forall ambient code width c,
  cm2_word code width c.(cc_pc) = encode_cm2_instr CM2_Halt ->
  run_vm_u 12 cm2_interpreter_program (cm2_boundary ambient code width c) =
  cm2_after_halt ambient code width c.
Proof.
  intros ambient code width [pc c0 c1] Hword.
  cbn [cc_pc] in Hword.
  replace 12 with (9 + 3) by lia. rewrite run_vm_u_split, cm2_decode_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded. cbn [cc_pc cc_c0 cc_c1].
  rewrite Hword. vm_compute. unfold cm2_after_halt. cbn [cc_pc cc_c0 cc_c1].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity.
Qed.

Lemma cm2_rep_halt : forall ambient code width c z,
  cm2_word code width c.(cc_pc) = encode_cm2_instr CM2_Halt ->
  cm2_halt_rep code width c
    (run_vm_u 12 cm2_interpreter_program (cm2_boundary_s ambient code width c z)).
Proof.
  intros ambient code width [pc c0 c1] [a0 a1 a2 a3 a4 a5 a6 a7 a8 a15] Hword.
  cbn [cc_pc] in Hword. exists ambient,
    {| ms0 := a0; ms1 := a1; ms2 := a2; ms3 := a3; ms4 := a4;
       ms5 := a5; ms6 := a6; ms7 := a7; ms8 := a8; ms15 := a15 |}.
  replace 12 with (9 + 3) by lia. rewrite run_vm_u_split, cm2_decode_scratch_correct.
  unfold encode_cm2_instr in Hword. unfold cm2_decoded_s.
  cbn [cc_pc cc_c0 cc_c1 ms6 ms7 ms15]. rewrite Hword. vm_compute.
  cbn [cc_pc cc_c0 cc_c1 ms6 ms7 ms15].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity.
Qed.

Definition cm2_after_malformed (ambient : VMState) (code width word opcode : nat)
    (c : CM2ConfigU) : VMState :=
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                 u_sub (u_shl 1 width) 1; 7; word; 4; opcode - 4; opcode; 2;
                 c.(cc_c1); c.(cc_c0); c.(cc_pc); width; code; 0];
     vm_mem := ambient.(vm_mem); vm_pc := 60; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Lemma cm2_interpreter_malformed_exact : forall ambient code width c word opcode,
  cm2_word code width c.(cc_pc) = word ->
  u_and word 7 = opcode -> 5 <= opcode <= 7 ->
  run_vm_u 24 cm2_interpreter_program (cm2_boundary ambient code width c) =
  cm2_after_malformed ambient code width word opcode c.
Proof.
  intros ambient code width [pc c0 c1] word opcode Hword Hop Hrange.
  cbn [cc_pc] in Hword.
  replace 24 with (9 + 15) by lia. rewrite run_vm_u_split, cm2_decode_correct.
  unfold cm2_decoded. cbn [cc_pc cc_c0 cc_c1]. rewrite Hword, Hop.
  assert (opcode = 5 \/ opcode = 6 \/ opcode = 7) as [-> | [-> | ->]] by lia;
    vm_compute; unfold cm2_after_malformed; cbn [cc_pc cc_c0 cc_c1];
    repeat f_equal; try lia; try now rewrite !Nat.add_0_r; try reflexivity.
Qed.

Lemma cm2_rep_malformed : forall ambient code width c z word opcode,
  cm2_word code width c.(cc_pc) = word ->
  u_and word 7 = opcode -> 5 <= opcode <= 7 ->
  cm2_malformed
    (run_vm_u 24 cm2_interpreter_program (cm2_boundary_s ambient code width c z)).
Proof.
  intros ambient code width [pc c0 c1] [a0 a1 a2 a3 a4 a5 a6 a7 a8 a15]
    word opcode Hword Hop Hrange. cbn [cc_pc] in Hword.
  replace 24 with (9 + 15) by lia. rewrite run_vm_u_split, cm2_decode_scratch_correct.
  unfold cm2_decoded_s. cbn [cc_pc cc_c0 cc_c1 ms6 ms7 ms15]. rewrite Hword, Hop.
  assert (opcode = 5 \/ opcode = 6 \/ opcode = 7) as [-> | [-> | ->]] by lia;
    vm_compute; unfold cm2_malformed; vm_compute; split; reflexivity.
Qed.

Lemma cm2_halt_rep_observed : forall code width c s,
  cm2_halt_rep code width c s -> cm2_halted s.
Proof.
  intros code width c s (ambient & z & ->).
  unfold cm2_halted. rewrite cm2_interpreter_program_length.
  cbn [read_reg reg_index REG_COUNT]. split; reflexivity.
Qed.

Theorem cm2_guest_trap_unreachable : forall p c, ~ cm2_traps p c.
Proof. intros p c H. exact H. Qed.

Theorem cm2_uniform_interpreter_malformed : forall code width c s word opcode,
  cm2_rep code width c s ->
  cm2_word code width c.(cc_pc) = word ->
  u_and word 7 = opcode -> 5 <= opcode <= 7 ->
  exists s', run_vm_u 24 cm2_interpreter_program s = s' /\ cm2_malformed s'.
Proof.
  intros code width c s word opcode (ambient & z & ->) Hword Hop Hrange.
  exists (run_vm_u 24 cm2_interpreter_program
    (cm2_boundary_s ambient code width c z)). split; [reflexivity|].
  eapply cm2_rep_malformed; eauto.
Qed.

Theorem cm2_halt_malformed_disjoint : forall s,
  cm2_halted s -> cm2_malformed s -> False.
Proof.
  intros s [_ Hhalt] [_ Hbad]. rewrite Hhalt in Hbad. discriminate.
Qed.

(** One guest step is simulated by a finite, strictly positive execution
    of the single fixed host program.  The quantified host state may carry
    arbitrary scratch values at the boundary. *)
Theorem cm2_uniform_interpreter_simulation : forall code width c s i c',
  cm2_rep code width c s ->
  cm2_word code width c.(cc_pc) = encode_cm2_instr i ->
  cm2_step_instr i c = Some c' ->
  exists s',
    0 < cm2_host_steps i c /\
    run_vm_u (cm2_host_steps i c) cm2_interpreter_program s = s' /\
    cm2_rep code width c' s'.
Proof.
  intros code width c s i c' (ambient & z & ->) Hword Hstep.
  destruct i as [| | |target|target].
  - cbn [cm2_step_instr] in Hstep. discriminate.
  - cbn [cm2_step_instr] in Hstep. inversion Hstep; subst c'.
    destruct (cm2_rep_inc0 ambient code width c z Hword) as [z' Hz].
    exists (cm2_boundary_s ambient code width
      {| cc_pc := S c.(cc_pc); cc_c0 := S c.(cc_c0); cc_c1 := c.(cc_c1) |} z').
    cbn [cm2_host_steps]. repeat split; try lia; try exact Hz.
    exists ambient, z'. reflexivity.
  - cbn [cm2_step_instr] in Hstep. inversion Hstep; subst c'.
    destruct (cm2_rep_inc1 ambient code width c z Hword) as [z' Hz].
    exists (cm2_boundary_s ambient code width
      {| cc_pc := S c.(cc_pc); cc_c0 := c.(cc_c0); cc_c1 := S c.(cc_c1) |} z').
    cbn [cm2_host_steps]. repeat split; try lia; try exact Hz.
    exists ambient, z'. reflexivity.
  - cbn [cm2_step_instr] in Hstep.
    destruct (Nat.eqb c.(cc_c0) 0) eqn:E0.
    + pose proof E0 as Eb. apply Nat.eqb_eq in E0. inversion Hstep; subst c'.
      destruct (cm2_rep_decjump0_zero ambient code width c z target E0 Hword) as [z' Hz].
      exists (cm2_boundary_s ambient code width
        {| cc_pc := S c.(cc_pc); cc_c0 := 0; cc_c1 := c.(cc_c1) |} z').
      cbn [cm2_host_steps]. split.
      * rewrite Eb. lia.
      * rewrite Eb. split; [exact Hz|].
      exists ambient, z'. reflexivity.
    + pose proof E0 as Eb. apply Nat.eqb_neq in E0. inversion Hstep; subst c'.
      destruct (cm2_rep_decjump0_nonzero ambient code width c z target E0 Hword) as [z' Hz].
      exists (cm2_boundary_s ambient code width
        {| cc_pc := target; cc_c0 := pred c.(cc_c0); cc_c1 := c.(cc_c1) |} z').
      cbn [cm2_host_steps]. rewrite Eb. split; [lia|]. split; [exact Hz|].
      exists ambient, z'. reflexivity.
  - cbn [cm2_step_instr] in Hstep.
    destruct (Nat.eqb c.(cc_c1) 0) eqn:E1.
    + pose proof E1 as Eb. apply Nat.eqb_eq in E1. inversion Hstep; subst c'.
      destruct (cm2_rep_decjump1_zero ambient code width c z target E1 Hword) as [z' Hz].
      exists (cm2_boundary_s ambient code width
        {| cc_pc := S c.(cc_pc); cc_c0 := c.(cc_c0); cc_c1 := 0 |} z').
      cbn [cm2_host_steps]. rewrite Eb. split; [lia|]. split; [exact Hz|].
      exists ambient, z'. reflexivity.
    + pose proof E1 as Eb. apply Nat.eqb_neq in E1. inversion Hstep; subst c'.
      destruct (cm2_rep_decjump1_nonzero ambient code width c z target E1 Hword) as [z' Hz].
      exists (cm2_boundary_s ambient code width
        {| cc_pc := target; cc_c0 := c.(cc_c0); cc_c1 := pred c.(cc_c1) |} z').
      cbn [cm2_host_steps]. rewrite Eb. split; [lia|]. split; [exact Hz|].
      exists ambient, z'. reflexivity.
Qed.

Definition cm2_after_inc0 (ambient : VMState) (code width : nat)
    (c : CM2ConfigU) : VMState :=
  {| vm_graph := ambient.(vm_graph); vm_csrs := ambient.(vm_csrs);
     vm_regs := [c.(cc_pc); c.(cc_pc) * width; 1;
                 u_sub (u_shl 1 width) 1; 7; 1; 1; 0; 1; 0;
                 c.(cc_c1); S c.(cc_c0); S c.(cc_pc); width; code; 0];
     vm_mem := ambient.(vm_mem); vm_pc := 0; vm_mu := ambient.(vm_mu);
     vm_mu_tensor := ambient.(vm_mu_tensor); vm_err := ambient.(vm_err);
     vm_logic_acc := ambient.(vm_logic_acc); vm_mstatus := ambient.(vm_mstatus);
     vm_witness := ambient.(vm_witness); vm_certified := ambient.(vm_certified) |}.

Lemma cm2_interpreter_inc0_exact : forall ambient code width c,
  cm2_word code width c.(cc_pc) = encode_cm2_instr CM2_Inc0 ->
  run_vm_u 16 cm2_interpreter_program (cm2_boundary ambient code width c) =
  cm2_after_inc0 ambient code width c.
Proof.
  intros ambient code width [pc c0 c1] Hword.
  replace 16 with (9 + 7) by lia. rewrite run_vm_u_split, cm2_decode_correct.
  unfold encode_cm2_instr in Hword. cbn [cc_pc] in Hword.
  unfold cm2_decoded. cbn [cc_pc cc_c0 cc_c1]. rewrite Hword.
  vm_compute. unfold cm2_after_inc0. cbn [cc_pc cc_c0 cc_c1].
  repeat f_equal; try lia; try now rewrite !Nat.add_0_r;
    try now rewrite Nat.add_1_r; try reflexivity.
  all: match goal with
       | |- ?lhs = S ?x => change (x + 1 = S x); apply Nat.add_1_r
       end.
Qed.
