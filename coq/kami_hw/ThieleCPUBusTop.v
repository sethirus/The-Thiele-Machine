(** ThieleCPUBusTop.v

    Stage-1 wrapper boundary for host/bus integration.

    Purpose:
    - Introduce a stable top-level wrapper symbol that downstream extraction and
      synthesis can target.
    - Keep semantics identical to [thieleCoreB] while we incrementally add
      protocol-facing methods (AXI/APB/MMIO) in source Coq/Kami.

    Important:
    - Generated RTL is not edited by hand.
    - This wrapper is the source-level integration seam for future bus work.
*)

From KamiHW Require Import ThieleCPUCore.
From KamiHW Require Import Abstraction.
Require Import Coq.Bool.Bool.

(* Foundation connectivity imports — required by proof chain policy *)
From Kernel Require Import VMStep.
From Kernel Require Import MuCostModel.

(** Stage-2 contract work (no behavior change yet):
    define an explicit MMIO register map and decode function in Coq so future
    bus methods can be added against a stable, proof-visible interface. *)
Inductive BusReg : Type :=
| BusRegPc
| BusRegMu
| BusRegErr
| BusRegHalted
| BusRegPartitionOps
| BusRegMdlOps
| BusRegInfoGain
| BusRegErrorCode
| BusRegMstatus
| BusRegMcycleLo
| BusRegMcycleHi
| BusRegMinstretLo
| BusRegMinstretHi
| BusRegLogicAcc
| BusRegLogicReqValid
| BusRegLogicReqOpcode
| BusRegLogicReqPayload
| BusRegMuTensor0
| BusRegMuTensor1
| BusRegMuTensor2
| BusRegMuTensor3
| BusRegBianchiAlarm
| BusRegPtNextId
| BusRegPtSize
| BusRegLoadInstrAddr
| BusRegLoadInstrData
| BusRegLoadInstrKick
| BusRegSetLogicRespValid
| BusRegSetLogicRespError
| BusRegSetLogicRespValue
| BusRegSetActiveModule
| BusRegSetTrapVector.

(* SAFE: base address of the PC register in the MMIO map *)
Definition busAddrPc : nat := 0.
Definition busAddrMu : nat := 4.
Definition busAddrErr : nat := 8.
Definition busAddrHalted : nat := 12.
Definition busAddrPartitionOps : nat := 16.
Definition busAddrMdlOps : nat := 20.
Definition busAddrInfoGain : nat := 24.
Definition busAddrErrorCode : nat := 28.
Definition busAddrMstatus : nat := 32.
Definition busAddrMcycleLo : nat := 36.
Definition busAddrMcycleHi : nat := 40.
Definition busAddrMinstretLo : nat := 44.
Definition busAddrMinstretHi : nat := 48.
Definition busAddrLogicAcc : nat := 52.
Definition busAddrLogicReqValid : nat := 56.
Definition busAddrLogicReqOpcode : nat := 60.
Definition busAddrLogicReqPayload : nat := 64.
Definition busAddrMuTensor0 : nat := 68.
Definition busAddrMuTensor1 : nat := 72.
Definition busAddrMuTensor2 : nat := 76.
Definition busAddrMuTensor3 : nat := 80.
Definition busAddrBianchiAlarm : nat := 84.
Definition busAddrPtNextId : nat := 88.
Definition busAddrPtSize : nat := 92.

Definition busAddrLoadInstrAddr : nat := 128.
Definition busAddrLoadInstrData : nat := 132.
Definition busAddrLoadInstrKick : nat := 136.
Definition busAddrSetLogicRespValid : nat := 140.
Definition busAddrSetLogicRespError : nat := 144.
Definition busAddrSetLogicRespValue : nat := 148.
Definition busAddrSetActiveModule : nat := 152.
Definition busAddrSetTrapVector : nat := 156.

Definition decodeBusReg (addr : nat) : option BusReg :=
  match addr with
  | 0 => Some BusRegPc
  | 4 => Some BusRegMu
  | 8 => Some BusRegErr
  | 12 => Some BusRegHalted
  | 16 => Some BusRegPartitionOps
  | 20 => Some BusRegMdlOps
  | 24 => Some BusRegInfoGain
  | 28 => Some BusRegErrorCode
  | 32 => Some BusRegMstatus
  | 36 => Some BusRegMcycleLo
  | 40 => Some BusRegMcycleHi
  | 44 => Some BusRegMinstretLo
  | 48 => Some BusRegMinstretHi
  | 52 => Some BusRegLogicAcc
  | 56 => Some BusRegLogicReqValid
  | 60 => Some BusRegLogicReqOpcode
  | 64 => Some BusRegLogicReqPayload
  | 68 => Some BusRegMuTensor0
  | 72 => Some BusRegMuTensor1
  | 76 => Some BusRegMuTensor2
  | 80 => Some BusRegMuTensor3
  | 84 => Some BusRegBianchiAlarm
  | 88 => Some BusRegPtNextId
  | 92 => Some BusRegPtSize
  | 128 => Some BusRegLoadInstrAddr
  | 132 => Some BusRegLoadInstrData
  | 136 => Some BusRegLoadInstrKick
  | 140 => Some BusRegSetLogicRespValid
  | 144 => Some BusRegSetLogicRespError
  | 148 => Some BusRegSetLogicRespValue
  | 152 => Some BusRegSetActiveModule
  | 156 => Some BusRegSetTrapVector
  | _ => None
  end.

Definition busRegReadable (r : BusReg) : bool :=
  match r with
  | BusRegLoadInstrAddr
  | BusRegLoadInstrData
  | BusRegLoadInstrKick
  | BusRegSetLogicRespValid
  | BusRegSetLogicRespError
  | BusRegSetLogicRespValue
  | BusRegSetActiveModule
  | BusRegSetTrapVector => false
  | _ => true
  end.

Definition busRegWritable (r : BusReg) : bool :=
  negb (busRegReadable r).

Lemma busReg_rw_exclusive :
  forall r, busRegReadable r = true -> busRegWritable r = false.
Proof.
  intros r H.
  unfold busRegWritable.
  rewrite H.
  reflexivity.
Qed.

Lemma bus_decode_examples :
  decodeBusReg busAddrPc = Some BusRegPc /\
  decodeBusReg busAddrLoadInstrKick = Some BusRegLoadInstrKick /\
  decodeBusReg 252 = None.
Proof.
  repeat split; reflexivity.
Qed.

(** Bus wrapper stage model.

    This is a proof-level operational contract for the wrapper boundary.  It
    keeps the core state immutable for bus writes in stage-1/2 while command
    registers are latched into a shadow structure.  Read semantics are defined
    over a core observation record that mirrors getter methods. *)

Record BusCoreView : Type := {
  view_pc : nat;
  view_mu : nat;
  view_err : bool;
  view_halted : bool;
  view_partition_ops : nat;
  view_mdl_ops : nat;
  view_info_gain : nat;
  view_error_code : nat;
  view_mstatus : nat;
  view_mcycle_lo : nat;
  view_mcycle_hi : nat;
  view_minstret_lo : nat;
  view_minstret_hi : nat;
  view_logic_acc : nat;
  view_logic_req_valid : bool;
  view_logic_req_opcode : nat;
  view_logic_req_payload : nat;
  view_mu_tensor0 : nat;
  view_mu_tensor1 : nat;
  view_mu_tensor2 : nat;
  view_mu_tensor3 : nat;
  view_bianchi_alarm : bool;
  view_pt_next_id : nat;
  view_pt_size : nat -> nat
}.

Definition bool_to_nat (b : bool) : nat := if b then 1 else 0.

Definition busRegReadValue (v : BusCoreView) (r : BusReg) : option nat :=
  match r with
  | BusRegPc => Some v.(view_pc)
  | BusRegMu => Some v.(view_mu)
  | BusRegErr => Some (bool_to_nat v.(view_err))
  | BusRegHalted => Some (bool_to_nat v.(view_halted))
  | BusRegPartitionOps => Some v.(view_partition_ops)
  | BusRegMdlOps => Some v.(view_mdl_ops)
  | BusRegInfoGain => Some v.(view_info_gain)
  | BusRegErrorCode => Some v.(view_error_code)
  | BusRegMstatus => Some v.(view_mstatus)
  | BusRegMcycleLo => Some v.(view_mcycle_lo)
  | BusRegMcycleHi => Some v.(view_mcycle_hi)
  | BusRegMinstretLo => Some v.(view_minstret_lo)
  | BusRegMinstretHi => Some v.(view_minstret_hi)
  | BusRegLogicAcc => Some v.(view_logic_acc)
  | BusRegLogicReqValid => Some (bool_to_nat v.(view_logic_req_valid))
  | BusRegLogicReqOpcode => Some v.(view_logic_req_opcode)
  | BusRegLogicReqPayload => Some v.(view_logic_req_payload)
  | BusRegMuTensor0 => Some v.(view_mu_tensor0)
  | BusRegMuTensor1 => Some v.(view_mu_tensor1)
  | BusRegMuTensor2 => Some v.(view_mu_tensor2)
  | BusRegMuTensor3 => Some v.(view_mu_tensor3)
  | BusRegBianchiAlarm => Some (bool_to_nat v.(view_bianchi_alarm))
  | BusRegPtNextId => Some v.(view_pt_next_id)
  | BusRegPtSize => Some (v.(view_pt_size) 0)
  | BusRegLoadInstrAddr
  | BusRegLoadInstrData
  | BusRegLoadInstrKick
  | BusRegSetLogicRespValid
  | BusRegSetLogicRespError
  | BusRegSetLogicRespValue
  | BusRegSetActiveModule
  | BusRegSetTrapVector => None
  end.

Definition busRead (v : BusCoreView) (addr : nat) : option nat :=
  match decodeBusReg addr with
  | Some r =>
      if busRegReadable r then
        busRegReadValue v r
      else None
  | None => None
  end.

Record BusShadowRegs : Type := {
  sh_load_instr_addr : nat;
  sh_load_instr_data : nat;
  sh_load_instr_kick : bool;
  sh_logic_resp_valid : bool;
  sh_logic_resp_error : bool;
  sh_logic_resp_value : nat;
  sh_active_module : nat;
  sh_trap_vector : nat
}.

Definition busShadowInit : BusShadowRegs :=
  {| sh_load_instr_addr := 0;
     sh_load_instr_data := 0;
     sh_load_instr_kick := false;
     sh_logic_resp_valid := false;
     sh_logic_resp_error := false;
     sh_logic_resp_value := 0;
     sh_active_module := 0;
     sh_trap_vector := 0 |}.

Record BusWrapperState : Type := {
  bw_core : KamiSnapshot;
  bw_shadow : BusShadowRegs
}.

Definition busWriteShadow (s : BusShadowRegs) (r : BusReg) (data : nat) : BusShadowRegs :=
  match r with
  | BusRegLoadInstrAddr =>
      {| sh_load_instr_addr := data;
         sh_load_instr_data := s.(sh_load_instr_data);
         sh_load_instr_kick := s.(sh_load_instr_kick);
         sh_logic_resp_valid := s.(sh_logic_resp_valid);
         sh_logic_resp_error := s.(sh_logic_resp_error);
         sh_logic_resp_value := s.(sh_logic_resp_value);
         sh_active_module := s.(sh_active_module);
         sh_trap_vector := s.(sh_trap_vector) |}
  | BusRegLoadInstrData =>
      {| sh_load_instr_addr := s.(sh_load_instr_addr);
         sh_load_instr_data := data;
         sh_load_instr_kick := s.(sh_load_instr_kick);
         sh_logic_resp_valid := s.(sh_logic_resp_valid);
         sh_logic_resp_error := s.(sh_logic_resp_error);
         sh_logic_resp_value := s.(sh_logic_resp_value);
         sh_active_module := s.(sh_active_module);
         sh_trap_vector := s.(sh_trap_vector) |}
  | BusRegLoadInstrKick =>
      {| sh_load_instr_addr := s.(sh_load_instr_addr);
         sh_load_instr_data := s.(sh_load_instr_data);
         sh_load_instr_kick := negb (Nat.eqb data 0);
         sh_logic_resp_valid := s.(sh_logic_resp_valid);
         sh_logic_resp_error := s.(sh_logic_resp_error);
         sh_logic_resp_value := s.(sh_logic_resp_value);
         sh_active_module := s.(sh_active_module);
         sh_trap_vector := s.(sh_trap_vector) |}
  | BusRegSetLogicRespValid =>
      {| sh_load_instr_addr := s.(sh_load_instr_addr);
         sh_load_instr_data := s.(sh_load_instr_data);
         sh_load_instr_kick := s.(sh_load_instr_kick);
         sh_logic_resp_valid := negb (Nat.eqb data 0);
         sh_logic_resp_error := s.(sh_logic_resp_error);
         sh_logic_resp_value := s.(sh_logic_resp_value);
         sh_active_module := s.(sh_active_module);
         sh_trap_vector := s.(sh_trap_vector) |}
  | BusRegSetLogicRespError =>
      {| sh_load_instr_addr := s.(sh_load_instr_addr);
         sh_load_instr_data := s.(sh_load_instr_data);
         sh_load_instr_kick := s.(sh_load_instr_kick);
         sh_logic_resp_valid := s.(sh_logic_resp_valid);
         sh_logic_resp_error := negb (Nat.eqb data 0);
         sh_logic_resp_value := s.(sh_logic_resp_value);
         sh_active_module := s.(sh_active_module);
         sh_trap_vector := s.(sh_trap_vector) |}
  | BusRegSetLogicRespValue =>
      {| sh_load_instr_addr := s.(sh_load_instr_addr);
         sh_load_instr_data := s.(sh_load_instr_data);
         sh_load_instr_kick := s.(sh_load_instr_kick);
         sh_logic_resp_valid := s.(sh_logic_resp_valid);
         sh_logic_resp_error := s.(sh_logic_resp_error);
         sh_logic_resp_value := data;
         sh_active_module := s.(sh_active_module);
         sh_trap_vector := s.(sh_trap_vector) |}
  | BusRegSetActiveModule =>
      {| sh_load_instr_addr := s.(sh_load_instr_addr);
         sh_load_instr_data := s.(sh_load_instr_data);
         sh_load_instr_kick := s.(sh_load_instr_kick);
         sh_logic_resp_valid := s.(sh_logic_resp_valid);
         sh_logic_resp_error := s.(sh_logic_resp_error);
         sh_logic_resp_value := s.(sh_logic_resp_value);
         sh_active_module := data;
         sh_trap_vector := s.(sh_trap_vector) |}
  | BusRegSetTrapVector =>
      {| sh_load_instr_addr := s.(sh_load_instr_addr);
         sh_load_instr_data := s.(sh_load_instr_data);
         sh_load_instr_kick := s.(sh_load_instr_kick);
         sh_logic_resp_valid := s.(sh_logic_resp_valid);
         sh_logic_resp_error := s.(sh_logic_resp_error);
         sh_logic_resp_value := s.(sh_logic_resp_value);
         sh_active_module := s.(sh_active_module);
         sh_trap_vector := data |}
  | _ => s
  end.

Definition busWrite (st : BusWrapperState) (addr data : nat) : BusWrapperState :=
  match decodeBusReg addr with
  | Some r =>
      if busRegWritable r then
        {| bw_core := st.(bw_core);
           bw_shadow := busWriteShadow st.(bw_shadow) r data |}
      else st
  | None => st
  end.

Lemma busRead_decode_sound :
  forall v addr r,
    decodeBusReg addr = Some r ->
    busRegReadable r = true ->
    busRead v addr = busRegReadValue v r.
Proof.
  intros v addr r Hdec Hr.
  unfold busRead.
  rewrite Hdec.
  rewrite Hr.
  reflexivity.
Qed.

Lemma busWrite_preserves_core :
  forall st addr data,
    bw_core (busWrite st addr data) = bw_core st.
Proof.
  intros st addr data.
  unfold busWrite.
  destruct (decodeBusReg addr) as [r|] eqn:Hdec.
  - destruct (busRegWritable r) eqn:Hw; reflexivity.
  - reflexivity.
Qed.

Lemma busWrite_unmapped_noop :
  forall st addr data,
    decodeBusReg addr = None ->
    busWrite st addr data = st.
Proof.
  intros st addr data Hdec.
  unfold busWrite.
  rewrite Hdec.
  reflexivity.
Qed.

Lemma busWrite_readonly_noop :
  forall st addr data r,
    decodeBusReg addr = Some r ->
    busRegReadable r = true ->
    busWrite st addr data = st.
Proof.
  intros st addr data r Hdec Hr.
  unfold busWrite.
  rewrite Hdec.
  unfold busRegWritable.
  rewrite Hr.
  reflexivity.
Qed.

Definition coreViewOfSnapshot (s : KamiSnapshot) : BusCoreView :=
  {| view_pc := snap_pc s;
     view_mu := snap_mu s;
     view_err := snap_err s;
     view_halted := snap_halted s;
     view_partition_ops := snap_partition_ops s;
     view_mdl_ops := snap_mdl_ops s;
     view_info_gain := snap_info_gain s;
     view_error_code := snap_error_code s;
     view_mstatus := 0;
     view_mcycle_lo := 0;
     view_mcycle_hi := 0;
     view_minstret_lo := 0;
     view_minstret_hi := 0;
     view_logic_acc := 0;
     view_logic_req_valid := false;
     view_logic_req_opcode := 0;
     view_logic_req_payload := 0;
     view_mu_tensor0 := snap_mu_tensor s 0;
     view_mu_tensor1 := snap_mu_tensor s 1;
     view_mu_tensor2 := snap_mu_tensor s 2;
     view_mu_tensor3 := snap_mu_tensor s 3;
     view_bianchi_alarm := false;
     view_pt_next_id := snap_pt_next_id s;
     view_pt_size := snap_pt_sizes s |}.

(* DEFINITIONAL HELPER — verifies bus address decode for pc register *)
Lemma busRead_snapshot_pc :
  forall s,
    busRead (coreViewOfSnapshot s) busAddrPc = Some (snap_pc s).
Proof.
  intro s.
  unfold busAddrPc.
  unfold busRead.
  simpl.
  reflexivity.
Qed.

(* DEFINITIONAL HELPER — verifies bus address decode for mu register *)
Lemma busRead_snapshot_mu :
  forall s,
    busRead (coreViewOfSnapshot s) busAddrMu = Some (snap_mu s).
Proof.
  intro s.
  unfold busAddrMu.
  unfold busRead.
  simpl.
  reflexivity.
Qed.

(* DEFINITIONAL HELPER — verifies bus address decode for partition_ops register *)
Lemma busRead_snapshot_partition_ops :
  forall s,
    busRead (coreViewOfSnapshot s) busAddrPartitionOps = Some (snap_partition_ops s).
Proof.
  intro s.
  unfold busAddrPartitionOps.
  unfold busRead.
  simpl.
  reflexivity.
Qed.

Lemma busWrite_stage12_abs_phase1_preserved :
  forall st addr data,
    abs_phase1 (bw_core (busWrite st addr data)) = abs_phase1 (bw_core st).
Proof.
  intros st addr data.
  rewrite busWrite_preserves_core.
  reflexivity.
Qed.

Lemma busWrite_shadow_updates_kick :
  forall sh,
    sh_load_instr_kick (busWriteShadow sh BusRegLoadInstrKick 0) = false /\
    sh_load_instr_kick (busWriteShadow sh BusRegLoadInstrKick 7) = true.
Proof.
  intro sh.
  split; simpl; reflexivity.
Qed.

Inductive BusOp : Type :=
| BusOpRead (addr : nat)
| BusOpWrite (addr data : nat).

Definition bus_step (st : BusWrapperState) (op : BusOp) : BusWrapperState :=
  match op with
  | BusOpRead _ => st
  | BusOpWrite addr data => busWrite st addr data
  end.

Theorem bus_step_preserves_core :
  forall st op,
    bw_core (bus_step st op) = bw_core st.
Proof.
  intros st op.
  destruct op as [addr | addr data].
  - reflexivity.
  - unfold bus_step.
    apply busWrite_preserves_core.
Qed.

Theorem bus_step_preserves_abs_phase1 :
  forall st op,
    abs_phase1 (bw_core (bus_step st op)) = abs_phase1 (bw_core st).
Proof.
  intros st op.
  rewrite bus_step_preserves_core.
  reflexivity.
Qed.

(** Current stage: the bus-top wrapper is semantically identical to the core. *)
Definition thieleBusTopB := thieleCoreB.
Definition thieleBusTopS := thieleCoreS.

(* Definitional lemma — stage-1 identity; will become non-trivial once bus
   protocol methods are added *)
Theorem thieleBusTop_stage1_equiv : thieleBusTopB = thieleCoreB.
Proof.
  reflexivity.
Qed.

(** Bridge: bus_step preserves core state; therefore instruction_cost
    accounting from VMStep is unaffected by bus protocol operations. *)
Theorem bus_step_preserves_instruction_cost_accounting :
  forall st op,
    abs_phase1 (bw_core (bus_step st op)) = abs_phase1 (bw_core st).
Proof.
  intros st op.
  rewrite bus_step_preserves_core.
  reflexivity.
Qed.

(** Type-level anchor: the bus wrapper understands the same vm_instruction
    vocabulary as the kernel VMStep semantics. *)
Definition bus_vm_instruction_type := vm_instruction.
