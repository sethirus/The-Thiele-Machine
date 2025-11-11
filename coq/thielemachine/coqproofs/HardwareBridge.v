(*
 * HardwareBridge.v
 * -----------------
 *
 * A shallow refinement argument that links the cycle-level RTL model of the
 * Thiele CPU (as implemented in `thielecpu/hardware/thiele_cpu.v`) to the
 * instruction/receipt semantics already mechanised in `ThieleMachine.v`.
 *
 * The RTL design fetches 32-bit words, interprets the high byte as an opcode,
 * and increments the byte-addressed program counter by four on every completed
 * instruction.  The Coq model below collapses that behaviour into an
 * instruction-indexed small-step semantics and exposes the invariants needed to
 * compare decoded hardware traces against the abstract Thiele machine.  The
 * proof scripts stop short of replaying whole RTL traces; instead they provide
 * reusable decoding lemmas that the Python tooling and downstream proof work
 * rely on when checking receipts.
 *
 * This refinement is intentionally lightweight – it does not try to reproduce
 * the full register file or the XOR-matrix datapaths.  Instead, it isolates the
 * fetch/decode/acknowledge skeleton that determines which instruction fires,
 * which receipt is emitted, and how the program counter advances.  Those are the
 * precise pieces that the abstract Thiele machine cares about, so matching them
 * suffices to align the mechanised proof artefacts with the shipped RTL.
 *)

From Coq Require Import List NArith.
From ThieleMachine Require Import ThieleMachine.
Import ListNotations.

Module TM := ThieleMachine.

Open Scope N_scope.

(* ------------------------------------------------------------------------- *)
(* Basic byte manipulation matching the Verilog slicing idiom                *)
(* ------------------------------------------------------------------------- *)

Definition mask8 : N := 255%N.

Definition byte_at (w : N) (shift : N) : N :=
  N.land (N.shiftr w shift) mask8.

Definition opcode_of (w : N) : N := byte_at w 24.
Definition operand_a_of (w : N) : N := byte_at w 16.
Definition operand_b_of (w : N) : N := byte_at w 8.

Definition opcode_PNEW      : N := 0%N.
Definition opcode_PSPLIT    : N := 1%N.
Definition opcode_PMERGE    : N := 2%N.
Definition opcode_LASSERT   : N := 3%N.
Definition opcode_LJOIN     : N := 4%N.
Definition opcode_MDLACC    : N := 5%N.
Definition opcode_EMIT      : N := 14%N.  (* Matches RTL constant 8'h0E. *)
Definition opcode_XFER      : N := 7%N.
Definition opcode_PYEXEC    : N := 8%N.
Definition opcode_XOR_LOAD  : N := 10%N.
Definition opcode_XOR_ADD   : N := 11%N.
Definition opcode_XOR_SWAP  : N := 12%N.
Definition opcode_XOR_RANK  : N := 13%N.
Definition opcode_HALT      : N := 255%N.

Definition decode_kind (opc : N) : TM.InstrKind :=
  if N.eqb opc opcode_LASSERT then TM.InstrLASSERT
  else if N.eqb opc opcode_MDLACC then TM.InstrMDLACC
  else TM.InstrOther.

Definition decode_event (opc : N) (op_a : N) : option TM.Event :=
  if N.eqb opc opcode_LASSERT then Some (N.to_nat op_a)
  else if N.eqb opc opcode_EMIT then Some (N.to_nat op_a)
  else None.

Definition decode_cert (opc : N) (op_b : N) : TM.Cert :=
  (*
     Hardware receipts expose operand_b for EMIT instructions (the status low
     byte encodes the emitted μ-information).  Other opcodes only contribute a
     zero certificate so the μ-accumulator in Coq tracks precisely the values
     that appear in RTL test logs.
   *)
  if N.eqb opc opcode_EMIT then N.to_nat op_b else 0%nat.

Definition decode_instr (word : N) : TM.Instr :=
  let opc := opcode_of word in
  let op_a := operand_a_of word in
  let op_b := operand_b_of word in
  {| TM.instr_kind  := decode_kind opc;
     TM.instr_event := decode_event opc op_a;
     TM.instr_cert  := decode_cert opc op_b |}.

Definition decode_program (prog : list N) : list TM.Instr :=
  map decode_instr prog.

Definition partition_delta (opc : N) : nat :=
  if N.eqb opc opcode_XOR_ADD then 1%nat
  else if N.eqb opc opcode_XOR_SWAP then 1%nat
  else 0%nat.

Fixpoint partition_ops_of_program (prog : list N) : nat :=
  match prog with
  | [] => 0%nat
  | word :: tl => partition_delta (opcode_of word) + partition_ops_of_program tl
  end.

(* ------------------------------------------------------------------------- *)
(* RTL micro-semantics collapsed to instruction-indexed steps                *)
(* ------------------------------------------------------------------------- *)

Record RTLState := {
  rtl_pc   : nat;        (* Program counter measured in 32-bit words        *)
  rtl_prog : list N;     (* Instruction memory as fetched by the Verilog    *)
}.

Definition rtl_fetch (s : RTLState) : option N :=
  nth_error s.(rtl_prog) s.(rtl_pc).

Definition rtl_step (s : RTLState) : option (RTLState * TM.StepObs) :=
  match rtl_fetch s with
  | None => None
  | Some word =>
      let instr := decode_instr word in
      let obs := TM.obs_of_instr instr in
      Some ({| rtl_pc := S s.(rtl_pc); rtl_prog := s.(rtl_prog) |}, obs)
  end.

Definition project_state (s : RTLState) : TM.State :=
  {| TM.pc := s.(rtl_pc) |}.

Definition project_program (s : RTLState) : TM.Prog :=
  {| TM.code := decode_program s.(rtl_prog) |}.

Lemma rtl_step_preserves_program : forall s s' obs,
  rtl_step s = Some (s', obs) -> s'.(rtl_prog) = s.(rtl_prog).
Proof.
  intros s s' obs Hstep.
  unfold rtl_step in Hstep.
  destruct (rtl_fetch s) as [word|] eqn:Hfetch; try discriminate.
  inversion Hstep; subst; reflexivity.
Qed.

Lemma decode_program_nth : forall prog idx word,
  nth_error prog idx = Some word ->
  nth_error (decode_program prog) idx = Some (decode_instr word).
Proof.
  intros prog idx word Hnth.
  unfold decode_program.
  rewrite nth_error_map. now rewrite Hnth.
Qed.

(* ------------------------------------------------------------------------- *)
(* The helper definitions above are sufficient for lightweight refinement      *)
(* arguments and for tooling that decodes RTL traces inside Python.            *)

