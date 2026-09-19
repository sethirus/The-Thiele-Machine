(** OutsideDomain.v: the trap-class guards are false for an admitted
    instruction's own opcode.

    [StepFaults.dd_guard_opcode] says the locality, partition-overflow and NFI
    guards can only fire on an opcode in [guard_opcodes]. [not_guard_of_opcode]
    turns that into a decision procedure: an opcode outside that list takes the
    disjunction to [false], for an arbitrary boundary and fetched word. The
    per-opcode [op_off_*] facts below name the opcodes the admitted
    constructors use and discharge the membership test by computation, so each
    admitted instruction's trap-class guards are false without re-deriving any
    decode reasoning. The admitted constructors that do lie in the guard class
    (the locality opcodes, the partition opcodes and PDISCOVER) carry the bound
    premise that makes their own guard false.

    Not covered here: the rich-format guard, which inspects operand and format
    fields and so needs a per-encoding argument, and the morph-runtime guard,
    which the morph constructors admit by design. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets Abstraction ImplementationContract
  StepFields StepFieldsMorph StepFaults.
Local Open Scope nat_scope.
Local Open Scope list_scope.

(** An opcode outside [guard_opcodes] never raises the locality, partition or
    NFI guard, whatever the operands and boundary. *)
Lemma not_guard_of_opcode : forall (b : HWB) (w : word InstrSz) (c : word OpcodeSz),
  dd_opcode b w = c -> op_member c guard_opcodes = false ->
  dd_locality_violation b w || dd_ptable_overflow_violation b w ||
  dd_nfi_violation b w = false.
Proof.
  intros b w c Ho Hm.
  destruct (dd_locality_violation b w || dd_ptable_overflow_violation b w ||
            dd_nfi_violation b w) eqn:H; [|reflexivity].
  exfalso. pose proof (dd_guard_opcode b w H) as Hin. rewrite Ho in Hin.
  exact (op_in_member_false c c guard_opcodes Hin Hm eq_refl).
Qed.

(** Every opcode the admitted constructors use, tested against the guard
    class. Each holds by computation. *)
Lemma op_off_add : op_member OP_ADD guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_sub : op_member OP_SUB guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_and : op_member OP_AND guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_or : op_member OP_OR guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_xor_add : op_member OP_XOR_ADD guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_mul : op_member OP_MUL guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_xfer : op_member OP_XFER guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_load_imm : op_member OP_LOAD_IMM guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_shl : op_member OP_SHL guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_shr : op_member OP_SHR guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_lui : op_member OP_LUI guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_xor_load : op_member OP_XOR_LOAD guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_jump : op_member OP_JUMP guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_jnez : op_member OP_JNEZ guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_mdlacc : op_member OP_MDLACC guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_ljoin : op_member OP_LJOIN guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_certify : op_member OP_CERTIFY guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_read_port : op_member OP_READ_PORT guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_emit : op_member OP_EMIT guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_reveal : op_member OP_REVEAL guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_xor_swap : op_member OP_XOR_SWAP guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_tensor_set : op_member OP_TENSOR_SET guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_tensor_get : op_member OP_TENSOR_GET guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_chsh_trial : op_member OP_CHSH_TRIAL guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_xor_rank : op_member OP_XOR_RANK guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_halt : op_member OP_HALT guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_checkpoint : op_member OP_CHECKPOINT guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_write_port : op_member OP_WRITE_PORT guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_morph_delete : op_member OP_MORPH_DELETE guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_morph_assert : op_member OP_MORPH_ASSERT guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_morph_get : op_member OP_MORPH_GET guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_morph_id : op_member OP_MORPH_ID guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_morph : op_member OP_MORPH guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_compose : op_member OP_COMPOSE guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_lassert : op_member OP_LASSERT guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.
Lemma op_off_chsh_lassert : op_member OP_CHSH_LASSERT guard_opcodes = false.
Proof. vm_compute. reflexivity. Qed.

(** The guard class is exactly the six locality opcodes, the three partition
    opcodes and PDISCOVER. *)
Lemma guard_opcodes_exact :
  guard_opcodes = OP_LOAD :: OP_HEAP_LOAD :: OP_STORE :: OP_HEAP_STORE ::
    OP_CALL :: OP_RET :: OP_PNEW :: OP_PSPLIT :: OP_PMERGE :: OP_PDISCOVER :: nil.
Proof. reflexivity. Qed.

Lemma locality_opcodes_sub_guard : forall c, In c locality_opcodes -> In c guard_opcodes.
Proof. intros c H. unfold locality_opcodes, guard_opcodes in *. simpl in *. tauto. Qed.

Lemma partition_opcodes_sub_guard : forall c, In c partition_opcodes -> In c guard_opcodes.
Proof. intros c H. unfold partition_opcodes, guard_opcodes in *. simpl in *. tauto. Qed.

(** * From an admitted instruction to its guard facts

    Each admitted constructor carries the fetched word, so the opcode lane is
    determined and [not_guard_of_opcode] applies for every opcode outside
    [guard_opcodes]. The six memory opcodes, the three partition opcodes and
    PDISCOVER are inside [guard_opcodes]; their constructors instead carry the
    bound premise, so the corresponding guard is false by that premise rather
    than by opcode membership. This file records the opcode-membership half;
    the premise half is the constructors' own bounds, already present. *)

Lemma op_member_guard_of_in : forall c, In c guard_opcodes -> op_member c guard_opcodes = true.
Proof.
  intros c H. apply Bool.not_false_iff_true. intro Hf.
  exact (op_in_member_false c c guard_opcodes H Hf eq_refl).
Qed.
