(** RichFaultRetireMaster.v: generated. dd_rich_fault falsity for each
    of RetireMaster.v's 55 admitted constructors' own fetched word, cited
    verbatim against RichFaultMaster.v's three general theorems -- the
    room bound each corollary needs (MORPH_ID, MORPH_EXT, COMPOSE_EXT and
    their fault siblings only) is exactly the premise that constructor
    already carries in RetireMaster.v, extracted mechanically from that
    file's own admitted inductive rather than retyped by hand. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia NArith.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext RuleStep BoundaryDecoded
  StepEval StepWordFacts DispatchLets StepFields StepFieldsMorph ChshStepFields LassertStepFields
  LegacyWordDecode RichWordDecode RichFaultWords RichFaultMaster.
Local Open Scope nat_scope.

Lemma dd_rich_fault_false_add : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (add_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold add_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_sub : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (sub_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold sub_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_and : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (and_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold and_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_or : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (or_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold or_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_xor_add : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (xor_add_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold xor_add_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_mul : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (mul_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold mul_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_xfer : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (xfer_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold xfer_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_load_imm : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (load_imm_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold load_imm_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_shl : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (shl_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold shl_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_shr : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (shr_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold shr_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_lui : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (lui_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold lui_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_xor_load : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (xor_load_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold xor_load_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_jump : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (jump_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold jump_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_jnez : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (jnez_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold jnez_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_mdlacc : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (mdlacc_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold mdlacc_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_ljoin : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (ljoin_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold ljoin_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_certify : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (certify_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold certify_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_read_port : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (read_port_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold read_port_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_emit : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (emit_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold emit_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_reveal : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (reveal_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold reveal_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_xor_swap : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (xor_swap_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold xor_swap_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_tensor_set : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (tensor_set_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold tensor_set_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_tensor_get : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (tensor_get_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold tensor_get_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_pdiscover : forall a0 a1 a2 a3 a4 a5 a6 a7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (pdiscover_word a0 a1 a2 a3 a4 a5 a6 a7 false false false false false false false false c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold pdiscover_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_load : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (load_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold load_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_store : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (store_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold store_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_heap_load : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (heap_load_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold heap_load_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_heap_store : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (heap_store_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold heap_store_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_call : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (call_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold call_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_ret : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (ret_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold ret_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_pnew : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (pnew_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold pnew_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_psplit : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (psplit_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold psplit_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_pmerge : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (pmerge_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold pmerge_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_chsh_trial : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (chsh_trial_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold chsh_trial_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_xor_rank : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (xor_rank_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold xor_rank_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_halt : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (halt_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold halt_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_checkpoint : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (checkpoint_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold checkpoint_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_write_port : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (write_port_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold write_port_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_morph_delete : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (morph_delete_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold morph_delete_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_morph_assert : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (morph_assert_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold morph_assert_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_morph_get : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (morph_get_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold morph_get_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_morph_id : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  wordToNat (hw_morph_next_id b) < 16 ->
  dd_rich_fault b (morph_id_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b Hroom.
  unfold morph_id_word. apply dd_rich_fault_false_legacy.
  intros _. exact Hroom.
Qed.

Lemma dd_rich_fault_false_morph_delete_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
  dd_rich_fault b (StepFieldsMorph.morph_delete_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b.
  unfold StepFieldsMorph.morph_delete_ext_word. apply dd_rich_fault_false_morph_inline.
  - right; right; right; left; reflexivity.
  - intros [H|[H|H]]; discriminate H.
  - intro H; discriminate H.
Qed.

Lemma dd_rich_fault_false_morph_id_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
  wordToNat (hw_morph_next_id b) < 16 ->
  dd_rich_fault b (StepFieldsMorph.morph_id_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hmr.
  unfold StepFieldsMorph.morph_id_ext_word. apply dd_rich_fault_false_morph_inline.
  - right; right; left; reflexivity.
  - intros _. exact Hmr.
  - intro H; discriminate H.
Qed.

Lemma dd_rich_fault_false_morph_assert_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
  dd_rich_fault b (StepFieldsMorph.morph_assert_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b.
  unfold StepFieldsMorph.morph_assert_ext_word. apply dd_rich_fault_false_cert_inline.
Qed.

Lemma dd_rich_fault_false_morph_get_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
  dd_rich_fault b (StepFieldsMorph.morph_get_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b.
  unfold StepFieldsMorph.morph_get_ext_word. apply dd_rich_fault_false_morph_inline.
  - right; right; right; right; right; right; reflexivity.
  - intros [H|[H|H]]; discriminate H.
  - intro H; discriminate H.
Qed.

Lemma dd_rich_fault_false_morph_tensor : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (morph_tensor_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold morph_tensor_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_morph_tensor_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
  dd_rich_fault b (StepFieldsMorph.morph_tensor_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b.
  unfold StepFieldsMorph.morph_tensor_ext_word. apply dd_rich_fault_false_morph_inline.
  - right; right; right; right; right; left; reflexivity.
  - intros [H|[H|H]]; discriminate H.
  - intro H; discriminate H.
Qed.

Lemma dd_rich_fault_false_morph_ext_fault : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
  wordToNat (hw_morph_next_id b) < 16 ->
  wordToNat (hw_coupling_desc_next_id b) < 16 ->
  dd_rich_fault b (StepFieldsMorph.morph_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hmr Hdr.
  unfold StepFieldsMorph.morph_ext_word. apply dd_rich_fault_false_morph_inline.
  - left; reflexivity.
  - intros _. exact Hmr.
  - intros _. exact Hdr.
Qed.

Lemma dd_rich_fault_false_compose_ext_fault : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
  wordToNat (hw_morph_next_id b) < 16 ->
  dd_rich_fault b (StepFieldsMorph.compose_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hmr.
  unfold StepFieldsMorph.compose_ext_word. apply dd_rich_fault_false_morph_inline.
  - right; left; reflexivity.
  - intros _. exact Hmr.
  - intro H; discriminate H.
Qed.

Lemma dd_rich_fault_false_lassert_unsat : forall a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (lassert_unsat_word a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold lassert_unsat_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_chsh_lassert : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (chsh_lassert_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold chsh_lassert_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.

Lemma dd_rich_fault_false_morph_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
  wordToNat (hw_morph_next_id b) < 16 ->
  wordToNat (hw_coupling_desc_next_id b) < 16 ->
  dd_rich_fault b (StepFieldsMorph.morph_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hmr Hdr.
  unfold StepFieldsMorph.morph_ext_word. apply dd_rich_fault_false_morph_inline.
  - left; reflexivity.
  - intros _. exact Hmr.
  - intros _. exact Hdr.
Qed.

Lemma dd_rich_fault_false_compose_ext : forall a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 (b : HWB),
  wordToNat (hw_morph_next_id b) < 16 ->
  wordToNat (hw_coupling_desc_next_id b) < 16 ->
  dd_rich_fault b (StepFieldsMorph.compose_ext_word a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31) = false.
Proof.
  intros a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19 e20 e21 e22 e23 e24 e25 e26 e27 e28 e29 e30 e31 b Hmr Hdr.
  unfold StepFieldsMorph.compose_ext_word. apply dd_rich_fault_false_morph_inline.
  - right; left; reflexivity.
  - intros _. exact Hmr.
  - intro H; discriminate H.
Qed.

Lemma dd_rich_fault_false_lassert_sat : forall a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 (b : HWB),
  dd_rich_fault b (lassert_sat_word a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7) = false.
Proof.
  intros a0 a1 a2 a3 a4 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 c0 c1 c2 c3 c4 c5 c6 c7 b.
  unfold lassert_sat_word. apply dd_rich_fault_false_legacy.
  intros [H|[H|H]]; discriminate H.
Qed.
