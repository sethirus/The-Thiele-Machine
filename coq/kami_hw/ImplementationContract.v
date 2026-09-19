(** Finite implementation interface. Definitions are specifications, not an
    assumed refinement theorem; see C1_IMPLEMENTATION_CONTRACT.md. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import List String NArith Arith Lia.
From KamiHW Require Import ThieleTypes ThieleCPUCore ThieleCPUBusTop
  HWBoundary Abstraction.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

Definition implementation_core := thieleCore.
Definition implementation_bus_top := thieleBusTopB.
Definition implementation_reset := initRegs (getRegInits implementation_core).
Definition supported_opcodes : list (word OpcodeSz) :=
  [OP_PNEW; OP_PSPLIT; OP_PMERGE; OP_LASSERT; OP_LJOIN; OP_MDLACC; OP_PDISCOVER; OP_XFER; OP_LOAD_IMM; OP_CHSH_TRIAL; OP_XOR_LOAD; OP_XOR_ADD; OP_XOR_SWAP; OP_XOR_RANK; OP_EMIT; OP_REVEAL; OP_LOAD; OP_STORE; OP_ADD; OP_SUB; OP_JUMP; OP_JNEZ; OP_CALL; OP_RET; OP_CHECKPOINT; OP_READ_PORT; OP_WRITE_PORT; OP_HEAP_LOAD; OP_HEAP_STORE; OP_CERTIFY; OP_AND; OP_OR; OP_SHL; OP_SHR; OP_MUL; OP_LUI; OP_TENSOR_SET; OP_TENSOR_GET; OP_MORPH; OP_COMPOSE; OP_MORPH_ID; OP_MORPH_DELETE; OP_MORPH_ASSERT; OP_MORPH_TENSOR; OP_MORPH_GET; OP_CHSH_LASSERT; OP_HALT].
Definition supported_opcode (op : word OpcodeSz) := In op supported_opcodes.
Lemma supported_opcode_count : List.length supported_opcodes = 47.
Proof. reflexivity. Qed.

(** Exactly the masking/placement performed by thiele_asm._encode. *)
Definition isa_v2_encode (op a b cost version format flags ext0 ext1 : N) : N :=
  N.lor (N.shiftl (N.land version 255) 120)
  (N.lor (N.shiftl (N.land format 255) 112)
  (N.lor (N.shiftl (N.land flags 65535) 96)
  (N.lor (N.shiftl (N.land ext1 4294967295) 64)
  (N.lor (N.shiftl (N.land ext0 4294967295) 32)
  (N.lor (N.shiftl (N.land op 255) 24)
  (N.lor (N.shiftl (N.land a 255) 16)
  (N.lor (N.shiftl (N.land b 255) 8) (N.land cost 255)))))))).
Definition isa_field (w shift mask : N) := N.land (N.shiftr w shift) mask.
Definition tensor_set_a (mid i j : N) :=
  N.lor (N.shiftl (N.land mid 15) 4)
    (N.lor (N.shiftl (N.land i 3) 2) (N.land j 3)).
Definition canonical_tensor_operands (mid i j value : nat) : Prop :=
  mid < 16 /\ i < 4 /\ j < 4 /\ value < 256.

(** Finite observations extend by zero/None, never by modular aliasing. *)
Definition hwb_vector_nat {n w} (v : type (Vector (Bit w) n)) (i : nat) : nat :=
  if Nat.ltb i (2 ^ n) then wordToNat (v (natToWord n i)) else 0.
Definition hwb_valid {n} (v : type (Vector Bool n)) (i : nat) : bool :=
  if Nat.ltb i (2 ^ n) then v (natToWord n i) else false.
(** A coupling label is stored as a list of atoms joined by ";": [n] atoms,
    atom [k] being the kernel's "empty" label when bit [k] of [mask] is set and
    the empty string otherwise. MORPH commits one "" atom; a morphism without a
    descriptor carries the single "empty" atom; COMPOSE appends the lists. *)
Definition label_atom (mask : nat) : string :=
  if Nat.odd mask then "empty"%string else ""%string.

Fixpoint atom_label (n mask : nat) : string :=
  match n with
  | O => ""%string
  | S O => label_atom mask
  | S m => (label_atom mask ++ String (Ascii.ascii_of_nat 59) (atom_label m (Nat.div2 mask)))%string
  end.

Lemma append_assoc_s : forall a b c : string, ((a ++ b) ++ c)%string = (a ++ (b ++ c))%string.
Proof. induction a as [|x a IH]; intros b c; cbn; [reflexivity|]. f_equal. apply IH. Qed.

Lemma odd_add_double : forall a b, Nat.odd (a + 2 * b) = Nat.odd a.
Proof. intros a b. rewrite Nat.odd_add, Nat.odd_mul. cbn [Nat.odd Nat.even negb andb]. destruct (Nat.odd a); reflexivity. Qed.

Lemma div2_add_double : forall a b, Nat.div2 (a + 2 * b) = Nat.div2 a + b.
Proof.
  intros a b. rewrite !Nat.div2_div.
  replace (a + 2 * b) with (b * 2 + a) by lia. rewrite Nat.div_add_l by lia. lia.
Qed.

Lemma atom_label_cons : forall n m, 1 <= n ->
  atom_label (S n) m = (label_atom m ++ ";" ++ atom_label n (Nat.div2 m))%string.
Proof. intros n m H. destruct n as [|n]; [lia|]. reflexivity. Qed.

(** Appending two atom lists: the second mask sits above the first [n1] bits. *)
Theorem atom_label_compose : forall n1 n2 m1 m2,
  1 <= n1 -> 1 <= n2 -> m1 < 2 ^ n1 ->
  (atom_label n1 m1 ++ ";" ++ atom_label n2 m2)%string = atom_label (n1 + n2) (m1 + m2 * 2 ^ n1).
Proof.
  induction n1 as [|n1 IH]; intros n2 m1 m2 H1 H2 Hm; [lia|].
  rewrite Nat.pow_succ_r'. replace (m1 + m2 * (2 * 2 ^ n1)) with (m1 + 2 * (m2 * 2 ^ n1)) by lia.
  destruct n1 as [|n1].
  - cbn [Nat.add]. rewrite (atom_label_cons n2) by exact H2.
    cbn [Nat.pow] in Hm |- *. rewrite Nat.mul_1_r.
    unfold label_atom. rewrite odd_add_double, div2_add_double.
    assert (Nat.div2 m1 = 0) by (rewrite Nat.div2_div; apply Nat.div_small; lia).
    rewrite H. reflexivity.
  - rewrite atom_label_cons by lia.
    replace (S (S n1) + n2) with (S (S n1 + n2)) by lia.
    rewrite (atom_label_cons (S n1 + n2)) by lia.
    rewrite !append_assoc_s. f_equal.
    + unfold label_atom. rewrite odd_add_double. reflexivity.
    + cbn [append]. f_equal. rewrite div2_add_double. apply IH; [lia|lia|].
      rewrite Nat.div2_div. apply Nat.div_lt_upper_bound; [lia|]. rewrite Nat.pow_succ_r' in Hm. lia.
Qed.

(** Pair-table cells at or above [coupling_pair_next_id] are unallocated:
    normalization compacts retained pairs below the new pointer and leaves the
    cells it dropped marked valid, so the observation reads pairs only below
    the allocation pointer. *)
(** LASSERT FSM scratch registers are implementation state, like the CHSH and
    coupling FSM scratch. [kami_step] never reads or writes the assertion
    shadow, so the boundary observation carries the empty shadow. *)
Definition hwb_rich (b : HWB) : RichSnapshotState :=
  {| rich_morph_table := fun i => if hwb_valid (hw_morph_valid_table b) i then Some {| morph_entry_source := hwb_vector_nat (hw_morph_src_table b) i; morph_entry_target := hwb_vector_nat (hw_morph_dst_table b) i; morph_entry_coupling_desc := hwb_vector_nat (hw_morph_coupling_desc_table b) i; morph_entry_is_identity := hwb_valid (hw_morph_identity_table b) i |} else None;
     rich_next_morph_id := wordToNat (hw_morph_next_id b);
     rich_coupling_desc_table := fun i => if hwb_valid (hw_coupling_desc_valid_table b) i then Some {| coupling_desc_base := hwb_vector_nat (hw_coupling_desc_base_table b) i; coupling_desc_count := hwb_vector_nat (hw_coupling_desc_count_table b) i; coupling_desc_label := atom_label (hwb_vector_nat (hw_coupling_desc_label_len_table b) i) (hwb_vector_nat (hw_coupling_desc_label_table b) i) |} else None;
     rich_next_coupling_desc_id := wordToNat (hw_coupling_desc_next_id b);
     rich_coupling_pair_table := fun i => if Nat.ltb i (wordToNat (hw_coupling_pair_next_id b)) then (if hwb_valid (hw_coupling_pair_valid_table b) i then Some {| coupling_pair_source := hwb_vector_nat (hw_coupling_pair_src_table b) i; coupling_pair_target := hwb_vector_nat (hw_coupling_pair_dst_table b) i |} else None) else None;
     rich_next_coupling_pair_id := wordToNat (hw_coupling_pair_next_id b);
     rich_formula_desc_table := fun i => if hwb_valid (hw_formula_desc_valid_table b) i then Some {| formula_desc_base := hwb_vector_nat (hw_formula_desc_base_table b) i; formula_desc_count := hwb_vector_nat (hw_formula_desc_count_table b) i |} else None;
     rich_next_formula_desc_id := wordToNat (hw_formula_desc_next_id b);
     rich_cert_desc_table := fun i => if hwb_valid (hw_cert_desc_valid_table b) i then Some {| cert_desc_base := hwb_vector_nat (hw_cert_desc_base_table b) i; cert_desc_count := hwb_vector_nat (hw_cert_desc_count_table b) i |} else None;
     rich_next_cert_desc_id := wordToNat (hw_cert_desc_next_id b);
     rich_desc_meta_table := fun i => if hwb_valid (hw_desc_meta_valid_table b) i then Some {| desc_meta_subtype := hwb_vector_nat (hw_desc_meta_subtype_table b) i; desc_meta_kind := hwb_vector_nat (hw_desc_meta_kind_table b) i; desc_meta_inline_len := hwb_vector_nat (hw_desc_meta_inline_len_table b) i; desc_meta_aux := hwb_vector_nat (hw_desc_meta_aux_table b) i |} else None;
     rich_next_desc_meta_id := wordToNat (hw_desc_meta_next_id b);
     rich_lassert_state := empty_lassert_shadow_state |}.

Definition hwb_snapshot (b : HWB) : KamiSnapshot :=
  {| snap_pc := wordToNat (hw_pc b);
     snap_mu := wordToNat (hw_mu b);
     snap_err := hw_err b;
     snap_halted := hw_halted b;
     snap_regs := hwb_vector_nat (hw_regs b);
     snap_mem := hwb_vector_nat (hw_mem b);
     snap_partition_ops := wordToNat (hw_partition_ops b);
     snap_mdl_ops := wordToNat (hw_mdl_ops b);
     snap_info_gain := wordToNat (hw_info_gain b);
     snap_error_code := wordToNat (hw_error_code b);
     snap_mu_tensor := hwb_vector_nat (hw_mu_tensor b);
     snap_pt_sizes := hwb_vector_nat (hw_ptTable b);
     snap_pt_next_id := wordToNat (hw_pt_next_id b);
     snap_certified := hw_certified b;
     snap_wc_same_00 := wordToNat (hw_wc_same_00 b);
     snap_wc_diff_00 := wordToNat (hw_wc_diff_00 b);
     snap_wc_same_01 := wordToNat (hw_wc_same_01 b);
     snap_wc_diff_01 := wordToNat (hw_wc_diff_01 b);
     snap_wc_same_10 := wordToNat (hw_wc_same_10 b);
     snap_wc_diff_10 := wordToNat (hw_wc_diff_10 b);
     snap_wc_same_11 := wordToNat (hw_wc_same_11 b);
     snap_wc_diff_11 := wordToNat (hw_wc_diff_11 b);
     snap_module_tensors := fun mid i => if Nat.ltb mid 16 then hwb_vector_nat (hw_module_tensors b (natToWord ModTensorIdxSz mid)) i else 0;
     snap_rich_state := hwb_rich b;
     snap_csr_cert_addr := wordToNat (hw_cert_addr b);
     snap_csr_status := wordToNat (hw_csr_status b);
     snap_csr_err := if hw_err b then 1 else 0;
     snap_csr_heap_base := wordToNat (hw_csr_heap_base b);
     snap_logic_acc := wordToNat (hw_logic_acc b);
     snap_mstatus := wordToNat (hw_mstatus b) |}.

Definition hwb_observes (b : HWB) (s : KamiSnapshot) := s = hwb_snapshot b.
Definition implementation_target := kami_step.
Definition retirement_boundary (b : HWB) : Prop :=
  wordToNat (hw_lassert_phase b) = 0 /\
  wordToNat (hw_chsh_phase b) = 0 /\ wordToNat (hw_mc_phase b) = 0.
Definition live_boundary (b : HWB) : Prop :=
  retirement_boundary b /\ hw_halted b = false /\ hw_err b = false.
Definition in_region_address (b : HWB) (address : nat) : Prop :=
  address < MemSize /\
  address < hwb_vector_nat (hw_ptTable b) (wordToNat (hw_active_module b)).
Definition finite_pc_mu (b : HWB) (next_pc next_mu : nat) : Prop :=
  wordToNat (hw_pc b) < MemSize /\ next_pc < MemSize /\ next_mu < 2 ^ WordSz.
Definition raw_pair_capacity (b : HWB) (raw_intermediate : nat) : Prop :=
  wordToNat (hw_coupling_pair_next_id b) + raw_intermediate <= CouplingPairSz.
Definition represented_label (label : string) := exists n mask, 1 <= n /\ label = atom_label n mask.
Definition represented_region (region : list nat) :=
  exists size, 0 < size /\ size <= MemSize /\ region = List.seq 0 size.
Definition represented_endpoint (endpoint : nat) := endpoint < MemSize.

(** A schedule lists actual CPU rule firings only; host methods occur before
    this trace. Enabled-rule progress/fairness is a separate C2 obligation. *)
Definition execution_schedule (names : list string) : Prop :=
  Forall (fun name => In name (List.map (@attrName _) (getRules thieleCore))) names.

Lemma hwb_snapshot_module_tensors : forall b mid i,
  mid < 16 -> i < 16 ->
  snap_module_tensors (hwb_snapshot b) mid i =
  wordToNat (hw_module_tensors b (natToWord ModTensorIdxSz mid)
    (natToWord MuTensorIdxSz i)).
Proof.
  intros b mid i Hm Hi.
  change ((if Nat.ltb mid 16 then
    hwb_vector_nat (hw_module_tensors b (natToWord ModTensorIdxSz mid)) i
    else 0) = wordToNat (hw_module_tensors b (natToWord ModTensorIdxSz mid)
      (natToWord MuTensorIdxSz i))).
  assert (Hm' : Nat.ltb mid 16 = true) by (apply Nat.ltb_lt; exact Hm).
  assert (Hi' : Nat.ltb i (2 ^ MuTensorIdxSz) = true)
    by (apply Nat.ltb_lt; exact Hi).
  rewrite Hm'. unfold hwb_vector_nat. rewrite Hi'. reflexivity.
Qed.
Lemma hwb_snapshot_csrs : forall b,
  snap_csr_status (hwb_snapshot b) = wordToNat (hw_csr_status b) /\
  snap_csr_heap_base (hwb_snapshot b) = wordToNat (hw_csr_heap_base b).
Proof. intro b; split; reflexivity. Qed.

Lemma hwb_pc_mu_word_bounds : forall b,
  wordToNat (hw_pc b) < 2 ^ WordSz /\
  wordToNat (hw_mu b) < 2 ^ WordSz.
Proof. intro b; split; apply wordToNat_bound. Qed.

(** The outer wire format is independent of state-dependent descriptor and
    fault checks. In particular this does not assume decoder correctness. *)
Record ISAWordFields := {
  isa_opcode : word OpcodeSz;
  isa_a : word 8;
  isa_b : word 8;
  isa_cost : word CostSz;
  isa_format : word FormatIdSz;
  isa_flags : word 16;
  isa_ext0 : word WordSz;
  isa_ext1 : word WordSz
}.
Definition isa_word (f : ISAWordFields) : N :=
  isa_v2_encode (wordToN (isa_opcode f)) (wordToN (isa_a f))
    (wordToN (isa_b f)) (wordToN (isa_cost f)) 2
    (wordToN (isa_format f)) (wordToN (isa_flags f))
    (wordToN (isa_ext0 f)) (wordToN (isa_ext1 f)).
Definition isa_supported_word (f : ISAWordFields) : Prop :=
  supported_opcode (isa_opcode f).
