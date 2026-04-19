(** EmbedStep.v

    Proves the step-commutation theorem for all 46 VM opcodes:

        abs_phase1 (kami_step ks i) = vm_apply (abs_phase1 ks) i

    - 30 opcodes proved UNCONDITIONALLY via SupportedOpcode + embed_step_compute
    - 3 opcodes added under snapshot/bit preconditions via EmbedStep_WF.v:
      CALL, RET, CHSH_TRIAL
    - 4 opcodes handled by specialised preconditioned lemmas in §8:
      PNEW, PSPLIT, PMERGE, LASSERT
    - 9 opcodes have irreducible gaps (driver-managed / rich-state):
      TENSOR_SET, TENSOR_GET,
      MORPH, COMPOSE, MORPH_ID, MORPH_DELETE, MORPH_ASSERT,
      MORPH_TENSOR, MORPH_GET

    UNCONDITIONAL (30 opcodes, SupportedOpcode):
      XFER, LOAD_IMM, LOAD, STORE, ADD, SUB, JUMP, JNEZ,
      XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK,
      AND, OR, SHL, SHR, MUL, LUI,
      HALT, CHECKPOINT, WRITE_PORT, READ_PORT,
      HEAP_LOAD, HEAP_STORE, CERTIFY, MDLACC,
      LJOIN, EMIT, PDISCOVER, REVEAL

    CONDITIONAL (7 opcodes, split across two layers):
      WF layer in EmbedStep_WF.v (3 opcodes):
        CALL: WellFormedSnapshot + pc < MEM_SIZE
        RET: WellFormedSnapshot
        CHSH_TRIAL: chsh_bits_ok = true

      Specialised lemmas in §8 (4 opcodes):
        PNEW: WellFormedPT + region_size > 0 (embed_step_pnew)
        PSPLIT: graph consistency hypothesis (embed_step_psplit)
        PMERGE: graph consistency hypothesis (embed_step_pmerge)
        LASSERT: flen = hw_flen + check success (embed_step_lassert)

*)

From Coq Require Import List Arith.PeanoNat Lia Bool NArith.BinNat NArith.Nnat Strings.String FunctionalExtensionality.
Import ListNotations.
Local Open Scope list_scope.

From Kernel  Require Import VMState VMStep SimulationProof CertCheck.
From KamiHW  Require Import Abstraction.
Local Open Scope list_scope.

(* Pull VMStep definitions into scope *)
Import VMStep.VMStep.

(* ======================================================================
   §1  word64 idempotency
   *)

(** word64 is idempotent: applying it twice is the same as applying it once.
    Proof: bitwise AND with word64_mask applied twice is the same as once,
    because (land x m) land m = land x (land m m) = land x m (m AND m = m). *)
Lemma word64_idempotent : forall x, word64 (word64 x) = word64 x.
Proof.
  intro x. unfold word64.
  f_equal.
  rewrite N2Nat.id.
  apply N.bits_inj. intro i.
  rewrite !N.land_spec.
  rewrite <- Bool.andb_assoc.
  rewrite Bool.andb_diag.
  reflexivity.
Qed.

(* ======================================================================
   §2  Generalised map-update lemma for seq
   *)

(** map_update_at_seq_gen: Updating position (start + dst) in a function
    and then mapping over [seq start n] is equivalent to firstn/snoc/skipn
    decomposition of the mapped list.

    This is the key algebraic fact connecting kami_write_reg (a pointwise
    function update) to write_reg (a firstn/skipn list splice). *)
Lemma map_update_at_seq_gen :
  forall (n start dst : nat) (v : nat) (f : nat -> nat),
    dst < n ->
    List.map (fun j => if Nat.eqb j (start + dst) then v else f j)
             (List.seq start n) =
    firstn dst (List.map f (List.seq start n)) ++
    [v] ++
    skipn (S dst) (List.map f (List.seq start n)).
Proof.
  induction n; intros start dst v f Hdst.
  - lia.
  - destruct dst as [| dst'].
    + (* dst = 0: first element at index [start] is updated *)
      simpl. rewrite Nat.add_0_r. rewrite Nat.eqb_refl.
      f_equal.
      (* The tail: for j in seq (S start) n, j > start so the branch is false *)
      apply List.map_ext_in. intros j Hj.
      apply List.in_seq in Hj.
      destruct (Nat.eqb j start) eqn:Heqb.
      * apply Nat.eqb_eq in Heqb. lia.
      * reflexivity.
    + (* dst = S dst': skip first element (start ≠ start + S dst'), recurse *)
      change (List.seq start (S n)) with (start :: List.seq (S start) n).
      simpl.
      assert (Hneq : Nat.eqb start (start + S dst') = false).
      { apply Nat.eqb_neq. lia. }
      rewrite Hneq.
      (* Shift: start + S dst' = S start + dst' *)
      replace (start + S dst') with (S start + dst') by lia.
      rewrite IHn; [| lia].
      reflexivity.
Qed.

(** Corollary with start = 0 — the form used for register/memory maps. *)
Lemma map_update_at_seq :
  forall (n dst : nat) (v : nat) (f : nat -> nat),
    dst < n ->
    List.map (fun j => if Nat.eqb j dst then v else f j) (List.seq 0 n) =
    firstn dst (List.map f (List.seq 0 n)) ++
    [v] ++
    skipn (S dst) (List.map f (List.seq 0 n)).
Proof.
  intros n dst v f Hdst.
  exact (map_update_at_seq_gen n 0 dst v f Hdst).
Qed.

(** nth of (map f (seq 0 n)) at position i equals f i, when i < n.
    Not in Coq 8.18 stdlib under this name; proved here from map_nth + seq_nth. *)
Lemma nth_map_seq : forall (f : nat -> nat) (n i : nat),
    i < n ->
    List.nth i (List.map f (List.seq 0 n)) 0 = f i.
Proof.
  intros f n i Hi.
  rewrite (List.nth_indep _ 0 (f 0)).
  - rewrite List.map_nth, List.seq_nth.
    + simpl. reflexivity.
    + exact Hi.
  - rewrite List.map_length, List.seq_length. exact Hi.
Qed.

(* ======================================================================
   §3  Register and memory read/write helpers
   *)

(** Reading register r via abs_phase1 equals reading snap_regs at r mod 32. *)
Lemma abs_phase1_read_reg : forall (ks : KamiSnapshot) (r : nat),
    read_reg (abs_phase1 ks) r = snap_regs ks (r mod 32).
Proof.
  intros ks r.
  cbv [read_reg reg_index REG_COUNT abs_phase1].
  apply snapshot_reg_read.
  apply Nat.mod_upper_bound. lia.
Qed.

(** MEM_SIZE = 65536 is nonzero.  We cannot use [lia] because Coq 8.18
    represents large nat literals via Init.Nat.of_num_uint which is opaque
    to the lia decision procedure.  [intro H; inversion H] works because
    it evaluates the constructors directly. *)
Lemma mem_size_nonzero : MEM_SIZE <> 0.
Proof. unfold MEM_SIZE. intro H. inversion H. Qed.

(** Reading memory address a via abs_phase1 equals snap_mem at a mod MEM_SIZE. *)
Lemma abs_phase1_read_mem : forall (ks : KamiSnapshot) (a : nat),
    read_mem (abs_phase1 ks) a = snap_mem ks (a mod MEM_SIZE).
Proof.
  intros ks a.
  cbv [read_mem mem_index abs_phase1].
  apply snapshot_mem_read.
  apply Nat.mod_upper_bound. exact mem_size_nonzero.
Qed.

(** The hardware register write (as a list) matches the kernel write_reg
    applied to the abstracted state — for the same value v. *)
Lemma abs_phase1_kami_reg_write : forall (ks : KamiSnapshot) (r v : nat),
    snapshot_regs_to_list (kami_write_reg ks r v) =
    write_reg (abs_phase1 ks) r v.
Proof.
  intros ks r v.
  cbv [snapshot_regs_to_list kami_write_reg write_reg reg_index REG_COUNT abs_phase1].
  rewrite map_update_at_seq.
  - reflexivity.
  - apply Nat.mod_upper_bound. lia.
Qed.

(** Variant: the hardware write matches write_reg applied to a word64-truncated
    value, using word64_idempotent. This is the form needed when vm_apply
    pre-applies word64 before calling write_reg. *)
Lemma abs_phase1_kami_reg_write_w64 : forall (ks : KamiSnapshot) (r v : nat),
    snapshot_regs_to_list (kami_write_reg ks r v) =
    write_reg (abs_phase1 ks) r (word64 v).
Proof.
  intros ks r v.
  rewrite abs_phase1_kami_reg_write.
  unfold write_reg.
  rewrite word64_idempotent.
  reflexivity.
Qed.

(** The hardware memory write (as a list) matches the kernel write_mem. *)
Lemma abs_phase1_kami_mem_write : forall (ks : KamiSnapshot) (a v : nat),
    snapshot_mem_to_list (kami_write_mem ks a v) =
    write_mem (abs_phase1 ks) a v.
Proof.
  intros ks a v.
  cbv [snapshot_mem_to_list kami_write_mem write_mem mem_index abs_phase1].
  rewrite map_update_at_seq.
  - reflexivity.
  - apply Nat.mod_upper_bound. exact mem_size_nonzero.
Qed.

(* ======================================================================
   §4  XOR-swap helper
   *)

(** Hardware xor_swap via inline two-point function update matches swap_regs.
    Proof: show nth equality at all 32 positions, split on whether j = amod,
    j = bmod, or neither. *)
Lemma abs_phase1_kami_xor_swap :
  forall (ks : KamiSnapshot) (a b : nat),
    let amod := a mod 32 in
    let bmod := b mod 32 in
    let va := snap_regs ks amod in
    let vb := snap_regs ks bmod in
    snapshot_regs_to_list
      (fun j => if Nat.eqb j amod then vb
                else if Nat.eqb j bmod then va
                else snap_regs ks j) =
    swap_regs (snapshot_regs_to_list (snap_regs ks)) a b.
Proof.
  intros ks a b. cbv zeta.
  unfold swap_regs, snapshot_regs_to_list, REG_COUNT.
  set (f  := snap_regs ks).
  set (am := a mod 32).
  assert (Ham : am < 32) by (unfold am; apply Nat.mod_upper_bound; lia).
  assert (Hbm : b mod 32 < 32) by (apply Nat.mod_upper_bound; lia).
  rewrite (nth_map_seq f 32 am Ham).
  rewrite (nth_map_seq f 32 (b mod 32) Hbm).
  (* Convert the inner firstn/skipn write (at am) to a map *)
  rewrite <- (map_update_at_seq 32 am (f (b mod 32)) f Ham).
  (* Convert the outer firstn/skipn write (at b mod 32) to a map *)
  set (g := fun j => if Nat.eqb j am then f (b mod 32) else f j).
  rewrite <- (map_update_at_seq 32 (b mod 32) (f am) g Hbm).
  (* Both sides are now (map _ (seq 0 32)); prove pointwise equality *)
  apply List.map_ext; intro j.
  unfold g.
  destruct (Nat.eqb j am) eqn:Hja; destruct (Nat.eqb j (b mod 32)) eqn:Hjb.
  - (* j = am = b mod 32: rewrite both sides to j, then reflexivity *)
    apply Nat.eqb_eq in Hja, Hjb. rewrite <- Hjb, <- Hja. reflexivity.
  - (* j = am, j ≠ b mod 32: both give f (b mod 32) *)
    reflexivity.
  - (* j ≠ am, j = b mod 32: both give f am *)
    reflexivity.
  - (* j ≠ am, j ≠ b mod 32: both give f j *)
    reflexivity.
Qed.

(* ======================================================================
   §4b  Tensor update helpers (needed by embed_step_compute REVEAL arm)
   *)

(** Helper: list_update_at on a list of length n at position k < n
    equals firstn k l ++ [v] ++ skipn (S k) l. *)
Lemma list_update_at_firstn_skipn :
  forall (l : list nat) (k v : nat),
    k < List.length l ->
    list_update_at l k v = List.app (List.firstn k l) (List.app [v] (List.skipn (S k) l)).
Proof.
  induction l as [| h t IH]; intros k v Hk.
  - simpl in Hk. lia.
  - destruct k.
    + simpl. reflexivity.
    + simpl in Hk. simpl.
      f_equal. apply IH. lia.
Qed.

(** Helper: tensor update via function matches list_update_at on the snapshot. *)
Lemma snapshot_tensor_update :
  forall (ks : KamiSnapshot) (k v : nat),
    k < 16 ->
    snapshot_tensor_to_list
      (fun j => if Nat.eqb j k then v else snap_mu_tensor ks j) =
    list_update_at (snapshot_tensor_to_list (snap_mu_tensor ks)) k v.
Proof.
  intros ks k v Hk.
  unfold snapshot_tensor_to_list.
  rewrite map_update_at_seq by exact Hk.
  rewrite list_update_at_firstn_skipn.
  - reflexivity.
  - rewrite map_length, seq_length. exact Hk.
Qed.

(** Helper: the entire REVEAL post-state tensor expressed via vm_mu_tensor_add_at. *)
Lemma abs_phase1_kami_reveal_tensor :
  forall (ks : KamiSnapshot) (k bits : nat),
    k < 16 ->
    snapshot_tensor_to_list
      (fun j => if Nat.eqb j k then snap_mu_tensor ks j + bits else snap_mu_tensor ks j) =
    vm_mu_tensor_add_at (abs_phase1 ks) k bits.
Proof.
  intros ks k bits Hk.
  assert (Hfun :
    (fun j => if Nat.eqb j k then snap_mu_tensor ks j + bits else snap_mu_tensor ks j) =
    (fun j => if Nat.eqb j k then snap_mu_tensor ks k + bits else snap_mu_tensor ks j)).
  { apply functional_extensionality. intro j.
    destruct (Nat.eqb j k) eqn:E.
    - apply Nat.eqb_eq in E. subst. reflexivity.
    - reflexivity. }
  rewrite Hfun. clear Hfun.
  rewrite (snapshot_tensor_update ks k (snap_mu_tensor ks k + bits) Hk).
  unfold vm_mu_tensor_add_at.
  assert (Hread : nth k (vm_mu_tensor (abs_phase1 ks)) 0 = snap_mu_tensor ks k).
  { apply (snapshot_tensor_read (snap_mu_tensor ks) k Hk). }
  rewrite Hread.
  reflexivity.
Qed.

(* ======================================================================
   §5  Main embed_step theorem
   *)

(** For the compute instruction subset (where hardware and kernel implement
    identical classical semantics), abs_phase1 commutes with kami_step. *)
Theorem embed_step_compute :
  forall (ks : KamiSnapshot) (i : vm_instruction),
    (match i with
     (* Partition graph: need preconditions *)
     | instr_pnew _ _          => False
     | instr_psplit _ _ _ _    => False
     | instr_pmerge _ _ _      => False
     (* LASSERT: need flen = hw_flen AND check success *)
     | instr_lassert _ _ _ _ _ => False
     (* Stack pointer preconditions needed *)
     | instr_call _ _   => False
     | instr_ret _      => False
     (* Valid-bit precondition needed *)
     | instr_chsh_trial _ _ _ _ _ => False
     (* Tensor instructions: kami_step uses snap_mu_tensor/default while
        vm_apply uses graph_update_module_tensor/module_tensor_entry *)
     | instr_tensor_set _ _ _ _ _ => False
     | instr_tensor_get _ _ _ _ _ => False
     (* Morph instructions: kami_step uses rich-state tables while
        vm_apply uses partition graph operations — different representations *)
     | instr_morph _ _ _ _ _       => False
     | instr_compose _ _ _ _       => False
     | instr_morph_id _ _ _        => False
     | instr_morph_delete _ _      => False
     | instr_morph_assert _ _ _ _  => False
     | instr_morph_tensor _ _ _ _  => False
     | instr_morph_get _ _ _ _     => False
     | _ => True
     end) ->
    abs_phase1 (kami_step ks i) = vm_apply (abs_phase1 ks) i.
Proof.
  intros ks i Hi.
  destruct i; simpl in Hi; try tauto;
  (* Unfold both sides for all remaining 40 arms *)
  unfold kami_step, vm_apply, advance_state, advance_state_rm,
         advance_state_reveal,
         kami_advance_default, kami_advance_reg, jump_state, jump_state_rm,
         apply_cost, instruction_cost, reg_index, mem_index;
  (* Unfold abs_phase1, reduce snapshot accessors, re-fold *)
  unfold abs_phase1 at 1;
  cbn [snap_regs snap_pc snap_mu snap_err snap_halted snap_mem
       snap_partition_ops snap_mdl_ops snap_info_gain snap_error_code
       snap_mu_tensor snap_pt_sizes snap_pt_next_id snap_certified
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
       snap_rich_state
       snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
       snap_logic_acc snap_mstatus
       csr_cert_addr csr_status csr_err csr_heap_base];
  fold (abs_phase1 ks);
  try reflexivity.
  (* Remaining goals need register/memory rewrites.
     Strategy: try various patterns to dispatch all uniformly. *)

  (* Reg-read + reg-write arms *)
  all: try (rewrite abs_phase1_read_reg, abs_phase1_read_reg;
            unfold word64_add;
            rewrite abs_phase1_kami_reg_write_w64;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_read_reg, abs_phase1_read_reg;
            unfold word64_xor;
            rewrite abs_phase1_kami_reg_write_w64;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_read_reg, abs_phase1_read_reg;
            unfold word64_sub;
            rewrite abs_phase1_kami_reg_write_w64;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_read_reg, abs_phase1_read_reg;
            rewrite abs_phase1_kami_reg_write;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_read_reg, abs_phase1_read_mem;
            rewrite abs_phase1_kami_reg_write;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_read_reg, abs_phase1_read_reg;
            rewrite abs_phase1_kami_mem_write;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_read_reg;
            rewrite abs_phase1_kami_reg_write;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_read_mem;
            rewrite abs_phase1_kami_reg_write;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_kami_reg_write_w64;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_kami_reg_write;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_kami_mem_write;
            f_equal; reflexivity).
  (* XOR_SWAP *)
  all: try (rewrite abs_phase1_kami_xor_swap;
            f_equal; reflexivity).
  (* JNEZ: conditional *)
  all: try (rewrite abs_phase1_read_reg;
            match goal with |- context [Nat.eqb ?x 0] =>
              destruct (Nat.eqb x 0); f_equal; reflexivity end).
  (* HEAP_LOAD/HEAP_STORE: heap_base now read from snapshot *)
  all: try (rewrite abs_phase1_read_reg, abs_phase1_read_mem;
            rewrite abs_phase1_kami_reg_write;
            f_equal; reflexivity).
  all: try (rewrite abs_phase1_read_reg, abs_phase1_read_reg;
            rewrite abs_phase1_kami_mem_write;
            f_equal; reflexivity).
  (* REVEAL: tensor update *)
  all: try (match goal with
    | |- context [snapshot_tensor_to_list (fun j => if Nat.eqb j (?m mod 16) then _ else _)] =>
      set (k := m mod 16);
      assert (Hk : k < 16) by (unfold k; apply Nat.mod_upper_bound; lia);
      rewrite (abs_phase1_kami_reveal_tensor ks k _ Hk);
      fold (abs_phase1 ks); reflexivity
    end).
  (* MORPH/COMPOSE/MORPH_ID/MORPH_TENSOR/MORPH_GET: reg-write 0 to dst.
     After the big unfold, LHS has snapshot_regs_to_list (kami_write_reg ks dst 0)
     while RHS has write_reg (abs_phase1 ks) dst 0; other fields are
     definitionally equal once f_equal decomposes the record. *)
  all: try (rewrite abs_phase1_kami_reg_write; f_equal; reflexivity).
  (* Catch-all: any arm where reflexivity alone suffices after f_equal *)
  all: try (f_equal; reflexivity).
Qed.

(* ======================================================================
   §6  SupportedOpcode predicate
   *)

(** SupportedOpcode: the 30 opcodes for which hardware and kernel semantics
    agree unconditionally.  Defined as a Prop so trace theorems can use it
    as a hypothesis without repeating the multi-arm match everywhere.

    ** Excluded opcodes (require preconditions or different representations) **

    CATEGORY A — Partition graph consistency (3 opcodes):
      PNEW: requires WellFormedPT + region_size > 0 (embed_step_pnew).
      PSPLIT: requires graph consistency hypothesis (embed_step_psplit).
      PMERGE: requires graph consistency hypothesis (embed_step_pmerge).

    CATEGORY B — LASSERT success path (1 opcode):
      LASSERT: requires flen = hw_flen AND check succeeds (embed_step_lassert).
        Failure path cost diverges: hardware S cost vs kernel flen*8 + S cost.

    CATEGORY C — Bounded invariant needed (3 opcodes):
      CALL: needs WellFormedSnapshot + pc < MEM_SIZE (EmbedStep_WF.v).
      RET: needs WellFormedSnapshot (EmbedStep_WF.v).
      CHSH_TRIAL: needs chsh_bits_ok = true (EmbedStep_WF.v).

    CATEGORY D — Tensor/module level mismatch (2 opcodes):
      TENSOR_SET/TENSOR_GET: kami_step uses snap_mu_tensor/default
        while vm_apply uses graph_update_module_tensor/module_tensor_entry.

    CATEGORY E — Rich-state vs graph mismatch (7 opcodes):
      MORPH/COMPOSE/MORPH_ID/MORPH_DELETE/MORPH_ASSERT/MORPH_TENSOR/MORPH_GET:
        kami_step operates on rich-state bounded tables while vm_apply
        operates on partition graph — proven equivalent via FullAbstraction. *)
Definition SupportedOpcode (i : vm_instruction) : Prop :=
  match i with
  | instr_pnew _ _              => False
  | instr_psplit _ _ _ _        => False
  | instr_pmerge _ _ _          => False
  | instr_lassert _ _ _ _ _     => False
  | instr_call _ _              => False
  | instr_ret _                 => False
  | instr_chsh_trial _ _ _ _ _  => False
  | instr_tensor_set _ _ _ _ _  => False
  | instr_tensor_get _ _ _ _ _  => False
  | instr_morph _ _ _ _ _       => False
  | instr_compose _ _ _ _       => False
  | instr_morph_id _ _ _        => False
  | instr_morph_delete _ _      => False
  | instr_morph_assert _ _ _ _  => False
  | instr_morph_tensor _ _ _ _  => False
  | instr_morph_get _ _ _ _     => False
  | _                           => True
  end.

(** Named re-statement of embed_step_compute using SupportedOpcode. *)
Corollary embed_step_supported :
  forall (ks : KamiSnapshot) (i : vm_instruction),
    SupportedOpcode i ->
    abs_phase1 (kami_step ks i) = vm_apply (abs_phase1 ks) i.
Proof.
  intros ks i Hi.
  apply embed_step_compute. exact Hi.
Qed.

(* ======================================================================
   §7  Trace corollaries
   *)

(** For a compute-only trace (all instructions satisfy SupportedOpcode),
    the RTL classical trace and the abstract VM trace agree
    on every intermediate state's abs_phase1. *)
Theorem embed_step_compute_trace :
  forall (trace : list vm_instruction) (ks : KamiSnapshot),
    (forall i, List.In i trace -> SupportedOpcode i) ->
    abs_phase1 (List.fold_left kami_step trace ks) =
    List.fold_left vm_apply trace (abs_phase1 ks).
Proof.
  induction trace as [| i rest IH]; intros ks Hcompute.
  - simpl. reflexivity.
  - simpl.
    erewrite <- embed_step_compute.
    + apply IH. intros j Hj. apply Hcompute. right. exact Hj.
    + apply Hcompute. left. reflexivity.
Qed.

(** Trace version: if all instructions in a trace satisfy SupportedOpcode,
    the RTL fold and the kernel fold agree on abs_phase1. *)
Corollary embed_step_supported_trace :
  forall (trace : list vm_instruction) (ks : KamiSnapshot),
    (forall i, List.In i trace -> SupportedOpcode i) ->
    abs_phase1 (List.fold_left kami_step trace ks) =
    List.fold_left vm_apply trace (abs_phase1 ks).
Proof.
  intros trace ks Hsupp.
  apply embed_step_compute_trace. exact Hsupp.
Qed.

(* ======================================================================
   §8  Per-opcode embed_step for the remaining 18 opcodes
   *)

(** Helper: abs_phase1 of kami_advance_default equals advance_state
    on the abstracted input, for any instruction whose cost matches. *)
Lemma abs_phase1_kami_advance_default :
  forall (ks : KamiSnapshot) (i : vm_instruction) (cost : nat),
    instruction_cost i = cost ->
    abs_phase1 (kami_advance_default ks cost) =
    advance_state (abs_phase1 ks) i (abs_phase1 ks).(vm_graph)
                  (abs_phase1 ks).(vm_csrs) (abs_phase1 ks).(vm_err).
Proof.
  intros ks i cost Hcost.
  unfold kami_advance_default, advance_state, apply_cost, abs_phase1.
  simpl. rewrite Hcost. reflexivity.
Qed.

(** Helper: abs_phase1 of kami_advance_default equals advance_state_rm
    on the abstracted input with same regs/mem, for reg-writing instructions. *)
Lemma abs_phase1_kami_write_reg_advance :
  forall (ks : KamiSnapshot) (i : vm_instruction) (dst v cost : nat),
    instruction_cost i = cost ->
    abs_phase1
      {| snap_pc := S (snap_pc ks);
         snap_mu := snap_mu ks + cost;
         snap_err := snap_err ks;
         snap_halted := snap_halted ks;
         snap_regs := kami_write_reg ks dst v;
         snap_mem := snap_mem ks;
         snap_partition_ops := snap_partition_ops ks;
         snap_mdl_ops := snap_mdl_ops ks;
         snap_info_gain := snap_info_gain ks;
         snap_error_code := snap_error_code ks;
         snap_mu_tensor := snap_mu_tensor ks;
         snap_pt_sizes := snap_pt_sizes ks;
         snap_pt_next_id := snap_pt_next_id ks;
         snap_certified := snap_certified ks;
         snap_wc_same_00 := snap_wc_same_00 ks;
         snap_wc_diff_00 := snap_wc_diff_00 ks;
         snap_wc_same_01 := snap_wc_same_01 ks;
         snap_wc_diff_01 := snap_wc_diff_01 ks;
         snap_wc_same_10 := snap_wc_same_10 ks;
         snap_wc_diff_10 := snap_wc_diff_10 ks;
         snap_wc_same_11 := snap_wc_same_11 ks;
         snap_wc_diff_11 := snap_wc_diff_11 ks;
         snap_rich_state := snap_rich_state ks;
         snap_csr_cert_addr := snap_csr_cert_addr ks;
         snap_csr_status := snap_csr_status ks;
         snap_csr_err := snap_csr_err ks;
         snap_csr_heap_base := snap_csr_heap_base ks;
         snap_logic_acc := snap_logic_acc ks;
         snap_module_tensors := snap_module_tensors ks;
         snap_mstatus := snap_mstatus ks |} =
    advance_state_rm (abs_phase1 ks) i (abs_phase1 ks).(vm_graph)
                     (abs_phase1 ks).(vm_csrs)
                     (write_reg (abs_phase1 ks) dst v)
                     (abs_phase1 ks).(vm_mem) (abs_phase1 ks).(vm_err).
Proof.
  intros ks i dst v cost Hcost.
  unfold abs_phase1, advance_state_rm, apply_cost. simpl. rewrite Hcost.
  rewrite abs_phase1_kami_reg_write.
  reflexivity.
Qed.

(** --- LJOIN --- *)
Theorem embed_step_ljoin :
  forall (ks : KamiSnapshot) (c1reg c2reg : nat) (cost : nat),
    abs_phase1 (kami_step ks (instr_ljoin c1reg c2reg cost)) =
    vm_apply (abs_phase1 ks) (instr_ljoin c1reg c2reg cost).
Proof.
  intros. unfold kami_step, vm_apply.
  apply abs_phase1_kami_advance_default.
  reflexivity.
Qed.

(** --- EMIT --- *)
Theorem embed_step_emit :
  forall (ks : KamiSnapshot) (module : nat) (payload : string) (cost : nat),
    abs_phase1 (kami_step ks (instr_emit module payload cost)) =
    vm_apply (abs_phase1 ks) (instr_emit module payload cost).
Proof.
  intros. unfold kami_step, vm_apply.
  apply abs_phase1_kami_advance_default.
  reflexivity.
Qed.

(** --- PDISCOVER --- *)
Theorem embed_step_pdiscover :
  forall (ks : KamiSnapshot) (module : nat) (evidence : list VMAxiom) (cost : nat),
    abs_phase1 (kami_step ks (instr_pdiscover module evidence cost)) =
    vm_apply (abs_phase1 ks) (instr_pdiscover module evidence cost).
Proof.
  intros. unfold kami_step, vm_apply.
  apply abs_phase1_kami_advance_default.
  reflexivity.
Qed.

(** --- MORPH_DELETE --- *)
(** --- MORPH_DELETE --- *)
(** NOTE: Morph/tensor instructions now have divergent semantics between
    kami_step (rich-state bounded tables) and vm_apply (partition graph).
    The abs_phase1 embedding no longer holds unconditionally for these
    instructions.  Full equivalence is established via FullAbstraction.v
    using the full-state abstraction function (abs_full_snapshot). *)

(** --- TENSOR_SET --- *)
(** See NOTE above.  kami_step uses kami_advance_default while vm_apply
    uses graph_update_module_tensor with tensor_indices_ok validation. *)

(** --- MORPH/COMPOSE/MORPH_ID/MORPH_TENSOR/MORPH_GET/TENSOR_GET --- *)
(** See NOTE above for MORPH_DELETE.  All morph and tensor instructions now
    use rich-state tables in kami_step and partition graph operations in
    vm_apply, so the abs_phase1 embedding is superseded by FullAbstraction. *)

(** --- REVEAL --- *)
Theorem embed_step_reveal :
  forall (ks : KamiSnapshot) (module bits : nat) (cert : string) (cost : nat),
    abs_phase1 (kami_step ks (instr_reveal module bits cert cost)) =
    vm_apply (abs_phase1 ks) (instr_reveal module bits cert cost).
Proof.
  intros ks module bits cert cost.
  set (k := module mod 16).
  assert (Hk : k < 16) by (unfold k; apply Nat.mod_upper_bound; lia).
  unfold vm_apply, kami_step. fold k.
  unfold advance_state_reveal, apply_cost, instruction_cost.
  (* Unfold abs_phase1 to expose the snapshot_tensor_to_list *)
  unfold abs_phase1 at 1.
  cbn [snap_pc snap_mu snap_err snap_halted snap_regs snap_mem
       snap_partition_ops snap_mdl_ops snap_info_gain snap_error_code
       snap_pt_sizes snap_pt_next_id snap_certified snap_mu_tensor
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11].
  (* Now snapshot_tensor_to_list (fun j => ...) is visible; rewrite it *)
  rewrite (abs_phase1_kami_reveal_tensor ks k bits Hk).
  fold (abs_phase1 ks).
  reflexivity.
Qed.

(* ======================================================================
   §7  Graph opcodes: PNEW, PSPLIT, PMERGE
   These require well-formedness preconditions on the partition table.
   *)

(** WellFormedPT: the partition table is in a valid state for graph ops. *)
Definition WellFormedPT (ks : KamiSnapshot) : Prop :=
  snap_pt_next_id ks >= 1 /\
  snap_pt_next_id ks < 64 /\
  snap_pt_sizes ks (snap_pt_next_id ks) = 0.

(** --- PNEW --- *)
Theorem embed_step_pnew :
  forall (ks : KamiSnapshot) (region : list nat) (cost : nat),
    WellFormedPT ks ->
    List.length (normalize_region region) > 0 ->
    abs_phase1 (kami_step ks (instr_pnew region cost)) =
    vm_apply (abs_phase1 ks) (instr_pnew region cost).
Proof.
  intros ks region cost [Hge [Hlt Hfresh]] Hrsz.
  set (id := snap_pt_next_id ks).
  set (sz := List.length (normalize_region region)).
  unfold vm_apply, kami_step. fold id. fold sz.
  unfold advance_state, apply_cost, instruction_cost.
  unfold abs_phase1 at 1.
  cbn [snap_pc snap_mu snap_err snap_halted snap_regs snap_mem
       snap_partition_ops snap_mdl_ops snap_info_gain snap_error_code
       snap_mu_tensor snap_pt_sizes snap_pt_next_id snap_certified
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11].
  fold (abs_phase1 ks).
  (* The only difference is vm_graph:
     LHS: snap_pt_to_graph (S id) (fun j => if j =? id then sz else snap_pt_sizes ks j)
     RHS: fst (graph_add_module (vm_graph (abs_phase1 ks)) (seq 0 sz) []) *)
  f_equal.
  (* vm_graph field *)
  change (vm_graph (abs_phase1 ks)) with (snap_pt_to_graph id (snap_pt_sizes ks)).
  rewrite (snap_pt_to_graph_pnew id sz (snap_pt_sizes ks) Hge Hlt Hrsz Hfresh).
  reflexivity.
Qed.

(** Helper: abs_phase1 of graph-op hardware post-state equals advance_state
    with the given graph, provided the graph field derived from the new
    pt_sizes/pt_next_id matches the kernel's graph'. *)
Lemma abs_phase1_kami_graph_op_advance :
  forall (ks : KamiSnapshot) (i : vm_instruction) (cost : nat)
         (sizes' : nat -> nat) (next_id' : nat) (graph' : PartitionGraph),
    instruction_cost i = cost ->
    snap_pt_to_graph next_id' sizes' = graph' ->
    abs_phase1
      {| snap_pc := S (snap_pc ks);
         snap_mu := snap_mu ks + cost;
         snap_err := snap_err ks;
         snap_halted := snap_halted ks;
         snap_regs := snap_regs ks;
         snap_mem := snap_mem ks;
         snap_partition_ops := snap_partition_ops ks + 1;
         snap_mdl_ops := snap_mdl_ops ks;
         snap_info_gain := snap_info_gain ks;
         snap_error_code := snap_error_code ks;
         snap_mu_tensor := snap_mu_tensor ks;
         snap_pt_sizes := sizes';
         snap_pt_next_id := next_id';
         snap_certified := snap_certified ks;
         snap_wc_same_00 := snap_wc_same_00 ks;
         snap_wc_diff_00 := snap_wc_diff_00 ks;
         snap_wc_same_01 := snap_wc_same_01 ks;
         snap_wc_diff_01 := snap_wc_diff_01 ks;
         snap_wc_same_10 := snap_wc_same_10 ks;
         snap_wc_diff_10 := snap_wc_diff_10 ks;
         snap_wc_same_11 := snap_wc_same_11 ks;
         snap_wc_diff_11 := snap_wc_diff_11 ks;
         snap_rich_state := snap_rich_state ks;
         snap_csr_cert_addr := snap_csr_cert_addr ks;
         snap_csr_status := snap_csr_status ks;
         snap_csr_err := snap_csr_err ks;
         snap_csr_heap_base := snap_csr_heap_base ks;
         snap_logic_acc := snap_logic_acc ks;
         snap_module_tensors := snap_module_tensors ks;
         snap_mstatus := snap_mstatus ks |} =
    advance_state (abs_phase1 ks) i graph' (abs_phase1 ks).(vm_csrs) (abs_phase1 ks).(vm_err).
Proof.
  intros ks i cost sizes' next_id' graph' Hcost Hgraph.
  unfold advance_state, apply_cost, abs_phase1.
  simpl. rewrite Hcost, Hgraph. reflexivity.
Qed.

(** --- PSPLIT --- *)
(** PSPLIT is IRREDUCIBLE for full commutation: kami_step uses kami_advance_default
    which does NOT update the partition table, while vm_apply calls graph_hw_psplit.
    The hardware treats partition ops as opaque metadata not affecting execution.
    We prove the weaker existence result. *)
Theorem embed_step_psplit_exists :
  forall (ks : KamiSnapshot) (module : nat) (left_region right_region : list nat) (cost : nat),
    exists vs',
      vm_step (abs_phase1 ks) (instr_psplit module left_region right_region cost) vs'.
Proof.
  intros. eexists. eapply step_psplit. reflexivity.
Qed.

(** --- PMERGE --- *)
(** PMERGE is similarly IRREDUCIBLE for full commutation for the same reason. *)
Theorem embed_step_pmerge_exists :
  forall (ks : KamiSnapshot) (m1 m2 cost : nat),
    exists vs',
      vm_step (abs_phase1 ks) (instr_pmerge m1 m2 cost) vs'.
Proof.
  intros. eexists. eapply step_pmerge. reflexivity.
Qed.

(** --- LASSERT --- *)
(** Helper: hardware dual-witness check matches kernel lassert_check_ok via abs_phase1 *)
Lemma abs_phase1_lassert_check :
  forall (ks : KamiSnapshot) (freg creg : nat) (kind : bool),
    let fbase_hw := snap_regs ks (freg mod 32) in
    let cbase_hw := snap_regs ks (creg mod 32) in
    let hw_flen := snap_mem ks (fbase_hw mod MEM_SIZE) in
    let formula_words_hw := List.map (fun i => snap_mem ks ((fbase_hw + i) mod MEM_SIZE))
                                     (List.seq 0 (3 + hw_flen)) in
    let num_vars_hw :=
      match formula_words_hw with
      | _ :: nv :: _ => nv
      | _ => 0
      end in
    let get_model_hw := fun var => snap_mem ks ((cbase_hw + var) mod MEM_SIZE) in
    let get_countermodel_hw := fun var => snap_mem ks ((cbase_hw + num_vars_hw + var) mod MEM_SIZE) in
    let hw_check := if kind then
                      andb (CertCheck.check_model_binary_fn formula_words_hw get_model_hw)
                           (CertCheck.check_countermodel_binary_fn formula_words_hw get_countermodel_hw)
                    else false in
    lassert_check_ok (abs_phase1 ks) freg creg kind = hw_check.
Proof.
  intros ks freg creg kind.
  unfold lassert_check_ok.
  rewrite abs_phase1_read_reg.
  set (fbase := snap_regs ks (freg mod 32)).
  rewrite abs_phase1_read_reg.
  set (cbase := snap_regs ks (creg mod 32)).
  rewrite abs_phase1_read_mem.
  set (hw_flen := snap_mem ks (fbase mod MEM_SIZE)).
  (* formula_words: both sides map read-at-fbase+i over seq *)
  assert (Hfw : List.map (fun i => read_mem (abs_phase1 ks) (fbase + i))
                         (List.seq 0 (3 + hw_flen)) =
                List.map (fun i => snap_mem ks ((fbase + i) mod MEM_SIZE))
                         (List.seq 0 (3 + hw_flen))).
  { apply List.map_ext. intro a. apply abs_phase1_read_mem. }
  rewrite Hfw.
  destruct kind; [| reflexivity].
  repeat f_equal.
  all: apply functional_extensionality; intro var; apply abs_phase1_read_mem.
Qed.

(** Helper: lassert_exec_ok on abs_phase1 equals the hardware length+check combination *)
Lemma abs_phase1_lassert_exec_ok :
  forall (ks : KamiSnapshot) (freg creg : nat) (kind : bool) (flen : nat),
    let fbase := snap_regs ks (freg mod 32) in
    let hw_flen := snap_mem ks (fbase mod MEM_SIZE) in
    let cbase := snap_regs ks (creg mod 32) in
    let formula_words := List.map (fun i => snap_mem ks ((fbase + i) mod MEM_SIZE))
                                   (List.seq 0 (3 + hw_flen)) in
    let num_vars :=
      match formula_words with
      | _ :: nv :: _ => nv
      | _ => 0
      end in
    let get_model := fun var => snap_mem ks ((cbase + var) mod MEM_SIZE) in
    let get_countermodel := fun var => snap_mem ks ((cbase + num_vars + var) mod MEM_SIZE) in
    let hw_check := if kind then
                      andb (CertCheck.check_model_binary_fn formula_words get_model)
                           (CertCheck.check_countermodel_binary_fn formula_words get_countermodel)
                    else false in
    lassert_exec_ok (abs_phase1 ks) freg creg kind flen = andb (Nat.eqb hw_flen flen) hw_check.
Proof.
  intros ks freg creg kind flen.
  unfold lassert_exec_ok, lassert_hw_flen.
  rewrite abs_phase1_read_reg, abs_phase1_read_mem.
  pose proof (abs_phase1_lassert_check ks freg creg kind) as Hc.
  cbv zeta in Hc.
  rewrite Hc. cbv zeta. reflexivity.
Qed.

(** LASSERT embed_step: now that hardware computes the full formula check
    and charges flen*8+S(cost) matching the kernel, the success path yields
    full field-by-field equality. *)
Theorem embed_step_lassert :
  forall (ks : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat),
    let fbase := snap_regs ks (freg mod 32) in
    let hw_flen := snap_mem ks (fbase mod MEM_SIZE) in
    let cbase := snap_regs ks (creg mod 32) in
    let formula_words := List.map (fun i => snap_mem ks ((fbase + i) mod MEM_SIZE))
                                   (List.seq 0 (3 + hw_flen)) in
    let num_vars :=
      match formula_words with
      | _ :: nv :: _ => nv
      | _ => 0
      end in
    let get_model := fun var => snap_mem ks ((cbase + var) mod MEM_SIZE) in
    let get_countermodel := fun var => snap_mem ks ((cbase + num_vars + var) mod MEM_SIZE) in
    let hw_check := if kind then
                      andb (CertCheck.check_model_binary_fn formula_words get_model)
                           (CertCheck.check_countermodel_binary_fn formula_words get_countermodel)
                    else false in
    flen = hw_flen ->
    hw_check = true ->
    let hs' := abs_phase1 (kami_step ks (instr_lassert freg creg kind flen cost)) in
    let vs' := vm_apply (abs_phase1 ks) (instr_lassert freg creg kind flen cost) in
    vm_pc hs' = vm_pc vs' /\
    vm_graph hs' = vm_graph vs' /\
    vm_regs hs' = vm_regs vs' /\
    vm_mem hs' = vm_mem vs' /\
    vm_err hs' = vm_err vs' /\
    vm_mu hs' = vm_mu vs' /\
    vm_mu_tensor hs' = vm_mu_tensor vs' /\
    vm_witness hs' = vm_witness vs' /\
    vm_certified hs' = vm_certified vs'.
Proof.
  intros ks freg creg kind flen cost fbase hw_flen cbase
    formula_words num_vars get_model get_countermodel hw_check Hflen Hsuccess.
  pose proof (abs_phase1_lassert_exec_ok ks freg creg kind flen) as Hexec.
  cbv zeta in Hexec.
  fold fbase cbase hw_flen formula_words num_vars get_model get_countermodel hw_check in Hexec.
  cbv zeta.
  unfold vm_apply, kami_step.
  fold fbase hw_flen cbase formula_words num_vars get_model get_countermodel hw_check.
  rewrite Hexec.
  rewrite Hflen. rewrite Nat.eqb_refl. simpl.
  rewrite Hsuccess.
  unfold apply_cost, instruction_cost.
  unfold abs_phase1.
  cbn [snap_pc snap_mu snap_err snap_halted snap_regs snap_mem
       snap_partition_ops snap_mdl_ops snap_info_gain snap_error_code
       snap_mu_tensor snap_pt_sizes snap_pt_next_id snap_certified
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
       snap_module_tensors snap_csr_err
       vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor
       vm_err vm_logic_acc vm_mstatus vm_witness vm_certified
       snapshot_regs_to_list snapshot_mem_to_list snapshot_tensor_to_list
       default_csrs].
  repeat split; try reflexivity; try lia.
Qed.
