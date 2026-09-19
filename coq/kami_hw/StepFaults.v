(** Fault outcomes of the actual step rule for an arbitrary fetched word.

    The step rule computes six guards: [bianchi_violation],
    [locality_violation], [ptable_overflow_violation], [nfi_violation],
    [rich_fault] and [morph_runtime_fault]. Every result here is stated for
    an arbitrary boundary and an arbitrary 128-bit fetched word, with the
    guards named by their [DispatchLets] definitions, which are the CPU's own
    LET expressions. No opcode, format or operand is fixed.

    The first five guards form the trap class: the PC takes the trap vector.
    [kami_step] has none of these guards, so their outcomes are the specified
    outside-domain behaviour of C1. [morph_runtime_fault] advances the PC and
    is the hardware side of the morph failure cases of [kami_step].

    One premise is used throughout: every valid coupling descriptor lies below
    [coupling_desc_next_id]. A trapped MORPH or COMPOSE word still writes its
    label into the unallocated descriptor slot at that pointer; the premise
    makes that write invisible to the observation. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Bool Arith Lia FunctionalExtensionality.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary RuleNext
  BoundaryDecoded RuleStep StepEval StepWordFacts DispatchLets Abstraction
  ImplementationContract.
Import ListNotations.

Ltac dd_cbn := cbn [evalExpr evalBinBool evalUniBool evalConstT isEq].
Ltac bool_red := cbv beta iota delta [orb andb negb].

(** Every valid coupling descriptor lies below the allocation pointer. *)
Definition hwb_coupling_desc_valid_below_next (b : HWB) : Prop :=
  forall i, hw_coupling_desc_valid_table b i = true ->
  wordToNat i < wordToNat (hw_coupling_desc_next_id b).

Definition guard_opcodes : list (word OpcodeSz) :=
  [OP_LOAD; OP_HEAP_LOAD; OP_STORE; OP_HEAP_STORE; OP_CALL; OP_RET;
   OP_PNEW; OP_PSPLIT; OP_PMERGE; OP_PDISCOVER].
Definition locality_opcodes : list (word OpcodeSz) :=
  [OP_LOAD; OP_HEAP_LOAD; OP_STORE; OP_HEAP_STORE; OP_CALL; OP_RET].
Definition partition_opcodes : list (word OpcodeSz) := [OP_PNEW; OP_PSPLIT; OP_PMERGE].
Definition morph_opcodes : list (word OpcodeSz) :=
  [OP_MORPH; OP_COMPOSE; OP_MORPH_ID; OP_MORPH_DELETE; OP_MORPH_ASSERT;
   OP_MORPH_TENSOR; OP_MORPH_GET].

Definition op_test (x c : word OpcodeSz) : bool := if weq x c then true else false.
Definition op_member (c : word OpcodeSz) (l : list (word OpcodeSz)) : bool :=
  existsb (fun y => op_test y c) l.

(** An opcode test against a constant outside a class is false for every
    opcode inside it; the membership test is a closed computation. *)
Lemma op_test_outside : forall x c l,
  In x l -> op_member c l = false -> op_test x c = false.
Proof.
  intros x c l Hin Hl. unfold op_test. destruct (weq x c) as [E|E]; [|reflexivity].
  subst x. exfalso. rewrite <- Bool.not_true_iff_false in Hl. apply Hl.
  apply existsb_exists. exists c. split; [exact Hin|].
  unfold op_test. destruct (weq c c); [reflexivity|contradiction].
Qed.

Lemma op_in_member_false : forall x c l,
  In x l -> op_member c l = false -> x = c -> False.
Proof.
  intros x c l Hin Hl E. pose proof (op_test_outside x c l Hin Hl) as H.
  unfold op_test in H. destruct (weq x c); [discriminate H|contradiction].
Qed.

(** Every test of the opcode against a constant outside the class of [Hin]
    takes its [false] branch. *)
Ltac op_off Hin :=
  repeat match goal with
  | |- context [weq ?x ?c] =>
      let E := fresh "E" in
      destruct (weq x c) as [E|E];
      [exfalso; exact (op_in_member_false x c _ Hin eq_refl E)|]
  end.

(** Decide an opcode test whose two sides are constants. *)
Ltac close_weq :=
  repeat match goal with
  | |- context [weq ?x ?y] =>
      lazymatch x with dd_opcode _ _ => fail | _ =>
      destruct (weq x y) as [Hq|Hq];
      [first [discriminate Hq | clear Hq] | first [exfalso; exact (Hq eq_refl) | clear Hq]]
      end
  end.

Ltac same_branches :=
  match goal with |- (if ?c then ?x else ?x) = ?x => destruct c; reflexivity end.

Lemma op_disjoint : forall x l1 l2,
  In x l1 -> In x l2 -> forallb (fun c => negb (op_member c l2)) l1 = true -> False.
Proof.
  intros x l1 l2 H1 H2 H. apply forallb_forall with (x := x) in H; [|exact H1].
  rewrite Bool.negb_true_iff in H. unfold op_member in H.
  rewrite <- Bool.not_true_iff_false in H. apply H. apply existsb_exists.
  exists x. split; [exact H2|]. unfold op_test. destruct (weq x x); [reflexivity|contradiction].
Qed.

Lemma split1_4_1_small : forall x : word 5,
  wordToNat x < 16 -> wordToNat (split1 4 1 x) = wordToNat x.
Proof.
  intros x H. shatter_word x.
  destruct x0, x1, x2, x3, x4; cbn in *; lia.
Qed.

Section Guards.
Variables (b : HWB) (w : word InstrSz).

Definition dd_trap : bool :=
  hwb_bianchi b || dd_locality_violation b w || dd_ptable_overflow_violation b w ||
  dd_nfi_violation b w || dd_rich_fault b w.
Definition dd_freeze : bool := dd_trap || dd_morph_runtime_fault b w.

Ltac in_list :=
  match goal with E : dd_opcode b w = _ |- _ =>
    rewrite E; cbn [In]; repeat first [left; reflexivity | right] end.

Ltac opcode_class :=
  repeat match goal with
  | |- context [weq (dd_opcode b w) ?c] =>
      destruct (weq (dd_opcode b w) c) as [E|E]; [intros _; in_list|clear E]
  end;
  bool_red; let H := fresh "H" in intro H; discriminate H.

(** * Which opcodes can raise which guard *)

Lemma dd_locality_opcode :
  dd_locality_violation b w = true -> In (dd_opcode b w) locality_opcodes.
Proof.
  unfold dd_locality_violation, dd_load_locality_bad, dd_store_locality_bad,
    dd_call_locality_bad, dd_ret_locality_bad, dd_is_load_op, dd_is_store_op,
    dd_is_call_op, dd_is_ret_op, locality_opcodes.
  dd_cbn. opcode_class.
Qed.

Lemma dd_ptable_opcode :
  dd_ptable_overflow_violation b w = true -> In (dd_opcode b w) partition_opcodes.
Proof.
  unfold dd_ptable_overflow_violation, dd_pnew_overflow, dd_psplit_overflow,
    dd_pmerge_overflow, partition_opcodes.
  dd_cbn. opcode_class.
Qed.

Lemma dd_nfi_opcode : dd_nfi_violation b w = true -> dd_opcode b w = OP_PDISCOVER.
Proof.
  unfold dd_nfi_violation, dd_is_declared_bound_op. dd_cbn.
  destruct (weq (dd_opcode b w) OP_PDISCOVER) as [E|E]; [intros _; exact E|].
  bool_red. intro H. discriminate H.
Qed.

Lemma dd_morph_opcode :
  dd_morph_runtime_fault b w = true -> In (dd_opcode b w) morph_opcodes.
Proof.
  unfold dd_morph_runtime_fault, dd_morph_ext_endpoint_fault,
    dd_morph_legacy_endpoint_fault, dd_compose_lookup_fault, dd_compose_type_fault,
    dd_morph_delete_fault, dd_morph_get_fault, dd_morph_get_coupling_fault,
    dd_morph_assert_fault, dd_morph_tensor_fault, dd_is_morph_ext, dd_is_morph_id_ext,
    dd_is_morph_legacy, dd_is_morph_id_legacy, dd_is_compose_ext, dd_is_compose_legacy,
    dd_is_morph_delete_ext, dd_is_morph_delete_legacy, dd_is_morph_get_ext,
    dd_is_morph_get_legacy, dd_is_morph_assert_ext, dd_is_morph_assert_legacy,
    dd_is_morph_tensor, morph_opcodes.
  dd_cbn. opcode_class.
Qed.

Lemma dd_guard_opcode :
  dd_locality_violation b w || dd_ptable_overflow_violation b w ||
  dd_nfi_violation b w = true -> In (dd_opcode b w) guard_opcodes.
Proof.
  intro H. unfold guard_opcodes.
  destruct (dd_locality_violation b w) eqn:Hl.
  - pose proof (dd_locality_opcode Hl) as Hi. unfold locality_opcodes in Hi.
    cbn [In] in Hi |- *. tauto.
  - destruct (dd_ptable_overflow_violation b w) eqn:Hp.
    + pose proof (dd_ptable_opcode Hp) as Hi. unfold partition_opcodes in Hi.
      cbn [In] in Hi |- *. tauto.
    + cbn [orb] in H. rewrite (dd_nfi_opcode H). cbn [In]. tauto.
Qed.

Lemma dd_morph_not_guard :
  dd_morph_runtime_fault b w = true ->
  dd_locality_violation b w || dd_ptable_overflow_violation b w ||
  dd_nfi_violation b w = false.
Proof.
  intro Hm. destruct (_ || _ || _) eqn:Hg; [|reflexivity]. exfalso.
  exact (op_disjoint _ _ _ (dd_morph_opcode Hm) (dd_guard_opcode Hg) eq_refl).
Qed.

Lemma dd_locality_not_ptable :
  dd_locality_violation b w = true -> dd_ptable_overflow_violation b w = false.
Proof.
  intro Hl. destruct (dd_ptable_overflow_violation b w) eqn:Hp; [|reflexivity]. exfalso.
  exact (op_disjoint _ _ _ (dd_locality_opcode Hl) (dd_ptable_opcode Hp) eq_refl).
Qed.

Lemma dd_locality_not_nfi :
  dd_locality_violation b w = true -> dd_nfi_violation b w = false.
Proof.
  intro Hl. destruct (dd_nfi_violation b w) eqn:Hn; [|reflexivity]. exfalso.
  apply (op_disjoint _ _ [OP_PDISCOVER] (dd_locality_opcode Hl)); [|reflexivity].
  rewrite (dd_nfi_opcode Hn). left. reflexivity.
Qed.

Lemma dd_ptable_not_nfi :
  dd_ptable_overflow_violation b w = true -> dd_nfi_violation b w = false.
Proof.
  intro Hp. destruct (dd_nfi_violation b w) eqn:Hn; [|reflexivity]. exfalso.
  apply (op_disjoint _ _ [OP_PDISCOVER] (dd_ptable_opcode Hp)); [|reflexivity].
  rewrite (dd_nfi_opcode Hn). left. reflexivity.
Qed.

Lemma dd_ptable_not_locality :
  dd_ptable_overflow_violation b w = true -> dd_locality_violation b w = false.
Proof.
  intro Hp. destruct (dd_locality_violation b w) eqn:Hl; [|reflexivity].
  rewrite (dd_locality_not_ptable Hl) in Hp. discriminate Hp.
Qed.

Lemma dd_nfi_not_locality :
  dd_nfi_violation b w = true -> dd_locality_violation b w = false.
Proof.
  intro Hn. destruct (dd_locality_violation b w) eqn:Hl; [|reflexivity].
  rewrite (dd_locality_not_nfi Hl) in Hn. discriminate Hn.
Qed.

Lemma dd_nfi_not_ptable :
  dd_nfi_violation b w = true -> dd_ptable_overflow_violation b w = false.
Proof.
  intro Hn. destruct (dd_ptable_overflow_violation b w) eqn:Hp; [|reflexivity].
  rewrite (dd_ptable_not_nfi Hp) in Hn. discriminate Hn.
Qed.

Lemma dd_guard_not_morph :
  dd_locality_violation b w || dd_ptable_overflow_violation b w ||
  dd_nfi_violation b w = true -> dd_morph_runtime_fault b w = false.
Proof.
  intro Hg. destruct (dd_morph_runtime_fault b w) eqn:Hm; [|reflexivity].
  rewrite (dd_morph_not_guard Hm) in Hg. discriminate Hg.
Qed.

Lemma dd_trap_false : dd_trap = false ->
  hwb_bianchi b = false /\ dd_locality_violation b w = false /\
  dd_ptable_overflow_violation b w = false /\ dd_nfi_violation b w = false /\
  dd_rich_fault b w = false.
Proof.
  unfold dd_trap. destruct (hwb_bianchi b), (dd_locality_violation b w),
    (dd_ptable_overflow_violation b w), (dd_nfi_violation b w), (dd_rich_fault b w);
    cbn [orb]; intro H; try discriminate H; auto.
Qed.

End Guards.

(** * Registers every trap or morph fault leaves unchanged *)

Section Frames.
Variables (b : HWB) (w : word InstrSz).

Ltac freeze_rewrite H :=
  unfold dd_freeze, dd_trap in H; dd_cbn; rewrite H; reflexivity.

Lemma dd_pc_trap : dd_trap b w = true -> dd_new_pc b w = hw_trap_vector b.
Proof. intro H. unfold dd_trap in H. unfold dd_new_pc. dd_cbn. rewrite H. reflexivity. Qed.

Lemma dd_regs_freeze : dd_freeze b w = true -> dd_new_regs b w = hw_regs b.
Proof. intro H. unfold dd_new_regs. freeze_rewrite H. Qed.
Lemma dd_mem_freeze : dd_freeze b w = true -> dd_new_mem b w = hw_mem b.
Proof. intro H. unfold dd_new_mem. freeze_rewrite H. Qed.
Lemma dd_certified_freeze : dd_freeze b w = true -> dd_new_certified b w = hw_certified b.
Proof. intro H. unfold dd_new_certified. freeze_rewrite H. Qed.
Lemma dd_cert_addr_freeze : dd_freeze b w = true -> dd_new_cert_addr b w = hw_cert_addr b.
Proof. intro H. unfold dd_new_cert_addr. freeze_rewrite H. Qed.
Lemma dd_morph_src_freeze : dd_freeze b w = true ->
  dd_new_morph_src_table b w = hw_morph_src_table b.
Proof. intro H. unfold dd_new_morph_src_table. freeze_rewrite H. Qed.
Lemma dd_morph_dst_freeze : dd_freeze b w = true ->
  dd_new_morph_dst_table b w = hw_morph_dst_table b.
Proof. intro H. unfold dd_new_morph_dst_table. freeze_rewrite H. Qed.
Lemma dd_morph_coupling_desc_freeze : dd_freeze b w = true ->
  dd_new_morph_coupling_desc_table b w = hw_morph_coupling_desc_table b.
Proof. intro H. unfold dd_new_morph_coupling_desc_table. freeze_rewrite H. Qed.
Lemma dd_morph_identity_freeze : dd_freeze b w = true ->
  dd_new_morph_identity_table b w = hw_morph_identity_table b.
Proof. intro H. unfold dd_new_morph_identity_table. freeze_rewrite H. Qed.
Lemma dd_morph_valid_freeze : dd_freeze b w = true ->
  dd_new_morph_valid_table b w = hw_morph_valid_table b.
Proof. intro H. unfold dd_new_morph_valid_table. freeze_rewrite H. Qed.
Lemma dd_morph_next_id_freeze : dd_freeze b w = true ->
  dd_new_morph_next_id b w = hw_morph_next_id b.
Proof. intro H. unfold dd_new_morph_next_id. freeze_rewrite H. Qed.

Lemma dd_info_gain_freeze : dd_freeze b w = true -> dd_new_info_gain b w = hw_info_gain b.
Proof.
  unfold dd_freeze, dd_trap, dd_new_info_gain. dd_cbn.
  destruct (dd_is_info_gain_op b w), (hwb_bianchi b), (dd_locality_violation b w),
    (dd_ptable_overflow_violation b w), (dd_nfi_violation b w), (dd_rich_fault b w),
    (dd_morph_runtime_fault b w); bool_red; intro H; try discriminate H; reflexivity.
Qed.

Lemma dd_module_tensors_freeze : dd_freeze b w = true ->
  dd_new_module_tensors b w = hw_module_tensors b.
Proof.
  intro H. unfold dd_freeze, dd_trap in H. unfold dd_new_module_tensors. dd_cbn.
  rewrite H. destruct (weq (dd_opcode b w) OP_TENSOR_SET); bool_red; reflexivity.
Qed.

Lemma dd_assertion_dispatch_freeze : dd_freeze b w = true ->
  dd_assertion_dispatch_allowed b w = false.
Proof.
  intro H. unfold dd_freeze, dd_trap in H. unfold dd_assertion_dispatch_allowed. dd_cbn.
  rewrite H. reflexivity.
Qed.

Lemma dd_is_chsh_valid_trap : dd_trap b w = true -> dd_is_chsh_valid b w = false.
Proof.
  unfold dd_trap, dd_is_chsh_valid. dd_cbn.
  destruct (weq (dd_opcode b w) OP_CHSH_TRIAL), (hwb_bianchi b), (dd_locality_violation b w),
    (dd_ptable_overflow_violation b w), (dd_nfi_violation b w), (dd_rich_fault b w);
    bool_red; intro H; try discriminate H; reflexivity.
Qed.

Lemma dd_is_chsh_valid_morph : dd_morph_runtime_fault b w = true -> dd_is_chsh_valid b w = false.
Proof.
  intro Hm. pose proof (dd_morph_opcode b w Hm) as Hin.
  unfold dd_is_chsh_valid. dd_cbn. op_off Hin. reflexivity.
Qed.

Lemma dd_mu_tensor_trap : dd_trap b w = true -> dd_new_mu_tensor b w = hw_mu_tensor b.
Proof.
  unfold dd_trap, dd_new_mu_tensor. dd_cbn.
  destruct (dd_locality_violation b w || dd_ptable_overflow_violation b w ||
    dd_nfi_violation b w) eqn:Hg.
  - intros _. pose proof (dd_guard_opcode b w Hg) as Hin. op_off Hin. reflexivity.
  - revert Hg. destruct (weq (dd_opcode b w) OP_REVEAL), (hwb_bianchi b),
      (dd_locality_violation b w), (dd_ptable_overflow_violation b w),
      (dd_nfi_violation b w), (dd_rich_fault b w), (dd_morph_runtime_fault b w);
      bool_red; intros Hg H; try discriminate H; try discriminate Hg; reflexivity.
Qed.

Lemma dd_mu_tensor_morph : dd_morph_runtime_fault b w = true ->
  dd_new_mu_tensor b w = hw_mu_tensor b.
Proof.
  intro Hm. unfold dd_new_mu_tensor. dd_cbn. rewrite Hm.
  destruct (weq (dd_opcode b w) OP_REVEAL), (hwb_bianchi b), (dd_rich_fault b w);
    bool_red; reflexivity.
Qed.

Lemma dd_mdl_ops_trap : dd_trap b w = true -> dd_new_mdl_ops b w = hw_mdl_ops b.
Proof.
  unfold dd_trap, dd_new_mdl_ops. dd_cbn.
  destruct (dd_locality_violation b w || dd_ptable_overflow_violation b w ||
    dd_nfi_violation b w) eqn:Hg.
  - intros _. pose proof (dd_guard_opcode b w Hg) as Hin. op_off Hin. reflexivity.
  - revert Hg. destruct (weq (dd_opcode b w) OP_MDLACC), (hwb_bianchi b),
      (dd_locality_violation b w), (dd_ptable_overflow_violation b w),
      (dd_nfi_violation b w), (dd_rich_fault b w), (dd_morph_runtime_fault b w);
      bool_red; intros Hg H; try discriminate H; try discriminate Hg; reflexivity.
Qed.

Lemma dd_mdl_ops_morph : dd_morph_runtime_fault b w = true -> dd_new_mdl_ops b w = hw_mdl_ops b.
Proof.
  intro Hm. unfold dd_new_mdl_ops. dd_cbn. rewrite Hm.
  destruct (weq (dd_opcode b w) OP_MDLACC), (hwb_bianchi b), (dd_rich_fault b w);
    bool_red; reflexivity.
Qed.

Lemma dd_partition_ops_morph : dd_morph_runtime_fault b w = true ->
  dd_new_partition_ops b w = hw_partition_ops b.
Proof.
  intro Hm. unfold dd_new_partition_ops. dd_cbn. rewrite Hm.
  destruct (dd_is_partition_op b w), (hwb_bianchi b), (dd_rich_fault b w);
    bool_red; reflexivity.
Qed.

Lemma dd_pt_tables_trap : dd_trap b w = true ->
  dd_new_pt_sizes b w = hw_ptTable b /\ dd_new_pt_next_id b w = hw_pt_next_id b.
Proof.
  unfold dd_trap, dd_new_pt_sizes, dd_new_pt_next_id. dd_cbn.
  destruct (dd_locality_violation b w) eqn:Hl.
  - intros _. pose proof (dd_locality_opcode b w Hl) as Hin. op_off Hin.
    bool_red. split; same_branches.
  - destruct (dd_nfi_violation b w) eqn:Hn.
    + intros _. assert (Hin : In (dd_opcode b w) [OP_PDISCOVER])
        by (rewrite (dd_nfi_opcode b w Hn); left; reflexivity).
      op_off Hin. bool_red. split; same_branches.
    + destruct (hwb_bianchi b), (dd_ptable_overflow_violation b w), (dd_rich_fault b w);
        bool_red; intro H; try discriminate H; split; reflexivity.
Qed.

Lemma dd_pt_tables_morph : dd_morph_runtime_fault b w = true ->
  dd_new_pt_sizes b w = hw_ptTable b /\ dd_new_pt_next_id b w = hw_pt_next_id b.
Proof.
  intro Hm. unfold dd_new_pt_sizes, dd_new_pt_next_id. dd_cbn. rewrite Hm.
  destruct (hwb_bianchi b), (dd_ptable_overflow_violation b w), (dd_rich_fault b w);
    bool_red; split; reflexivity.
Qed.

End Frames.

(** * Values of the committed registers under each guard *)

Section Values.
Variables (b : HWB) (w : word InstrSz).

Lemma dd_err_eq : dd_new_err b w =
  dd_locality_violation b w || dd_ptable_overflow_violation b w || dd_nfi_violation b w ||
  dd_rich_fault b w || dd_morph_runtime_fault b w ||
  (dd_is_lassert b w && negb (dd_lassert_is_sat b w)).
Proof.
  unfold dd_new_err, dd_lassert_unsat_trap, dd_chsh_lassert_trap. dd_cbn.
  apply Bool.orb_false_r.
Qed.

Lemma dd_halted_eq : dd_new_halted b w =
  dd_locality_violation b w || dd_ptable_overflow_violation b w || dd_nfi_violation b w ||
  op_test (dd_opcode b w) OP_HALT.
Proof. unfold dd_new_halted. dd_cbn. reflexivity. Qed.

(** ** Bianchi *)

Hypothesis Hb : hwb_bianchi b = true.

Lemma dd_mu_bianchi : dd_final_mu b w = hw_mu b.
Proof. unfold dd_final_mu. dd_cbn. rewrite Hb. reflexivity. Qed.

Lemma dd_error_code_bianchi : dd_new_error_code b w = ERR_BIANCHI_VAL.
Proof. unfold dd_new_error_code. dd_cbn. rewrite Hb. reflexivity. Qed.

Lemma dd_partition_ops_bianchi : dd_new_partition_ops b w = hw_partition_ops b.
Proof.
  unfold dd_new_partition_ops. dd_cbn. rewrite Hb.
  destruct (dd_is_partition_op b w); bool_red; reflexivity.
Qed.

End Values.

Section GuardValues.
Variables (b : HWB) (w : word InstrSz).

(** ** Locality *)

Lemma dd_mu_locality : hwb_bianchi b = false -> dd_locality_violation b w = true ->
  dd_final_mu b w = dd_new_mu b w.
Proof.
  intros Hb Hl. pose proof (dd_locality_opcode b w Hl) as Hin.
  unfold dd_final_mu, dd_rich_fault_mu, dd_normal_step_mu. dd_cbn.
  rewrite Hb, (dd_locality_not_ptable b w Hl), (dd_locality_not_nfi b w Hl).
  op_off Hin. bool_red. same_branches.
Qed.

Lemma dd_error_code_locality : hwb_bianchi b = false -> dd_locality_violation b w = true ->
  dd_new_error_code b w = ERR_LOCALITY_VAL.
Proof. intros Hb Hl. unfold dd_new_error_code. dd_cbn. rewrite Hb, Hl. reflexivity. Qed.

Lemma dd_partition_ops_locality : dd_locality_violation b w = true ->
  dd_new_partition_ops b w = hw_partition_ops b.
Proof.
  intro Hl. pose proof (dd_locality_opcode b w Hl) as Hin.
  unfold dd_new_partition_ops, dd_is_partition_op. dd_cbn. op_off Hin. bool_red. reflexivity.
Qed.

(** ** Partition-table overflow *)

Lemma dd_mu_ptable : hwb_bianchi b = false -> dd_ptable_overflow_violation b w = true ->
  dd_final_mu b w = hw_mu b.
Proof. intros Hb Hp. unfold dd_final_mu. dd_cbn. rewrite Hb, Hp. reflexivity. Qed.

Lemma dd_error_code_ptable : hwb_bianchi b = false -> dd_ptable_overflow_violation b w = true ->
  dd_new_error_code b w = ERR_PARTITION_VAL.
Proof.
  intros Hb Hp. unfold dd_new_error_code. dd_cbn.
  rewrite Hb, (dd_ptable_not_locality b w Hp), Hp. reflexivity.
Qed.

Lemma dd_partition_ops_ptable : hwb_bianchi b = false -> dd_ptable_overflow_violation b w = true ->
  dd_new_partition_ops b w =
  if dd_rich_fault b w then hw_partition_ops b
  else wplus (hw_partition_ops b) (natToWord WordSz 1).
Proof.
  intros Hb Hp. pose proof (dd_ptable_opcode b w Hp) as Hin.
  assert (Hm : dd_morph_runtime_fault b w = false).
  { apply (dd_guard_not_morph b w). rewrite Hp, Bool.orb_true_r. reflexivity. }
  unfold dd_new_partition_ops, dd_is_partition_op. dd_cbn. rewrite Hb, Hm.
  unfold partition_opcodes in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|F]]]; try destruct F; rewrite <- E; close_weq; bool_red;
    destruct (dd_rich_fault b w); reflexivity.
Qed.

(** ** No-Free-Insight *)

Lemma dd_mu_nfi : hwb_bianchi b = false -> dd_nfi_violation b w = true ->
  dd_final_mu b w = hw_mu b.
Proof.
  intros Hb Hn. unfold dd_final_mu. dd_cbn.
  rewrite Hb, (dd_nfi_not_ptable b w Hn), Hn. reflexivity.
Qed.

Lemma dd_error_code_nfi : hwb_bianchi b = false -> dd_nfi_violation b w = true ->
  dd_new_error_code b w = ERR_LOGIC_VAL.
Proof.
  intros Hb Hn. unfold dd_new_error_code. dd_cbn.
  rewrite Hb, (dd_nfi_not_locality b w Hn), (dd_nfi_not_ptable b w Hn), Hn. reflexivity.
Qed.

Lemma dd_partition_ops_nfi : dd_nfi_violation b w = true ->
  dd_new_partition_ops b w = hw_partition_ops b.
Proof.
  intro Hn. assert (Hin : In (dd_opcode b w) [OP_PDISCOVER])
    by (rewrite (dd_nfi_opcode b w Hn); left; reflexivity).
  unfold dd_new_partition_ops, dd_is_partition_op. dd_cbn. op_off Hin. bool_red. reflexivity.
Qed.

Lemma dd_err_guard : dd_locality_violation b w || dd_ptable_overflow_violation b w ||
  dd_nfi_violation b w = true -> dd_new_err b w = true /\ dd_new_halted b w = true.
Proof.
  rewrite dd_err_eq, dd_halted_eq. intro H. rewrite H. split; reflexivity.
Qed.

(** ** Rich-format faults *)

Section Rich.
Hypotheses (Hb : hwb_bianchi b = false) (Hl : dd_locality_violation b w = false)
  (Hp : dd_ptable_overflow_violation b w = false) (Hn : dd_nfi_violation b w = false)
  (Hr : dd_rich_fault b w = true).

Lemma dd_mu_rich : dd_final_mu b w = dd_rich_fault_mu b w.
Proof. unfold dd_final_mu. dd_cbn. rewrite Hb, Hp, Hn, Hr. reflexivity. Qed.

Lemma dd_error_code_rich : dd_new_error_code b w = dd_rich_fault_error_code b w.
Proof. unfold dd_new_error_code. dd_cbn. rewrite Hb, Hl, Hp, Hn, Hr. reflexivity. Qed.

Lemma dd_err_halted_rich :
  dd_new_err b w = true /\ dd_new_halted b w = op_test (dd_opcode b w) OP_HALT.
Proof. rewrite dd_err_eq, dd_halted_eq, Hl, Hp, Hn, Hr. split; reflexivity. Qed.

Lemma dd_partition_ops_rich : dd_new_partition_ops b w = hw_partition_ops b.
Proof.
  unfold dd_new_partition_ops. dd_cbn. rewrite Hb, Hr.
  destruct (dd_is_partition_op b w), (dd_morph_runtime_fault b w); bool_red; reflexivity.
Qed.
End Rich.

(** ** Morph runtime faults *)

Section Morph.
Hypotheses (Ht : dd_trap b w = false) (Hm : dd_morph_runtime_fault b w = true).

Lemma dd_pc_morph : dd_new_pc b w = dd_pc_plus_1 b w.
Proof.
  destruct (dd_trap_false b w Ht) as (Hb & Hl & Hp & Hn & Hr).
  pose proof (dd_morph_opcode b w Hm) as Hin.
  unfold dd_new_pc, dd_chsh_lassert_trap. dd_cbn. rewrite Hb, Hl, Hp, Hn, Hr.
  op_off Hin. bool_red. reflexivity.
Qed.

Lemma dd_mu_morph : dd_final_mu b w = dd_normal_step_mu b w.
Proof.
  destruct (dd_trap_false b w Ht) as (Hb & Hl & Hp & Hn & Hr).
  unfold dd_final_mu. dd_cbn. rewrite Hb, Hp, Hn, Hr. reflexivity.
Qed.

Lemma dd_error_code_morph : dd_new_error_code b w = dd_morph_runtime_error_code b w.
Proof.
  destruct (dd_trap_false b w Ht) as (Hb & Hl & Hp & Hn & Hr).
  unfold dd_new_error_code. dd_cbn. rewrite Hb, Hl, Hp, Hn, Hr, Hm. reflexivity.
Qed.

Lemma dd_err_halted_morph : dd_new_err b w = true /\ dd_new_halted b w = false.
Proof.
  destruct (dd_trap_false b w Ht) as (Hb & Hl & Hp & Hn & Hr).
  pose proof (dd_morph_opcode b w Hm) as Hin.
  rewrite dd_err_eq, dd_halted_eq, Hl, Hp, Hn, Hr, Hm. split; [reflexivity|].
  unfold op_test. op_off Hin. reflexivity.
Qed.
End Morph.

End GuardValues.

(** * The label write of a trapped allocation is unobservable *)

Lemma step_label_frame : forall b, hwb_coupling_desc_valid_below_next b ->
  forall i, hw_coupling_desc_valid_table b i = true ->
  hw_coupling_desc_label_table (step_next b) i = hw_coupling_desc_label_table b i /\
  hw_coupling_desc_label_len_table (step_next b) i = hw_coupling_desc_label_len_table b i.
Proof.
  intros b Hd i Hv.
  rewrite step_next_coupling_desc_label_table, step_next_coupling_desc_label_len_table.
  dd_cbn. set (w := step_fetched b).
  destruct (dd_mc_enters_fsm b w) eqn:He; [|split; reflexivity].
  assert (Hroom : dd_coupling_alloc_room b w = true).
  { revert He. unfold dd_mc_enters_fsm, dd_morph_alloc_success, dd_compose_success,
      dd_legacy_compose_success. dd_cbn.
    destruct (dd_coupling_alloc_room b w); [reflexivity|].
    rewrite !Bool.andb_false_r. cbn [andb orb]. intro E. discriminate E. }
  assert (Hlt : wordToNat (hw_coupling_desc_next_id b) < 16).
  { revert Hroom. unfold dd_coupling_alloc_room. dd_cbn. cbn [evalBinBitBool].
    destruct (wlt_dec (hw_coupling_desc_next_id b) _) as [L|L]; [|discriminate].
    intros _. apply wlt_lt in L. exact L. }
  assert (Hidx : wordToNat (dd_morph_alloc_coupling b w) = wordToNat (hw_coupling_desc_next_id b)).
  { unfold dd_morph_alloc_coupling. dd_cbn. rewrite He. cbn [evalUniBit].
    exact (split1_4_1_small _ Hlt). }
  pose proof (Hd i Hv) as Hi.
  destruct (weq i (dd_morph_alloc_coupling b w)) as [E|E]; [|split; reflexivity].
  exfalso. subst i. unfold CouplingDescIdxSz, DescIdxSz, DescTableNextIdSz in *. lia.
Qed.

Lemma step_rich_freeze : forall b, hwb_coupling_desc_valid_below_next b ->
  dd_freeze b (step_fetched b) = true -> hwb_rich (step_next b) = hwb_rich b.
Proof.
  intros b Hd H. unfold hwb_rich.
  rewrite step_next_morph_valid_table, step_next_morph_src_table, step_next_morph_dst_table,
    step_next_morph_coupling_desc_table, step_next_morph_identity_table,
    step_next_morph_next_id, (dd_morph_valid_freeze _ _ H), (dd_morph_src_freeze _ _ H),
    (dd_morph_dst_freeze _ _ H), (dd_morph_coupling_desc_freeze _ _ H),
    (dd_morph_identity_freeze _ _ H), (dd_morph_next_id_freeze _ _ H).
  rewrite step_keeps_coupling_desc_valid_table, step_keeps_coupling_desc_base_table,
    step_keeps_coupling_desc_count_table, step_keeps_coupling_desc_next_id,
    step_keeps_coupling_pair_valid_table, step_keeps_coupling_pair_src_table,
    step_keeps_coupling_pair_dst_table, step_keeps_coupling_pair_next_id,
    step_keeps_formula_desc_valid_table, step_keeps_formula_desc_base_table,
    step_keeps_formula_desc_count_table, step_keeps_formula_desc_next_id,
    step_keeps_cert_desc_valid_table, step_keeps_cert_desc_base_table,
    step_keeps_cert_desc_count_table, step_keeps_cert_desc_next_id,
    step_keeps_desc_meta_valid_table, step_keeps_desc_meta_subtype_table,
    step_keeps_desc_meta_kind_table, step_keeps_desc_meta_inline_len_table,
    step_keeps_desc_meta_aux_table, step_keeps_desc_meta_next_id.
  f_equal. apply functional_extensionality. intro i. unfold hwb_valid, hwb_vector_nat.
  destruct (Nat.ltb i _); [|reflexivity].
  destruct (hw_coupling_desc_valid_table b _) eqn:Hv; [|reflexivity].
  destruct (step_label_frame b Hd _ Hv) as [L1 L2]. rewrite L1, L2. reflexivity.
Qed.

(** * Snapshot-level outcomes *)

(** The observation after a fault: the listed fields take the given values,
    CSR err follows err, and every other observed field is unchanged. *)
Definition snap_fault (s : KamiSnapshot) (pc mu : nat) (err halted : bool)
    (code partition_ops : nat) : KamiSnapshot :=
  {| snap_pc := pc; snap_mu := mu; snap_err := err; snap_halted := halted;
     snap_regs := snap_regs s; snap_mem := snap_mem s;
     snap_partition_ops := partition_ops; snap_mdl_ops := snap_mdl_ops s;
     snap_info_gain := snap_info_gain s; snap_error_code := code;
     snap_mu_tensor := snap_mu_tensor s; snap_pt_sizes := snap_pt_sizes s;
     snap_pt_next_id := snap_pt_next_id s; snap_certified := snap_certified s;
     snap_wc_same_00 := snap_wc_same_00 s; snap_wc_diff_00 := snap_wc_diff_00 s;
     snap_wc_same_01 := snap_wc_same_01 s; snap_wc_diff_01 := snap_wc_diff_01 s;
     snap_wc_same_10 := snap_wc_same_10 s; snap_wc_diff_10 := snap_wc_diff_10 s;
     snap_wc_same_11 := snap_wc_same_11 s; snap_wc_diff_11 := snap_wc_diff_11 s;
     snap_module_tensors := snap_module_tensors s; snap_rich_state := snap_rich_state s;
     snap_csr_cert_addr := snap_csr_cert_addr s; snap_csr_status := snap_csr_status s;
     snap_csr_err := if err then 1 else 0; snap_csr_heap_base := snap_csr_heap_base s;
     snap_logic_acc := snap_logic_acc s; snap_mstatus := snap_mstatus s |}.

Ltac fault_fields :=
  unfold hwb_snapshot, snap_fault;
  apply kami_snapshot_ext;
  cbn [snap_pc snap_mu snap_err snap_halted snap_regs snap_mem snap_partition_ops
    snap_mdl_ops snap_info_gain snap_error_code snap_mu_tensor snap_pt_sizes
    snap_pt_next_id snap_certified snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01
    snap_wc_diff_01 snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
    snap_module_tensors snap_rich_state snap_csr_cert_addr snap_csr_status snap_csr_err
    snap_csr_heap_base snap_logic_acc snap_mstatus];
  rewrite ?step_next_pc, ?step_next_mu, ?step_next_err, ?step_next_halted,
    ?step_next_regs, ?step_next_mem, ?step_next_partition_ops, ?step_next_mdl_ops,
    ?step_next_info_gain, ?step_next_error_code, ?step_next_mu_tensor,
    ?step_next_ptTable, ?step_next_pt_next_id, ?step_next_certified,
    ?step_next_wc_same_00, ?step_next_wc_diff_00, ?step_next_wc_same_01,
    ?step_next_wc_diff_01, ?step_next_wc_same_10, ?step_next_wc_diff_10,
    ?step_next_wc_same_11, ?step_next_wc_diff_11, ?step_next_module_tensors,
    ?step_next_cert_addr, ?step_keeps_csr_status, ?step_keeps_csr_heap_base,
    ?step_keeps_logic_acc, ?step_keeps_mstatus.

Ltac wc_frozen Hc :=
  match goal with
  | |- context [dd_new_wc_same_00 ?b ?w] => unfold dd_new_wc_same_00
  | |- context [dd_new_wc_diff_00 ?b ?w] => unfold dd_new_wc_diff_00
  | |- context [dd_new_wc_same_01 ?b ?w] => unfold dd_new_wc_same_01
  | |- context [dd_new_wc_diff_01 ?b ?w] => unfold dd_new_wc_diff_01
  | |- context [dd_new_wc_same_10 ?b ?w] => unfold dd_new_wc_same_10
  | |- context [dd_new_wc_diff_10 ?b ?w] => unfold dd_new_wc_diff_10
  | |- context [dd_new_wc_same_11 ?b ?w] => unfold dd_new_wc_same_11
  | |- context [dd_new_wc_diff_11 ?b ?w] => unfold dd_new_wc_diff_11
  end; dd_cbn; rewrite Hc; reflexivity.

(** Every trap-class guard: PC at the trap vector; data, tables, tensors,
    certification, witness counters and descriptors unchanged. mu, err,
    halted, error code and the partition counter are the committed values,
    evaluated per guard below. *)
Theorem step_trap_snapshot : forall b,
  hwb_coupling_desc_valid_below_next b ->
  dd_trap b (step_fetched b) = true ->
  hwb_snapshot (step_next b) =
  snap_fault (hwb_snapshot b) (wordToNat (hw_trap_vector b))
    (wordToNat (dd_final_mu b (step_fetched b))) (dd_new_err b (step_fetched b))
    (dd_new_halted b (step_fetched b))
    (wordToNat (dd_new_error_code b (step_fetched b)))
    (wordToNat (dd_new_partition_ops b (step_fetched b))).
Proof.
  intros b Hd H.
  assert (Hf : dd_freeze b (step_fetched b) = true)
    by (unfold dd_freeze; rewrite H; reflexivity).
  destruct (dd_pt_tables_trap _ _ H) as [Hpt Hptn].
  pose proof (dd_is_chsh_valid_trap _ _ H) as Hc.
  fault_fields;
  rewrite ?(dd_pc_trap _ _ H), ?(dd_regs_freeze _ _ Hf), ?(dd_mem_freeze _ _ Hf),
    ?(dd_certified_freeze _ _ Hf), ?(dd_cert_addr_freeze _ _ Hf),
    ?(dd_info_gain_freeze _ _ Hf), ?(dd_module_tensors_freeze _ _ Hf),
    ?(dd_mu_tensor_trap _ _ H), ?(dd_mdl_ops_trap _ _ H), ?Hpt, ?Hptn,
    ?(step_rich_freeze b Hd Hf);
  first [reflexivity | wc_frozen Hc].
Qed.

(** A trap-class guard leaves every assertion and coupling FSM idle. *)
Theorem step_freeze_phases : forall b,
  dd_freeze b (step_fetched b) = true ->
  hw_lassert_phase (step_next b) = natToWord 3 0 /\
  hw_chsh_phase (step_next b) = natToWord 5 0 /\
  hw_mc_phase (step_next b) = natToWord 4 0.
Proof.
  intros b H. pose proof (dd_assertion_dispatch_freeze _ _ H) as Ha.
  rewrite step_next_lassert_phase, step_next_chsh_phase, step_next_mc_phase.
  unfold dd_freeze, dd_trap in H. dd_cbn. rewrite Ha, H.
  destruct (dd_is_lassert b (step_fetched b)), (dd_lassert_is_sat b (step_fetched b)),
    (dd_is_chsh_lassert b (step_fetched b)); bool_red; repeat split; reflexivity.
Qed.

Section Corollaries.
Variable b : HWB.
Hypothesis Hd : hwb_coupling_desc_valid_below_next b.
Local Notation w := (step_fetched b).

(** Bianchi: trap PC, ERR_BIANCHI_VAL, mu and partition counter unchanged.
    err and halted stay the committed disjunctions of the other guards
    ([dd_err_eq], [dd_halted_eq]); Bianchi alone latches neither. *)
Theorem step_bianchi_snapshot : hwb_bianchi b = true ->
  hwb_snapshot (step_next b) =
  snap_fault (hwb_snapshot b) (wordToNat (hw_trap_vector b)) (wordToNat (hw_mu b))
    (dd_new_err b w) (dd_new_halted b w) (wordToNat ERR_BIANCHI_VAL)
    (wordToNat (hw_partition_ops b)).
Proof.
  intro Hb. rewrite step_trap_snapshot by (exact Hd || (unfold dd_trap; rewrite Hb; reflexivity)).
  rewrite dd_mu_bianchi, dd_error_code_bianchi, dd_partition_ops_bianchi by exact Hb.
  reflexivity.
Qed.

Theorem step_locality_snapshot :
  hwb_bianchi b = false -> dd_locality_violation b w = true ->
  hwb_snapshot (step_next b) =
  snap_fault (hwb_snapshot b) (wordToNat (hw_trap_vector b))
    (wordToNat (wplus (hw_mu b) (dd_cost32 b w))) true true
    (wordToNat ERR_LOCALITY_VAL) (wordToNat (hw_partition_ops b)).
Proof.
  intros Hb Hl. rewrite step_trap_snapshot
    by (exact Hd || (unfold dd_trap; rewrite Hl, Bool.orb_true_r; reflexivity)).
  destruct (dd_err_guard b w) as [He Hh]; [rewrite Hl; reflexivity|].
  rewrite He, Hh, (dd_mu_locality b w Hb Hl), (dd_error_code_locality b w Hb Hl),
    (dd_partition_ops_locality b w Hl).
  reflexivity.
Qed.

Theorem step_ptable_snapshot :
  hwb_bianchi b = false -> dd_ptable_overflow_violation b w = true ->
  hwb_snapshot (step_next b) =
  snap_fault (hwb_snapshot b) (wordToNat (hw_trap_vector b)) (wordToNat (hw_mu b)) true true
    (wordToNat ERR_PARTITION_VAL)
    (wordToNat (if dd_rich_fault b w then hw_partition_ops b
                else wplus (hw_partition_ops b) (natToWord WordSz 1))).
Proof.
  intros Hb Hp. rewrite step_trap_snapshot
    by (exact Hd || (unfold dd_trap; rewrite Hp, !Bool.orb_true_r; reflexivity)).
  destruct (dd_err_guard b w) as [He Hh]; [rewrite Hp, Bool.orb_true_r; reflexivity|].
  rewrite He, Hh, (dd_mu_ptable b w Hb Hp), (dd_error_code_ptable b w Hb Hp),
    (dd_partition_ops_ptable b w Hb Hp).
  reflexivity.
Qed.

Theorem step_nfi_snapshot :
  hwb_bianchi b = false -> dd_nfi_violation b w = true ->
  hwb_snapshot (step_next b) =
  snap_fault (hwb_snapshot b) (wordToNat (hw_trap_vector b)) (wordToNat (hw_mu b)) true true
    (wordToNat ERR_LOGIC_VAL) (wordToNat (hw_partition_ops b)).
Proof.
  intros Hb Hn. rewrite step_trap_snapshot
    by (exact Hd || (unfold dd_trap; rewrite Hn, !Bool.orb_true_r; reflexivity)).
  destruct (dd_err_guard b w) as [He Hh]; [rewrite Hn, Bool.orb_true_r; reflexivity|].
  rewrite He, Hh, (dd_mu_nfi b w Hb Hn), (dd_error_code_nfi b w Hb Hn),
    (dd_partition_ops_nfi b w Hn).
  reflexivity.
Qed.

(** Rich-format fault with no higher-priority guard: err latched, halted
    only for a HALT opcode, the format charge and the rich error code. *)
Theorem step_rich_snapshot :
  hwb_bianchi b = false -> dd_locality_violation b w = false ->
  dd_ptable_overflow_violation b w = false -> dd_nfi_violation b w = false ->
  dd_rich_fault b w = true ->
  hwb_snapshot (step_next b) =
  snap_fault (hwb_snapshot b) (wordToNat (hw_trap_vector b))
    (wordToNat (dd_rich_fault_mu b w)) true (op_test (dd_opcode b w) OP_HALT)
    (wordToNat (dd_rich_fault_error_code b w)) (wordToNat (hw_partition_ops b)).
Proof.
  intros Hb Hl Hp Hn Hr. rewrite step_trap_snapshot
    by (exact Hd || (unfold dd_trap; rewrite Hr, !Bool.orb_true_r; reflexivity)).
  destruct (dd_err_halted_rich b w Hl Hp Hn Hr) as [He Hh].
  rewrite He, Hh, (dd_mu_rich b w Hb Hp Hn Hr), (dd_error_code_rich b w Hb Hl Hp Hn Hr),
    (dd_partition_ops_rich b w Hb Hr).
  reflexivity.
Qed.

(** Morph runtime fault with no trap-class guard: PC advances by one, err
    latched, not halted, the ordinary charge, the morph error code, and every
    other observed field unchanged. *)
Theorem step_morph_fault_snapshot :
  dd_trap b w = false -> dd_morph_runtime_fault b w = true ->
  hwb_snapshot (step_next b) =
  snap_fault (hwb_snapshot b) (wordToNat (wplus (hw_pc b) (natToWord WordSz 1)))
    (wordToNat (dd_normal_step_mu b w)) true false
    (wordToNat (dd_morph_runtime_error_code b w)) (wordToNat (hw_partition_ops b)).
Proof.
  intros Ht Hm.
  assert (Hf : dd_freeze b w = true)
    by (unfold dd_freeze; rewrite Hm, Bool.orb_true_r; reflexivity).
  destruct (dd_pt_tables_morph b w Hm) as [Hpt Hptn].
  destruct (dd_err_halted_morph b w Ht Hm) as [He Hh].
  pose proof (dd_is_chsh_valid_morph b w Hm) as Hc.
  fault_fields;
  rewrite ?(dd_pc_morph b w Ht Hm), ?(dd_mu_morph b w Ht), ?He, ?Hh,
    ?(dd_error_code_morph b w Ht Hm), ?(dd_regs_freeze _ _ Hf), ?(dd_mem_freeze _ _ Hf),
    ?(dd_certified_freeze _ _ Hf), ?(dd_cert_addr_freeze _ _ Hf),
    ?(dd_info_gain_freeze _ _ Hf), ?(dd_module_tensors_freeze _ _ Hf),
    ?(dd_mu_tensor_morph b w Hm), ?(dd_mdl_ops_morph b w Hm),
    ?(dd_partition_ops_morph b w Hm), ?Hpt, ?Hptn, ?(step_rich_freeze b Hd Hf);
  first [reflexivity | wc_frozen Hc].
Qed.

End Corollaries.
