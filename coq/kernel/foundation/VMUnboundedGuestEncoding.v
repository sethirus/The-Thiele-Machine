(** VMUnboundedGuestEncoding.v — the bridge between get_slot/set_slot
    (which operate on one packed nat) and a guest's actual register file
    (list nat, matching how vm_apply/vm_apply_u represent vm_regs).

    Scope, stated plainly: each slot is 64 bits (Kn), matching the
    physical VM's own register width — this is not a regression relative
    to the bounded model. What B3 needs to be unbounded is the guest
    PROGRAM (arbitrarily many/long instructions), not necessarily
    individual guest register VALUES; a guest whose register values stay
    below 2^64 is correctly simulated exactly (no masking artifact), and
    that is the premise `encode_regs_correct` below is stated under. This
    is a deliberate, disclosed scope choice, not an oversight: widening or
    parameterizing the slot size is a separate, later refinement if a
    guest program that produces genuinely unbounded register values is
    ever the actual target. *)

From Coq Require Import Arith Lia List Bool.
From Coq Require Import NArith.NArith.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep VMUnboundedInterpreterSlots.

(** * 1. encode_regs: pack a guest register list into one nat, slot i
    holding the value at index i, starting from a chosen base slot. *)

Fixpoint encode_regs_aux (regs : list nat) (base : nat) : nat :=
  match regs with
  | [] => 0
  | r :: rest => set_slot (encode_regs_aux rest (S base)) base r
  end.

Definition encode_regs (regs : list nat) : nat := encode_regs_aux regs 0.

(** * 2. get_slot of the empty packing is always 0. *)

Lemma get_slot_zero : forall k, get_slot 0 k = 0.
Proof.
  intro k. rewrite get_slot_unfold. unfold u_shr, u_and.
  cbn [N.of_nat]. rewrite N.shiftr_0_l. reflexivity.
Qed.

(** * 3. Reading back slot i of encode_regs_aux: exactly nth (i - base)
    regs 0, masked to 64 bits, for i in [base, base+length regs); 0
    outside that range (matching an out-of-range register read's default
    via read_reg's own 0 default). *)

Lemma get_slot_encode_regs_aux : forall regs base i,
  get_slot (encode_regs_aux regs base) i =
    if andb (Nat.leb base i) (Nat.ltb i (base + length regs))
    then u_and (nth (i - base) regs 0) slot_mask
    else 0.
Proof.
  induction regs as [| r rest IH]; intros base i; cbn [encode_regs_aux length].
  - rewrite get_slot_zero.
    destruct (andb (Nat.leb base i) (Nat.ltb i (base + 0))) eqn:E; [| reflexivity].
    exfalso. apply andb_true_iff in E. destruct E as [E1 E2].
    apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. lia.
  - destruct (Nat.eq_dec i base) as [Heq | Hne].
    + subst i. rewrite get_slot_set_slot_same.
      rewrite Nat.leb_refl, Nat.sub_diag. cbn [nth].
      destruct (Nat.ltb base (base + S (length rest))) eqn:E2; [reflexivity |].
      apply Nat.ltb_ge in E2. lia.
    + rewrite (get_slot_set_slot_other _ _ _ _ (Nat.neq_sym _ _ Hne)).
      rewrite (IH (S base) i).
      destruct (andb (Nat.leb (S base) i) (Nat.ltb i (S base + length rest))) eqn:E1;
      destruct (andb (Nat.leb base i) (Nat.ltb i (base + S (length rest)))) eqn:E2.
      * (* both true: real content, indices line up after peeling one cons *)
        apply andb_true_iff in E1. destruct E1 as [E1a E1b]. apply Nat.leb_le in E1a.
        f_equal. replace (i - base) with (S (i - S base)) by lia. reflexivity.
      * (* E1 true, E2 false: impossible *)
        apply andb_true_iff in E1. destruct E1 as [E1a E1b].
        apply andb_false_iff in E2.
        apply Nat.leb_le in E1a. apply Nat.ltb_lt in E1b.
        exfalso. destruct E2 as [E2 | E2].
        -- apply Nat.leb_gt in E2. lia.
        -- apply Nat.ltb_ge in E2. lia.
      * (* E1 false, E2 true: impossible *)
        apply andb_true_iff in E2. destruct E2 as [E2a E2b].
        apply andb_false_iff in E1.
        apply Nat.leb_le in E2a. apply Nat.ltb_lt in E2b.
        exfalso. destruct E1 as [E1 | E1].
        -- apply Nat.leb_gt in E1. lia.
        -- apply Nat.ltb_ge in E1. lia.
      * (* both false *)
        reflexivity.
Qed.

(** * 4. u_and with slot_mask is the identity on values already at most
    slot_mask (i.e. already below 2^64) — proved via slot_mask_N_eq only,
    never by reducing slot_mask's actual value. *)

Lemma u_and_slot_mask_id : forall v, v <= slot_mask -> u_and v slot_mask = v.
Proof.
  intros v Hle. unfold u_and.
  rewrite slot_mask_N_eq, N.land_ones.
  assert (Hlt : (N.of_nat v < 2 ^ K)%N).
  { assert (H1 : (N.of_nat v <= N.of_nat slot_mask)%N) by lia.
    rewrite slot_mask_N_eq, N.ones_equiv in H1.
    assert (H2 : (0 < 2 ^ K)%N) by lia.
    lia. }
  rewrite N.mod_small by exact Hlt.
  apply Nat2N.id.
Qed.

(** * 4b. The write half: encode_regs of a list-updated register file
    equals set_slot applied to the original encoding. Needed so
    set_slot_program's output connects back to the guest's actual
    post-write register list, not just an isolated packed value. Built
    from set_slot_set_slot_same (same-slot overwrite) and set_slot_comm
    (different-slot writes commute), both already proved in
    VMUnboundedInterpreterSlots.v via the same bit-level technique. *)

Lemma encode_regs_aux_update : forall regs base i v,
  i < length regs ->
  encode_regs_aux (list_update_at regs i v) base =
    set_slot (encode_regs_aux regs base) (base + i) v.
Proof.
  induction regs as [| r rest IH]; intros base i v Hi.
  - cbn in Hi. lia.
  - destruct i as [| i'].
    + cbn [list_update_at encode_regs_aux].
      rewrite Nat.add_0_r, set_slot_set_slot_same. reflexivity.
    + cbn [list_update_at encode_regs_aux length] in *.
      assert (Hi' : i' < length rest) by lia.
      rewrite (IH (S base) i' v Hi').
      replace (base + S i') with (S base + i') by lia.
      rewrite (set_slot_comm (encode_regs_aux rest (S base)) base (S base + i') r v ltac:(lia)).
      reflexivity.
Qed.

Theorem encode_regs_update : forall regs i v,
  i < length regs ->
  encode_regs (list_update_at regs i v) = set_slot (encode_regs regs) i v.
Proof.
  intros regs i v Hi. unfold encode_regs.
  rewrite (encode_regs_aux_update regs 0 i v Hi). reflexivity.
Qed.

(** * 5. The clean corollary: for i within the register file and every
    value already below 2^64, encode_regs represents each register
    exactly — no masking artifact. This is the premise under which the
    ADD/SUB/etc. opcode blocks will state their simulation theorems. *)

Theorem encode_regs_correct : forall regs i,
  i < length regs ->
  Forall (fun v => v <= slot_mask) regs ->
  get_slot (encode_regs regs) i = nth i regs 0.
Proof.
  intros regs i Hi Hbound.
  unfold encode_regs.
  rewrite (get_slot_encode_regs_aux regs 0 i).
  cbn [Nat.leb Nat.sub].
  destruct (Nat.ltb i (0 + length regs)) eqn:E.
  - cbn [andb]. rewrite Nat.sub_0_r.
    apply u_and_slot_mask_id.
    eapply Forall_forall in Hbound; [exact Hbound | apply nth_In; exact Hi].
  - apply Nat.ltb_ge in E. lia.
Qed.

(** Actual register writes normalize the operand with reg_index. The
    in-range premise is necessary: list surgery can extend a short list,
    whereas list_update_at cannot. *)
Lemma list_update_at_splice : forall regs i v,
  i < length regs ->
  list_update_at regs i v = firstn i regs ++ [v] ++ skipn (S i) regs.
Proof.
  induction regs as [|r rest IH]; intros [|i] v Hi;
    cbn [length] in Hi; try lia.
  - reflexivity.
  - cbn [list_update_at firstn skipn app]. f_equal. apply IH. lia.
Qed.

Lemma write_reg_u_list_update_at : forall s r v,
  reg_index r < length (vm_regs s) ->
  write_reg_u s r v = list_update_at (vm_regs s) (reg_index r) v.
Proof.
  intros s r v Hr. unfold write_reg_u.
  symmetry. apply list_update_at_splice. exact Hr.
Qed.

Theorem encode_regs_write_reg_u : forall s r v,
  reg_index r < length (vm_regs s) ->
  encode_regs (write_reg_u s r v) =
    set_slot (encode_regs (vm_regs s)) (reg_index r) v.
Proof.
  intros s r v Hr. rewrite write_reg_u_list_update_at by exact Hr.
  apply encode_regs_update. exact Hr.
Qed.

(** This is the guest-side ADD encoding equation, not execution of a
    host interpreter block. For exact unbounded guest simulation the sum
    must also fit a slot; set_slot otherwise retains only its low bits. *)
Theorem encode_regs_vm_apply_u_add : forall s dst rs1 rs2 cost,
  reg_index dst < length (vm_regs s) ->
  encode_regs (vm_regs (vm_apply_u s (instr_add dst rs1 rs2 cost))) =
    set_slot (encode_regs (vm_regs s)) (reg_index dst)
      (u_add (read_reg s rs1) (read_reg s rs2)).
Proof.
  intros s dst rs1 rs2 cost Hd.
  cbn [vm_apply_u advance_state_rm vm_regs].
  apply encode_regs_write_reg_u. exact Hd.
Qed.
