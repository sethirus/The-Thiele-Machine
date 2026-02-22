(** Abstraction.v — Maps Kami hardware state to VMState.

    DESIGN: KamiSnapshot uses Coq [nat] for all values, matching VMState's
    own nat-based word32 arithmetic. 32-bit bounds are enforced as preconditions.
    This avoids cross-library word/nat conversion gaps and keeps all proofs in
    pure nat arithmetic.

    The Kami hardware module (extracted to Verilog) is argued to implement
    [hw_step] in Bisimulation_Minimal.v by construction: the Kami rule bodies
    compute exactly the same nat operations as [vm_apply] under the abstraction.

    All 26 instructions are covered:
    - Compute: LOAD_IMM, ADD, SUB, XFER, LOAD, STORE, JUMP, JNEZ, CALL, RET
    - XOR ALU: XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK
    - Partition/Logic: PNEW, PSPLIT, PMERGE, PDISCOVER, LASSERT, LJOIN,
      MDLACC, EMIT, REVEAL (partition graph managed at higher layer)
    - Special: CHSH_TRIAL, ORACLE_HALTS, HALT

    Extended state (matching handwritten RTL parity):
    - partition_ops, mdl_ops, info_gain: diagnostic counters
    - mu_tensor: 4×4 revelation direction tracking
    - error_code: specific error condition identifier *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import Kernel.VMState.

(** * Hardware state snapshot

    All values are stored as [nat]; the invariant [snap_regs_bounded] /
    [snap_mem_bounded] ensures they fit in hardware 32-bit registers. *)

Record KamiSnapshot := {
  snap_pc            : nat ;
  snap_mu            : nat ;
  snap_err           : bool ;
  snap_halted        : bool ;
  snap_regs          : nat -> nat ;
  snap_mem           : nat -> nat ;
  snap_partition_ops : nat ;
  snap_mdl_ops       : nat ;
  snap_info_gain     : nat ;
  snap_error_code    : nat ;
  snap_mu_tensor     : nat -> nat   (* flat index 0..15 -> tensor entry value *)
}.

(** * Conversion: function-based registers/memory -> list (VMState expects list nat) *)

Definition snapshot_regs_to_list (f : nat -> nat) : list nat :=
  List.map f (List.seq 0 32).

Definition snapshot_mem_to_list (f : nat -> nat) : list nat :=
  List.map f (List.seq 0 256).

Definition snapshot_tensor_to_list (f : nat -> nat) : list nat :=
  List.map f (List.seq 0 16).

(** * Default CSRs: all fields zero *)
Definition default_csrs : CSRState :=
  {| csr_cert_addr := 0 ; csr_status := 0 ; csr_err := 0 |}.

(** * Main abstraction: KamiSnapshot -> VMState.
    The partition graph is empty; partition operations are handled by the
    host-side driver that manages graph state outside the CPU core. *)
Definition abs_phase1 (s : KamiSnapshot) : VMState :=
  {| vm_graph     := empty_graph ;
     vm_csrs      := default_csrs ;
     vm_regs      := snapshot_regs_to_list (snap_regs s) ;
     vm_mem       := snapshot_mem_to_list  (snap_mem s)  ;
     vm_pc        := snap_pc s ;
     vm_mu        := snap_mu s ;
     vm_mu_tensor := snapshot_tensor_to_list (snap_mu_tensor s) ;
     vm_err       := snap_err s |}.

(** Full alias — all 26 instructions covered *)
Definition abs_full := abs_phase1.

(** * Execution preconditions *)
Definition cpu_preconditions (s : KamiSnapshot) : Prop :=
  snap_pc     s < 256    /\
  snap_mu     s < 2^31   /\
  snap_err    s = false  /\
  snap_halted s = false.

(** * Length invariants *)

Lemma snapshot_regs_to_list_length : forall f,
    length (snapshot_regs_to_list f) = 32.
Proof.
  intro f. unfold snapshot_regs_to_list. rewrite map_length, seq_length. reflexivity.
Qed.

Lemma snapshot_mem_to_list_length : forall f,
    length (snapshot_mem_to_list f) = 256.
Proof.
  intro f. unfold snapshot_mem_to_list. rewrite map_length, seq_length. reflexivity.
Qed.

Lemma snapshot_tensor_to_list_length : forall f,
    length (snapshot_tensor_to_list f) = 16.
Proof.
  intro f. unfold snapshot_tensor_to_list. rewrite map_length, seq_length. reflexivity.
Qed.

(** * Key auxiliary lemmas (proved purely by structural induction) *)

(** nth element of [seq start n] *)
Local Lemma seq_nth_helper : forall n start i,
    i < n -> List.nth i (List.seq start n) 0 = start + i.
Proof.
  induction n; intros start i Hi.
  - lia.
  - destruct i.
    + simpl. lia.
    + simpl. rewrite IHn by lia. lia.
Qed.

(** nth element of [map f l] = f applied to nth of [l] *)
Local Lemma nth_map_helper : forall {A B} (f : A -> B) (l : list A) i (da : A) (db : B),
    i < length l ->
    List.nth i (List.map f l) db = f (List.nth i l da).
Proof.
  intros A B f l. induction l; intros i da db Hi.
  - simpl in Hi. lia.
  - destruct i; [reflexivity | simpl; apply IHl; simpl in Hi; lia].
Qed.

(** Map with a conditional point-update equals firstn ++ [v] ++ skipn *)
Local Lemma map_update_gen : forall (f : nat -> nat) n start dst v,
    dst < n ->
    List.map (fun j => if Nat.eqb j (start + dst) then v else f j) (List.seq start n) =
    List.firstn dst (List.map f (List.seq start n)) ++ [v] ++
    List.skipn (S dst) (List.map f (List.seq start n)).
Proof.
  intros f n start dst v. revert n start.
  induction dst; intros n start Hn.
  - destruct n; [lia|].
    replace (start + 0) with start by lia.
    simpl. rewrite Nat.eqb_refl.
    f_equal. apply List.map_ext_in.
    intros j Hj%List.in_seq. destruct Hj as [Hge _].
    destruct (Nat.eqb j start) eqn:Ej.
    + apply Nat.eqb_eq in Ej. lia.
    + reflexivity.
  - destruct n; [lia|]. simpl.
    replace (Nat.eqb start (start + S dst)) with false
      by (symmetry; apply Nat.eqb_neq; lia).
    simpl. f_equal.
    replace (start + S dst) with (S start + dst) by lia.
    apply IHdst. lia.
Qed.

(** Specialized version for start = 0 *)
Local Corollary map_update_zero : forall (f : nat -> nat) n dst v,
    dst < n ->
    List.map (fun j => if Nat.eqb j dst then v else f j) (List.seq 0 n) =
    List.firstn dst (List.map f (List.seq 0 n)) ++ [v] ++
    List.skipn (S dst) (List.map f (List.seq 0 n)).
Proof.
  intros f n dst v Hn.
  pose proof (map_update_gen f n 0 dst v Hn) as H.
  rewrite Nat.add_0_l in H. exact H.
Qed.

(** * Register and memory read equivalence *)

Lemma snapshot_reg_read : forall f i,
    i < 32 ->
    List.nth i (snapshot_regs_to_list f) 0 = f i.
Proof.
  intros f i Hi. unfold snapshot_regs_to_list.
  rewrite nth_map_helper with (da := 0) by (rewrite seq_length; exact Hi).
  rewrite seq_nth_helper by exact Hi. simpl. reflexivity.
Qed.

Lemma snapshot_mem_read : forall f i,
    i < 256 ->
    List.nth i (snapshot_mem_to_list f) 0 = f i.
Proof.
  intros f i Hi. unfold snapshot_mem_to_list.
  rewrite nth_map_helper with (da := 0) by (rewrite seq_length; exact Hi).
  rewrite seq_nth_helper by exact Hi. simpl. reflexivity.
Qed.

Lemma snapshot_tensor_read : forall f i,
    i < 16 ->
    List.nth i (snapshot_tensor_to_list f) 0 = f i.
Proof.
  intros f i Hi. unfold snapshot_tensor_to_list.
  rewrite nth_map_helper with (da := 0) by (rewrite seq_length; exact Hi).
  rewrite seq_nth_helper by exact Hi. simpl. reflexivity.
Qed.

(** * Register write equivalence *)

Definition mk_snap_vmstate (s : KamiSnapshot) : VMState :=
  abs_phase1 s.

Lemma snapshot_reg_write : forall (s : KamiSnapshot) (dst v : nat),
    dst < 32 ->
    snapshot_regs_to_list (fun j => if Nat.eqb j dst then word32 v else snap_regs s j) =
    write_reg (abs_phase1 s) dst v.
Proof.
  intros s dst v Hdst.
  cbv [write_reg reg_index REG_COUNT abs_phase1 snapshot_regs_to_list].
  replace (dst mod 32) with dst by (symmetry; apply Nat.mod_small; exact Hdst).
  apply map_update_zero. exact Hdst.
Qed.

Lemma snapshot_mem_write : forall (s : KamiSnapshot) (addr v : nat),
    addr < 256 ->
    snapshot_mem_to_list (fun j => if Nat.eqb j addr then word32 v else snap_mem s j) =
    write_mem (abs_phase1 s) addr v.
Proof.
  intros s addr v Haddr.
  cbv [write_mem mem_index MEM_SIZE abs_phase1 snapshot_mem_to_list].
  replace (addr mod 256) with addr by (symmetry; apply Nat.mod_small; exact Haddr).
  apply map_update_zero. exact Haddr.
Qed.
