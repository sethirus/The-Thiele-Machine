(** A random-access machine base for the cross-base comparison.

    The machine is the standard unit-cost RAM of Cook and Reckhow (1973) over
    natural numbers: unboundedly many registers [X 0, X 1, ...], constants,
    addition, truncated subtraction, indirect load and store, conditional and
    unconditional jumps, and halt. Input and output are the initial and final
    register contents. A program is a list of instructions; the machine halts
    when the program counter leaves the program. *)

From Coq Require Import List Arith.PeanoNat.
From Kernel Require Import StructuralCoreAnyBase StructuralRecordAxis CrossBaseGranularityCore.
Import ListNotations.

(** * Machine *)

Inductive RAMInstr : Type :=
| RConst (i c : nat)          (* X i := c *)
| RAdd (i j k : nat)          (* X i := X j + X k *)
| RSub (i j k : nat)          (* X i := X j - X k, truncated at zero *)
| RLoadInd (i j : nat)        (* X i := X (X j) *)
| RStoreInd (i j : nat)       (* X (X i) := X j *)
| RJumpPos (j target : nat)   (* if X j > 0 then pc := target *)
| RJump (target : nat)        (* pc := target *)
| RHalt.

Record RAM : Type := {
  ram_regs : nat -> nat;
  ram_pc : nat
}.

Definition reg (s : RAM) (i : nat) : nat := ram_regs s i.

Definition set_reg (r : nat -> nat) (i v : nat) : nat -> nat :=
  fun k => if Nat.eqb k i then v else r k.

Definition with_reg (s : RAM) (i v : nat) : RAM :=
  {| ram_regs := set_reg (ram_regs s) i v; ram_pc := S (ram_pc s) |}.

Definition jump_to (s : RAM) (target : nat) : RAM :=
  {| ram_regs := ram_regs s; ram_pc := target |}.

(** Executing one instruction. [RHalt] leaves the state unchanged. *)
Definition ram_exec (ins : RAMInstr) (s : RAM) : RAM :=
  match ins with
  | RConst i c => with_reg s i c
  | RAdd i j k => with_reg s i (reg s j + reg s k)
  | RSub i j k => with_reg s i (reg s j - reg s k)
  | RLoadInd i j => with_reg s i (reg s (reg s j))
  | RStoreInd i j => with_reg s (reg s i) (reg s j)
  | RJumpPos j target =>
      if Nat.ltb 0 (reg s j) then jump_to s target else jump_to s (S (ram_pc s))
  | RJump target => jump_to s target
  | RHalt => s
  end.

Definition ram_fetch (p : list RAMInstr) (s : RAM) : option RAMInstr :=
  nth_error p (ram_pc s).

Definition ram_halted (p : list RAMInstr) (s : RAM) : Prop :=
  match ram_fetch p s with
  | None | Some RHalt => True
  | Some _ => False
  end.

(** One machine step: execute the fetched instruction, or stay put outside
    the program. *)
Definition ram_step (p : list RAMInstr) (s : RAM) : RAM :=
  match ram_fetch p s with
  | Some ins => ram_exec ins s
  | None => s
  end.

(** * Register laws *)

Lemma set_reg_same : forall r i v, set_reg r i v i = v.
Proof. intros r i v. unfold set_reg. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma set_reg_other : forall r i v k, k <> i -> set_reg r i v k = r k.
Proof.
  intros r i v k Hne. unfold set_reg.
  destruct (Nat.eqb_spec k i); [contradiction | reflexivity].
Qed.

(** Indirect store writes the register whose index is held in [X i]. *)
Theorem ram_store_indirect_writes :
  forall p s i j,
    ram_fetch p s = Some (RStoreInd i j) ->
    reg (ram_step p s) (reg s i) = reg s j.
Proof.
  intros p s i j H. unfold ram_step. rewrite H. simpl.
  unfold reg at 1. simpl. apply set_reg_same.
Qed.

(** Indirect load reads the register whose index is held in [X j]. *)
Theorem ram_load_indirect_reads :
  forall p s i j,
    ram_fetch p s = Some (RLoadInd i j) ->
    reg (ram_step p s) i = reg s (reg s j).
Proof.
  intros p s i j H. unfold ram_step. rewrite H. simpl.
  unfold reg at 1. simpl. apply set_reg_same.
Qed.

(** A store leaves every other register unchanged. *)
Theorem ram_store_indirect_frame :
  forall p s i j k,
    ram_fetch p s = Some (RStoreInd i j) -> k <> reg s i ->
    reg (ram_step p s) k = reg s k.
Proof.
  intros p s i j k H Hk. unfold ram_step. rewrite H. simpl.
  unfold reg. simpl. apply set_reg_other. exact Hk.
Qed.

(** Address arithmetic: one indirect store followed by an indirect load
    through the same address register reads back the stored value. *)
Theorem ram_store_then_load :
  forall p s a src dst,
    ram_fetch p s = Some (RStoreInd a src) ->
    ram_fetch p (ram_step p s) = Some (RLoadInd dst a) ->
    reg s a <> a ->
    reg (ram_step p (ram_step p s)) dst = reg s src.
Proof.
  intros p s a src dst H1 H2 Hna.
  rewrite (ram_load_indirect_reads _ _ _ _ H2).
  rewrite (ram_store_indirect_frame _ _ _ _ a H1).
  - apply ram_store_indirect_writes. exact H1.
  - intro E. apply Hna. symmetry. exact E.
Qed.

(** Conditional jumps branch on register contents. *)
Theorem ram_jump_pos_taken :
  forall p s j target,
    ram_fetch p s = Some (RJumpPos j target) -> 0 < reg s j ->
    ram_pc (ram_step p s) = target.
Proof.
  intros p s j target H Hpos. unfold ram_step. rewrite H. simpl.
  apply Nat.ltb_lt in Hpos. rewrite Hpos. reflexivity.
Qed.

Theorem ram_jump_pos_not_taken :
  forall p s j target,
    ram_fetch p s = Some (RJumpPos j target) -> reg s j = 0 ->
    ram_pc (ram_step p s) = S (ram_pc s).
Proof.
  intros p s j target H Hz. unfold ram_step. rewrite H. simpl.
  rewrite Hz. reflexivity.
Qed.

(** A halted machine stays where it is. *)
Theorem ram_halted_stutters : forall p s, ram_halted p s -> ram_step p s = s.
Proof.
  intros p s Hh. unfold ram_halted, ram_step in *.
  destruct (ram_fetch p s) as [ins |]; [| reflexivity].
  destruct ins; try contradiction. reflexivity.
Qed.

(** * Example: the machine computes with unbounded indirect addressing *)

(** Copy [X 1] into the register whose index is [X 0], then read it back
    into [X 2] through the same pointer. *)
Definition ram_pointer_demo : list RAMInstr :=
  [RStoreInd 0 1; RLoadInd 2 0; RHalt].

Definition ram_demo_input (addr v : nat) : RAM :=
  {| ram_regs := set_reg (set_reg (fun _ => 0) 0 addr) 1 v; ram_pc := 0 |}.

Example ram_pointer_demo_runs :
  let s := Nat.iter 2 (ram_step ram_pointer_demo) (ram_demo_input 1000 42) in
  reg s 1000 = 42 /\ reg s 2 = 42 /\ ram_halted ram_pointer_demo s.
Proof. vm_compute. repeat split. Qed.

(** * The base *)

Definition ram_base (p : list RAMInstr) : BaseMachine := {|
  b_state := RAM;
  b_next := ram_step p;
  b_init := fun s => ram_pc s = 0;
  b_halted := ram_halted p
|}.

(** Halted RAM bases stutter, as the cross-base comparison requires of a
    base whose run has ended. *)
Theorem ram_base_halted_stutters :
  forall p s, b_halted (ram_base p) s -> b_next (ram_base p) s = s.
Proof. intros p s. apply ram_halted_stutters. Qed.

(** Base runs are machine runs. *)
Theorem ram_base_run_is_ram_run :
  forall p n s, base_run (ram_base p) n s = Nat.iter n (ram_step p) s.
Proof. reflexivity. Qed.

(** Every program has a starting state, so the initial predicate is
    inhabited. *)
Theorem ram_base_has_initial : forall p, exists s, b_init (ram_base p) s.
Proof.
  intro p. exists {| ram_regs := fun _ => 0; ram_pc := 0 |}. reflexivity.
Qed.

(** The record axis is a latch on every RAM base, by the base-parametric
    theorem used for the TM and L bases. *)
Theorem record_axis_is_latch_on_ram_holds : forall p, record_axis_is_latch_on (ram_base p).
Proof.
  intros p M C Hhonest.
  exact (record_axis_is_latch_holds M _ C Hhonest).
Qed.

Print Assumptions ram_store_then_load.
Print Assumptions ram_jump_pos_taken.
Print Assumptions ram_halted_stutters.
Print Assumptions ram_pointer_demo_runs.
Print Assumptions ram_base_has_initial.
Print Assumptions record_axis_is_latch_on_ram_holds.
