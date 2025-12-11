(* ThieleUniversalBridge Module: BridgeCore *)
(* Cleaned extraction for repository build. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.


(* ----------------------------------------------------------------- *)
(* CPU Execution - from ThieleUniversal_Run1.v                      *)
(* ----------------------------------------------------------------- *)

(* Decode the instruction at the current program counter. *)
Definition decode_instr (st : CPU.State) : CPU.Instr :=
  UTM_Encode.decode_instr_from_mem st.(CPU.mem) (4 * CPU.read_reg CPU.REG_PC st).

(* Single step execution *)
Definition run1 (s : CPU.State) : CPU.State :=
  CPU.step (decode_instr s) s.

(* Multi-step execution *)
Fixpoint run_n (s : CPU.State) (n : nat) : CPU.State :=
  match n with
  | 0 => s
  | S n' => run_n (run1 s) n'
  end.

(* A reflection-friendly equality on states.  The CPU.State record contains
   only lists and naturals, so a structural Boolean equality lets us delegate
   large execution traces to [vm_compute]/[native_compute] without building a
   massive symbolic proof term. *)
Fixpoint list_eqb {A} (eqb : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x1 :: t1, x2 :: t2 => eqb x1 x2 && list_eqb eqb t1 t2
  | _, _ => false
  end.

Lemma list_eqb_spec {A} (eqb : A -> A -> bool) (eqb_spec : forall x y, eqb x y = true <-> x = y) :
  forall l1 l2, list_eqb eqb l1 l2 = true <-> l1 = l2.
Proof.
  induction l1 as [|x1 t1 IH]; destruct l2 as [|x2 t2]; simpl; try firstorder congruence.
  rewrite Bool.andb_true_iff, eqb_spec, IH. firstorder congruence.
Qed.

Lemma list_eqb_refl {A} (eqb : A -> A -> bool) (eqb_refl : forall x, eqb x x = true) :
  forall l, list_eqb eqb l l = true.
  Proof.
    induction l as [|x t IH]; simpl; rewrite ?eqb_refl, ?IH; reflexivity.
  Qed.

Definition state_eqb (s1 s2 : CPU.State) : bool :=
  Nat.eqb s1.(CPU.cost) s2.(CPU.cost)
    && list_eqb Nat.eqb s1.(CPU.regs) s2.(CPU.regs)
    && list_eqb Nat.eqb s1.(CPU.mem) s2.(CPU.mem).

Lemma state_eqb_refl : forall s, state_eqb s s = true.
Proof.
  intro s. destruct s as [r m c].
  simpl.
  apply Bool.andb_true_iff. split.
  - apply Bool.andb_true_iff. split.
    + apply Nat.eqb_refl.
    + apply list_eqb_refl. intros x. apply Nat.eqb_refl.
  - apply list_eqb_refl. intros x. apply Nat.eqb_refl.
Qed.

Lemma state_eqb_true_iff : forall s1 s2, state_eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros s1 s2; split; intro H.
  - destruct s1 as [r1 m1 c1], s2 as [r2 m2 c2]; simpl in H.
    apply Bool.andb_true_iff in H as [Hcost_reg Hmem].
    apply Bool.andb_true_iff in Hcost_reg as [Hcost Hregs].
    apply Nat.eqb_eq in Hcost.
    apply (list_eqb_spec Nat.eqb Nat.eqb_eq) in Hregs.
    apply (list_eqb_spec Nat.eqb Nat.eqb_eq) in Hmem.
    simpl in Hcost, Hregs, Hmem.
    subst c2 r2 m2. reflexivity.
  - rewrite H. destruct s2 as [r m c].
    apply state_eqb_refl.
  Qed.

Definition check_transition (start_state end_state : CPU.State) (steps : nat) : bool :=
  state_eqb (run_n start_state steps) end_state.

Lemma check_transition_sound : forall s1 s2 n,
  check_transition s1 s2 n = true -> run_n s1 n = s2.
Proof.
  unfold check_transition.
  intros s1 s2 n H.
  apply state_eqb_true_iff in H; assumption.
Qed.

Ltac vm_run_n :=
  match goal with
  | |- run_n ?s ?n = ?t =>
      apply (check_transition_sound s t n);
      vm_compute; reflexivity
  end.

(* Symbolic steppers for small, concrete prefixes.  These avoid the
   `vm_compute`/`native_compute` path when the starting state is still
   symbolic, but the program being fetched is concrete. *)
Ltac step_symbolic :=
  cbv [run1 CPU.step UTM_Encode.decode_instr_from_mem] in *;
  simpl.

(* ----------------------------------------------------------------- *)
(* State Setup - extracted from ThieleUniversal.v                   *)
(* ----------------------------------------------------------------- *)

(* Helper: set nth element of a list *)
Definition set_nth {A : Type} (l : list A) (n : nat) (v : A) : list A :=
  firstn n l ++ [v] ++ skipn (S n) l.

(* Helper: pad list to length n with zeros *)
Definition pad_to (n : nat) (l : list nat) : list nat :=
  l ++ repeat 0 (n - length l).

Lemma pad_to_expand : forall n l,
  pad_to n l = l ++ repeat 0 (n - length l).
Proof. reflexivity. Qed.

Lemma length_pad_to_ge : forall l n,
  length l <= n -> length (pad_to n l) = n.
Proof.
  intros l n Hle.
  unfold pad_to.
  rewrite app_length, repeat_length.
  lia.
Qed.

Lemma length_pad_to_ge_base : forall l n,
  length (pad_to n l) >= length l.
Proof.
  intros l n.
  unfold pad_to.
  rewrite app_length, repeat_length.
  lia.
Qed.

Lemma nth_app_lt : forall {A} (l1 l2 : list A) n d,
  n < length l1 -> nth n (l1 ++ l2) d = nth n l1 d.
Proof.
  intros A l1 l2 n d Hlt.
  revert n Hlt.
  induction l1 as [|x l1 IH]; intros [|n] Hlt; simpl in *; try lia; auto.
  apply IH. lia.
Qed.

Lemma firstn_pad_to : forall l n,
  length l <= n -> firstn (length l) (pad_to n l) = l.
Proof.
  intros l n Hle.
  unfold pad_to.
  rewrite firstn_app.
  replace (length l - length l) with 0 by lia.
  simpl.
  rewrite firstn_all.
  rewrite app_nil_r.
  reflexivity.
Qed.

