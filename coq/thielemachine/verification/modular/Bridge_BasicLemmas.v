(* ThieleUniversalBridge Module: BasicLemmas *)
(* Extracted from lines 701-900 *)
(* NOTE: This is a standalone extraction for analysis purposes. *)
(*       It may not compile independently due to dependencies. *)
(*       Use the original ThieleUniversalBridge.v for actual compilation. *)
(* ================================================================= *)

From Coq Require Import List Arith Lia PeanoNat Bool ZArith String.
From ThieleUniversal Require Import TM UTM_Rules CPU UTM_Program UTM_Encode.
Import ListNotations.
Local Open Scope nat_scope.
Local Notation length := List.length.

  n < m -> nth n (firstn m l) d = nth n l d.
Proof.
  intros A n m l d Hn.
  revert n m Hn.
  induction l as [|x l IH]; intros n m Hn.
  - destruct n; destruct m; simpl; try reflexivity; try lia.
  - destruct n; destruct m; simpl; try reflexivity; try lia.
    apply IH. lia.
Qed.

(* Placeholder transition lemmas - these would need full proofs *)
(* For now we provide stubs that can be filled in *)

(* ----------------------------------------------------------------- *)
(* Common Infrastructure Lemmas                                      *)
(* ----------------------------------------------------------------- *)

(* Step composition lemmas *)
Lemma run_n_add : forall cpu m n,
  run_n cpu (m + n) = run_n (run_n cpu m) n.
Proof.
  intros cpu m n.
  revert cpu.
  induction m as [|m' IH]; intros cpu.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma run_n_S : forall cpu n,
  run_n cpu (S n) = run_n (run1 cpu) n.
Proof.
  intros cpu n.
  simpl. reflexivity.
Qed.

Lemma run_n_0 : forall cpu,
  run_n cpu 0 = cpu.
Proof.
  intros cpu. reflexivity.
Qed.

Lemma run_n_1 : forall cpu,
  run_n cpu 1 = run1 cpu.
Proof.
  intros cpu. reflexivity.
Qed.

(* Prevent large proof terms from repeatedly unfolding the small-step
   interpreter.  The structural lemmas above expose the only rewrites we
   rely on, so the operational definitions can remain opaque during the
   heavy FindRule proofs. *)
#[local] Opaque run_n decode_instr.

(* Make key definitions opaque to prevent expensive unfolding during proofs.
   This stops the unifier from expanding massive symbolic lists. *)
#[global] Opaque program.
#[global] Opaque pad_to.
#[global] Opaque setup_state.

(* Rewrite run_n in terms of iterations *)
Lemma run_n_unfold_3 : forall cpu,
  run_n cpu 3 = run1 (run1 (run1 cpu)).
Proof.
  intros cpu.
  simpl. reflexivity.
Qed.

(* Memory and register helpers *)
Lemma read_reg_bounds : forall cpu r,
  r < 10 ->
  exists v, CPU.read_reg r cpu = v.
Proof.
  intros cpu r Hr.
  exists (CPU.read_reg r cpu).
  reflexivity.
Qed.

(* Key lemma: reading from the register you just wrote gives the value *)
Lemma read_reg_write_reg_same : forall r v st,
  r < length st.(CPU.regs) ->
  CPU.read_reg r (CPU.write_reg r v st) = v.
Proof.
  intros r v st Hr.
  unfold CPU.read_reg, CPU.write_reg. simpl.
  (* After write_reg r v, the register file is: firstn r regs ++ [v] ++ skipn (S r) regs *)
  (* Reading at position r gives v *)
  rewrite app_nth2.
  - rewrite firstn_length.
    rewrite Nat.min_l by lia.
    replace (r - r) with 0 by lia.
    simpl. reflexivity.
  - rewrite firstn_length.
    rewrite Nat.min_l by lia.
    lia.
Qed.

(* Reading a different register after write *)
Lemma read_reg_write_reg_diff : forall r1 r2 v st,
  r1 <> r2 ->
  r1 < length st.(CPU.regs) ->
  r2 < length st.(CPU.regs) ->
  CPU.read_reg r1 (CPU.write_reg r2 v st) = CPU.read_reg r1 st.
Proof.
  intros r1 r2 v st Hneq Hr1 Hr2.
  unfold CPU.read_reg, CPU.write_reg. simpl.
  (* Need to show: nth r1 (firstn r2 regs ++ [v] ++ skipn (S r2) regs) 0 = nth r1 regs 0 *)
  destruct (Nat.ltb r1 r2) eqn:Hlt.
  - (* Case r1 < r2: r1 is in the firstn part *)
    apply Nat.ltb_lt in Hlt.
    rewrite app_nth1.
    + apply nth_firstn_lt. exact Hlt.
    + rewrite firstn_length. rewrite Nat.min_l; [lia|lia].
  - (* Case r1 >= r2, but r1 <> r2, so r1 > r2 *)
    apply Nat.ltb_nlt in Hlt.
    assert (r1 > r2) by lia.
    (* r1 is beyond the firstn r2 part *)
    rewrite app_nth2.
    + rewrite firstn_length. rewrite Nat.min_l; [|lia].
      (* nth (r1 - r2) ([v] ++ skipn (S r2) regs) 0 = nth r1 regs 0 *)
      destruct (r1 - r2) as [|n] eqn:Hdiff; [lia|].
      simpl.
      (* nth n (skipn (S r2) regs) 0 = nth r1 regs 0 *)
      assert (Heqr1: r1 = S r2 + n) by lia.
      rewrite Heqr1.
      (* Now prove: nth n (skipn (S r2) regs) 0 = nth (S r2 + n) regs 0 *)
      clear Heqr1 Hdiff Hneq Hr1 Hr2 H Hlt v r1.
      generalize dependent n. generalize dependent r2.
      induction (CPU.regs st) as [|x xs IH]; intros.
      { destruct n, r2; reflexivity. }
      destruct r2; simpl.
      { destruct n; reflexivity. }
      { apply IH. }
    + rewrite firstn_length. rewrite Nat.min_l; [lia|lia].
Qed.

(*Writing to a register never shrinks the register file. *)
Lemma length_write_reg_ge : forall r v st,
  length (CPU.write_reg r v st).(CPU.regs) >= length st.(CPU.regs).
Proof.
  intros r v st.
  unfold CPU.write_reg. simpl.
  (* After unfolding: firstn r (CPU.regs st) ++ [v] ++ skipn (S r) (CPU.regs st) *)
  set (regs := CPU.regs st).
  assert (Hlen: forall (l : list nat) n m,
    length (firstn n l ++ m :: skipn (S n) l) >= length l).
  { intros l. induction l as [|x xs IHxs]; intros n m.
    - destruct n; simpl; lia.
    - destruct n; simpl.
      + lia.
      + simpl in IHxs. specialize (IHxs n m). simpl. lia. }
  apply (Hlen regs r v).
Qed.

(* Stepping cannot shorten the register file. *)
Lemma length_step_ge : forall instr st,
  length (CPU.regs (CPU.step instr st)) >= length st.(CPU.regs).
Proof.
  intros instr st.
  unfold CPU.step.
  remember (CPU.write_reg CPU.REG_PC (S (CPU.read_reg CPU.REG_PC st)) st) as st_pc eqn:Heq_st_pc.
  assert (Hlen_pc : length (CPU.regs st_pc) >= length st.(CPU.regs)).
  { subst st_pc. apply length_write_reg_ge. }
  clear Heq_st_pc.
  destruct instr; simpl.
  - (* LoadConst *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* LoadIndirect *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* StoreIndirect *) unfold CPU.write_mem; simpl; assumption.
  - (* CopyReg *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* AddConst *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* AddReg *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* SubReg *) eapply Nat.le_trans; [apply Hlen_pc|apply length_write_reg_ge].
  - (* Jz: if zero, write_reg to st; otherwise st_pc *)
    destruct (Nat.eqb (CPU.read_reg rc st) 0).
    + apply length_write_reg_ge.
    + assumption.
  - (* Jnz: if zero, st_pc; otherwise write_reg to st *)
    destruct (Nat.eqb (CPU.read_reg rc st) 0).
    + assumption.
    + apply length_write_reg_ge.
  - (* Halt: returns st unchanged *)
    apply Nat.le_refl.
Qed.

(* Multi-step execution preserves or grows the register file length. *)
Lemma length_run_n_ge : forall st n,
  length (CPU.regs (run_n st n)) >= length st.(CPU.regs).
Proof.
  intros st n.
  revert st. (* Generalize st before induction so IH is universal *)
  induction n as [|n' IHn]; intros st.
  - (* Base case: n = 0 *)
    simpl. apply Nat.le_refl.
  - (* Inductive case: n = S n' *)
    simpl. (* run_n st (S n') = run_n (run1 st) n' *)
    (* IHn : forall st', length (run_n st' n') >= length st' *)
    (* Need: length (run_n (run1 st) n') >= length st *)
    assert (H1: length (CPU.regs (run1 st)) >= length (CPU.regs st)).
    { unfold run1. apply length_step_ge. }
    assert (H2: length (CPU.regs (run_n (run1 st) n')) >= length (CPU.regs (run1 st))).
