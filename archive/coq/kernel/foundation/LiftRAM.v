(** LiftRAM: a random-access machine as a base, step by step.

    The base is the unit-cost RAM of Cook and Reckhow in
    CrossBaseGranularityRAM.v: unboundedly many registers, constants,
    addition, truncated subtraction, indirect load and store, conditional and
    unconditional jumps.  A move of the base machine is a RAM program together
    with a step bound: the move runs the program from its first instruction
    for that many RAM steps and leaves the registers it computed (a program
    whose pc has left the program stays put, so a bound that is too large
    changes nothing).

    Register 0 holds the program counter of the two-counter machine being
    simulated, registers 1 and 2 its two counters, register 3 the constant 1
    (the live invariant).  The move for CINC r is two RAM instructions; the
    move for CDEC r j is the six-instruction program

        0: RJumpPos r 3     if r > 0 goto 3, else fall through
        1: RAdd 0 0 3       zero case: pc register := pc register + 1
        2: RJump 6          leave
        3: RSub r r 3       positive case: r := r - 1
        4: RConst 0 j       pc register := j
        5: RJump 6          leave.

    [lift_ram_base] is a universal base in the sense of ThieleComplete.v for the
    machine [lift_ram_machine]; every RAM micro-step is the repository's own
    ram_step.

    No axioms and no unfinished proofs.                                                  *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import CrossBaseGranularityRAM.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Definition lift_ram_move : Type := (list RAMInstr * nat)%type.

Definition lift_ram_restart (s : RAM) : RAM := {| ram_regs := ram_regs s; ram_pc := 0 |}.

Definition lift_ram_macro (s : RAM) (m : lift_ram_move) : RAM :=
  Nat.iter (snd m) (ram_step (fst m)) (lift_ram_restart s).

Definition lift_ram_machine : T.machine :=
  T.mk_machine RAM lift_ram_move lift_ram_macro (fun _ => 0) (fun _ => false).

Definition lift_ram_creg (r : T.reg) : nat := match r with T.RA => 1 | T.RB => 2 end.

Definition lift_ram_compile (i : T.cm_instr) : lift_ram_move :=
  match i with
  | T.CINC r => ([RAdd (lift_ram_creg r) (lift_ram_creg r) 3; RAdd 0 0 3], 2)
  | T.CDEC r j => ([RJumpPos (lift_ram_creg r) 3; RAdd 0 0 3; RJump 6;
                    RSub (lift_ram_creg r) (lift_ram_creg r) 3; RConst 0 j; RJump 6], 6)
  end.

Definition lift_ram_window (s : RAM) : T.cm_conf :=
  (ram_regs s 0, (ram_regs s 1, ram_regs s 2)).

Definition lift_ram_live (s : RAM) : Prop := ram_regs s 3 = 1.

Definition lift_ram_load (a b : nat) : RAM :=
  {| ram_regs := fun k => match k with 0 => 1 | 1 => a | 2 => b | 3 => 1 | _ => 0 end;
     ram_pc := 0 |}.

Lemma lift_ram_sim : forall s i, lift_ram_live s ->
  lift_ram_window (lift_ram_macro s (lift_ram_compile i)) = T.cm_exec i (lift_ram_window s) /\
  lift_ram_live (lift_ram_macro s (lift_ram_compile i)).
Proof.
  intros [regs pc] i Hl. unfold lift_ram_live in Hl. simpl in Hl.
  destruct i as [r | r j]; destruct r;
    unfold lift_ram_macro, lift_ram_compile, lift_ram_window, lift_ram_live, lift_ram_restart; simpl.
  - unfold ram_step, ram_fetch, reg, set_reg; simpl. rewrite Hl.
    split; [repeat f_equal; lia | reflexivity].
  - unfold ram_step, ram_fetch, reg, set_reg; simpl. rewrite Hl.
    split; [repeat f_equal; lia | reflexivity].
  - destruct (regs 1) as [| n] eqn:E1;
      unfold ram_step, ram_fetch, reg, set_reg; simpl; rewrite ?E1, ?Hl; simpl;
      unfold set_reg; simpl; rewrite ?E1, ?Hl; simpl;
      split; try (repeat f_equal; lia); try reflexivity; try exact Hl.
  - destruct (regs 2) as [| n] eqn:E1;
      unfold ram_step, ram_fetch, reg, set_reg; simpl; rewrite ?E1, ?Hl; simpl;
      unfold set_reg; simpl; rewrite ?E1, ?Hl; simpl;
      split; try (repeat f_equal; lia); try reflexivity; try exact Hl.
Qed.

Definition lift_ram_base : T.universal_base lift_ram_machine :=
  T.mk_ub lift_ram_machine lift_ram_window lift_ram_live lift_ram_compile lift_ram_load
    (fun a b => eq_refl) (fun a b => eq_refl) lift_ram_sim.

Print Assumptions lift_ram_base.
