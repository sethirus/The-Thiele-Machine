(** VMUnboundedInterpreterCompose.v — general subroutine-embedding
    infrastructure, so get_slot_program/set_slot_program (and every future
    opcode block's straight-line helper code) can be proved correct once,
    at pc=0, and then reused unchanged inside a larger program at any
    absolute offset, instead of re-deriving register bookkeeping from
    scratch for every composition.

    The core fact: for the specific arithmetic/load-immediate instructions
    used by get_slot_program/set_slot_program (all straight-line — none of
    them is a jump, call, ret, or taken branch), vm_apply_u's effect on
    every field except vm_pc does not depend on the incoming vm_pc value,
    and vm_pc always becomes exactly one more than it was. So running such
    a program embedded at offset `base` inside a bigger program behaves
    exactly like running it alone from pc=0, with every field identical
    except vm_pc, which is shifted by the constant `base` throughout. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep VMUnboundedInterpreterCode.

(** * 1. The instructions get_slot_program/set_slot_program are built from. *)

Inductive straightline_arith : vm_instruction -> Prop :=
| sl_xfer : forall d s c, straightline_arith (instr_xfer d s c)
| sl_load_imm : forall d imm c, straightline_arith (instr_load_imm d imm c)
| sl_mul : forall d r1 r2 c, straightline_arith (instr_mul d r1 r2 c)
| sl_add : forall d r1 r2 c, straightline_arith (instr_add d r1 r2 c)
| sl_sub : forall d r1 r2 c, straightline_arith (instr_sub d r1 r2 c)
| sl_shr : forall d r1 r2 c, straightline_arith (instr_shr d r1 r2 c)
| sl_shl : forall d r1 r2 c, straightline_arith (instr_shl d r1 r2 c)
| sl_and : forall d r1 r2 c, straightline_arith (instr_and d r1 r2 c)
| sl_or  : forall d r1 r2 c, straightline_arith (instr_or  d r1 r2 c).

(** * 2. pc_shifted_by base s1 s2: s2 is s1 with vm_pc offset by base and
    every other field identical. *)

Definition pc_shifted_by (base : nat) (s1 s2 : VMState) : Prop :=
  s2.(vm_pc) = base + s1.(vm_pc) /\
  s2.(vm_graph) = s1.(vm_graph) /\
  s2.(vm_csrs) = s1.(vm_csrs) /\
  s2.(vm_regs) = s1.(vm_regs) /\
  s2.(vm_mem) = s1.(vm_mem) /\
  s2.(vm_mu) = s1.(vm_mu) /\
  s2.(vm_mu_tensor) = s1.(vm_mu_tensor) /\
  s2.(vm_err) = s1.(vm_err) /\
  s2.(vm_logic_acc) = s1.(vm_logic_acc) /\
  s2.(vm_mstatus) = s1.(vm_mstatus) /\
  s2.(vm_witness) = s1.(vm_witness) /\
  s2.(vm_certified) = s1.(vm_certified).

Lemma pc_shifted_by_refl0 : forall s, pc_shifted_by 0 s s.
Proof. intro s. unfold pc_shifted_by. repeat split; try lia; try reflexivity. Qed.

(** * 3. Each straightline_arith instruction preserves pc_shifted_by,
    for the same base, on any pair of states related by it. *)

Lemma write_reg_u_ext : forall s1 s2 r v,
  s1.(vm_regs) = s2.(vm_regs) -> write_reg_u s1 r v = write_reg_u s2 r v.
Proof. intros s1 s2 r v H. unfold write_reg_u. rewrite H. reflexivity. Qed.

Lemma vm_apply_u_pc_shift : forall base s1 s2 instr,
  straightline_arith instr ->
  pc_shifted_by base s1 s2 ->
  pc_shifted_by base (vm_apply_u s1 instr) (vm_apply_u s2 instr).
Proof.
  intros base s1 s2 instr Hsl Hshift.
  unfold pc_shifted_by in Hshift.
  destruct Hshift as (Hpc & Hg & Hc & Hr & Hm & Hmu & Ht & Herr & Hla & Hst & Hw & Hcert).
  destruct Hsl; cbn [vm_apply_u];
    unfold advance_state_rm, read_reg;
    rewrite ?Hr, ?Hg, ?Hc, ?Hm, ?Herr;
    rewrite (write_reg_u_ext s2 s1 _ _ Hr);
    unfold pc_shifted_by; cbn [vm_pc vm_graph vm_csrs vm_regs vm_mem vm_mu vm_mu_tensor
                                vm_err vm_logic_acc vm_mstatus vm_witness vm_certified];
    unfold apply_cost; rewrite ?Hmu, ?Ht, ?Hla, ?Hst, ?Hw, ?Hcert;
    repeat split; try lia; try reflexivity.
Qed.

(** * 4. Each straightline_arith instruction advances vm_pc by exactly 1,
    regardless of the incoming state. *)

Lemma vm_apply_u_pc_succ : forall s instr,
  straightline_arith instr -> (vm_apply_u s instr).(vm_pc) = S s.(vm_pc).
Proof.
  intros s instr Hsl.
  destruct Hsl; cbn [vm_apply_u]; unfold advance_state_rm; cbn [vm_pc]; reflexivity.
Qed.

(** * 5. A straight-line program run from pc=k reaches pc=k+n after n
    steps, as long as k+n stays within the program's length. *)

Lemma run_vm_u_straightline_pc_gen : forall P,
  Forall straightline_arith P ->
  forall n k s, k + n <= length P -> s.(vm_pc) = k ->
  (run_vm_u n P s).(vm_pc) = k + n.
Proof.
  intros P HallP.
  induction n as [| n IH]; intros k s Hlen Hpc.
  - cbn [run_vm_u]. lia.
  - cbn [run_vm_u]. rewrite Hpc.
    assert (Hk : k < length P) by lia.
    destruct (nth_error P k) as [instr |] eqn:E.
    2: { apply nth_error_None in E. lia. }
    assert (Hsl : straightline_arith instr)
      by (eapply Forall_forall; [exact HallP | eapply nth_error_In; exact E]).
    assert (Hpc' : (vm_apply_u s instr).(vm_pc) = S k)
      by (rewrite (vm_apply_u_pc_succ s instr Hsl), Hpc; reflexivity).
    replace (k + S n) with (S k + n) by lia.
    apply (IH (S k)); [lia | exact Hpc'].
Qed.

Corollary run_vm_u_straightline_pc : forall P,
  Forall straightline_arith P ->
  forall n s, n <= length P -> s.(vm_pc) = 0 ->
  (run_vm_u n P s).(vm_pc) = n.
Proof.
  intros P HP n s Hn Hpc.
  pose proof (run_vm_u_straightline_pc_gen P HP n 0 s ltac:(lia) Hpc) as H.
  rewrite H. lia.
Qed.

(** * 6. The main embedding theorem: running a straight-line program P for
    n steps from a state at pc=k, or running it embedded inside
    prefix++P++suffix from a pc_shifted_by-related state at pc=length
    prefix+k, produces pc_shifted_by-related results — every field but
    vm_pc identical, vm_pc offset by the same constant throughout. *)

Lemma run_vm_u_embed_gen : forall P prefix suffix,
  Forall straightline_arith P ->
  forall n k s1 s2, k + n <= length P ->
  s1.(vm_pc) = k ->
  pc_shifted_by (length prefix) s1 s2 ->
  pc_shifted_by (length prefix) (run_vm_u n P s1) (run_vm_u n (prefix ++ P ++ suffix) s2).
Proof.
  intros P prefix suffix HallP.
  induction n as [| n IH]; intros k s1 s2 Hlen Hpc Hshift.
  - cbn [run_vm_u]. exact Hshift.
  - cbn [run_vm_u].
    assert (Hpc2 : s2.(vm_pc) = length prefix + k)
      by (destruct Hshift as [Hp _]; rewrite Hp, Hpc; reflexivity).
    rewrite Hpc, Hpc2.
    assert (Hk : k < length P) by lia.
    destruct (nth_error P k) as [instr |] eqn:E.
    2: { apply nth_error_None in E. lia. }
    assert (Hsl : straightline_arith instr)
      by (eapply Forall_forall; [exact HallP | eapply nth_error_In; exact E]).
    assert (E2 : nth_error (prefix ++ P ++ suffix) (length prefix + k) = Some instr).
    { rewrite nth_error_app2 by lia.
      replace (length prefix + k - length prefix) with k by lia.
      rewrite nth_error_app1 by lia. exact E. }
    rewrite E2.
    assert (Hshift' : pc_shifted_by (length prefix) (vm_apply_u s1 instr) (vm_apply_u s2 instr))
      by (apply vm_apply_u_pc_shift; assumption).
    assert (Hpc1' : (vm_apply_u s1 instr).(vm_pc) = S k)
      by (rewrite (vm_apply_u_pc_succ s1 instr Hsl), Hpc; reflexivity).
    apply (IH (S k)); [lia | exact Hpc1' | exact Hshift'].
Qed.

Corollary run_vm_u_embed : forall P prefix suffix s1 s2,
  Forall straightline_arith P ->
  s1.(vm_pc) = 0 ->
  pc_shifted_by (length prefix) s1 s2 ->
  pc_shifted_by (length prefix)
    (run_vm_u (length P) P s1) (run_vm_u (length P) (prefix ++ P ++ suffix) s2).
Proof.
  intros P prefix suffix s1 s2 HP Hpc Hshift.
  apply (run_vm_u_embed_gen P prefix suffix HP (length P) 0 s1 s2); [lia | exact Hpc | exact Hshift].
Qed.

(** Both get_slot_program and set_slot_program are entirely built from
    straightline_arith instructions. *)
Lemma get_slot_program_straightline :
  Forall straightline_arith get_slot_program.
Proof.
  unfold get_slot_program.
  repeat constructor.
Qed.

Lemma set_slot_program_straightline :
  Forall straightline_arith set_slot_program.
Proof.
  unfold set_slot_program.
  repeat constructor.
Qed.

(** * 7. Fuel splitting: running n1+n2 steps is the same as running n1
    then n2 more from wherever that lands — including past a halt, where
    extra fuel is a no-op. Needed to carve an exact 5- or 15-step
    sub-computation (matching a get_slot_program/set_slot_program call)
    out of the middle of a longer run, without re-deriving it. *)

Lemma run_vm_u_halted_stable : forall n trace s,
  nth_error trace s.(vm_pc) = None -> run_vm_u n trace s = s.
Proof.
  induction n as [| n IH]; intros trace s Hnone; cbn [run_vm_u].
  - reflexivity.
  - rewrite Hnone. reflexivity.
Qed.

Lemma run_vm_u_split : forall n1 n2 trace s,
  run_vm_u (n1 + n2) trace s = run_vm_u n2 trace (run_vm_u n1 trace s).
Proof.
  induction n1 as [| n1' IH]; intros n2 trace s.
  - reflexivity.
  - cbn [Nat.add run_vm_u].
    destruct (nth_error trace s.(vm_pc)) as [instr |] eqn:E.
    + apply IH.
    + symmetry. apply run_vm_u_halted_stable. exact E.
Qed.

(** * 8. reset_pc: a copy of a state with vm_pc zeroed, everything else
    identical — always pc_shifted_by-related to the original by its own
    (whatever) pc value. Used to manufacture the "standalone, pc=0" state
    a get_slot_program_correct/set_slot_program_correct call needs, from
    a state already embedded partway through a bigger program. *)

Definition reset_pc (s : VMState) : VMState :=
  {| vm_graph := s.(vm_graph); vm_csrs := s.(vm_csrs); vm_regs := s.(vm_regs);
     vm_mem := s.(vm_mem); vm_pc := 0; vm_mu := s.(vm_mu);
     vm_mu_tensor := s.(vm_mu_tensor); vm_err := s.(vm_err);
     vm_logic_acc := s.(vm_logic_acc); vm_mstatus := s.(vm_mstatus);
     vm_witness := s.(vm_witness); vm_certified := s.(vm_certified) |}.

Lemma reset_pc_pc0 : forall s, (reset_pc s).(vm_pc) = 0.
Proof. reflexivity. Qed.

Lemma pc_shifted_by_reset_pc : forall s, pc_shifted_by s.(vm_pc) (reset_pc s) s.
Proof.
  intro s. unfold pc_shifted_by, reset_pc.
  cbn [vm_pc vm_graph vm_csrs vm_regs vm_mem vm_mu vm_mu_tensor vm_err
       vm_logic_acc vm_mstatus vm_witness vm_certified].
  repeat split; try lia; try reflexivity.
Qed.

(** * 9. Register-file length is preserved by any straight-line run — used
    at every subroutine call site to keep re-establishing REG_COUNT
    without re-deriving it instruction by instruction. *)

Lemma vm_apply_u_preserves_reglen : forall s instr,
  straightline_arith instr ->
  length s.(vm_regs) = REG_COUNT -> length (vm_apply_u s instr).(vm_regs) = REG_COUNT.
Proof.
  intros s instr Hsl Hlen.
  destruct Hsl; cbn [vm_apply_u]; unfold advance_state_rm; cbn [vm_regs];
    apply write_reg_u_length; exact Hlen.
Qed.

Lemma run_vm_u_preserves_reglen : forall n P s,
  Forall straightline_arith P -> length s.(vm_regs) = REG_COUNT ->
  length (run_vm_u n P s).(vm_regs) = REG_COUNT.
Proof.
  induction n as [| n IH]; intros P s HP Hlen; cbn [run_vm_u].
  - exact Hlen.
  - destruct (nth_error P s.(vm_pc)) as [instr |] eqn:E.
    + apply IH; [exact HP |].
      apply vm_apply_u_preserves_reglen; [| exact Hlen].
      eapply Forall_forall; [exact HP | eapply nth_error_In; exact E].
    + exact Hlen.
Qed.
