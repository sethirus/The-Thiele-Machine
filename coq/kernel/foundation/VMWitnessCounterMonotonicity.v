(** Monotonicity of the witness-counter buckets under actual vm_step.

    The only mutation ever applied to WitnessCounts anywhere in this VM's
    semantics is record_trial, invoked by exactly one vm_step constructor
    (step_chsh_trial_ok) with a per-trial increment of exactly one of the
    eight bucket fields; every other constructor leaves vm_witness
    unchanged. Consequently every field of the bucket record is
    non-decreasing across any single actual step, and therefore across any
    finite actual run. This is the precise sense in which a bucket pair,
    once used to answer an equality test, cannot be driven back to a value
    indistinguishable from a state it could not otherwise have reached: no
    finite continuation can ever lower a field again. This is a fact about
    the witness-counter buckets specifically; it says nothing about the
    VM's ordinary registers or memory, which are unrestricted read/write
    storage and are not the subject of this file. This is the
    witness-counter fact used by the current VM contracts: no macro built
    only from record_trial calls and guard reads can restore a drained bucket
    pair to encode an independent second value, because restoration would
    require a field decrease that no actual step can produce. *)
From Coq Require Import Arith Lia List.
From Kernel Require Import VMState VMStep.
Import ListNotations.

Definition wc_le (wc1 wc2 : WitnessCounts) : Prop :=
  wc_same_00 wc1 <= wc_same_00 wc2 /\ wc_diff_00 wc1 <= wc_diff_00 wc2 /\
  wc_same_01 wc1 <= wc_same_01 wc2 /\ wc_diff_01 wc1 <= wc_diff_01 wc2 /\
  wc_same_10 wc1 <= wc_same_10 wc2 /\ wc_diff_10 wc1 <= wc_diff_10 wc2 /\
  wc_same_11 wc1 <= wc_same_11 wc2 /\ wc_diff_11 wc1 <= wc_diff_11 wc2.

Lemma wc_le_refl : forall wc, wc_le wc wc.
Proof. intros wc. unfold wc_le. lia. Qed.

Lemma wc_le_trans : forall wc1 wc2 wc3,
  wc_le wc1 wc2 -> wc_le wc2 wc3 -> wc_le wc1 wc3.
Proof. unfold wc_le. intros wc1 wc2 wc3. lia. Qed.

(** record_trial only ever increments exactly one field by one and leaves
    the other seven syntactically untouched. *)
Theorem record_trial_monotone : forall wc x y a b,
  wc_le wc (record_trial wc x y a b).
Proof.
  intros wc x y a b.
  unfold record_trial, wc_le.
  destruct x as [|x']; destruct y as [|y']; destruct (Nat.eqb a b);
    cbn; lia.
Qed.

(** advance_state, advance_state_reveal, and advance_state_rm are the three
    shared state builders used across vm_step; each preserves vm_witness
    exactly. *)
Lemma advance_state_witness : forall s instr graph csrs err_flag,
  (advance_state s instr graph csrs err_flag).(vm_witness) = s.(vm_witness).
Proof. reflexivity. Qed.

Lemma advance_state_reveal_witness : forall s instr flat_idx delta graph csrs err_flag,
  (advance_state_reveal s instr flat_idx delta graph csrs err_flag).(vm_witness) = s.(vm_witness).
Proof. reflexivity. Qed.

Lemma advance_state_rm_witness : forall s instr graph csrs regs mem err_flag,
  (advance_state_rm s instr graph csrs regs mem err_flag).(vm_witness) = s.(vm_witness).
Proof. reflexivity. Qed.

(** The central fact: no single actual vm_step ever decreases any witness
    bucket field. Every constructor either delegates to one of the three
    shared builders (witness passed through unchanged, by the three lemmas
    above) or lists vm_witness := s.(vm_witness) directly in its own
    result record, except step_chsh_trial_ok, whose only change is a
    record_trial call, covered by record_trial_monotone. *)
Theorem vm_step_witness_monotone : forall s i s',
  vm_step s i s' -> wc_le s.(vm_witness) s'.(vm_witness).
Proof.
  intros s i s' Hstep.
  destruct Hstep; subst;
    repeat match goal with
    | |- context [advance_state] => rewrite advance_state_witness
    | |- context [advance_state_reveal] => rewrite advance_state_reveal_witness
    | |- context [advance_state_rm] => rewrite advance_state_rm_witness
    end;
    cbn [vm_witness];
    match goal with
    | |- wc_le _ (record_trial _ _ _ _ _) => apply record_trial_monotone
    | |- wc_le ?w ?w => apply wc_le_refl
    | _ => apply wc_le_refl
    end.
Qed.

(** Extension to finite actual runs: any sequence of steps only grows the
    buckets. Stated over an explicit list of intermediate states linked by
    vm_step, matching this file's run-of-steps idiom rather than assuming a
    separate run_vm driver. *)
Fixpoint vm_step_star (s : VMState) (is_ : list vm_instruction) (s' : VMState) : Prop :=
  match is_ with
  | [] => s = s'
  | i :: rest => exists s_mid, vm_step s i s_mid /\ vm_step_star s_mid rest s'
  end.

Theorem vm_run_witness_monotone : forall is_ s s',
  vm_step_star s is_ s' -> wc_le s.(vm_witness) s'.(vm_witness).
Proof.
  induction is_ as [| i rest IH]; intros s s' Hrun.
  - cbn in Hrun. subst. apply wc_le_refl.
  - cbn in Hrun. destruct Hrun as [s_mid [Hstep Hrest]].
    apply (wc_le_trans _ s_mid.(vm_witness) _).
    + apply (vm_step_witness_monotone _ _ _ Hstep).
    + apply (IH _ _ Hrest).
Qed.

(** Corollary making the B2c obstacle precise: once a bucket field reaches
    some value k anywhere in a run, no later state in that same run can
    show a smaller value for that field. In particular, a bucket pair
    driven to equality (the only way any CHSH guard variant can look past
    the base test) cannot subsequently be read back down to whatever
    strictly smaller value it held before that drain: doing so would need
    a witness field to decrease, which vm_run_witness_monotone rules out
    for every actual run. This is what blocks a save/restore macro for a
    second independent counter built only from record_trial and guard
    reads; it does not constrain the VM's ordinary registers or memory. *)
Corollary wc_field_never_shrinks_same_00 : forall is_ s s',
  vm_step_star s is_ s' -> wc_same_00 s.(vm_witness) <= wc_same_00 s'.(vm_witness).
Proof. intros is_ s s' H. apply vm_run_witness_monotone in H. unfold wc_le in H. lia. Qed.
