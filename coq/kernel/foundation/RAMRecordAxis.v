(** RAMRecordAxis: the tied and untied list-memory RAMs on the record axis.

    SCOPE NOTE: standalone proof scope.
    The RAM of [ConcreteRAMTarget] is an independent comparison model, so no
    VM semantic anchor is used and no bridge to VM semantics is claimed.

    Part 5.3 round 2 proved the four frozen single-step propositions of
    [ConcreteRAMTarget] (in [ConcreteRAM]) and left the Round 4 adapters
    BLOCKED: no [BaseMachine], no [BaseCover], no [HonestExtension4], no
    [latch_factorization] for the RAM.  This file supplies those adapters.

    - A program is a list of [RAMOp] indexed by the program counter.  A state
      whose program counter has no instruction is halted and stays put.
    - The base machine runs over memory and program counter only, with the
      step given by [ram_base_step].
    - TIED runs [ram_tied_step] and UNTIED runs [ram_untied_step] on full
      [RAMState]s.  Both have a [BaseCover] over the same base machine with
      [ram_projection] as the map down.
    - The ledger is the record length.  The Boolean reading is whether the
      record is nonempty.  The multi-valued record is [ram_record] itself,
      ordered by the prefix order.

    Results.  TIED appends exactly the overwrite entry on every step, so its
    record grows in prefix order and is driven by the computation.  For every
    nonempty program it is an honest growing extension, it is an honest
    Round 4 extension, and its Boolean reading factors as the latch of the
    event "the current instruction addresses an existing cell".  UNTIED never
    writes its record, so it fails the reachable-write clause of both honesty
    notions.  The two machines have identical base projections along every
    run.  A concrete two-instruction run shows equal projections with
    different records. *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.

From Kernel Require Import StructuralCore StructuralCoreRound2 StructuralCoreRound4.
From Kernel Require Import GrowingRecordCore GrowingRecord.
From Kernel Require Import ConcreteRAMTarget ConcreteRAM.

(** * Programs and steps *)

Definition ram_fetch (prog : list RAMOp) (s : RAMState) : option RAMOp :=
  nth_error prog (ram_pc s).

Definition prog_tied_next (prog : list RAMOp) (s : RAMState) : RAMState :=
  match ram_fetch prog s with
  | Some op => ram_tied_step op s
  | None => s
  end.

Definition prog_untied_next (prog : list RAMOp) (s : RAMState) : RAMState :=
  match ram_fetch prog s with
  | Some op => ram_untied_step op s
  | None => s
  end.

(** The base state is the pair of memory and program counter. *)
Definition ram_base_of (b : list nat * nat) : RAMState :=
  {| ram_memory := fst b; ram_pc := snd b; ram_record := [] |}.

Definition prog_base_next (prog : list RAMOp) (b : list nat * nat)
  : list nat * nat :=
  match nth_error prog (snd b) with
  | Some op => ram_projection (ram_base_step op (ram_base_of b))
  | None => b
  end.

Definition RAMBase (prog : list RAMOp) : BaseMachine := {|
  b_state := list nat * nat;
  b_next := prog_base_next prog;
  b_init := fun b => snd b = 0;
  b_halted := fun b => nth_error prog (snd b) = None
|}.

Definition record_nonempty (r : list (nat * nat)) : bool :=
  match r with [] => false | _ :: _ => true end.

Definition TiedRAM (prog : list RAMOp) : RCM := {|
  rc_state := RAMState;
  rc_next := prog_tied_next prog;
  rc_init := fun s => ram_pc s = 0 /\ ram_record s = [];
  rc_cert := fun s => record_nonempty (ram_record s);
  rc_mu := fun s => length (ram_record s);
  rc_halted := fun s => nth_error prog (ram_pc s) = None
|}.

Definition UntiedRAM (prog : list RAMOp) : RCM := {|
  rc_state := RAMState;
  rc_next := prog_untied_next prog;
  rc_init := fun s => ram_pc s = 0 /\ ram_record s = [];
  rc_cert := fun s => record_nonempty (ram_record s);
  rc_mu := fun s => length (ram_record s);
  rc_halted := fun s => nth_error prog (ram_pc s) = None
|}.

(** * The base covers *)

Lemma ram_base_step_projection : forall op s,
  ram_projection (ram_base_step op s) =
  ram_projection (ram_base_step op (ram_base_of (ram_projection s))).
Proof.
  intros op s. unfold ram_base_step, cell_at. simpl.
  destruct (nth_error (ram_memory s) (op_address op)); reflexivity.
Qed.

Lemma prog_untied_projection : forall prog s,
  ram_projection (prog_untied_next prog s) =
  prog_base_next prog (ram_projection s).
Proof.
  intros prog s. unfold prog_untied_next, prog_base_next, ram_fetch. simpl.
  destruct (nth_error prog (ram_pc s)) as [op |]; [| reflexivity].
  unfold ram_untied_step. apply ram_base_step_projection.
Qed.

Lemma prog_tied_projection : forall prog s,
  ram_projection (prog_tied_next prog s) =
  prog_base_next prog (ram_projection s).
Proof.
  intros prog s. rewrite <- prog_untied_projection.
  unfold prog_tied_next, prog_untied_next.
  destruct (ram_fetch prog s) as [op |]; [| reflexivity].
  apply concrete_tied_and_untied_same_base.
Qed.

Lemma ram_init_surjective : forall b : list nat * nat, snd b = 0 ->
  exists s, (ram_pc s = 0 /\ ram_record s = []) /\ ram_projection s = b.
Proof.
  intros [mem pc] H. simpl in H. subst pc.
  exists (ram_base_of (mem, 0)). split; [split |]; reflexivity.
Qed.

Definition TiedCover (prog : list RAMOp) : BaseCover (TiedRAM prog) (RAMBase prog).
Proof.
  refine (@Build_BaseCover (TiedRAM prog) (RAMBase prog) ram_projection _ _ _ _).
  - intros m [H _]. exact H.
  - exact ram_init_surjective.
  - exact (prog_tied_projection prog).
  - intros m. simpl. reflexivity.
Defined.

Definition UntiedCover (prog : list RAMOp) : BaseCover (UntiedRAM prog) (RAMBase prog).
Proof.
  refine (@Build_BaseCover (UntiedRAM prog) (RAMBase prog) ram_projection _ _ _ _).
  - intros m [H _]. exact H.
  - exact ram_init_surjective.
  - exact (prog_untied_projection prog).
  - intros m. simpl. reflexivity.
Defined.

(** A cover maps every run down to the base run. *)
Lemma cover_run : forall (M : RCM) (B : BaseMachine) (C : BaseCover M B) n m,
  base_state M B C (rc_run M n m) = Nat.iter n (b_next B) (base_state M B C m).
Proof.
  intros M B C n m. induction n as [| n IH]; [reflexivity |].
  change (base_state M B C (rc_next M (rc_run M n m)) =
          b_next B (Nat.iter n (b_next B) (base_state M B C m))).
  rewrite base_step, IH. reflexivity.
Qed.

(** * The prefix order on records *)

Fixpoint prefixb (u v : list (nat * nat)) : bool :=
  match u, v with
  | [], _ => true
  | _ :: _, [] => false
  | (a, b) :: u', (c, d) :: v' => Nat.eqb a c && Nat.eqb b d && prefixb u' v'
  end.

Lemma prefixb_spec : forall u v, prefixb u v = true <-> exists w, v = u ++ w.
Proof.
  induction u as [| [a b] u IH]; intros [| [c d] v]; simpl.
  - split; intros; [exists []; reflexivity | reflexivity].
  - split; intros; [eexists; reflexivity | reflexivity].
  - split; [discriminate | intros [w Hw]; discriminate].
  - rewrite !andb_true_iff, !Nat.eqb_eq, IH. split.
    + intros [[-> ->] [w ->]]. exists w. reflexivity.
    + intros [w Hw]. injection Hw as -> -> ->. split; [split |]; eauto.
Qed.

Lemma prefixb_app : forall u w, prefixb u (u ++ w) = true.
Proof. intros u w. apply prefixb_spec. exists w. reflexivity. Qed.

Definition PrefixOrder : BoolPartialOrder (list (nat * nat)).
Proof.
  refine {| gr_leq := prefixb |}.
  - intros x. rewrite <- (app_nil_r x) at 2. apply prefixb_app.
  - intros x y H1 H2.
    apply prefixb_spec in H1 as [w Hw]. apply prefixb_spec in H2 as [w' Hw'].
    pose proof (f_equal (@length _) Hw) as L1.
    pose proof (f_equal (@length _) Hw') as L2.
    rewrite app_length in L1, L2.
    destruct w as [| p w]; [rewrite app_nil_r in Hw; congruence | simpl in L1; lia].
  - intros x y z H1 H2.
    apply prefixb_spec in H1 as [w1 ->]. apply prefixb_spec in H2 as [w2 ->].
    rewrite <- app_assoc. apply prefixb_app.
Defined.

(** * TIED: the record grows by exactly the overwrite entry *)

(** The entry a step appends, read from the base state alone. *)
Definition tied_log (prog : list RAMOp) (b : list nat * nat) : list (nat * nat) :=
  match nth_error prog (snd b) with
  | Some op =>
      match nth_error (fst b) (op_address op) with
      | Some old => [(op_address op, old)]
      | None => []
      end
  | None => []
  end.

Theorem tied_next_record : forall prog s,
  ram_record (rc_next (TiedRAM prog) s) =
  ram_record s ++ tied_log prog (ram_projection s).
Proof.
  intros prog s. change (rc_next (TiedRAM prog) s) with (prog_tied_next prog s).
  unfold prog_tied_next, tied_log, ram_fetch. simpl.
  destruct (nth_error prog (ram_pc s)) as [op |];
    [| rewrite app_nil_r; reflexivity].
  unfold ram_tied_step, cell_at.
  destruct (nth_error (ram_memory s) (op_address op)) as [old |] eqn:H;
    [reflexivity |].
  unfold ram_base_step, cell_at. rewrite H. simpl. rewrite app_nil_r. reflexivity.
Qed.

(** The frozen overwrite equation, lifted to a program step. *)
Theorem tied_program_records_overwrite : forall prog s op old,
  nth_error prog (ram_pc s) = Some op ->
  cell_at (op_address op) s = Some old ->
  ram_record (rc_next (TiedRAM prog) s) = ram_record s ++ [(op_address op, old)].
Proof.
  intros prog s op old Hop Hold.
  change (rc_next (TiedRAM prog) s) with (prog_tied_next prog s).
  unfold prog_tied_next, ram_fetch. rewrite Hop.
  apply concrete_tied_ram_records_overwrite. exact Hold.
Qed.

Theorem tied_record_grows : forall prog,
  record_grows (TiedRAM prog) PrefixOrder ram_record.
Proof.
  intros prog m.
  change (prefixb (ram_record m) (ram_record (rc_next (TiedRAM prog) m)) = true).
  rewrite tied_next_record. apply prefixb_app.
Qed.

Theorem tied_record_driven : forall prog,
  record_driven (TiedRAM prog) (RAMBase prog) (TiedCover prog) ram_record.
Proof.
  intros prog. exists (fun b r => r ++ tied_log prog b).
  intros m. apply tied_next_record.
Qed.

(** Along a run, every earlier record is a prefix of every later one. *)
Theorem tied_run_prefix : forall prog n k s,
  prefixb (ram_record (rc_run (TiedRAM prog) n s))
          (ram_record (rc_run (TiedRAM prog) (k + n) s)) = true.
Proof.
  intros prog n k s. unfold rc_run. rewrite Nat.iter_add.
  generalize (Nat.iter n (rc_next (TiedRAM prog)) s) as t.
  induction k as [| k IH]; intros t.
  - simpl. rewrite <- (app_nil_r (ram_record t)) at 2. apply prefixb_app.
  - change (prefixb (ram_record t)
      (ram_record (rc_next (TiedRAM prog)
         (Nat.iter k (rc_next (TiedRAM prog)) t))) = true).
    rewrite tied_next_record.
    specialize (IH t). apply prefixb_spec in IH as [w Hw]. rewrite Hw, <- app_assoc.
    apply prefixb_app.
Qed.

Lemma tied_step_cost : forall prog m,
  step_cost (TiedRAM prog) m = length (tied_log prog (ram_projection m)).
Proof.
  intros prog m. unfold step_cost.
  change (length (ram_record (rc_next (TiedRAM prog) m)) - length (ram_record m) =
          length (tied_log prog (ram_projection m))).
  rewrite tied_next_record, app_length. lia.
Qed.

Lemma record_nonempty_app : forall u v,
  record_nonempty (u ++ v) = orb (record_nonempty u) (record_nonempty v).
Proof. intros [| x u] v; reflexivity. Qed.

Lemma nth_error_repeat_zero : forall a, nth_error (repeat 0 (S a)) a = Some 0.
Proof. induction a as [| a IH]; [reflexivity | exact IH]. Qed.

(** The witness start state: enough zero cells for the first instruction. *)
Definition first_write_start (op : RAMOp) : RAMState :=
  {| ram_memory := repeat 0 (S (op_address op)); ram_pc := 0; ram_record := [] |}.

Lemma first_write_log : forall op rest,
  tied_log (op :: rest) (ram_projection (first_write_start op)) =
  [(op_address op, 0)].
Proof.
  intros op rest.
  change (match nth_error (repeat 0 (S (op_address op))) (op_address op) with
          | Some old => [(op_address op, old)] | None => [] end =
          [(op_address op, 0)]).
  rewrite nth_error_repeat_zero.
  reflexivity.
Qed.

Theorem tied_honest_growing : forall prog, prog <> [] ->
  HonestGrowingExtension (TiedRAM prog) (RAMBase prog) (TiedCover prog)
    PrefixOrder ram_record.
Proof.
  intros prog Hne. split; [apply tied_record_driven |].
  split; [apply tied_record_grows |]. split.
  - split.
    + intros m. change (length (ram_record m) <= length (ram_record (rc_next (TiedRAM prog) m))).
      rewrite tied_next_record, app_length. lia.
    + intros m Hneq. rewrite tied_step_cost.
      rewrite tied_next_record in Hneq.
      destruct (tied_log prog (ram_projection m)); simpl; [| lia].
      rewrite app_nil_r in Hneq. contradiction.
  - destruct prog as [| op rest]; [contradiction |].
    exists (first_write_start op), 0. split; [split; reflexivity |].
    change (ram_record (first_write_start op) <>
            ram_record (rc_next (TiedRAM (op :: rest)) (first_write_start op))).
    rewrite tied_next_record, first_write_log. discriminate.
Qed.

(** Threshold decomposition of the TIED record, from [GrowingRecord]. *)
Theorem tied_threshold_decomposition : forall prog, prog <> [] ->
  exists h,
    threshold_latch_factorization (TiedRAM prog) (RAMBase prog) (TiedCover prog)
      PrefixOrder ram_record h /\
    record_schedule_priced (TiedRAM prog) ram_record.
Proof.
  intros prog Hne.
  exact (growing_record_decomposes_holds _ _ _ _ _ _ (tied_honest_growing prog Hne)).
Qed.

(** The Round 4 event: the current instruction addresses an existing cell. *)
Definition tied_event (prog : list RAMOp) (b : list nat * nat) : bool :=
  record_nonempty (tied_log prog b).

Lemma tied_next_cert : forall prog m,
  rc_cert (TiedRAM prog) (rc_next (TiedRAM prog) m) =
  orb (rc_cert (TiedRAM prog) m) (tied_event prog (ram_projection m)).
Proof.
  intros prog m.
  change (record_nonempty (ram_record (rc_next (TiedRAM prog) m)) =
          orb (record_nonempty (ram_record m)) (tied_event prog (ram_projection m))).
  rewrite tied_next_record. apply record_nonempty_app.
Qed.

Theorem tied_latch_factorization : forall prog,
  latch_factorization (TiedRAM prog) (RAMBase prog) (TiedCover prog)
    (tied_event prog).
Proof.
  intros prog m. unfold latch_next. simpl fst. simpl snd.
  rewrite tied_next_cert. f_equal. apply prog_tied_projection.
Qed.

Theorem tied_honest_round4 : forall prog, prog <> [] ->
  HonestExtension4 (TiedRAM prog) (RAMBase prog) (TiedCover prog).
Proof.
  intros prog Hne. split.
  { exists (fun b c => orb c (tied_event prog b)). apply tied_next_cert. }
  split. { intros m. change (length (ram_record m) <= length (ram_record (rc_next (TiedRAM prog) m))).
      rewrite tied_next_record, app_length. lia. }
  split.
  { intros m H0 H1. rewrite tied_step_cost.
    rewrite tied_next_cert, H0 in H1. unfold tied_event in H1.
    destruct (tied_log prog (ram_projection m)); simpl; [discriminate | lia]. }
  split. { intros m H. rewrite tied_next_cert, H. reflexivity. }
  destruct prog as [| op rest]; [contradiction |].
  exists (first_write_start op), 0. split; [split; reflexivity |]. split.
  - reflexivity.
  - change (rc_cert (TiedRAM (op :: rest))
      (rc_next (TiedRAM (op :: rest)) (first_write_start op)) = true).
    rewrite tied_next_cert. unfold tied_event. rewrite first_write_log.
    apply orb_true_r.
Qed.

(** * UNTIED: the record is never written *)

Theorem untied_next_record : forall prog s,
  ram_record (rc_next (UntiedRAM prog) s) = ram_record s.
Proof.
  intros prog s. change (rc_next (UntiedRAM prog) s) with (prog_untied_next prog s).
  unfold prog_untied_next. destruct (ram_fetch prog s) as [op |]; [| reflexivity].
  apply concrete_untied_ram_record_unchanged.
Qed.

Theorem untied_run_record_constant : forall prog n s,
  ram_record (rc_run (UntiedRAM prog) n s) = ram_record s.
Proof.
  intros prog n s. induction n as [| n IH]; [reflexivity |].
  change (ram_record (rc_next (UntiedRAM prog) (rc_run (UntiedRAM prog) n s)) =
          ram_record s).
  rewrite untied_next_record. exact IH.
Qed.

Theorem untied_no_strict_record_write : forall prog,
  ~ reachable_strict_record_write (UntiedRAM prog) ram_record.
Proof.
  intros prog [m [n [_ Hneq]]]. apply Hneq. symmetry. apply untied_next_record.
Qed.

Theorem untied_no_record_write : forall prog,
  ~ reachable_record_write (UntiedRAM prog).
Proof.
  intros prog [m [n [_ [H0 H1]]]].
  change (record_nonempty (ram_record (rc_run (UntiedRAM prog) n m)) = false) in H0.
  change (record_nonempty (ram_record (rc_next (UntiedRAM prog)
            (rc_run (UntiedRAM prog) n m))) = true) in H1.
  rewrite untied_next_record in H1. congruence.
Qed.

Theorem untied_not_honest_growing : forall prog
    (P : BoolPartialOrder (list (nat * nat))),
  ~ HonestGrowingExtension (UntiedRAM prog) (RAMBase prog) (UntiedCover prog)
      P ram_record.
Proof.
  intros prog P [_ [_ [_ Hw]]]. exact (untied_no_strict_record_write prog Hw).
Qed.

Theorem untied_not_honest_round4 : forall prog,
  ~ HonestExtension4 (UntiedRAM prog) (RAMBase prog) (UntiedCover prog).
Proof.
  intros prog [_ [_ [_ [_ Hw]]]]. exact (untied_no_record_write prog Hw).
Qed.

(** UNTIED factors only through the latch whose event never fires. *)
Theorem untied_trivial_latch : forall prog,
  latch_factorization (UntiedRAM prog) (RAMBase prog) (UntiedCover prog)
    (fun _ => false).
Proof.
  intros prog m. unfold latch_next. simpl fst. simpl snd. rewrite orb_false_r.
  f_equal; [apply prog_untied_projection |].
  change (record_nonempty (ram_record (rc_next (UntiedRAM prog) m)) =
          record_nonempty (ram_record m)).
  rewrite untied_next_record. reflexivity.
Qed.

(** * Same base along every run *)

Theorem tied_untied_same_base_run : forall prog n s s',
  ram_projection s = ram_projection s' ->
  ram_projection (rc_run (TiedRAM prog) n s) =
  ram_projection (rc_run (UntiedRAM prog) n s').
Proof.
  intros prog n s s' H.
  pose proof (cover_run _ _ (TiedCover prog) n s) as Ht.
  pose proof (cover_run _ _ (UntiedCover prog) n s') as Hu.
  simpl in Ht, Hu. rewrite Ht, Hu, H. reflexivity.
Qed.

(** * Classification *)

Theorem ram_record_axis_classification : forall prog, prog <> [] ->
  HonestGrowingExtension (TiedRAM prog) (RAMBase prog) (TiedCover prog)
    PrefixOrder ram_record /\
  HonestExtension4 (TiedRAM prog) (RAMBase prog) (TiedCover prog) /\
  latch_factorization (TiedRAM prog) (RAMBase prog) (TiedCover prog)
    (tied_event prog) /\
  (forall P, ~ HonestGrowingExtension (UntiedRAM prog) (RAMBase prog)
                 (UntiedCover prog) P ram_record) /\
  ~ HonestExtension4 (UntiedRAM prog) (RAMBase prog) (UntiedCover prog) /\
  (forall n s, ram_projection (rc_run (TiedRAM prog) n s) =
               ram_projection (rc_run (UntiedRAM prog) n s)).
Proof.
  intros prog Hne.
  split; [exact (tied_honest_growing prog Hne) |].
  split; [exact (tied_honest_round4 prog Hne) |].
  split; [apply tied_latch_factorization |].
  split; [intros P; exact (untied_not_honest_growing prog P) |].
  split; [apply untied_not_honest_round4 |].
  intros n s. apply tied_untied_same_base_run. reflexivity.
Qed.

(** * Non-vacuity: a concrete run *)

Definition witness_prog : list RAMOp := [RAMLoad 0 5; RAMInc 1].

Definition witness_start : RAMState :=
  {| ram_memory := [1; 2]; ram_pc := 0; ram_record := [] |}.

Example witness_run_computed :
  ram_projection (rc_run (TiedRAM witness_prog) 2 witness_start) = ([5; 3], 2) /\
  ram_projection (rc_run (UntiedRAM witness_prog) 2 witness_start) = ([5; 3], 2) /\
  ram_record (rc_run (TiedRAM witness_prog) 2 witness_start) = [(0, 1); (1, 2)] /\
  ram_record (rc_run (UntiedRAM witness_prog) 2 witness_start) = [].
Proof. vm_compute. repeat split. Qed.

Theorem record_axis_separates_ram :
  exists prog s n,
    rc_init (TiedRAM prog) s /\ rc_init (UntiedRAM prog) s /\
    (forall k, ram_projection (rc_run (TiedRAM prog) k s) =
               ram_projection (rc_run (UntiedRAM prog) k s)) /\
    ram_record (rc_run (TiedRAM prog) n s) <>
    ram_record (rc_run (UntiedRAM prog) n s).
Proof.
  exists witness_prog, witness_start, 2.
  split; [split; reflexivity |]. split; [split; reflexivity |].
  split; [intros k; apply tied_untied_same_base_run; reflexivity |].
  destruct witness_run_computed as [_ [_ [Ht Hu]]]. rewrite Ht, Hu. discriminate.
Qed.

Print Assumptions tied_next_record.
Print Assumptions tied_program_records_overwrite.
Print Assumptions tied_record_grows.
Print Assumptions tied_record_driven.
Print Assumptions tied_run_prefix.
Print Assumptions tied_honest_growing.
Print Assumptions tied_threshold_decomposition.
Print Assumptions tied_latch_factorization.
Print Assumptions tied_honest_round4.
Print Assumptions untied_next_record.
Print Assumptions untied_run_record_constant.
Print Assumptions untied_not_honest_growing.
Print Assumptions untied_not_honest_round4.
Print Assumptions untied_trivial_latch.
Print Assumptions tied_untied_same_base_run.
Print Assumptions ram_record_axis_classification.
Print Assumptions witness_run_computed.
Print Assumptions record_axis_separates_ram.
