(** Finite executions of the actual scan rule, including its terminal j=end
    firing. These are selected Kami Multistep traces, not scheduling fairness
    or the outer emit/commit loop. Labels use Kami's reverse trace convention. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart
 NormalizationSteps NormalizationLoop NormalizationExecution.
From Coq Require Import List String Bool Arith Lia.
Import ListNotations.
Open Scope string_scope.

Record scan_registers (st : RegsT) (i j e : nat) (dup : bool) (src dst : PairTable) : Prop := {
 scan_reg_phase : M.find "mc_phase" st = Some (reg4 (natToWord 4 8));
 scan_reg_i : M.find "mc_i" st = Some (reg5 (natToWord 5 i));
 scan_reg_j : M.find "mc_j" st = Some (reg5 (natToWord 5 j));
 scan_reg_end : M.find "mc_write_ptr" st = Some (reg5 (natToWord 5 e));
 scan_reg_dup : M.find "mc_duplicate" st = Some (regbool dup);
 scan_reg_src : M.find "coupling_pair_src_table" st = Some (regpairs src);
 scan_reg_dst : M.find "coupling_pair_dst_table" st = Some (regpairs dst)
}.
Definition scan_accumulated src dst i lo count dup :=
 orb dup (scan_seen src dst i lo count).
Fixpoint scan_prefix_state (src dst : PairTable) (i lo e : nat) (dup : bool)
 (count : nat) (old : RegsT) : RegsT :=
 match count with
 | O => old
 | S n => M.union
     (normalization_scan_updates (natToWord 5 i) (natToWord 5 (lo+n))
       (natToWord 5 e) (scan_accumulated src dst i lo n dup) src dst)
     (scan_prefix_state src dst i lo e dup n old)
 end.
Definition scan_rule_label := normalization_label "mc_normalize_scan".

Lemma scan_prefix_frame : forall src dst i lo e dup count old key,
 ~ In key ["mc_duplicate"; "mc_j"; "mc_phase"] ->
 M.find key (scan_prefix_state src dst i lo e dup count old) = M.find key old.
Proof.
 intros src dst i lo e dup count. induction count; intros old key Hkey; simpl.
 - reflexivity.
 - rewrite normalization_scan_frame by exact Hkey. apply IHcount; exact Hkey.
Qed.

Lemma scan_prefix_registers_advance : forall old src dst i lo e dup n,
 (lo+n<e)%nat -> (e<=16)%nat ->
 scan_registers old i (lo+n) e (scan_accumulated src dst i lo n dup) src dst ->
 scan_registers
  (M.union (normalization_scan_updates (natToWord 5 i) (natToWord 5 (lo+n))
    (natToWord 5 e) (scan_accumulated src dst i lo n dup) src dst) old)
  i (lo+S n) e (scan_accumulated src dst i lo (S n) dup) src dst.
Proof.
 intros old src dst i lo e dup n Hlt He Hregs. destruct Hregs.
 constructor.
 - apply normalization_scan_continues_phase; assumption.
 - rewrite normalization_scan_frame; [assumption|simpl; intuition discriminate].
 - rewrite M.find_union. unfold normalization_scan_updates.
   rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity.
   rewrite <- natToWord_plus. replace (lo+n+1)%nat with (lo+S n)%nat by lia.
   reflexivity.
 - rewrite normalization_scan_frame; [assumption|simpl; intuition discriminate].
 - rewrite M.find_union. unfold normalization_scan_updates.
   rewrite M.find_add_1 by reflexivity. rewrite bounded_word_ltb by lia.
   rewrite (proj2 (Nat.ltb_lt _ _) Hlt). simpl.
   unfold scan_accumulated. rewrite scan_seen_extend, orb_assoc. reflexivity.
 - rewrite normalization_scan_frame; [assumption|simpl; intuition discriminate].
 - rewrite normalization_scan_frame; [assumption|simpl; intuition discriminate].
Qed.

Theorem normalization_scan_prefix_execution : forall src dst i lo e dup count old,
 (lo+count<=e)%nat -> (e<=16)%nat -> scan_registers old i lo e dup src dst ->
 Multistep thieleCore old (scan_prefix_state src dst i lo e dup count old)
   (repeat scan_rule_label count) /\
 scan_registers (scan_prefix_state src dst i lo e dup count old)
   i (lo+count) e (scan_accumulated src dst i lo count dup) src dst.
Proof.
 intros src dst i lo e dup count. induction count as [|n IH]; intros old Hrange He Hregs.
 - simpl. unfold scan_accumulated. rewrite scan_seen_empty, orb_false_r, Nat.add_0_r.
   split; [constructor; reflexivity|assumption].
 - destruct (IH old ltac:(lia) He Hregs) as [Hexec Hreads].
   simpl scan_prefix_state. simpl repeat. split.
   + eapply normalization_step_extends_execution; [exact Hexec|].
     apply normalization_scan_actual_substep; destruct Hreads; assumption.
   + apply scan_prefix_registers_advance; [lia|assumption|exact Hreads].
Qed.

Definition scan_complete_state src dst i lo e dup old :=
 M.union (normalization_scan_updates (natToWord 5 i) (natToWord 5 e)
   (natToWord 5 e) (scan_accumulated src dst i lo (e-lo) dup) src dst)
   (scan_prefix_state src dst i lo e dup (e-lo) old).

Theorem normalization_scan_complete_execution : forall src dst i lo e dup old,
 (lo<=e)%nat -> (e<=16)%nat -> scan_registers old i lo e dup src dst ->
 Multistep thieleCore old (scan_complete_state src dst i lo e dup old)
   (repeat scan_rule_label (S (e-lo))).
Proof.
 intros src dst i lo e dup old Hlo He Hregs.
 destruct (normalization_scan_prefix_execution src dst i lo e dup (e-lo) old
   ltac:(lia) He Hregs) as [Hexec Hreads].
 replace (lo+(e-lo))%nat with e in Hreads by lia.
 unfold scan_complete_state. simpl repeat.
 eapply normalization_step_extends_execution; [exact Hexec|].
 apply normalization_scan_actual_substep; destruct Hreads; assumption.
Qed.

Theorem normalization_scan_complete_phase : forall src dst i lo e dup old,
 (e<=16)%nat ->
 M.find "mc_phase" (scan_complete_state src dst i lo e dup old) =
 Some (reg4 (natToWord 4 9)).
Proof. intros. unfold scan_complete_state. apply normalization_scan_terminal_phase; assumption. Qed.
Theorem normalization_scan_complete_duplicate : forall src dst i lo e dup old,
 (e<=16)%nat ->
 M.find "mc_duplicate" (scan_complete_state src dst i lo e dup old) =
 Some (regbool (orb dup (scan_seen src dst i lo (e-lo)))).
Proof.
 intros. unfold scan_complete_state. rewrite M.find_union.
 unfold normalization_scan_updates. rewrite M.find_add_1 by reflexivity.
 rewrite bounded_word_ltb by lia. rewrite Nat.ltb_irrefl, andb_false_l, orb_false_r.
 reflexivity.
Qed.
Theorem normalization_scan_complete_pointer : forall src dst i lo e dup old,
 M.find "mc_j" (scan_complete_state src dst i lo e dup old) =
 Some (reg5 (natToWord 5 (e+1))).
Proof.
 intros. unfold scan_complete_state. rewrite M.find_union.
 unfold normalization_scan_updates. rewrite M.find_add_2 by discriminate.
 rewrite M.find_add_1 by reflexivity. rewrite <- natToWord_plus. reflexivity.
Qed.
Theorem normalization_scan_complete_frame : forall src dst i lo e dup old key,
 ~ In key ["mc_duplicate"; "mc_j"; "mc_phase"] ->
 M.find key (scan_complete_state src dst i lo e dup old) = M.find key old.
Proof.
 intros. unfold scan_complete_state. rewrite normalization_scan_frame by assumption.
 apply scan_prefix_frame; assumption.
Qed.
Corollary normalization_scan_complete_tables : forall src dst i lo e dup old,
 scan_registers old i lo e dup src dst ->
 M.find "coupling_pair_src_table" (scan_complete_state src dst i lo e dup old) = Some (regpairs src) /\
 M.find "coupling_pair_dst_table" (scan_complete_state src dst i lo e dup old) = Some (regpairs dst).
Proof.
 intros. rewrite !normalization_scan_complete_frame by (simpl; intuition discriminate).
 destruct H. split; assumption.
Qed.

(** The number is of selected actual rule firings, including the terminal
    check. It is not a bound on clock cycles under an arbitrary scheduler. *)
Theorem normalization_scan_complete_firing_count : forall lo e,
 (lo<=e)%nat -> (e<=16)%nat ->
 List.length (repeat scan_rule_label (S (e-lo))) = S (e-lo) /\ (S (e-lo)<=17)%nat.
Proof. intros. rewrite repeat_length. split; [reflexivity|lia]. Qed.
