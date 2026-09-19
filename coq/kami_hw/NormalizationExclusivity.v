(** Necessity of the phase guards in the four actual normalization actions.
    This establishes mutual exclusion in one old register map. It does not
    establish determinism of arbitrary Kami Steps, exclusion of other module
    rules/methods, or a scheduler fairness/no-external-writes contract. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart NormalizationSteps.
From Coq Require Import List String.
Open Scope string_scope.

Lemma normalization_start_requires_phase : forall old u cs,
 SemAction old (attrType normalization_start_rule type) u cs WO ->
 M.find "mc_phase" old = Some (reg4 (natToWord 4 5)).
Proof.
 intros old u cs H. unfold normalization_start_rule in H.
 cbn [nth getRules attrType] in H.
 apply inversionSemAction in H. destruct H as [p [Hread Haction]].
 apply inversionSemAction in Haction. destruct Haction as [_ Hguard].
 change ((if weq p (natToWord 4 5) then true else false) = true) in Hguard.
 destruct (weq p (natToWord 4 5)); [subst; exact Hread|discriminate].
Qed.

Lemma normalization_scan_requires_phase : forall old u cs,
 SemAction old (attrType normalization_scan_rule type) u cs WO ->
 M.find "mc_phase" old = Some (reg4 (natToWord 4 8)).
Proof.
 intros old u cs H. unfold normalization_scan_rule, normalization_rule in H.
 cbn [nth getRules attrType] in H.
 apply inversionSemAction in H. destruct H as [p [Hread Haction]].
 apply inversionSemAction in Haction. destruct Haction as [_ Hguard].
 change ((if weq p (natToWord 4 8) then true else false) = true) in Hguard.
 destruct (weq p (natToWord 4 8)); [subst; exact Hread|discriminate].
Qed.

Lemma normalization_emit_requires_phase : forall old u cs,
 SemAction old (attrType normalization_emit_rule type) u cs WO ->
 M.find "mc_phase" old = Some (reg4 (natToWord 4 9)).
Proof.
 intros old u cs H. unfold normalization_emit_rule, normalization_rule in H.
 cbn [nth getRules attrType] in H.
 apply inversionSemAction in H. destruct H as [p [Hread Haction]].
 apply inversionSemAction in Haction. destruct Haction as [_ Hguard].
 change ((if weq p (natToWord 4 9) then true else false) = true) in Hguard.
 destruct (weq p (natToWord 4 9)); [subst; exact Hread|discriminate].
Qed.

Lemma normalization_commit_requires_phase : forall old u cs,
 SemAction old (attrType normalization_commit_rule type) u cs WO ->
 M.find "mc_phase" old = Some (reg4 (natToWord 4 11)).
Proof.
 intros old u cs H. unfold normalization_commit_rule, normalization_rule in H.
 cbn [nth getRules attrType] in H.
 apply inversionSemAction in H. destruct H as [p [Hread Haction]].
 apply inversionSemAction in Haction. destruct Haction as [_ Hguard].
 change ((if weq p (natToWord 4 11) then true else false) = true) in Hguard.
 destruct (weq p (natToWord 4 11)); [subst; exact Hread|discriminate].
Qed.

(** Tags select existing rule bodies only; this is not another state machine. *)
Inductive normalization_rule_kind :=
| NormalizeStart | NormalizeScan | NormalizeEmit | NormalizeCommit.
Definition normalization_kind_rule (kind : normalization_rule_kind) :=
 match kind with
 | NormalizeStart => normalization_start_rule
 | NormalizeScan => normalization_scan_rule
 | NormalizeEmit => normalization_emit_rule
 | NormalizeCommit => normalization_commit_rule
 end.
Definition normalization_kind_phase (kind : normalization_rule_kind) :=
 match kind with
 | NormalizeStart => 5 | NormalizeScan => 8
 | NormalizeEmit => 9 | NormalizeCommit => 11
 end.
Definition normalization_action_enabled old kind :=
 exists u cs, SemAction old (attrType (normalization_kind_rule kind) type) u cs WO.

Theorem normalization_enabled_requires_phase : forall old kind,
 normalization_action_enabled old kind ->
 M.find "mc_phase" old = Some (reg4 (natToWord 4 (normalization_kind_phase kind))).
Proof.
 intros old kind [u [cs H]]. destruct kind;
 cbn [normalization_kind_rule normalization_kind_phase] in *.
 - eapply normalization_start_requires_phase; eassumption.
 - eapply normalization_scan_requires_phase; eassumption.
 - eapply normalization_emit_requires_phase; eassumption.
 - eapply normalization_commit_requires_phase; eassumption.
Qed.

Definition normalization_register_bit_value (r : sigT (fullType type)) : nat :=
 match r with
 | existT _ (SyntaxKind (Bit n)) w => wordToNat w
 | _ => 0
 end.
Definition normalization_optional_bit_value (r : option (sigT (fullType type))) : nat :=
 match r with Some v => normalization_register_bit_value v | None => 0 end.

Theorem normalization_enabled_unique_kind : forall old first second,
 normalization_action_enabled old first -> normalization_action_enabled old second ->
 first = second.
Proof.
 intros old first second Hfirst Hsecond.
 apply normalization_enabled_requires_phase in Hfirst.
 apply normalization_enabled_requires_phase in Hsecond.
 rewrite Hfirst in Hsecond.
 apply (f_equal normalization_optional_bit_value) in Hsecond.
 destruct first, second; try reflexivity; discriminate Hsecond.
Qed.

Corollary normalization_distinct_actions_mutually_exclusive : forall old first second,
 first <> second -> normalization_action_enabled old first ->
 ~ normalization_action_enabled old second.
Proof.
 intros old first second Hne Hfirst Hsecond. apply Hne.
 eapply normalization_enabled_unique_kind; eassumption.
Qed.
