(** Actual normalization-start action from getRules thieleCore.
    This proves one real FSM substep, including its exact update map and
    empty method-call map. It is an intermediate retirement-proof dependency,
    not a proof of scan/compaction, dispatch admission, or eventual retirement.
    The rule-name and membership lemmas guard the concrete list selection. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore.
From Coq Require Import List String.
Import ListNotations.
Open Scope string_scope.
Definition normalization_start_rule := nth 7 (getRules thieleCore) {| attrName := "unused"; attrType := fun ty => Return (Const ty (natToWord 0 0)) |}.
Definition normalization_start_action := attrType normalization_start_rule type.
Definition reg5 (v : word 5) := existT (fullType type) (SyntaxKind (Bit 5)) v.
Definition reg4 (v : word 4) := existT (fullType type) (SyntaxKind (Bit 4)) v.
Definition regbool (v : bool) := existT (fullType type) (SyntaxKind Bool) v.
Definition normalization_start_updates (b e : word 5) : UpdatesT :=
 M.add "mc_i" (reg5 b)
 (M.add "mc_j" (reg5 (wplus b (natToWord 5 1)))
 (M.add "mc_norm_ptr" (reg5 b)
 (M.add "mc_duplicate" (regbool false)
 (M.add "mc_phase" (reg4 (if weq b e then natToWord 4 11 else natToWord 4 8)) (M.empty _))))).
Lemma normalization_start_rule_name : attrName normalization_start_rule = "mc_normalize_start".
Proof. reflexivity. Qed.
Lemma normalization_start_actual_action : forall old b e,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 5)) ->
 M.find "mc_write_base" old = Some (reg5 b) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 SemAction old normalization_start_action (normalization_start_updates b e) (M.empty _) WO.
Proof.
 intros old b e Hphase Hbase Hend.
 unfold normalization_start_action, normalization_start_rule.
 cbn [nth getRules attrType].
 eapply SemReadReg; [exact Hphase|].
 apply SemAssertTrue; [reflexivity|].
 eapply SemReadReg; [exact Hbase|].
 eapply SemReadReg; [exact Hend|].
 unfold normalization_start_updates.
 do 4 (eapply SemWriteReg; [shelve|reflexivity|]).
 eapply SemWriteReg; [shelve| |apply SemReturn; reflexivity].
 cbn [evalExpr evalConstT isEq DescTableNextIdSz].
 change (M.add "mc_phase" (reg4 (if weq b e then natToWord 4 11 else natToWord 4 8)) (M.empty _) =
 M.add "mc_phase" (reg4 (if (if weq b e then true else false) then natToWord 4 11 else natToWord 4 8)) (M.empty _)).
 destruct (weq b e); reflexivity.
 Unshelve. all: reflexivity.
Qed.
Lemma normalization_start_rule_in : In normalization_start_rule (getRules thieleCore).
Proof.
 unfold normalization_start_rule. apply nth_In.
 change (7 < 12)%nat. repeat constructor.
Qed.
Lemma normalization_start_actual_substep : forall old b e,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 5)) ->
 M.find "mc_write_base" old = Some (reg5 b) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 Substep thieleCore old (normalization_start_updates b e)
   (Rle (Some "mc_normalize_start")) (M.empty _).
Proof.
 intros old b e Hp Hb He.
 eapply SingleRule with (a := attrType normalization_start_rule).
 - exact normalization_start_rule_in.
 - apply normalization_start_actual_action; assumption.
Qed.
Print normalization_start_updates.
