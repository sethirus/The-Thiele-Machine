(** Lift actual no-call normalization substeps into Kami Step and Multistep.
    This supplies execution composition, not scheduler fairness or the complete
    loop invariant. Multistep labels are stored in reverse execution order. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore NormalizationStart NormalizationSteps.
From Coq Require Import List String.
Import ListNotations.
Open Scope string_scope.
Definition normalization_label (name : string) : LabelT :=
 {| annot := Some (Some name); defs := M.empty _; calls := M.empty _ |}.
Lemma no_call_rule_substep_is_step : forall m old u name,
 Substep m old u (Rle (Some name)) (M.empty _) ->
 Step m old u (normalization_label name).
Proof.
 intros m old u name H.
 pose (s := {| upd := u; unitAnnot := Rle (Some name); cms := M.empty _; substep := H |}).
 assert (HS : Step m old (foldSSUpds [s]) (hide (foldSSLabel [s]))).
 { apply StepIntro.
   - constructor; [constructor|intros x Hin; inversion Hin].
   - unfold wellHidden, hide, foldSSLabel, addLabelLeft, mergeLabel, getSLabel, getLabel, s; simpl.
     rewrite !M.union_empty_L, !M.subtractKV_empty_1. split; apply M.KeysDisj_empty. }
 unfold foldSSUpds, foldSSLabel, addLabelLeft, mergeLabel, getSLabel, getLabel, hide, s in HS; simpl in HS.
 rewrite !M.union_empty_L, !M.subtractKV_empty_1 in HS. exact HS.
Qed.
Lemma normalization_step_extends_execution : forall old current labels u name,
 Multistep thieleCore old current labels ->
 Substep thieleCore current u (Rle (Some name)) (M.empty _) ->
 Multistep thieleCore old (M.union u current) (normalization_label name :: labels).
Proof.
 intros. eapply Multi; [eassumption|]. apply no_call_rule_substep_is_step; assumption.
Qed.
Lemma normalization_substep_execution : forall old u name,
 Substep thieleCore old u (Rle (Some name)) (M.empty _) ->
 Multistep thieleCore old (M.union u old) [normalization_label name].
Proof.
 intros. eapply normalization_step_extends_execution; [constructor; reflexivity|assumption].
Qed.

Lemma normalization_start_actual_step : forall old b e,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 5)) ->
 M.find "mc_write_base" old = Some (reg5 b) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 Step thieleCore old (normalization_start_updates b e)
   (normalization_label "mc_normalize_start").
Proof.
 intros. apply no_call_rule_substep_is_step. eapply normalization_start_actual_substep; eassumption.
Qed.

Theorem normalization_scan_actual_step : forall old i j e dup src dst,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 8)) ->
 M.find "mc_i" old = Some (reg5 i) ->
 M.find "mc_j" old = Some (reg5 j) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 M.find "mc_duplicate" old = Some (regbool dup) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 Step thieleCore old (normalization_scan_updates i j e dup src dst)
   (normalization_label "mc_normalize_scan").
Proof.
 intros. apply no_call_rule_substep_is_step. eapply normalization_scan_actual_substep; eassumption.
Qed.

Theorem normalization_emit_actual_step : forall old i e out dup src dst,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 9)) ->
 M.find "mc_i" old = Some (reg5 i) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 M.find "mc_norm_ptr" old = Some (reg5 out) ->
 M.find "mc_duplicate" old = Some (regbool dup) ->
 M.find "coupling_pair_src_table" old = Some (regpairs src) ->
 M.find "coupling_pair_dst_table" old = Some (regpairs dst) ->
 Step thieleCore old (normalization_emit_updates i e out dup src dst)
   (normalization_label "mc_normalize_emit").
Proof.
 intros. apply no_call_rule_substep_is_step. eapply normalization_emit_actual_substep; eassumption.
Qed.

Theorem normalization_commit_actual_step : forall old b e d bases counts valid,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 11)) ->
 M.find "mc_write_base" old = Some (reg5 b) ->
 M.find "mc_write_ptr" old = Some (reg5 e) ->
 M.find "coupling_desc_next_id" old = Some (reg5 d) ->
 M.find "coupling_desc_base_table" old = Some (regbases bases) ->
 M.find "coupling_desc_count_table" old = Some (regcounts counts) ->
 M.find "coupling_desc_valid_table" old = Some (regvalid valid) ->
 Step thieleCore old (normalization_commit_updates b e d bases counts valid)
   (normalization_label "mc_commit").
Proof.
 intros. apply no_call_rule_substep_is_step. eapply normalization_commit_actual_substep; eassumption.
Qed.

(** Empty raw workspace: two actual rule firings reach phase zero and install
    the empty descriptor. This is an existence trace under typed reads, not a
    fairness claim, reset-reachability proof, or dispatch refinement. *)
Theorem normalization_empty_execution : forall old b d bases counts valid,
 M.find "mc_phase" old = Some (reg4 (natToWord 4 5)) ->
 M.find "mc_write_base" old = Some (reg5 b) ->
 M.find "mc_write_ptr" old = Some (reg5 b) ->
 M.find "coupling_desc_next_id" old = Some (reg5 d) ->
 M.find "coupling_desc_base_table" old = Some (regbases bases) ->
 M.find "coupling_desc_count_table" old = Some (regcounts counts) ->
 M.find "coupling_desc_valid_table" old = Some (regvalid valid) ->
 Multistep thieleCore old
  (M.union (normalization_commit_updates b b d bases counts valid)
    (M.union (normalization_start_updates b b) old))
  [normalization_label "mc_commit"; normalization_label "mc_normalize_start"].
Proof.
 intros old b d bases counts valid Hp Hb He Hd Hbs Hcs Hv.
 eapply normalization_step_extends_execution.
 - apply normalization_substep_execution. apply normalization_start_actual_substep; assumption.
 - apply normalization_commit_actual_substep.
   + rewrite M.find_union. unfold normalization_start_updates.
     repeat rewrite M.find_add_2 by discriminate.
     rewrite M.find_add_1 by reflexivity. destruct (weq b b); [reflexivity|contradiction].
   + rewrite M.find_union. unfold normalization_start_updates.
     repeat rewrite M.find_add_2 by discriminate. rewrite M.find_empty. exact Hb.
   + rewrite M.find_union. unfold normalization_start_updates.
     repeat rewrite M.find_add_2 by discriminate. rewrite M.find_empty. exact He.
   + rewrite M.find_union. unfold normalization_start_updates.
     repeat rewrite M.find_add_2 by discriminate. rewrite M.find_empty. exact Hd.
   + rewrite M.find_union. unfold normalization_start_updates.
     repeat rewrite M.find_add_2 by discriminate. rewrite M.find_empty. exact Hbs.
   + rewrite M.find_union. unfold normalization_start_updates.
     repeat rewrite M.find_add_2 by discriminate. rewrite M.find_empty. exact Hcs.
   + rewrite M.find_union. unfold normalization_start_updates.
     repeat rewrite M.find_add_2 by discriminate. rewrite M.find_empty. exact Hv.
Qed.

Lemma normalization_commit_phase_zero : forall old b e d bases counts valid,
 M.find "mc_phase" (M.union (normalization_commit_updates b e d bases counts valid) old) =
 Some (reg4 (natToWord 4 0)).
Proof.
 intros. rewrite M.find_union. unfold normalization_commit_updates.
 repeat rewrite M.find_add_2 by discriminate. rewrite M.find_add_1 by reflexivity. reflexivity.
Qed.
Lemma normalization_empty_descriptor_count : forall b d counts,
 put_vector counts (pair_index d) (wminus b b) (pair_index d) = natToWord 5 0.
Proof.
 intros. unfold put_vector. destruct (weq (pair_index d) (pair_index d));
 [apply wminus_diag|contradiction].
Qed.
