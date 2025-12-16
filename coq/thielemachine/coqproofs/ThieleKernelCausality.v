(**
  THIELE UNIFICATION — KERNEL CAUSALITY (local influence without spacetime)

  This module turns the remaining “causality/relativity” obligation into a
  purely operational statement: an instruction trace only influences the
  modules it explicitly targets.

  Here we discharge a non-interference / light-cone theorem for the kernel
  VM instruction `instr_pdiscover`.
*)

From Coq Require Import List Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.
From ThieleMachine Require Import ThieleUnificationProtocol.

Module ThieleKernelCausality.

  Definition ModuleID := VMState.ModuleID.

  (** ------------------------------------------------------------------
      State-dependent light-cone (kernel operational influence)

      For opcodes that allocate fresh module IDs (pnew/psplit/pmerge), the
      set of touched modules depends on the current graph state.

      We therefore define influence as a function of (state, instruction).
      This remains purely operational: it is computed from the kernel
      semantics primitives themselves.
      ------------------------------------------------------------------ *)

  Definition instr_targets (s : VMState.VMState) (instr : VMStep.vm_instruction)
    : list ModuleID :=
    match instr with
    | VMStep.instr_pnew region _ =>
        let '(_, mid) := VMState.graph_pnew s.(VMState.vm_graph) region in
        [mid]
    | VMStep.instr_psplit module left_region right_region _ =>
      match VMState.graph_psplit s.(VMState.vm_graph) module left_region right_region with
        | Some (_, left_id, right_id) => [module; left_id; right_id]
        | None => [module]
        end
    | VMStep.instr_pmerge m1 m2 _ =>
        match VMState.graph_pmerge s.(VMState.vm_graph) m1 m2 with
        | Some (_, merged_id) => [m1; m2; merged_id]
        | None => [m1; m2]
        end
    | VMStep.instr_lassert module _ _ _ => [module]
    | VMStep.instr_pdiscover module _ _ => [module]
    | _ => []
    end.

  Fixpoint targets_of_trace (s : VMState.VMState) (trace : list VMStep.vm_instruction)
    : list ModuleID :=
    match trace with
    | [] => []
    | instr :: tl =>
        instr_targets s instr ++
        targets_of_trace (SimulationProof.vm_apply s instr) tl
    end.

  Definition in_light_cone_trace (s : VMState.VMState) (trace : list VMStep.vm_instruction)
    (mid : ModuleID) : Prop :=
    In mid (targets_of_trace s trace).

  Fixpoint pdiscover_targets (trace : list VMStep.vm_instruction) : list ModuleID :=
    match trace with
    | [] => []
    | (VMStep.instr_pdiscover mid _ _ ) :: tl => mid :: pdiscover_targets tl
    | _ :: tl => pdiscover_targets tl
    end.

  Definition in_light_cone (trace : list VMStep.vm_instruction) (mid : ModuleID) : Prop :=
    In mid (pdiscover_targets trace).

  Inductive PDiscoverNot (other : ModuleID) : VMStep.vm_instruction -> Prop :=
  | PD_ok : forall mid evidence cost,
      mid <> other ->
      PDiscoverNot other (VMStep.instr_pdiscover mid evidence cost).

  Fixpoint vm_apply_list (s : VMState.VMState) (trace : list VMStep.vm_instruction)
    : VMState.VMState :=
    match trace with
    | [] => s
    | instr :: tl => vm_apply_list (SimulationProof.vm_apply s instr) tl
    end.

  Theorem no_superluminal_influence_pdiscover_trace :
    forall s trace other,
      Forall (PDiscoverNot other) trace ->
      VMState.graph_lookup (VMState.vm_graph (vm_apply_list s trace)) other =
      VMState.graph_lookup (VMState.vm_graph s) other.
  Proof.
    intros s trace other Hall.
    revert s.
    induction Hall as [|instr tl Hok Htl IH]; intro s; simpl.
    - reflexivity.
    - inversion Hok; subst.
      (* First apply IH to the post-state of the head instruction. *)
      rewrite (IH (SimulationProof.vm_apply s (VMStep.instr_pdiscover mid evidence cost))).
      (* Then show the head pdiscover does not affect [other]. *)
        apply ThieleUnificationProtocol.no_signaling_pdiscover_graph.
      exact H.
  Qed.

  (** ------------------------------------------------------------------
      Graph helper lemmas for pnew/psplit/pmerge
      ------------------------------------------------------------------ *)

  Lemma graph_lookup_add_module_other :
    forall g region axioms g' new_id other,
      VMState.graph_add_module g region axioms = (g', new_id) ->
      other <> new_id ->
      VMState.graph_lookup g' other = VMState.graph_lookup g other.
  Proof.
    intros g region axioms g' new_id other Hadd Hneq.
    unfold VMState.graph_add_module in Hadd.
    inversion Hadd; subst; clear Hadd.
    unfold VMState.graph_lookup.
    simpl.
    destruct (Nat.eqb (VMState.pg_next_id g) other) eqn:Heq.
    - apply Nat.eqb_eq in Heq. subst. contradiction.
    - reflexivity.
  Qed.

  Lemma graph_lookup_remove_modules_other :
    forall modules mid modules' removed other,
      VMState.graph_remove_modules modules mid = Some (modules', removed) ->
      other <> mid ->
      VMState.graph_lookup_modules modules' other = VMState.graph_lookup_modules modules other.
  Proof.
    induction modules as [|[id m] tl IH]; intros mid modules' removed other Hrm Hneq.
    - simpl in Hrm. discriminate Hrm.
    - simpl in Hrm.
      destruct (Nat.eqb id mid) eqn:Heq.
      + inversion Hrm; subst; clear Hrm.
        simpl.
        destruct (Nat.eqb id other) eqn:Heq2; [|reflexivity].
        apply Nat.eqb_eq in Heq2. subst.
        apply Nat.eqb_eq in Heq. subst.
        contradiction.
      + destruct (VMState.graph_remove_modules tl mid) as [[tl' removed']|] eqn:Htl;
          try discriminate.
        inversion Hrm; subst; clear Hrm.
        simpl.
        destruct (Nat.eqb id other) eqn:Heq2.
        * reflexivity.
        * eapply IH; eauto.
  Qed.

  Lemma graph_lookup_remove_other :
    forall g mid g' removed other,
      VMState.graph_remove g mid = Some (g', removed) ->
      other <> mid ->
      VMState.graph_lookup g' other = VMState.graph_lookup g other.
  Proof.
    intros g mid g' removed other Hrm Hneq.
    unfold VMState.graph_remove in Hrm.
    destruct (VMState.graph_remove_modules (VMState.pg_modules g) mid)
      as [[modules' removed']|] eqn:Hmods; try discriminate.
    inversion Hrm; subst; clear Hrm.
    unfold VMState.graph_lookup.
    simpl.
    eapply graph_lookup_remove_modules_other; eauto.
  Qed.

  Lemma graph_pnew_lookup_other :
    forall g region g' mid other,
      VMState.graph_pnew g region = (g', mid) ->
      other <> mid ->
      VMState.graph_lookup g' other = VMState.graph_lookup g other.
  Proof.
    intros g region g' mid other Hpnew Hneq.
    unfold VMState.graph_pnew in Hpnew.
    destruct (VMState.graph_find_region g (VMState.normalize_region region)) as [existing|] eqn:Hfind.
    - inversion Hpnew; subst; clear Hpnew.
      reflexivity.
    - eapply graph_lookup_add_module_other; eauto.
  Qed.

  Lemma graph_psplit_lookup_other :
    forall g mid left right g' left_id right_id other,
      VMState.graph_psplit g mid left right = Some (g', left_id, right_id) ->
      other <> mid ->
      other <> left_id ->
      other <> right_id ->
      VMState.graph_lookup g' other = VMState.graph_lookup g other.
  Proof.
    intros g mid left_region right_region g' left_id right_id other Hps Hmid Hleft Hright.
    unfold VMState.graph_psplit in Hps.
    destruct (VMState.graph_lookup g mid) as [m|] eqn:Hlookup; try discriminate.
    (* Split on the exact boolean that appears in [Hps]. *)
    match goal with
    | H : (if ?b then _ else _) = _ |- _ => destruct b eqn:Hempty
    end.
    - (* empty-side branch *)
      cbv zeta in Hps.
      destruct (VMState.graph_add_module g [] []) as [g_empty empty_id] eqn:Hadd.
      cbn in Hps.
      inversion Hps; subst g' left_id right_id; clear Hps.
      eapply (graph_lookup_add_module_other g [] [] g_empty empty_id other Hadd).
      exact Hright.
    - (* non-empty branch *)
      cbv zeta in Hps.
      (* Split on partition_valid (the next conditional in the definition). *)
      match goal with
      | H : (if ?b then _ else _) = _ |- _ => destruct b eqn:Hvalid
      end.
      + cbv zeta in Hps.
        destruct (VMState.graph_remove g mid) as [[g_removed removed]|] eqn:Hrm; try discriminate.
        destruct (VMState.graph_add_module g_removed (VMState.normalize_region left_region) (VMState.module_axioms m))
          as [g_left lid] eqn:HaddL.
        destruct (VMState.graph_add_module g_left (VMState.normalize_region right_region) (VMState.module_axioms m))
          as [g_right rid] eqn:HaddR.
        cbn in Hps.
        inversion Hps; subst g' left_id right_id; clear Hps.
        rewrite (graph_lookup_add_module_other g_left (VMState.normalize_region right_region) (VMState.module_axioms m)
                  g_right rid other HaddR) by exact Hright.
        rewrite (graph_lookup_add_module_other g_removed (VMState.normalize_region left_region) (VMState.module_axioms m)
                  g_left lid other HaddL) by exact Hleft.
        eapply graph_lookup_remove_other; eauto.
      + cbv zeta in Hps. discriminate.
  Qed.

  Lemma graph_pmerge_lookup_other :
    forall g m1 m2 g' merged_id other,
      VMState.graph_pmerge g m1 m2 = Some (g', merged_id) ->
      other <> m1 ->
      other <> m2 ->
      other <> merged_id ->
      VMState.graph_lookup g' other = VMState.graph_lookup g other.
  Proof.
    intros g m1 m2 g' merged_id other Hpm Hm1 Hm2 Hm3.
    unfold VMState.graph_pmerge in Hpm.
    destruct (Nat.eqb m1 m2) eqn:Heq in Hpm; try discriminate.
    destruct (VMState.graph_remove g m1) as [[g_wo_m1 mod1]|] eqn:Hrm1 in Hpm; try discriminate.
    destruct (VMState.graph_remove g_wo_m1 m2) as [[g_wo_both mod2]|] eqn:Hrm2 in Hpm; try discriminate.
    destruct (negb (VMState.nat_list_disjoint (VMState.module_region mod1) (VMState.module_region mod2)))
      eqn:Hdisj in Hpm; try discriminate.

    (* Expose the let-bound [union] and [combined_axioms] inside [Hpm]. *)
    cbv zeta in Hpm.
    set (union := VMState.nat_list_union (VMState.module_region mod1) (VMState.module_region mod2)) in Hpm.
    set (combined_axioms := VMState.module_axioms mod1 ++ VMState.module_axioms mod2) in Hpm.

    destruct (VMState.graph_find_region g_wo_both union) as [existing|] eqn:Hfind in Hpm.
    - destruct (VMState.graph_lookup g_wo_both existing) as [existing_mod|] eqn:Hex in Hpm; try discriminate.
      cbv zeta in Hpm.
      inversion Hpm; subst g' merged_id; clear Hpm.
      assert (existing <> other) as Hneq.
      { intro Heq'. apply Hm3. symmetry. exact Heq'. }
      rewrite (ThieleUnificationProtocol.graph_lookup_update_other
                g_wo_both existing other
                {| VMState.module_region := VMState.module_region existing_mod;
                   VMState.module_axioms := VMState.module_axioms existing_mod ++ combined_axioms |}
                Hneq).
      rewrite (graph_lookup_remove_other g_wo_m1 m2 g_wo_both mod2 other Hrm2 Hm2).
      rewrite (graph_lookup_remove_other g m1 g_wo_m1 mod1 other Hrm1 Hm1).
      reflexivity.
    - destruct (VMState.graph_add_module g_wo_both union combined_axioms) as [g_added new_id] eqn:Hadd in Hpm.
      cbv zeta in Hpm.
      inversion Hpm; subst g' merged_id; clear Hpm.
      rewrite (graph_lookup_add_module_other g_wo_both union combined_axioms g_added new_id other Hadd)
        by exact Hm3.
      rewrite (graph_lookup_remove_other g_wo_m1 m2 g_wo_both mod2 other Hrm2 Hm2).
      rewrite (graph_lookup_remove_other g m1 g_wo_m1 mod1 other Hrm1 Hm1).
      reflexivity.
  Qed.

  (** ------------------------------------------------------------------
      Single-step non-interference and trace theorem
      ------------------------------------------------------------------ *)

  Theorem no_influence_step_graph_lookup :
    forall s instr other,
      ~ In other (instr_targets s instr) ->
      VMState.graph_lookup (VMState.vm_graph (SimulationProof.vm_apply s instr)) other =
      VMState.graph_lookup (VMState.vm_graph s) other.
  Proof.
    intros s instr other Hnotin.
    destruct instr as
      [ region mu_pnew
      | mod_split left right mu_psplit
      | m1 m2 mu_pmerge
      | mod_assert formula cert mu_lassert
      | cert1 cert2 mu_ljoin
      | mod_mdlacc mu_mdlacc
      | mod_disc evidence mu_pdiscover
      | dst_xfer src_xfer mu_xfer
      | payload_pyexec mu_pyexec
      | dst_xor_load addr_xor_load mu_xor_load
      | dst_xor_add src_xor_add mu_xor_add
      | a_xor_swap b_xor_swap mu_xor_swap
      | dst_xor_rank src_xor_rank mu_xor_rank
      | mod_emit payload_emit mu_emit
      | mod_reveal bits_reveal cert_reveal mu_reveal
      | payload_oracle mu_oracle
      | mu_halt
      ]; simpl in *.
    - (* pnew *)
      destruct (VMState.graph_pnew (VMState.vm_graph s) region) as [g' mid] eqn:Hpnew.
      simpl in Hnotin.
      assert (other <> mid) as Hneq.
      { intro Heq; subst. apply Hnotin. simpl. left. reflexivity. }
      eapply graph_pnew_lookup_other; eauto.
    - (* psplit *)
      destruct (VMState.graph_psplit (VMState.vm_graph s) mod_split left right) as [[[g' lid] rid]|] eqn:Hps.
      + simpl in Hnotin.
        assert (other <> mod_split) as Hm.
        { intro Heq; subst. apply Hnotin. simpl. left. reflexivity. }
        assert (other <> lid) as Hl.
        { intro Heq; subst. apply Hnotin. simpl. right. left. reflexivity. }
        assert (other <> rid) as Hr.
        { intro Heq; subst. apply Hnotin. simpl. right. right. left. reflexivity. }
        eapply graph_psplit_lookup_other; eauto.
      + simpl in Hnotin.
        (* Failure branch: graph unchanged. *)
        reflexivity.
    - (* pmerge *)
      destruct (VMState.graph_pmerge (VMState.vm_graph s) m1 m2) as [[g' merged]|] eqn:Hpm.
      + simpl in Hnotin.
        assert (other <> m1) as H1.
        { intro Heq; subst. apply Hnotin. simpl. left. reflexivity. }
        assert (other <> m2) as H2.
        { intro Heq; subst. apply Hnotin. simpl. right. left. reflexivity. }
        assert (other <> merged) as H3.
        { intro Heq; subst. apply Hnotin. simpl. right. right. left. reflexivity. }
        eapply graph_pmerge_lookup_other; eauto.
      + (* Failure branch: graph unchanged. *)
        reflexivity.
    - (* lassert *)
      simpl in Hnotin.
      assert (mod_assert <> other) as Hneq.
      { intro Heq; subst. apply Hnotin. simpl. left. reflexivity. }
      destruct cert as [proof|model]; simpl.
      + destruct (VMStep.check_lrat formula proof); reflexivity.
      + destruct (VMStep.check_model formula model) eqn:Hcheck; [|reflexivity].
        (* Successful sat branch: graph_add_axiom touches only [module]. *)
        apply ThieleUnificationProtocol.graph_add_axiom_other_unchanged.
        exact Hneq.
    - (* ljoin *)
      destruct (String.eqb cert1 cert2); reflexivity.
    - (* mdlacc *)
      reflexivity.
    - (* pdiscover *)
      simpl in Hnotin.
      assert (mod_disc <> other) as Hneq.
      { intro Heq; subst. apply Hnotin. simpl. left. reflexivity. }
      eapply (ThieleUnificationProtocol.no_signaling_pdiscover_graph s mod_disc evidence mu_pdiscover other).
      exact Hneq.
    - (* xfer *)
      reflexivity.
    - (* pyexec *)
      reflexivity.
    - (* xor_load *)
      reflexivity.
    - (* xor_add *)
      reflexivity.
    - (* xor_swap *)
      reflexivity.
    - (* xor_rank *)
      reflexivity.
    - (* emit *)
      reflexivity.
    - (* reveal *)
      reflexivity.
    - (* oracle_halts *)
      reflexivity.
    - (* halt *)
      reflexivity.
  Qed.

  Theorem no_superluminal_influence_trace :
    forall s trace other,
      ~ in_light_cone_trace s trace other ->
      VMState.graph_lookup (VMState.vm_graph (vm_apply_list s trace)) other =
      VMState.graph_lookup (VMState.vm_graph s) other.
  Proof.
    intros s trace.
    revert s.
    induction trace as [|instr tl IH]; intro s; intro other; simpl.
    - intros _. reflexivity.
    - intro Hnotin.
      assert (~ In other (instr_targets s instr) /\
              ~ in_light_cone_trace (SimulationProof.vm_apply s instr) tl other)
        as [Hnotin_head Hnotin_tail].
      {
        split.
        - intro Hin.
          apply Hnotin.
          simpl.
          apply in_app_iff.
          left; exact Hin.
        - intro Hin.
          apply Hnotin.
          simpl.
          apply in_app_iff.
          right; exact Hin.
      }
      rewrite (IH (SimulationProof.vm_apply s instr) other Hnotin_tail).
      apply no_influence_step_graph_lookup.
      exact Hnotin_head.
  Qed.

End ThieleKernelCausality.
