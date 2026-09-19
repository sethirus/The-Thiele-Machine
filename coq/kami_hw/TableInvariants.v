(** TableInvariants.v: reachable-state invariants of the morph/coupling
    tables, needed as premises by [StepRefineMorph], [StepFaults] and
    [CouplingComposeKami]/[CouplingComposeRetire].

    [hwb_table_invariants] bundles the nine table predicates already named
    in those files. [hwb_table_invariants_reset]: they all hold at the reset
    boundary (the two valid-tables reset to all-false and the two
    pair/descriptor pointers reset to 0/1, so every implication is vacuous
    or a direct value check; closed under the global context beyond the
    two already-documented inherited axioms, [functional_extensionality_dep]
    and [eq_rect_eq]). This is the base case of C1/C2's "reachable-state
    invariants from reset" obligation.

    Preservation across [Retire] (needed to carry the invariants along any
    admitted instruction sequence, C1/C2's "reachable-state invariants from
    reset" obligation) is NOT done here. Scope for the next session:
    [RetireMaster.admitted] has 55 constructors (one per retirement theorem,
    covering 47 opcodes; a few opcodes have more than one constructor for a
    legacy/extended encoding or a success/fault branch). 47 leave every
    field named
    below unchanged: [StepEval.step_keeps_coupling_desc_base_table],
    [_count_table], [_valid_table], [_next_id], [step_keeps_coupling_pair_valid_table]
    and [_next_id] already hold for an arbitrary boundary (any opcode, no case
    split); the morph-table fields ([hw_morph_valid_table], [_next_id],
    [_coupling_desc_table], [_identity_table]) are unchanged for each of the
    38 single-cycle non-morph opcodes by that opcode's own named lemma in
    [StepFields.v] (pattern [step_<op>_morph_valid_table] etc.), and by the
    LASSERT/CHSH_LASSERT FSM files' own frame catalogues for the other two.
    The remaining 8 constructors touch these tables:
    [adm_morph_id]/[adm_morph_id_ext] and [adm_morph_delete]/
    [adm_morph_delete_ext] write exactly the morph-table fields in [step_next]
    (see [StepFieldsMorph.v]'s alloc/delete equations); [adm_morph_ext] and
    [adm_compose_ext] additionally run to [morph_fsm_final]/[compose_fsm_final],
    whose own field equations ([CouplingFsmRun.morph_fsm_run],
    [CouplingComposeRetire]'s analogous compose statement) already give the
    base/count/valid/next_id updates at exactly the current allocation
    pointer, which is what each invariant needs; [adm_morph_ext_fault] and
    [adm_compose_ext_fault] are frame ([CouplingFaults.v]: tables unchanged).
    A tenth invariant, "1 <= coupling_desc_next_id", is needed alongside
    [hwb_coupling_desc_zero_invalid] to know a fresh allocation index is
    never 0; DispatchReset.v's value 1 plus the single "+1" write site
    (mc_commit) gives it directly. *)
Require Import Kami.Kami Kami.Semantics.
From Coq Require Import String List Lia FunctionalExtensionality.
Import ListNotations.
From KamiHW Require Import ThieleTypes ThieleCPUCore HWBoundary HWBoundaryReads
  ActionEvaluator CoreExecution HWBoundaryCompleteness DispatchExecution DispatchReset
  StepFaults StepRefineMorph CouplingComposeKami.
Open Scope string_scope.
Local Open Scope nat_scope.

(** A fresh coupling-descriptor allocation index is never 0: needed
    alongside [hwb_coupling_desc_zero_invalid] so that MORPH_EXT/COMPOSE_EXT
    allocating at [hw_coupling_desc_next_id] never overwrites the reserved
    empty descriptor. Holds at reset ([DispatchReset]'s value 1) and is
    preserved by every opcode ([hw_coupling_desc_next_id] only ever grows,
    at the single "+1" write site in mc_commit). *)
Definition hwb_coupling_desc_next_id_ge1 (b : HWB) : Prop :=
  1 <= wordToNat (hw_coupling_desc_next_id b).

Definition hwb_table_invariants (b : HWB) : Prop :=
  hwb_morph_valid_below_next b /\
  hwb_morph_coupling_refs_ok b /\
  hwb_coupling_desc_zero_invalid b /\
  hwb_coupling_desc_valid_below_next b /\
  hwb_desc_pairs_below_next b /\
  hwb_pairs_valid_below_next b /\
  hwb_desc_zero_empty b /\
  hwb_identity_desc_zero b /\
  hwb_labels_represented b /\
  hwb_coupling_desc_next_id_ge1 b.

Lemma dispatch_reset_state_has_boundary : exists b : HWB, dispatch_reset_state = hwb_regs b.
Proof.
  pose proof (cpu_reset_run_has_boundary 0) as [b Hb].
  cbn [run_cpu_rules fst] in Hb. exact (ex_intro _ b Hb).
Qed.

Lemma hwb_table_invariants_reset : exists b : HWB, hwb_regs b = dispatch_reset_state /\ hwb_table_invariants b.
Proof.
  destruct dispatch_reset_state_has_boundary as [b Hb].
  exists b. split; [symmetry; exact Hb|].
  assert (Vmv : action_read dispatch_reset_state "morph_valid_table"
    (SyntaxKind (Vector Bool MorphTableIdxSz)) = Some (fun _ => false)).
  { vm_compute; f_equal; apply functional_extensionality; intro wv;
    shatter_word wv; repeat match goal with x : bool |- _ => destruct x end; reflexivity. }
  assert (Vcv : action_read dispatch_reset_state "coupling_desc_valid_table"
    (SyntaxKind (Vector Bool CouplingDescIdxSz)) = Some (fun _ => false)).
  { vm_compute; f_equal; apply functional_extensionality; intro wv;
    shatter_word wv; repeat match goal with x : bool |- _ => destruct x end; reflexivity. }
  assert (Vcb : action_read dispatch_reset_state "coupling_desc_base_table"
    (SyntaxKind (Vector (Bit CouplingPairIdxSz) CouplingDescIdxSz)) = Some (fun _ => natToWord _ 0)).
  { vm_compute; f_equal; apply functional_extensionality; intro wv;
    shatter_word wv; repeat match goal with x : bool |- _ => destruct x end; reflexivity. }
  assert (Vcc : action_read dispatch_reset_state "coupling_desc_count_table"
    (SyntaxKind (Vector (Bit CouplingPairCountSz) CouplingDescIdxSz)) = Some (fun _ => natToWord _ 0)).
  { vm_compute; f_equal; apply functional_extensionality; intro wv;
    shatter_word wv; repeat match goal with x : bool |- _ => destruct x end; reflexivity. }
  assert (Vpn : action_read dispatch_reset_state "coupling_pair_next_id"
    (SyntaxKind (Bit DescTableNextIdSz)) = Some (natToWord _ 0)) by (vm_compute; reflexivity).
  assert (Vdn : action_read dispatch_reset_state "coupling_desc_next_id"
    (SyntaxKind (Bit DescTableNextIdSz)) = Some (natToWord _ 1)) by (vm_compute; reflexivity).
  pose proof (hwb_read_morph_valid_table b) as Rmv.
  pose proof (hwb_read_coupling_desc_valid_table b) as Rcv.
  pose proof (hwb_read_coupling_desc_base_table b) as Rcb.
  pose proof (hwb_read_coupling_desc_count_table b) as Rcc.
  pose proof (hwb_read_coupling_pair_next_id b) as Rpn.
  pose proof (hwb_read_coupling_desc_next_id b) as Rdn.
  rewrite <- Hb in Rmv, Rcv, Rcb, Rcc, Rpn, Rdn.
  rewrite Vmv in Rmv. rewrite Vcv in Rcv. rewrite Vcb in Rcb. rewrite Vcc in Rcc. rewrite Vpn in Rpn. rewrite Vdn in Rdn.
  injection Rmv as Emv. injection Rcv as Ecv. injection Rcb as Ecb. injection Rcc as Ecc. injection Rpn as Epn. injection Rdn as Edn.
  symmetry in Emv, Ecv, Ecb, Ecc, Epn, Edn.
  unfold hwb_table_invariants.
  split. { intros i H. rewrite Emv in H. discriminate H. }
  split. { intros i H. rewrite Emv in H. discriminate H. }
  split. { unfold hwb_coupling_desc_zero_invalid. rewrite Ecv. reflexivity. }
  split. { intros i H. rewrite Ecv in H. discriminate H. }
  split. { intros d H. rewrite Ecv in H. discriminate H. }
  split. { intros k H. exfalso. rewrite Epn in H. cbn in H. lia. }
  split. { unfold hwb_desc_zero_empty. split. { rewrite Ecb. reflexivity. } { rewrite Ecc. reflexivity. } }
  split. { intros m H. rewrite Emv in H. discriminate H. }
  split. { intros d H. rewrite Ecv in H. discriminate H. }
  { unfold hwb_coupling_desc_next_id_ge1. rewrite Edn. cbn. lia. }
Qed.
