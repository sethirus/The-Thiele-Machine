(** PermanentCertification: on a finite machine, a certificate that can never
    be revoked is switched on only by a step that merges states.

    Setting: any state type with a finite enumeration, any instruction type,
    any step function, any yes/no certification reading.

    Permanence: no step ever switches the reading off.

    Conclusion: the step that switches it on is not injective. Some other
    state lands where the switching state lands, so the step forgets which
    of the two it came from. Merging two computation paths is the event
    Landauer's principle charges for.

    Three consequences follow.

    - A2 is derived. If every merging step costs at least one, every
      certification flip costs at least one, and the system is a
      [CertificationSystem] with no A2 premise supplied by hand.
    - A quantitative floor. A step that switches on k distinct states
      collapses at least k states: its image is at least k smaller than its
      domain.
    - Honest erasure accounting agrees with A2. The trusted erasure system
      of [CommitmentVsErasure] certifies at cost zero only because its
      erasure flag reports no erasure on a step that merges two states.
      Once the flag reports every merge, the two laws send the same bill
      for a permanent certificate on a finite machine.

    Each premise is needed. Unbounded memory lets a step keep its history
    and stay injective. A revocable certificate can be switched on by a
    bijection. A free merging step certifies at cost zero. The
    counterexamples at the end of the file are those three.

    Scope. The premise that merging steps cost at least one is Landauer's
    principle stated on the logic: it is a named premise here, not a
    theorem about heat. A machine with an unbounded ledger is not an
    instance: its state space is infinite. [FiniteCertMachine] gives a
    finite machine that is one. The theorem is about a permanent
    certificate on a finite machine. *)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Logic.FinFun.
Import ListNotations.

From Kernel Require Import UniversalCertificationCost.
From Kernel Require Import CommitmentVsErasure.

Section PermanentCertification.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cert : S -> bool.

(** The state space is finite: a duplicate-free list names every state. *)
Definition finite_states (all : list S) : Prop :=
  NoDup all /\ forall s, In s all.

(** Once certified, always certified. *)
Definition permanent : Prop :=
  forall s i, cert s = true -> cert (step s i) = true.

(** The step for one instruction forgets nothing. *)
Definition step_injective (i : I) : Prop :=
  forall a b, step a i = step b i -> a = b.

(** The certified states, as a list. *)
Definition certified_states (all : list S) : list S :=
  filter (fun t => cert t) all.

Lemma certified_states_spec :
  forall all,
    finite_states all ->
    forall t, In t (certified_states all) <-> cert t = true.
Proof.
  intros all [_ Hall] t. unfold certified_states. rewrite filter_In. split.
  - intros [_ H]. exact H.
  - intro H. split; [apply Hall | exact H].
Qed.

Lemma certified_states_nodup :
  forall all, finite_states all -> NoDup (certified_states all).
Proof.
  intros all [Hnd _]. apply NoDup_filter. exact Hnd.
Qed.

(** Under permanence, the step for any instruction sends certified states to
    certified states. *)
Lemma permanent_image_incl :
  permanent ->
  forall all i,
    finite_states all ->
    incl (map (fun t => step t i) (certified_states all))
         (certified_states all).
Proof.
  intros Hperm all i Hfin y Hy.
  apply in_map_iff in Hy as [x [<- Hx]].
  apply (certified_states_spec all Hfin).
  apply (certified_states_spec all Hfin) in Hx.
  apply Hperm. exact Hx.
Qed.

(** The core theorem. A step that switches a permanent certificate on is not
    injective. If it were, it would permute the certified states among
    themselves, leaving no certified landing place for an uncertified
    state. *)
Theorem permanent_flip_is_not_injective :
  forall all s i,
    finite_states all ->
    permanent ->
    cert s = false ->
    cert (step s i) = true ->
    ~ step_injective i.
Proof.
  intros all s i Hfin Hperm Hs Hflip Hinj.
  set (L := certified_states all).
  set (f := fun t => step t i).
  assert (HndM : NoDup (map f L)).
  { apply Injective_map_NoDup; [ | apply certified_states_nodup; exact Hfin].
    intros a b Hab. apply Hinj. exact Hab. }
  assert (Hback : incl L (map f L)).
  { apply NoDup_length_incl;
      [exact HndM | rewrite map_length; lia
      | apply permanent_image_incl; assumption]. }
  assert (Hfs : In (f s) (map f L)).
  { apply Hback. apply (certified_states_spec all Hfin). exact Hflip. }
  apply in_map_iff in Hfs as [c [Hc HcL]].
  apply Hinj in Hc. subst c.
  apply (certified_states_spec all Hfin) in HcL.
  rewrite Hs in HcL. discriminate.
Qed.

(** The quantitative form. Let [F] be distinct uncertified states that one
    instruction switches on. The step sends the certified states together
    with [F] into the certified states, so the number of distinct images is
    at most the number of certified states. The step therefore collapses at
    least [length F] states. Decidable equality is used only to count
    distinct images. *)
Theorem permanent_flips_collapse_at_least :
  forall (eq_dec : forall a b : S, {a = b} + {a <> b}) all i F,
    finite_states all ->
    permanent ->
    NoDup F ->
    (forall s, In s F -> cert s = false /\ cert (step s i) = true) ->
    length (F ++ certified_states all)
      >= length (nodup eq_dec (map (fun t => step t i)
                                   (F ++ certified_states all)))
         + length F.
Proof.
  intros eq_dec all i F Hfin Hperm HndF HF.
  set (L := certified_states all).
  set (f := fun t => step t i).
  assert (Himg : incl (nodup eq_dec (map f (F ++ L))) L).
  { intros y Hy. apply nodup_In in Hy.
    apply in_map_iff in Hy as [x [<- Hx]].
    apply in_app_or in Hx as [HxF | HxL].
    - apply (certified_states_spec all Hfin). apply HF. exact HxF.
    - apply (permanent_image_incl Hperm all i Hfin).
      apply in_map. exact HxL. }
  assert (Hle : length (nodup eq_dec (map f (F ++ L))) <= length L).
  { apply NoDup_incl_length; [apply NoDup_nodup | exact Himg]. }
  rewrite app_length. lia.
Qed.

(** Landauer's premise stated on the logic alone: an instruction whose step
    merges two states costs at least one. *)
Variable cost : I -> nat.

Definition merging_steps_priced : Prop :=
  forall i, ~ step_injective i -> cost i >= 1.

(** A2, the rule [cs_cert_costs] asks a [CertificationSystem] for: a step
    that switches the certificate on costs at least one. *)
Definition a2_holds : Prop :=
  forall s i, cert s = false -> cert (step s i) = true -> cost i >= 1.

(** A2 is a consequence. The price premise speaks only of merging steps; the
    permanent-flip theorem is what makes every certifying step one of them. *)
Theorem a2_from_merging_price_and_permanence :
  forall all,
    finite_states all ->
    permanent ->
    merging_steps_priced ->
    a2_holds.
Proof.
  intros all Hfin Hperm Hprice s i Hs Hflip.
  apply Hprice. eapply permanent_flip_is_not_injective; eauto.
Qed.

End PermanentCertification.

Arguments finite_states {S}.
Arguments permanent {S I}.
Arguments step_injective {S I}.
Arguments merging_steps_priced {S I}.
Arguments a2_holds {S I}.

(** Package the derived A2 as a [CertificationSystem]. The record's A2 field
    is discharged by the theorem above, not supplied as a premise. *)
Definition certification_system_from_merging_price
    (S I : Type) (step : S -> I -> S) (cost : I -> nat) (cert : S -> bool)
    (all : list S)
    (Hfin : finite_states all)
    (Hperm : permanent step cert)
    (Hprice : merging_steps_priced step cost) : CertificationSystem :=
  {| cs_state := S;
     cs_instr := I;
     cs_step := step;
     cs_cost := cost;
     cs_cert := cert;
     cs_cert_costs :=
       a2_from_merging_price_and_permanence S I step cert cost all
         Hfin Hperm Hprice |}.

(** The trace-level floor follows from [universal_nfi_any_substrate]. *)
Theorem permanent_certification_trace_floor :
  forall (S I : Type) (step : S -> I -> S) (cost : I -> nat) (cert : S -> bool)
         (all : list S)
         (Hfin : finite_states all)
         (Hperm : permanent step cert)
         (Hprice : merging_steps_priced step cost)
         (trace : list I) (s0 : S),
    cert s0 = false ->
    cert (cs_run (certification_system_from_merging_price
                    S I step cost cert all Hfin Hperm Hprice) trace s0) = true ->
    cs_total_cost (certification_system_from_merging_price
                     S I step cost cert all Hfin Hperm Hprice) trace >= 1.
Proof.
  intros S I step cost cert all Hfin Hperm Hprice trace s0 H0 H1.
  exact (universal_nfi_any_substrate
           (certification_system_from_merging_price
              S I step cost cert all Hfin Hperm Hprice) trace s0 H0 H1).
Qed.

(** Honest erasure accounting: the erasure flag reports every instruction
    whose step merges two states. *)
Definition honest_erasure (TE : TrustedErasureAccountingSystem) : Prop :=
  forall i, ~ step_injective (tea_step TE) i ->
            exists s, tea_erases TE s i = true.

(** Under honest erasure accounting, a finite machine with a permanent
    certificate satisfies A2. The erasure law and the A2 law send the same
    bill for the certification flip. *)
Theorem honest_erasure_accounting_implies_a2 :
  forall (TE : TrustedErasureAccountingSystem) (all : list (tea_state TE)),
    finite_states all ->
    permanent (tea_step TE) (tea_cert TE) ->
    honest_erasure TE ->
    forall s i,
      tea_cert TE s = false ->
      tea_cert TE (tea_step TE s i) = true ->
      tea_cost TE i >= 1.
Proof.
  intros TE all Hfin Hperm Hhon s i Hs Hflip.
  destruct (Hhon i (permanent_flip_is_not_injective _ _ _ _ all s i
                      Hfin Hperm Hs Hflip)) as [t Ht].
  exact (tea_erasure_costs TE t i Ht).
Qed.

(** The rival system in [CommitmentVsErasure] is finite and its certificate
    is permanent. Its certifying step sends both states to [true], a merge,
    and its erasure flag reports no erasure there. That is how it certifies at
    cost zero. *)
Theorem commit_without_erasure_system_is_not_honest :
  ~ honest_erasure commit_without_erasure_system.
Proof.
  intro Hhon.
  assert (Hmerge : ~ step_injective (tea_step commit_without_erasure_system) tt).
  { intro Hinj. specialize (Hinj false true eq_refl). discriminate. }
  destruct (Hhon tt Hmerge) as [s Hs]. discriminate.
Qed.

Lemma commit_without_erasure_system_finite_permanent :
  finite_states (S := tea_state commit_without_erasure_system) [false; true] /\
  permanent (tea_step commit_without_erasure_system)
            (tea_cert commit_without_erasure_system).
Proof.
  split.
  - split.
    + repeat constructor; simpl; intuition discriminate.
    + intro s. destruct s; simpl; auto.
  - intros s i _. reflexivity.
Qed.

(** Each premise is needed. *)

(** Drop finiteness: keep the whole history. Every step is injective, the
    certificate is permanent, and it still switches on at cost zero. This is
    the history-lift escape, and it needs unbounded memory. *)
Definition history_step (h : list bool) (_ : unit) : list bool := true :: h.
Definition history_cert (h : list bool) : bool :=
  match h with [] => false | _ => true end.

(* SAFE: four facts about the two-line history machine above, each closed
   by computation. *)
Theorem unbounded_history_escapes :
  step_injective history_step tt /\
  permanent history_step history_cert /\
  history_cert [] = false /\
  history_cert (history_step [] tt) = true.
Proof.
  repeat split.
  - intros a b H. inversion H. reflexivity.
Qed.

(** Drop permanence: negation on one bit is a bijection and switches the
    reading on. It also switches it off again. *)
Definition flip_step (b : bool) (_ : unit) : bool := negb b.

Theorem revocable_certificate_escapes :
  step_injective flip_step tt /\
  flip_step false tt = true /\
  flip_step true tt = false.
Proof.
  repeat split.
  intros a b H. destruct a, b; simpl in H; congruence.
Qed.

(** A two-state stamp. A blank sheet or a stamped one; the one instruction
    stamps whatever sheet it is handed. *)
Inductive Sheet := Blank | Stamped.

Definition stamped (x : Sheet) : bool :=
  match x with Blank => false | Stamped => true end.

Definition stamp_step (_ : Sheet) (_ : unit) : Sheet := Stamped.

Lemma sheets_finite : finite_states [Blank; Stamped].
Proof.
  split.
  - repeat constructor; simpl; intuition discriminate.
  - intro x. destruct x; simpl; auto.
Qed.

Lemma stamp_is_permanent : permanent stamp_step stamped.
Proof. intros x i _. reflexivity. Qed.

(** The premises hold together. The stamp, charged one, is finite, permanent,
    and prices its merge. *)
Theorem priced_reset_satisfies_premises :
  finite_states [Blank; Stamped] /\
  permanent stamp_step stamped /\
  merging_steps_priced stamp_step (fun (_ : unit) => 1).
Proof.
  split; [exact sheets_finite | split; [exact stamp_is_permanent | ]].
  intros i _. unfold ge. apply le_n.
Qed.

(** Drop the merging price: the stamp is finite and permanent, it switches
    the certificate on, and at cost zero A2 fails. *)
Theorem free_merge_escapes :
  finite_states [Blank; Stamped] /\
  permanent stamp_step stamped /\
  ~ a2_holds stamp_step stamped (fun (_ : unit) => 0).
Proof.
  split; [exact sheets_finite | split; [exact stamp_is_permanent | ]].
  intro Ha2. specialize (Ha2 Blank tt eq_refl eq_refl). inversion Ha2.
Qed.
