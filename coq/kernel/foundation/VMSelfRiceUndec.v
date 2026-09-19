(** VMSelfRiceUndec.v: Rice's theorem for the self-interpreted unbounded
    model, its dual orientation, deciders realized by guest programs, and two
    named unbounded predicates.  The transformer and its behaviour are in
    [VMSelfRice]. *)

From Coq Require Import Arith Lia List Bool.
From Coq Require Import Logic.ConstructiveEpsilon.
Import ListNotations.
From Kernel Require Import VMSelfGuest VMSelfRun VMSelfRice.
From Kernel Require Import MM2ComplementUndec.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.TM Require SBTM.

Unset Implicit Arguments.

(** * 7. Rice's theorem for the self-interpreted model. *)

Definition g_extensional (Pr : list GInstr -> Prop) : Prop :=
  forall p q, g_wf_program p -> g_wf_program q -> g_equiv p q -> Pr p -> Pr q.

Lemma g_equiv_sym : forall p q, g_equiv p q -> g_equiv q p.
Proof. intros p q H x g mu. symmetry. apply H. Qed.

(** A never-terminating program is excluded by [Pr]; some well-formed
    program satisfies it.  The complement of MM2 halting reduces to the
    complement of [Pr] restricted to well-formed programs. *)
Theorem self_rice : forall (Pr : list GInstr -> Prop) (w : list GInstr),
  g_extensional Pr -> g_wf_program w -> Pr w -> ~ Pr g_bottom ->
  undecidable (fun p => g_wf_program p /\ Pr p).
Proof.
  intros Pr w Hext Hw Hpw Hbot.
  apply undecidability_from_complement.
  apply (undecidability_from_reducibility MM2_HALTING_compl_undec).
  exists (fun pm => rice_prog pm w). intro pm. split.
  - intros Hnh (Hwf & Hpr). apply Hbot.
    apply (Hext (rice_prog pm w) g_bottom Hwf g_bottom_wf); [|exact Hpr].
    intros x g mu. split.
    + intro Hb. exfalso. exact (Hnh (rice_prog_nonhalting pm w x g mu Hb)).
    + intro Hb. exfalso. exact (g_bottom_beh x g mu Hb).
  - intros Hn Hh. apply Hn. split; [apply rice_prog_wf, Hw|].
    apply (Hext w (rice_prog pm w) Hw (rice_prog_wf pm w Hw)); [|exact Hpw].
    apply g_equiv_sym, rice_prog_halting; assumption.
Qed.

Lemma g_wf_dec : forall i, {g_wf i} + {~ g_wf i}.
Proof.
  intro i. unfold g_wf.
  destruct (lt_dec (g_dst i) 4), (lt_dec (g_rs1 i) 4), (lt_dec (g_rs2 i) 4), (lt_dec (g_cost i) 256);
    (left; tauto) || (right; tauto).
Qed.

Lemma g_wf_program_dec : forall p, {g_wf_program p} + {~ g_wf_program p}.
Proof.
  induction p as [|i r IH]; [left; constructor|].
  destruct (g_wf_dec i) as [Hi|Hi]; [|right; intro H; inversion H; contradiction].
  destruct IH as [Hr|Hr]; [left; constructor; assumption|right; intro H; inversion H; contradiction].
Qed.

(** The other orientation: the never-terminating program satisfies [Pr]
    and some well-formed program does not. *)
Corollary self_rice_dual : forall (Pr : list GInstr -> Prop) (w : list GInstr),
  g_extensional Pr -> g_wf_program w -> ~ Pr w -> Pr g_bottom ->
  undecidable (fun p => g_wf_program p /\ Pr p).
Proof.
  intros Pr w Hext Hw Hpw Hbot Hdec.
  apply (@self_rice (fun p => ~ Pr p) w).
  - intros p q Hp Hq Hpq Hnp Hq'. apply Hnp. exact (Hext q p Hq Hp (g_equiv_sym _ _ Hpq) Hq').
  - exact Hw.
  - exact Hpw.
  - intro H. exact (H Hbot).
  - destruct Hdec as [d Hd].
    exists (fun p => if g_wf_program_dec p then negb (d p) else false).
    intro p. specialize (Hd p). unfold reflects in *.
    destruct (g_wf_program_dec p) as [Hw'|Hw'].
    + destruct (d p) eqn:Ed; cbn [negb]; split.
      * intros (_ & Hn). exfalso. exact (Hn (proj2 (proj2 Hd eq_refl))).
      * discriminate.
      * intros _. reflexivity.
      * intros _. split; [exact Hw'|]. intro Hp.
        pose proof (proj1 Hd (conj Hw' Hp)). discriminate.
    + split; [intros (H & _); contradiction|discriminate].
Qed.

(** * 8. Deciders realized by guest programs.

    [g_decides D enc Pr]: the guest program [D], run on the encoding
    [enc p] of any well-formed program, terminates, and its final register 0
    is 1 exactly when [Pr p].  Any such decider yields a Boolean decider in
    Coq, so the upstream limitative conclusion applies to it. *)

Definition g_decides (D : list GInstr) (enc : list GInstr -> nat) (Pr : list GInstr -> Prop) : Prop :=
  g_wf_program D /\
  forall p, g_wf_program p ->
    exists g mu, g_beh D (enc p) g mu /\ (gr0 g = 1 <-> Pr p).

Lemma g_beh_unique : forall p x g1 mu1 g2 mu2,
  g_beh p x g1 mu1 -> g_beh p x g2 mu2 -> g1 = g2 /\ mu1 = mu2.
Proof.
  intros p x g1 mu1 g2 mu2 (n1 & T1 & G1 & M1) (n2 & T2 & G2 & M2).
  assert (E : g_run n1 p (g_input x) = g_run n2 p (g_input x)).
  { destruct (le_lt_dec n1 n2).
    - symmetry. apply g_run_terminal_after; assumption.
    - apply g_run_terminal_after; [exact T2|lia]. }
  subst. rewrite E. auto.
Qed.

Theorem g_decides_decidable : forall D enc Pr,
  g_decides D enc Pr -> decidable (fun p => g_wf_program p /\ Pr p).
Proof.
  intros D enc Pr (HD & Hdec).
  set (T := fun p n => g_terminal D (g_run n D (g_input (enc p)))).
  assert (Tdec : forall p n, {T p n} + {~ T p n}) by (intros; apply g_terminal_dec).
  assert (Hex : forall p, g_wf_program p -> exists n, T p n).
  { intros p Hp. destruct (Hdec p Hp) as (g & mu & (n & Hn & _) & _). exists n. exact Hn. }
  exists (fun p => match g_wf_program_dec p with
                   | left Hp =>
                       let n := proj1_sig (constructive_indefinite_ground_description_nat
                                             (T p) (Tdec p) (Hex p Hp)) in
                       Nat.eqb (gr0 (gc_g (g_run n D (g_input (enc p))))) 1
                   | right _ => false
                   end).
  intro p. unfold reflects. destruct (g_wf_program_dec p) as [Hp|Hp].
  - destruct (constructive_indefinite_ground_description_nat (T p) (Tdec p) (Hex p Hp)) as [n Hn].
    cbn [proj1_sig].
    destruct (Hdec p Hp) as (g & mu & Hb & Hiff).
    assert (Hb' : g_beh D (enc p) (gc_g (g_run n D (g_input (enc p))))
                              (gc_mu (g_run n D (g_input (enc p)))))
      by (exists n; auto).
    destruct (g_beh_unique _ _ _ _ _ _ Hb Hb') as (<- & _).
    rewrite Nat.eqb_eq. split; [intros (_ & H); apply Hiff, H|intro H; split; [exact Hp|apply Hiff, H]].
  - split; [intros (H & _); contradiction|discriminate].
Qed.

Corollary self_rice_representable : forall (Pr : list GInstr -> Prop) w D enc,
  g_extensional Pr -> g_wf_program w -> Pr w -> ~ Pr g_bottom ->
  g_decides D enc Pr -> enumerable (complement SBTM.SBTM_HALT).
Proof.
  intros Pr w D enc Hext Hw Hpw Hbot HD.
  exact (@self_rice Pr w Hext Hw Hpw Hbot (@g_decides_decidable D enc Pr HD)).
Qed.

(** * 9. Named unbounded predicates. *)

(** Termination on input 0. *)
Definition g_halts_on_zero (p : list GInstr) : Prop := exists g mu, g_beh p 0 g mu.

Theorem g_halts_on_zero_undecidable :
  undecidable (fun p => g_wf_program p /\ g_halts_on_zero p).
Proof.
  apply (@self_rice g_halts_on_zero []).
  - intros p q Hp Hq Hpq (g & mu & H). exists g, mu. apply Hpq, H.
  - constructor.
  - exists {| gr0 := 0; gr1 := 0; gr2 := 0; gr3 := 0 |}, 0. exists 0. unfold g_terminal; cbn. auto.
  - intros (g & mu & H). exact (g_bottom_beh 0 g mu H).
Qed.

(** Returning 0 in register 0 on every input on which the program terminates,
    together with termination on input 0. *)
Definition g_returns_zero (p : list GInstr) : Prop :=
  g_halts_on_zero p /\ forall x g mu, g_beh p x g mu -> gr0 g = 0.

Theorem g_returns_zero_undecidable :
  undecidable (fun p => g_wf_program p /\ g_returns_zero p).
Proof.
  apply (@self_rice g_returns_zero [GLoadImm 0 0 0]).
  - intros p q Hp Hq Hpq ((g & mu & H0) & Hall). split.
    + exists g, mu. apply Hpq, H0.
    + intros x g' mu' H. apply (Hall x g' mu'), Hpq, H.
  - apply Forall_cons; [unfold g_wf; cbn; lia|apply Forall_nil].
  - split.
    + exists {| gr0 := 0; gr1 := 0; gr2 := 0; gr3 := 0 |}, 0. exists 1. unfold g_terminal; cbn. auto.
    + intros x g mu (n & Ht & Hg & _).
      destruct n as [|n]; [unfold g_terminal in Ht; cbn in Ht; lia|].
      rewrite (g_run_terminal_after _ _ 1 (S n)) in Hg by (unfold g_terminal; cbn; lia || lia).
      subst g. reflexivity.
  - intros ((g & mu & H) & _). exact (g_bottom_beh 0 g mu H).
Qed.

(** * 10. The total-run record field.

    [Substrate.run] is a total function whose result on convergence is the
    converged state.  For this model, any such function decides termination
    on input 0, so its existence already yields the upstream limitative
    conclusion.  This is why the conditional VM substrate diagonal is not
    instantiated here and the limitative result is obtained by reduction. *)

Theorem total_run_obstruction :
  forall run : list GInstr -> nat -> option (GRegs * nat),
    (forall p x o, g_wf_program p -> (run p x = Some o <-> g_beh p x (fst o) (snd o))) ->
    enumerable (complement SBTM.SBTM_HALT).
Proof.
  intros run Hrun. apply g_halts_on_zero_undecidable.
  exists (fun p => if g_wf_program_dec p then
                     match run p 0 with Some _ => true | None => false end
                   else false).
  intro p. unfold reflects. destruct (g_wf_program_dec p) as [Hp|Hp].
  - destruct (run p 0) as [[g mu]|] eqn:E; split.
    + intros _. reflexivity.
    + intros _. split; [exact Hp|]. exists g, mu. apply (proj1 (Hrun p 0 (g, mu) Hp) E).
    + intros (_ & g & mu & H). pose proof (proj2 (Hrun p 0 (g, mu) Hp) H) as H'.
      rewrite E in H'. discriminate.
    + discriminate.
  - split; [intros (H & _); contradiction|discriminate].
Qed.
