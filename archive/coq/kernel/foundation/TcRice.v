(** TcRice.v: Rice's theorem for the small machine with an input in counter A.

    The small machine is the machine of EarnedCore.v: two counters A and B,
    INC, DEC, HALT, CHECK, COMMIT, CERTIFY, the ledger, the flag, the fact
    table, the channel and the trap latch. A program is run on an input n by
    starting it at (n, 0): counter A holds n, counter B holds 0, no facts, no
    commitment, flag down, ledger 0.

    What a program does on n, [tc_ends]: it runs forever, or it stops (a
    trap counts as stopping), and then what can be read is the two counters,
    the trap latch, the ledger, the flag, and the shape of the fact table and
    of the channel (which property and which counter each fact is about, not
    the version). Two programs behave the same on a set X of inputs when on
    every n in X they do the same thing [tc_equiv X].

    Theorem [tc_rice]. Let X be any set of inputs and Pi a property of
    programs that respects behaving the same on X, with Pi y for some
    program y and not Pi n for some program n. Then Pi is undecidable in the
    sense of the vendored Saarland library. The set X can be everything (plain
    inputs), the powers of two (packed inputs), or the single input 0 (the
    clean start).

    The input is not lost while the reduction runs a copy of a two-register
    machine: the copy runs inside the exponents of 2 and 3 of the counter
    (6n + 5) * 2^a * 3^b, and 6n + 5 is prime to 2 and to 3 (TcPrefix.v).

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, EarnedCore.v and the Tc files before it. No axioms and no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Synthetic Require Import Undecidability ReducibilityFacts.
From Undecidability.PCP Require Import PCP PCP_undec.
From Undecidability.PCP.Reductions Require PCPb_iff_iPCPb.
From Undecidability.StackMachines Require Import BSM.
From Undecidability.StackMachines.Reductions Require Import iPCPb_to_BSM_HALTING.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA MM2.
From Undecidability.MinskyMachines.Reductions Require Import BSM_MM.
From Undecidability.FRACTRAN Require Import FRACTRAN Reductions.MM_FRACTRAN.
From Undecidability.MinskyMachines.Reductions Require Import FRACTRAN_to_MMA2.
Require Import Kernel.TcGodel Kernel.TcCompile Kernel.TcBridge Kernel.TcRiceMM Kernel.TcGadget Kernel.TcPrefix Minimal.TcBlocks.
Module E := Minimal.EarnedCore.
Unset Implicit Arguments.

(* ================================================================= *)
(* The halting problem of the vendored two-register machine           *)
(* ================================================================= *)

Lemma tc_PCPb_to_MMA2 : PCPb ⪯ MMA2_HALTING.
Proof.
  eapply reduces_transitive.
  { exists id. exact PCPb_iff_iPCPb.PCPb_iff_iPCPb. }
  eapply reduces_transitive; [apply iPCPb_to_BSM_HALTING|].
  eapply reduces_transitive; [apply BSM_MM_HALTING|].
  eapply reduces_transitive; [apply MM_FRACTRAN_REG_HALTING|].
  apply FRACTRAN_REG_MMA2_HALTING.
Qed.

Theorem tc_MMA2_HALTING_compl_undec : undecidable (complement MMA2_HALTING).
Proof.
  apply (undecidability_from_reducibility PCPb_compl_undec).
  apply reduces_complement, tc_PCPb_to_MMA2.
Qed.

(* ================================================================= *)
(* Behaviour on an input                                              *)
(* ================================================================= *)

Definition tc_ends (n : nat) (P : list E.instr) (s : E.state) : Prop :=
  exists N, s = E.run_prog N P (E.start n 0) /\ E.halted P (E.core_of s).

Definition tc_shape (f : E.fact) : E.prop * E.ctr := (E.f_prop f, E.f_ctr f).

Definition tc_agree (s t : E.state) : Prop :=
  E.ca (E.core_of s) = E.ca (E.core_of t) /\ E.cb (E.core_of s) = E.cb (E.core_of t) /\
  E.err (E.core_of s) = E.err (E.core_of t) /\ E.mu s = E.mu t /\ E.cert s = E.cert t /\
  map tc_shape (E.facts (E.core_of s)) = map tc_shape (E.facts (E.core_of t)) /\
  option_map tc_shape (E.chan (E.core_of s)) = option_map tc_shape (E.chan (E.core_of t)).

Lemma tc_agree_sym : forall s t, tc_agree s t -> tc_agree t s.
Proof. intros s t (H1 & H2 & H3 & H4 & H5 & H6 & H7). repeat split; congruence. Qed.

Definition tc_equiv (X : nat -> Prop) (P Q : list E.instr) : Prop :=
  forall n, X n ->
    (forall s, tc_ends n P s -> exists t, tc_ends n Q t /\ tc_agree s t) /\
    (forall t, tc_ends n Q t -> exists s, tc_ends n P s /\ tc_agree s t).

Lemma tc_equiv_sym : forall X P Q, tc_equiv X P Q -> tc_equiv X Q P.
Proof.
  intros X P Q H n Hn. destruct (H n Hn) as [H1 H2]. split.
  - intros t Ht. destruct (H2 t Ht) as [s [Hs Ha]]. exists s. split; [exact Hs | apply tc_agree_sym, Ha].
  - intros s Hs. destruct (H1 s Hs) as [t [Ht Ha]]. exists t. split; [exact Ht | apply tc_agree_sym, Ha].
Qed.

Definition tc_ext (X : nat -> Prop) (Pi : list E.instr -> Prop) : Prop :=
  forall p q, tc_equiv X p q -> Pi p -> Pi q.

Lemma tc_shape_fsh : forall da db f, tc_shape (tc_fsh da db f) = tc_shape f.
Proof. intros da db [p c v]. reflexivity. Qed.

Lemma tc_gsrel_agree : forall off len da db s t, tc_gsrel off len da db s t -> tc_agree s t.
Proof.
  intros off len da db s t ((Ha & Hb & _ & _ & Hf & Hc & He & _) & Hm & Hk).
  refine (conj Ha (conj Hb (conj He (conj Hm (conj Hk (conj _ _)))))).
  - rewrite Hf, map_map. apply map_ext. intro f. symmetry. apply tc_shape_fsh.
  - rewrite Hc. destruct (E.chan (E.core_of s)) as [f |]; [| reflexivity].
    simpl. f_equal.
Qed.

Lemma tc_gfinal_two : forall Q P off da db n n',
  tc_gembeds Q P off -> length Q = off + length P ->
  (exists T0, tc_gsrel off (length P) da db (E.start n' 0) (E.run_prog T0 Q (E.start n 0))) ->
  (forall s, tc_ends n Q s -> exists t, tc_ends n' P t /\ tc_agree s t) /\
  (forall t, tc_ends n' P t -> exists s, tc_ends n Q s /\ tc_agree s t).
Proof.
  intros Q P off da db n n' Hemb HQ [T0 HT].
  assert (Hall : forall m, tc_gsrel off (length P) da db (E.run_prog m P (E.start n' 0))
                              (E.run_prog (T0 + m) Q (E.start n 0))).
  { intro m. rewrite tc_grun_add. apply (tc_gblock_run_final Q P off da db Hemb HQ), HT. }
  split.
  - intros s [N [-> HN]].
    set (m := N - T0).
    assert (Es : E.run_prog (T0 + m) Q (E.start n 0) = E.run_prog N Q (E.start n 0))
      by (apply tc_ghalted_after; [unfold m; lia | exact HN]).
    pose proof (Hall m) as Hr. rewrite Es in Hr.
    exists (E.run_prog m P (E.start n' 0)). split.
    + exists m. split; [reflexivity |].
      unfold E.halted. destruct (E.next_instr P (E.core_of (E.run_prog m P (E.start n' 0)))) eqn:Hn;
        [| reflexivity].
      exfalso. apply (tc_gblock_not_halted Q P off da db _ _ Hemb Hr); [congruence | exact HN].
    + apply tc_agree_sym. eapply tc_gsrel_agree. exact Hr.
  - intros t [m [-> Hm]].
    exists (E.run_prog (T0 + m) Q (E.start n 0)). split.
    + exists (T0 + m). split; [reflexivity |].
      apply (tc_gblock_halted Q P off da db (E.core_of (E.run_prog m P (E.start n' 0)))); auto.
      apply (Hall m).
    + apply tc_agree_sym. eapply tc_gsrel_agree. apply (Hall m).
Qed.

Lemma tc_gfinal_one : forall Q P off da db n,
  tc_gembeds Q P off -> length Q = off + length P ->
  (exists T0, tc_gsrel off (length P) da db (E.start n 0) (E.run_prog T0 Q (E.start n 0))) ->
  (forall s, tc_ends n Q s -> exists t, tc_ends n P t /\ tc_agree s t) /\
  (forall t, tc_ends n P t -> exists s, tc_ends n Q s /\ tc_agree s t).
Proof. intros. eapply tc_gfinal_two; eassumption. Qed.

(* ================================================================= *)
(* A program that never stops                                         *)
(* ================================================================= *)

Definition tc_gloop : list E.instr := [E.INC E.CA; E.DEC E.CA 1].

Lemma tc_gloop_runs : forall n s,
  E.err (E.core_of s) = false ->
  (E.pc (E.core_of s) = 1 \/ (E.pc (E.core_of s) = 2 /\ E.ca (E.core_of s) <> 0)) ->
  E.err (E.core_of (E.run_prog n tc_gloop s)) = false /\
  (E.pc (E.core_of (E.run_prog n tc_gloop s)) = 1 \/
   (E.pc (E.core_of (E.run_prog n tc_gloop s)) = 2 /\ E.ca (E.core_of (E.run_prog n tc_gloop s)) <> 0)).
Proof.
  induction n as [| n IH]; intros s He Hp; [auto |].
  rewrite tc_grun_succ.
  destruct Hp as [Hp | [Hp Hv]].
  - assert (Ek : E.core_of (E.step tc_gloop s) =
                 E.write (E.core_of s) E.CA (S (E.ca (E.core_of s))) 2).
    { unfold E.step, E.next_instr. rewrite He, Hp. simpl. unfold E.cexec. rewrite He, Hp.
      unfold E.write. simpl. rewrite He. reflexivity. }
    apply IH; rewrite Ek; simpl.
    + exact He.
    + right. split; [reflexivity | discriminate].
  - destruct (E.ca (E.core_of s)) as [| v] eqn:Ev; [congruence |].
    assert (Ek : E.core_of (E.step tc_gloop s) = E.write (E.core_of s) E.CA v 1).
    { unfold E.step, E.next_instr. rewrite He, Hp. simpl. unfold E.cexec. rewrite He. simpl.
      rewrite Ev. unfold E.write. simpl. rewrite He. reflexivity. }
    apply IH; rewrite Ek; simpl.
    + exact He.
    + left. reflexivity.
Qed.

Lemma tc_gloop_diverges : forall n N,
  ~ E.halted tc_gloop (E.core_of (E.run_prog N tc_gloop (E.start n 0))).
Proof.
  intros n N HN. destruct (tc_gloop_runs N (E.start n 0) eq_refl (or_introl eq_refl)) as [He Hp].
  unfold E.halted, E.next_instr in HN. rewrite He in HN.
  destruct Hp as [Hp | [Hp _]]; rewrite Hp in HN; discriminate.
Qed.

Lemma tc_never_equiv : forall X P Q,
  (forall n, X n -> forall N, ~ E.halted P (E.core_of (E.run_prog N P (E.start n 0)))) ->
  (forall n, X n -> forall N, ~ E.halted Q (E.core_of (E.run_prog N Q (E.start n 0)))) ->
  tc_equiv X P Q.
Proof.
  intros X P Q HP HQ n Hn. split.
  - intros s [N [-> HN]]. exfalso. exact (HP n Hn N HN).
  - intros t [N [-> HN]]. exfalso. exact (HQ n Hn N HN).
Qed.

(* ================================================================= *)
(* The prefix inside the small machine                                 *)
(* ================================================================= *)

Lemma tc_prefix_next : forall B R k, E.next_instr B k <> None -> E.next_instr (B ++ R) k = E.next_instr B k.
Proof.
  intros B R k H. unfold E.next_instr in *.
  destruct (E.err k); [congruence |].
  destruct (E.fetch B (E.pc k)) as [i |] eqn:Hf.
  - pose proof (tc_gfetch_range B _ _ Hf) as Hr. rewrite tc_gfetch_app_left by lia. rewrite Hf. reflexivity.
  - congruence.
Qed.

Lemma tc_prefix_run : forall B R m s,
  (forall k, k < m -> E.next_instr B (E.core_of (E.run_prog k B s)) <> None) ->
  E.run_prog m (B ++ R) s = E.run_prog m B s.
Proof.
  intros B R m. induction m as [| m IH]; intros s H; [reflexivity |].
  rewrite !tc_grun_succ.
  assert (Hs : E.step (B ++ R) s = E.step B s).
  { unfold E.step. rewrite (tc_prefix_next B R); [reflexivity |].
    apply (H 0). lia. }
  rewrite Hs. apply IH. intros k Hk. apply (H (S k)). lia.
Qed.

Definition tc_eprog (P : list (mm_instr (pos 2))) (K : nat) : list E.instr :=
  E.compile (tc_P (tc_pre P K)).

Lemma tc_eprog_length : forall P K, length (tc_eprog P K) = length (tc_pre P K).
Proof. intros P K. unfold tc_eprog, E.compile, tc_P. rewrite !map_length. reflexivity. Qed.

Definition tc_rice_prog (P : list (mm_instr (pos 2))) (v : vec nat 2) (y : list E.instr) : list E.instr :=
  tc_eprog P (tc_code v) ++ tc_greloc (length (tc_eprog P (tc_code v))) y.

Lemma tc_rice_prog_length : forall P v y,
  length (tc_rice_prog P v y) = length (tc_eprog P (tc_code v)) + length y.
Proof. intros. unfold tc_rice_prog. rewrite app_length, tc_greloc_length. reflexivity. Qed.

Lemma tc_rice_embeds : forall P v y,
  tc_gembeds (tc_rice_prog P v y) y (length (tc_eprog P (tc_code v))).
Proof.
  intros P v y. unfold tc_rice_prog. rewrite <- (app_nil_r (tc_greloc _ y)).
  apply tc_gembeds_app.
Qed.

(* the compiled prefix is not stopped while the counter program is not *)
Lemma tc_not_stopped : forall M s k c,
  E.err (E.core_of s) = false ->
  E.mrun k M (E.window (E.core_of s)) = c -> E.mstep M c <> None ->
  E.next_instr (E.compile M) (E.core_of (E.run_prog k (E.compile M) s)) <> None.
Proof.
  intros M s k c He Hr Hs.
  destruct (tc_compile_run M k s He) as (Hw & _ & _ & He' & _).
  destruct (E.simulation_step M _ He') as [Hnone _].
  intro Hn. apply Hs. rewrite <- Hr, <- Hw. apply Hnone. exact Hn.
Qed.

Lemma tc_steps_inside : forall M m c c', tc_steps M m c c' ->
  forall k, k < m -> exists ck, E.mrun k M c = ck /\ E.mstep M ck <> None.
Proof.
  intros M m c c' H. induction H as [c | m c c1 c2 Hs Hr IH]; intros k Hk; [lia |].
  destruct k as [| k].
  - exists c. split; [reflexivity |]. rewrite Hs. discriminate.
  - simpl. rewrite Hs. apply IH. lia.
Qed.

Lemma tc_start_window : forall n, E.window (E.core_of (E.start n 0)) = (1, (n, 0)).
Proof. reflexivity. Qed.

Lemma tc_rel_start : forall n off len (sm : E.state),
  E.ca (E.core_of sm) = n -> E.cb (E.core_of sm) = 0 -> E.facts (E.core_of sm) = [] ->
  E.chan (E.core_of sm) = None -> E.err (E.core_of sm) = false -> E.mu sm = 0 -> E.cert sm = false ->
  E.pc (E.core_of sm) = S off ->
  tc_gsrel off len (E.va (E.core_of sm)) (E.vb (E.core_of sm)) (E.start n 0) sm.
Proof.
  intros n off len sm Ha Hb Hf Hc He Hm Hk Hp.
  unfold tc_gsrel, tc_gcrel. cbn [E.start E.start_core E.core_of E.ca E.cb E.va E.vb E.facts E.chan E.err E.pc E.mu E.cert].
  rewrite Hf, Hc. cbn [map option_map].
  refine (conj (conj (eq_sym Ha) (conj (eq_sym Hb) (conj _ (conj _ (conj eq_refl (conj eq_refl (conj (eq_sym He) _))))))) (conj (eq_sym Hm) (eq_sym Hk))).
  - lia.
  - lia.
  - rewrite Hp. unfold tc_rj. destruct (Nat.leb_spec 1 1), (Nat.leb_spec 1 len); simpl; lia.
Qed.

Theorem tc_prog_halts : forall P v y,
  sss_terminates (@mma_sss 2) (1, P) (1, v) ->
  forall n, exists T0 da db,
    tc_gsrel (length (tc_eprog P (tc_code v))) (length y) da db (E.start n 0)
             (E.run_prog T0 (tc_rice_prog P v y) (E.start n 0)).
Proof.
  intros P v y [[j w] Hout] n.
  destruct (tc_vec2_ex v) as [a0 [b0 ->]]. destruct (tc_vec2_ex w) as [a1 [b1 ->]].
  pose proof (tc_pre_halts P a0 b0 j a1 b1 Hout n) as Hpre.
  apply tc_output_iff in Hpre. destruct Hpre as [m [Hsteps Hstop]].
  set (K := tc_code (tc_tovec a0 b0)) in *.
  set (M := tc_P (tc_pre P K)) in *.
  set (B := E.compile M).
  set (s0 := E.start n 0).
  change (tc_ofvec (tc_tovec n 0)) with (n, 0) in Hsteps, Hstop.
  assert (Hin : forall k, k < m -> E.next_instr B (E.core_of (E.run_prog k B s0)) <> None).
  { intros k Hk. destruct (tc_steps_inside M m _ _ Hsteps k Hk) as [ck [Hck Hs]].
    eapply tc_not_stopped; [reflexivity | exact Hck | exact Hs]. }
  assert (Hrun : E.run_prog m (tc_rice_prog P (tc_tovec a0 b0) y) s0 = E.run_prog m B s0).
  { unfold tc_rice_prog. fold B. apply tc_prefix_run. exact Hin. }
  destruct (tc_compile_run M m s0 eq_refl) as (Hw & Hf & Hc & He & Hm & Hk).
  change (E.window (E.core_of s0)) with (1, (n, 0)) in Hw. rewrite (tc_steps_mrun M m _ _ Hsteps) in Hw.
  exists m, (E.va (E.core_of (E.run_prog m B s0))), (E.vb (E.core_of (E.run_prog m B s0))).
  rewrite Hrun.
  pose proof (tc_pre_length P K) as Hl.
  pose proof (tc_eprog_length P K) as Hlen.
  unfold E.window in Hw. injection Hw as Hpc Hca Hcb.
  apply tc_rel_start.
  - exact Hca.
  - exact Hcb.
  - exact Hf.
  - exact Hc.
  - exact He.
  - exact Hm.
  - exact Hk.
  - assert (Hpc' : E.pc (E.core_of (E.run_prog m B s0)) = tc_end P K) by exact Hpc.
    rewrite Hpc'. lia.
Qed.

Theorem tc_prog_diverges : forall P v y,
  ~ sss_terminates (@mma_sss 2) (1, P) (1, v) ->
  forall n N, ~ E.halted (tc_rice_prog P v y) (E.core_of (E.run_prog N (tc_rice_prog P v y) (E.start n 0))).
Proof.
  intros P v y Hnt n N HN.
  destruct (tc_vec2_ex v) as [a0 [b0 ->]].
  pose proof (tc_pre_diverges P a0 b0 Hnt n) as Hd.
  set (K := tc_code (tc_tovec a0 b0)) in *.
  pose proof (tc_nonterm_never_stops (tc_pre P K) 1 (tc_tovec n 0) Hd) as Hns.
  set (M := tc_P (tc_pre P K)) in *.
  set (B := E.compile M).
  set (s0 := E.start n 0).
  assert (Hin : forall k, E.next_instr B (E.core_of (E.run_prog k B s0)) <> None).
  { intro k. eapply tc_not_stopped; [reflexivity | reflexivity | apply Hns]. }
  assert (Hrun : E.run_prog N (tc_rice_prog P (tc_tovec a0 b0) y) (E.start n 0) = E.run_prog N B (E.start n 0)).
  { unfold tc_rice_prog. fold B. apply tc_prefix_run. intros k _. apply Hin. }
  rewrite Hrun in HN.
  unfold E.halted in HN. unfold tc_rice_prog in HN. fold B in HN.
  rewrite (tc_prefix_next B _ _ (Hin N)) in HN.
  exact (Hin N HN).
Qed.

Theorem tc_prog_equiv_y : forall X P v y,
  sss_terminates (@mma_sss 2) (1, P) (1, v) ->
  tc_equiv X (tc_rice_prog P v y) y.
Proof.
  intros X P v y Hh n _.
  destruct (tc_prog_halts P v y Hh n) as [T0 [da [db HT]]].
  apply (tc_gfinal_one (tc_rice_prog P v y) y (length (tc_eprog P (tc_code v))) da db n).
  - apply tc_rice_embeds.
  - apply tc_rice_prog_length.
  - exists T0. exact HT.
Qed.

Theorem tc_prog_equiv_loop : forall X P v y,
  ~ sss_terminates (@mma_sss 2) (1, P) (1, v) ->
  tc_equiv X (tc_rice_prog P v y) tc_gloop.
Proof.
  intros X P v y Hnh. apply tc_never_equiv.
  - intros n _ N. apply tc_prog_diverges. exact Hnh.
  - intros n _ N. apply tc_gloop_diverges.
Qed.

Lemma tc_ext_compl : forall X Pi, tc_ext X Pi -> tc_ext X (complement Pi).
Proof.
  intros X Pi H p q Hpq Hnp Hq. apply Hnp. apply (H q p); [apply tc_equiv_sym, Hpq | exact Hq].
Qed.

Lemma tc_rice_loop : forall X (Pi : list E.instr -> Prop) y,
  tc_ext X Pi -> Pi y -> ~ Pi tc_gloop -> undecidable Pi.
Proof.
  intros X Pi y Hext Hy Hloop.
  apply undecidability_from_complement.
  apply (undecidability_from_reducibility tc_MMA2_HALTING_compl_undec).
  exists (fun q : MMA2_PROBLEM => let '(P, v) := q in tc_rice_prog P v y).
  intros [P v]. unfold complement. split.
  - intros Hnh HPi. apply Hloop.
    apply (Hext (tc_rice_prog P v y)); [| exact HPi].
    apply tc_prog_equiv_loop. exact Hnh.
  - intros HnPi Hh. apply HnPi.
    apply (Hext y); [apply tc_equiv_sym, tc_prog_equiv_y; exact Hh | exact Hy].
Qed.

(* Rice's theorem for the small machine with inputs in counter A. *)
Theorem tc_rice : forall X (Pi : list E.instr -> Prop) y n,
  tc_ext X Pi -> Pi y -> ~ Pi n -> undecidable Pi.
Proof.
  intros X Pi y n Hext Hy Hn Hdec.
  destruct Hdec as [d Hd] eqn:Hdec'.
  destruct (d tc_gloop) eqn:Hdl.
  - assert (Hl : Pi tc_gloop) by (apply Hd; exact Hdl).
    apply (undecidability_from_complement (p := Pi)); [| exact Hdec].
    apply (tc_rice_loop X (complement Pi) n).
    + apply tc_ext_compl, Hext.
    + exact Hn.
    + intro H. exact (H Hl).
  - assert (Hl : ~ Pi tc_gloop) by (intro H; apply Hd in H; congruence).
    exact (tc_rice_loop X Pi y Hext Hy Hl Hdec).
Qed.

Print Assumptions tc_rice.

(* ================================================================= *)
(* The three conventions for inputs, and a complete dichotomy          *)
(* ================================================================= *)

(* Plain inputs allow every number; 0 <= n holds of all of them. *)
Definition tc_plain (n : nat) : Prop := 0 <= n.
Definition tc_packed (n : nat) : Prop := exists x, n = 2 ^ x.
Definition tc_clean (n : nat) : Prop := n = 0.

(* every property that depends only on what programs do on plain inputs, and
   holds of one program and fails of another, is undecidable *)
Corollary tc_rice_plain : forall (Pi : list E.instr -> Prop) y n,
  tc_ext tc_plain Pi -> Pi y -> ~ Pi n -> undecidable Pi.
Proof. intros Pi y n. apply tc_rice. Qed.

Corollary tc_rice_packed : forall (Pi : list E.instr -> Prop) y n,
  tc_ext tc_packed Pi -> Pi y -> ~ Pi n -> undecidable Pi.
Proof. intros Pi y n. apply tc_rice. Qed.

Corollary tc_rice_clean : forall (Pi : list E.instr -> Prop) y n,
  tc_ext tc_clean Pi -> Pi y -> ~ Pi n -> undecidable Pi.
Proof. intros Pi y n. apply tc_rice. Qed.

(* the plain case is the strongest: behaving the same on all inputs implies
   behaving the same on any set of them *)
Lemma tc_equiv_mono : forall (X Y : nat -> Prop) p q,
  (forall n, Y n -> X n) -> tc_equiv X p q -> tc_equiv Y p q.
Proof. intros X Y p q H He n Hn. apply He. apply H. exact Hn. Qed.

Lemma tc_ext_mono : forall (X Y : nat -> Prop) Pi,
  (forall n, Y n -> X n) -> tc_ext Y Pi -> tc_ext X Pi.
Proof. intros X Y Pi H He p q Hpq. apply He. eapply tc_equiv_mono; [exact H | exact Hpq]. Qed.

(* the dichotomy: a property of what programs do on inputs is decidable
   exactly when it is trivial *)
Theorem tc_rice_dichotomy : forall X (Pi : list E.instr -> Prop),
  tc_ext X Pi ->
  ((exists y n, Pi y /\ ~ Pi n) -> undecidable Pi) /\
  (((forall p, Pi p) \/ (forall p, ~ Pi p)) -> decidable Pi).
Proof.
  intros X Pi Hext. split.
  - intros (y & n & Hy & Hn). exact (tc_rice X Pi y n Hext Hy Hn).
  - intros [H | H].
    (* SAFE: Pi holds of every program, so the constant decider is the intended witness. *)
    + exists (fun _ => true). intro p. split; [intros _; reflexivity | intros _; apply H].
    (* SAFE: Pi fails of every program, so the constant decider is the intended witness. *)
    + exists (fun _ => false). intro p. split; [intro Hp; exfalso; exact (H p Hp) | intro E1; discriminate E1].
Qed.

(* two examples of properties it covers *)
Definition tc_halts_all (P : list E.instr) : Prop :=
  forall n, exists N, E.halted P (E.core_of (E.run_prog N P (E.start n 0))).

Corollary tc_halts_all_undecidable : undecidable tc_halts_all.
Proof.
  apply (tc_rice tc_plain tc_halts_all [E.HALT] tc_gloop).
  - intros p q Hpq Hp n. destruct (Hp n) as [N HN].
    destruct (Hpq n (Nat.le_0_l n)) as [H1 _].
    destruct (H1 (E.run_prog N p (E.start n 0)) (ex_intro _ N (conj eq_refl HN))) as [t [[M [-> HM]] _]].
    exists M. exact HM.
  - intro n. exists 0. unfold E.halted, E.next_instr. simpl. destruct (E.err (E.start_core n 0)); reflexivity.
  - intro H. destruct (H 0) as [N HN]. exact (tc_gloop_diverges 0 N HN).
Qed.

Lemma tc_halt_only_halted : forall n, E.halted [E.HALT] (E.core_of (E.start n 0)).
Proof. intro n. reflexivity. Qed.

Lemma tc_halt_only_ends : forall n s, tc_ends n [E.HALT] s -> s = E.start n 0.
Proof.
  intros n s [N [-> HN]]. apply E.run_prog_halted. apply tc_halt_only_halted.
Qed.

Lemma tc_inc_halt_ends : forall n s, tc_ends n [E.INC E.CA; E.HALT] s -> E.ca (E.core_of s) = S n.
Proof.
  intros n s [N [-> HN]]. destruct N as [| N].
  - exfalso. revert HN. simpl. unfold E.halted, E.next_instr. simpl. discriminate.
  - assert (H1 : E.halted [E.INC E.CA; E.HALT] (E.core_of (E.run_prog 1 [E.INC E.CA; E.HALT] (E.start n 0)))) by reflexivity.
    rewrite (tc_ghalted_after 1 (S N) _ _ (le_n_S _ _ (Nat.le_0_l N)) H1). reflexivity.
Qed.

Definition tc_computes_identity (P : list E.instr) : Prop :=
  forall n y, (exists s, tc_ends n P s /\ E.ca (E.core_of s) = y) <-> y = n.

Corollary tc_identity_undecidable : undecidable tc_computes_identity.
Proof.
  apply (tc_rice tc_plain tc_computes_identity [E.HALT] [E.INC E.CA; E.HALT]).
  - intros p q Hpq Hp n y. split.
    + intros [t [Ht Hy]]. destruct (Hpq n (Nat.le_0_l n)) as [_ H2]. destruct (H2 t Ht) as [s [Hs Ha]].
      apply (proj1 (Hp n y)). exists s. split; [exact Hs |]. destruct Ha as (Ha & _). congruence.
    + intro Hyn. subst y. destruct (proj2 (Hp n n) eq_refl) as [s [Hs Hy]].
      destruct (Hpq n (Nat.le_0_l n)) as [H1 _]. destruct (H1 s Hs) as [t [Ht Ha]]. exists t. split; [exact Ht |].
      destruct Ha as (Ha & _). congruence.
  - intros n y. split.
    + intros [s [Hs Hy]]. rewrite (tc_halt_only_ends n s Hs) in Hy. simpl in Hy. congruence.
    + intros ->. exists (E.start n 0). split; [| reflexivity].
      exists 0. split; [reflexivity | apply tc_halt_only_halted].
  - intro H. destruct (proj2 (H 0 0) eq_refl) as [s [Hs Hy]].
    pose proof (tc_inc_halt_ends 0 s Hs) as H1. congruence.
Qed.

Print Assumptions tc_halts_all_undecidable.
Print Assumptions tc_identity_undecidable.
Print Assumptions tc_rice_dichotomy.
