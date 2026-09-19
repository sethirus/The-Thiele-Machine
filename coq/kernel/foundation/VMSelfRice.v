(** VMSelfRice.v: B4 over the self-interpreted unbounded model.

    Model.  Programs are well-formed guest programs [list GInstr].  Their
    execution is [g_run], which is the VM's own [run_vm_u] on [g_program p]
    ([g_run_is_run_vm_u]) and is realized by the fixed host [U]
    ([self_interpreter_correct]).  The input x is guest register 0; the other
    guest registers, pc and ledger start at 0.

    Observation.  [g_beh p x g mu]: some finite guest run from input x
    terminates, with final registers g and final guest ledger mu.  Program
    equivalence [g_equiv] is equality of this relation for all inputs.  It
    observes returned registers and the guest ledger; it does not observe the
    final pc or the number of steps.

    Construction.  The limitative result is Rice's theorem by reduction:
    for every predicate that respects [g_equiv] and separates the
    never-terminating program from some program, deciding it is undecidable
    in the upstream synthetic sense.  The effective transformer is
    [rice_prog]: save the input, run a relocated compiled MM2 instance, restore
    the input, then run the relocated witness.  No recursion-theorem field or
    representability premise is assumed. *)

From Coq Require Import Arith Lia List Bool.
From Coq Require Import Logic.ConstructiveEpsilon.
Import ListNotations.
From Undecidability.Synthetic Require Import Undecidability.
From Kernel Require Import VMState VMStep VMUnboundedStep.
From Undecidability.MinskyMachines Require Import MM2.
From Kernel Require Import VMUnboundedCM2Interpreter VMUnboundedCM2Correctness VMUnboundedCM2Bridge.
From Kernel Require Import VMSelfGuest VMSelfProgram VMSelfCorrect VMSelfRun VMSelfUniversal.

(** * 1. Behaviour and equivalence. *)

Definition g_input (x : nat) : GConf :=
  {| gc_pc := 0; gc_mu := 0; gc_g := {| gr0 := x; gr1 := 0; gr2 := 0; gr3 := 0 |} |}.

Definition g_beh (p : list GInstr) (x : nat) (g : GRegs) (mu : nat) : Prop :=
  exists n, g_terminal p (g_run n p (g_input x)) /\
            gc_g (g_run n p (g_input x)) = g /\ gc_mu (g_run n p (g_input x)) = mu.

Definition g_equiv (p q : list GInstr) : Prop :=
  forall x g mu, g_beh p x g mu <-> g_beh q x g mu.

Lemma g_terminal_dec : forall p c, {g_terminal p c} + {~ g_terminal p c}.
Proof. intros p c. unfold g_terminal. apply le_dec. Qed.

Lemma g_run_terminal_after : forall p c n m,
  g_terminal p (g_run n p c) -> n <= m -> g_run m p c = g_run n p c.
Proof.
  intros p c n m Ht Hle. replace m with (n + (m - n)) by lia.
  rewrite g_run_add. apply g_run_terminal, Ht.
Qed.

(** The behaviour is read from the actual host run of [U]. *)
Theorem g_beh_host_iff : forall amb hmu p x g mu z,
  g_wf_program p ->
  g_beh p x g mu <->
  exists F pc, (run_vm_u F U (hbc amb hmu (g_width p) p (g_input x) z)).(vm_pc) = U_END /\
               h_done_c amb hmu (g_width p) p {| gc_pc := pc; gc_mu := mu; gc_g := g |}
                 (run_vm_u F U (hbc amb hmu (g_width p) p (g_input x) z)).
Proof.
  intros amb hmu p x g mu z Hwf. pose proof (g_width_fits p) as Hfit.
  split.
  - intros (n & Ht & Hg & Hmu).
    destruct (proj1 (self_interpreter_correct amb hmu (g_width p) p Hwf Hfit (g_input x) z
                      (g_run n p (g_input x)))
                    (ex_intro _ n (conj Ht eq_refl))) as (F & HF & Hd).
    exists F, (gc_pc (g_run n p (g_input x))). split; [exact HF|].
    rewrite <- Hg, <- Hmu. destruct (g_run n p (g_input x)). exact Hd.
  - intros (F & pc & HF & Hd).
    destruct (proj2 (self_interpreter_correct amb hmu (g_width p) p Hwf Hfit (g_input x) z
                      {| gc_pc := pc; gc_mu := mu; gc_g := g |})
                    (ex_intro _ F (conj HF Hd))) as (n & Ht & He).
    exists n. split; [exact Ht|]. rewrite He. cbn. auto.
Qed.

(** * 2. Relocation.

    [reloc K q] places [q] at address K.  In-range jump targets move by K;
    out-of-range targets and falloff all land at K + length q. *)

Definition rpc (K L t : nat) : nat := if t <? L then K + t else K + L.

Definition reloc_i (K L : nat) (i : GInstr) : GInstr :=
  match i with
  | GJump t c => GJump (rpc K L t) c
  | GJnez r t c => GJnez r (rpc K L t) c
  | _ => i
  end.

Definition reloc (K : nat) (q : list GInstr) : list GInstr := map (reloc_i K (length q)) q.

Definition rconf (K L : nat) (c : GConf) : GConf :=
  {| gc_pc := rpc K L c.(gc_pc); gc_mu := c.(gc_mu); gc_g := c.(gc_g) |}.

Definition embeds (P : list GInstr) (K : nat) (q : list GInstr) : Prop :=
  forall i, i < length q -> nth_error P (K + i) = nth_error (reloc K q) i.

Lemma reloc_wf : forall K q, g_wf_program q -> g_wf_program (reloc K q).
Proof.
  intros K q Hq. unfold reloc, g_wf_program. apply Forall_map.
  eapply Forall_impl; [|exact Hq]. intros i Hi. destruct i; exact Hi.
Qed.

Lemma reloc_length : forall K q, length (reloc K q) = length q.
Proof. intros. apply map_length. Qed.

Lemma rpc_succ : forall K L pc, pc < L -> S (K + pc) = rpc K L (S pc).
Proof.
  intros K L pc H. unfold rpc. destruct (S pc <? L) eqn:E.
  - lia.
  - apply Nat.ltb_ge in E. lia.
Qed.

Lemma reloc_next : forall K L i pc mu g, pc < L ->
  g_next (reloc_i K L i) (K + pc) mu g =
  (let '(pc', mu', g') := g_next i pc mu g in (rpc K L pc', mu', g')).
Proof.
  intros K L i pc mu g H.
  destruct i; cbn [reloc_i g_next g_cost]; try (rewrite (rpc_succ K L pc H); reflexivity).
  - reflexivity.
  - destruct (Nat.eqb (g_get g r) 0); [rewrite (rpc_succ K L pc H)|]; reflexivity.
Qed.

Theorem reloc_run : forall P K q n c,
  embeds P K q ->
  (forall m, m < n -> ~ g_terminal q (g_run m q c)) ->
  g_run n P (rconf K (length q) c) = rconf K (length q) (g_run n q c).
Proof.
  intros P K q n. induction n as [|n IH]; intros c Hemb Hlive; [reflexivity|].
  assert (Hc : c.(gc_pc) < length q)
    by (pose proof (Hlive 0 ltac:(lia)) as H0; cbn [g_run] in H0; unfold g_terminal in H0; lia).
  cbn [g_run]. rewrite <- IH.
  - f_equal. unfold g_step. unfold rconf at 1. cbn [gc_pc gc_mu gc_g].
    unfold rpc at 1. rewrite (proj2 (Nat.ltb_lt _ _) Hc).
    rewrite (Hemb _ Hc). unfold reloc. rewrite nth_error_map.
    destruct (nth_error q (gc_pc c)) as [i|] eqn:Ei.
    2: { apply nth_error_None in Ei. lia. }
    cbn [option_map].
    change (gc_pc (rconf K (length q) c)) with (rpc K (length q) (gc_pc c)).
    change (gc_mu (rconf K (length q) c)) with (gc_mu c).
    change (gc_g (rconf K (length q) c)) with (gc_g c).
    unfold rpc at 1. rewrite (proj2 (Nat.ltb_lt _ _) Hc).
    rewrite (reloc_next K (length q) i _ _ _ Hc).
    destruct (g_next i (gc_pc c) (gc_mu c) (gc_g c)) as [[pc' mu'] g']. reflexivity.
  - exact Hemb.
  - intros m Hm. specialize (Hlive (S m) ltac:(lia)). cbn [g_run] in Hlive. exact Hlive.
Qed.

(** * 3. Search facts for decidable step predicates. *)

Lemma least_index : forall (T : nat -> Prop), (forall n, {T n} + {~ T n}) ->
  forall n, T n -> exists k, k <= n /\ T k /\ forall m, m < k -> ~ T m.
Proof.
  intros T dec n. induction n as [n IH] using lt_wf_ind. intros Hn.
  destruct (Nat.eq_dec n 0) as [->|Hnz].
  - exists 0. split; [lia|]. split; [exact Hn|]. intros m Hm; lia.
  - assert (Hb : (exists k, k < n /\ T k) \/ (forall k, k < n -> ~ T k)).
    { clear IH Hn Hnz. induction n as [|n IHn]; [right; intros; lia|].
      destruct IHn as [(k & Hk & Tk)|Hno].
      - left. exists k. split; [lia|exact Tk].
      - destruct (dec n) as [Tn|Tn].
        + left. exists n. split; [lia|exact Tn].
        + right. intros k Hk. destruct (Nat.eq_dec k n) as [->|Hne]; [exact Tn|].
          apply Hno. lia. }
    destruct Hb as [(k & Hk & Tk)|Hno].
    + destruct (IH k Hk Tk) as (j & Hj & Tj & Hmin). exists j. split; [lia|auto].
    + exists n. split; [lia|]. split; [exact Hn|exact Hno].
Qed.

Lemma bounded_search : forall (T : nat -> Prop), (forall n, {T n} + {~ T n}) ->
  forall m, (exists k, k <= m /\ T k) \/ (forall k, k <= m -> ~ T k).
Proof.
  intros T dec m. induction m as [|m IH].
  - destruct (dec 0) as [H|H]; [left; exists 0; auto|right; intros k Hk; replace k with 0 by lia; exact H].
  - destruct IH as [(k & Hk & Tk)|Hno].
    + left. exists k. split; [lia|exact Tk].
    + destruct (dec (S m)) as [H|H].
      * left. exists (S m). auto.
      * right. intros k Hk. destruct (Nat.eq_dec k (S m)) as [->|Hne]; [exact H|]. apply Hno. lia.
Qed.

(** * 4. Tail embedding: a program that reaches the relocated start of [w]
    has exactly the behaviour of [w] on that input. *)

Theorem tail_beh : forall P K w x N0 g mu,
  embeds P K w -> length P = K + length w ->
  g_run N0 P (g_input x) = rconf K (length w) (g_input x) ->
  g_beh P x g mu <-> g_beh w x g mu.
Proof.
  intros P K w x N0 g mu Hemb Hlen HN0.
  set (T := fun n => g_terminal w (g_run n w (g_input x))).
  assert (Tdec : forall n, {T n} + {~ T n}) by (intro n; apply g_terminal_dec).
  split.
  - intros (N & HtN & Hg & Hmu).
    set (N' := Nat.max N N0).
    assert (HN' : g_run N' P (g_input x) = g_run N P (g_input x))
      by (apply g_run_terminal_after; [exact HtN|lia]).
    replace N' with (N0 + (N' - N0)) in HN' by lia.
    rewrite g_run_add, HN0 in HN'.
    destruct (bounded_search T Tdec (N' - N0)) as [(k & Hk & Tk)|Hno].
    + destruct (least_index T Tdec k Tk) as (j & Hj & Tj & Hmin).
      pose proof (reloc_run P K w j (g_input x) Hemb Hmin) as Hr.
      exists j. split; [exact Tj|].
      assert (HPj : g_run (N' - N0) P (rconf K (length w) (g_input x)) =
                    g_run j P (rconf K (length w) (g_input x))).
      { apply g_run_terminal_after; [|lia].
        rewrite Hr. unfold g_terminal, rconf, rpc; cbn [gc_pc].
        unfold T, g_terminal in Tj. rewrite Hlen.
        destruct (gc_pc (g_run j w (g_input x)) <? length w) eqn:E;
          [apply Nat.ltb_lt in E; lia|lia]. }
      rewrite HPj, Hr in HN'. unfold rconf in HN'.
      rewrite <- HN' in Hg, Hmu. cbn in Hg, Hmu. split; assumption.
    + exfalso.
      assert (Hlive : forall m, m < N' - N0 -> ~ g_terminal w (g_run m w (g_input x)))
        by (intros m Hm; apply (Hno m); lia).
      pose proof (reloc_run P K w (N' - N0) (g_input x) Hemb Hlive) as Hr.
      rewrite Hr in HN'. unfold g_terminal in HtN. rewrite <- HN' in HtN.
      unfold rconf, rpc in HtN; cbn [gc_pc] in HtN.
      pose proof (Hno (N' - N0) ltac:(lia)) as Hnt. unfold T, g_terminal in Hnt.
      destruct (gc_pc (g_run (N' - N0) w (g_input x)) <? length w) eqn:E.
      * apply Nat.ltb_lt in E. lia.
      * apply Nat.ltb_ge in E. lia.
  - intros (n & Htn & Hg & Hmu).
    destruct (least_index T Tdec n Htn) as (j & Hj & Tj & Hmin).
    assert (Hsame : g_run j w (g_input x) = g_run n w (g_input x))
      by (symmetry; apply g_run_terminal_after; [exact Tj|lia]).
    pose proof (reloc_run P K w j (g_input x) Hemb Hmin) as Hr.
    exists (N0 + j). rewrite g_run_add, HN0, Hr.
    unfold T, g_terminal in Tj.
    unfold g_terminal, rconf, rpc; cbn [gc_pc gc_g gc_mu].
    rewrite Hsame in *. split; [|split; assumption].
    rewrite Hlen. destruct (gc_pc (g_run n w (g_input x)) <? length w) eqn:E;
      [apply Nat.ltb_lt in E; lia|lia].
Qed.

(** * 5. The effective transformer. *)

Definition qprog (p : list mm2_instr) : list GInstr := cm2_compile (mm2_guest_program p).

Definition rice_pre (a b Lq : nat) : list GInstr :=
  [GXfer 2 0 0; GLoadImm 0 a 0; GLoadImm 1 b 0; GJump (rpc 4 Lq 5) 0].

Definition rice_restore : list GInstr :=
  [GXfer 0 2 0; GLoadImm 1 0 0; GLoadImm 2 0 0; GLoadImm 3 0 0].

Definition rice_prog (pm : MM2_PROBLEM) (w : list GInstr) : list GInstr :=
  let '(p, a, b) := pm in
  rice_pre a b (length (qprog p)) ++ reloc 4 (qprog p) ++ rice_restore ++
  reloc (8 + length (qprog p)) w.

Definition g_bottom : list GInstr := [GJump 0 0].

Lemma g_bottom_wf : g_wf_program g_bottom.
Proof. apply Forall_cons; [unfold g_wf; cbn [g_dst g_rs1 g_rs2 g_cost]; lia|apply Forall_nil]. Qed.

Lemma g_bottom_beh : forall x g mu, ~ g_beh g_bottom x g mu.
Proof.
  intros x g mu (n & Ht & _). unfold g_terminal in Ht.
  assert (H : forall m mu' g', g_run m g_bottom {| gc_pc := 0; gc_mu := mu'; gc_g := g' |} =
      {| gc_pc := 0; gc_mu := mu'; gc_g := g' |}).
  { induction m as [|m IH]; intros; [reflexivity|]. cbn [g_run].
    unfold g_step. cbn. rewrite Nat.add_0_r. apply IH. }
  unfold g_input in Ht. rewrite H in Ht. cbn in Ht. lia.
Qed.

Lemma rice_prog_wf : forall pm w, g_wf_program w -> g_wf_program (rice_prog pm w).
Proof.
  intros [[p a] b] w Hw. unfold rice_prog, g_wf_program.
  apply Forall_app; split; [|apply Forall_app; split; [|apply Forall_app; split]].
  - repeat (apply Forall_cons; [unfold g_wf; cbn [g_dst g_rs1 g_rs2 g_cost]; lia|]).
    apply Forall_nil.
  - apply reloc_wf, cm2_compile_wf.
  - repeat (apply Forall_cons; [unfold g_wf; cbn [g_dst g_rs1 g_rs2 g_cost]; lia|]).
    apply Forall_nil.
  - apply reloc_wf, Hw.
Qed.

Lemma rice_prog_length : forall p a b w,
  length (rice_prog (p, a, b) w) = 8 + length (qprog p) + length w.
Proof.
  intros. unfold rice_prog. rewrite !app_length, !reloc_length. cbn. lia.
Qed.

Lemma rice_embeds_q : forall p a b w, embeds (rice_prog (p, a, b) w) 4 (qprog p).
Proof.
  intros p a b w i Hi. unfold rice_prog.
  rewrite nth_error_app2 by (cbn [rice_pre rice_restore length]; lia). cbn [rice_pre length].
  replace (4 + i - 4) with i by lia.
  rewrite nth_error_app1 by (rewrite reloc_length; exact Hi). reflexivity.
Qed.

Lemma rice_embeds_w : forall p a b w,
  embeds (rice_prog (p, a, b) w) (8 + length (qprog p)) w.
Proof.
  intros p a b w i Hi. unfold rice_prog.
  rewrite nth_error_app2 by (cbn [rice_pre rice_restore length]; lia). cbn [rice_pre length].
  rewrite nth_error_app2 by (rewrite reloc_length; lia). rewrite reloc_length.
  rewrite nth_error_app2 by (cbn [rice_pre rice_restore length]; lia). cbn [rice_restore length].
  f_equal. lia.
Qed.

(** The compiled MM2 guest never writes guest register 2 and has zero cost. *)
Lemma qprog_keeps : forall p n c,
  gr2 (gc_g (g_run n (qprog p) c)) = gr2 (gc_g c) /\ gc_mu (g_run n (qprog p) c) = gc_mu c.
Proof.
  intros p n. induction n as [|n IH]; intro c; [auto|].
  cbn [g_run]. destruct (IH (g_step (qprog p) c)) as [H2 Hm]. rewrite H2, Hm.
  unfold g_step. destruct (nth_error (qprog p) (gc_pc c)) as [i|] eqn:Ei; [|auto].
  assert (Hin : In i (qprog p)) by (eapply nth_error_In; exact Ei).
  unfold qprog, cm2_compile in Hin. generalize dependent Hin.
  generalize 0 at 1. generalize (length (mm2_guest_program p)).
  induction (mm2_guest_program p) as [|ci r IHr]; intros len a Hin; [contradiction|].
  cbn [compile_aux] in Hin. apply in_app_or in Hin. destruct Hin as [Hin|Hin].
  - destruct c as [pc mu [x0 x1 x2 x3]].
    destruct ci; cbn [cm2_block In] in Hin;
      repeat (destruct Hin as [<-|Hin]; [cbn; try destruct (Nat.eqb _ 0); cbn; split; lia|]);
      contradiction.
  - exact (IHr len (S a) Hin).
Qed.

(** Four prefix steps load the MM2 input and enter the relocated guest. *)
Lemma rice_prefix_run : forall p a b w x,
  g_run 4 (rice_prog (p, a, b) w) (g_input x) =
  rconf 4 (length (qprog p))
    {| gc_pc := 5; gc_mu := 0; gc_g := {| gr0 := a; gr1 := b; gr2 := x; gr3 := 0 |} |}.
Proof. intros. reflexivity. Qed.

Lemma rpc_zero : forall K L, rpc K L 0 = K.
Proof. intros K L. unfold rpc. destruct (0 <? L) eqn:E; [lia|apply Nat.ltb_ge in E; lia]. Qed.

Lemma g_run_S_at : forall n P c i,
  nth_error P c.(gc_pc) = Some i ->
  g_run (S n) P c =
  g_run n P (let '(pc', mu', g') := g_next i c.(gc_pc) c.(gc_mu) c.(gc_g) in
             {| gc_pc := pc'; gc_mu := mu'; gc_g := g' |}).
Proof. intros n P c i H. cbn [g_run]. unfold g_step. rewrite H. reflexivity. Qed.

Lemma rice_nth_restore : forall p a b w k, k < 4 ->
  nth_error (rice_prog (p, a, b) w) (4 + length (qprog p) + k) = nth_error rice_restore k.
Proof.
  intros p a b w k Hk. unfold rice_prog.
  rewrite nth_error_app2 by (cbn [rice_pre length]; lia). cbn [rice_pre length].
  rewrite nth_error_app2 by (rewrite reloc_length; lia). rewrite reloc_length.
  rewrite nth_error_app1 by (cbn [rice_restore length]; lia). f_equal. lia.
Qed.

Lemma rice_restore_run : forall p a b w x g,
  gr2 g = x ->
  g_run 4 (rice_prog (p, a, b) w) {| gc_pc := 4 + length (qprog p); gc_mu := 0; gc_g := g |} =
  rconf (8 + length (qprog p)) (length w) (g_input x).
Proof.
  intros p a b w x [g0 g1 g2 g3] H2. cbn [gr2] in H2. subst g2.
  rewrite (g_run_S_at _ _ _ (GXfer 0 2 0))
    by (cbn [gc_pc]; rewrite <- (Nat.add_0_r (4 + _)) at 1; apply (rice_nth_restore p a b w 0); lia).
  cbn [g_next g_cost g_get g_set gc_pc gc_mu gc_g gr0 gr1 gr2 gr3].
  rewrite (g_run_S_at _ _ _ (GLoadImm 1 0 0))
    by (cbn [gc_pc]; replace (S (4 + length (qprog p))) with (4 + length (qprog p) + 1) by lia;
        apply (rice_nth_restore p a b w 1); lia).
  cbn [g_next g_cost g_get g_set gc_pc gc_mu gc_g gr0 gr1 gr2 gr3].
  rewrite (g_run_S_at _ _ _ (GLoadImm 2 0 0))
    by (cbn [gc_pc]; replace (S (S (4 + length (qprog p)))) with (4 + length (qprog p) + 2) by lia;
        apply (rice_nth_restore p a b w 2); lia).
  cbn [g_next g_cost g_get g_set gc_pc gc_mu gc_g gr0 gr1 gr2 gr3].
  rewrite (g_run_S_at _ _ _ (GLoadImm 3 0 0))
    by (cbn [gc_pc]; replace (S (S (S (4 + length (qprog p))))) with (4 + length (qprog p) + 3) by lia;
        apply (rice_nth_restore p a b w 3); lia).
  cbn [g_run g_next g_cost g_get g_set gc_pc gc_mu gc_g gr0 gr1 gr2 gr3].
  unfold rconf, g_input. cbn [gc_pc gc_mu gc_g]. rewrite rpc_zero. f_equal.
Qed.

(** * 6. Behaviour of the transformer. *)

Theorem rice_prog_halting : forall pm w,
  g_wf_program w -> MM2_HALTING pm -> g_equiv (rice_prog pm w) w.
Proof.
  intros [[p a] b] w Hw Hh x g mu.
  unfold MM2_HALTING in Hh. apply mm2_termination_guest_iff in Hh. destruct Hh as (final & Hh).
  set (cq := {| gc_pc := 5; gc_mu := 0; gc_g := {| gr0 := a; gr1 := b; gr2 := x; gr3 := 0 |} |}).
  assert (Hc : crel (mm2_guest_config (1, (a, b))) cq) by (unfold crel; cbn; lia).
  destruct (cm2_compile_complete _ _ _ _ Hh Hc) as (n & Ht & _).
  set (T := fun m => g_terminal (qprog p) (g_run m (qprog p) cq)).
  destruct (least_index T (fun m => g_terminal_dec _ _) n Ht) as (j & _ & Tj & Hmin).
  pose proof (reloc_run _ 4 (qprog p) j cq (rice_embeds_q p a b w) Hmin) as Hr.
  destruct (qprog_keeps p j cq) as (H2 & Hmu).
  apply (tail_beh _ (8 + length (qprog p)) w x (4 + j + 4)).
  - apply rice_embeds_w.
  - rewrite rice_prog_length. lia.
  - rewrite !g_run_add, rice_prefix_run. fold cq. rewrite Hr.
    unfold rconf at 1. unfold T, g_terminal in Tj. unfold rpc.
    rewrite (proj2 (Nat.ltb_ge _ _) Tj).
    cbn [gc_mu gc_g] in *. rewrite Hmu. apply rice_restore_run. rewrite H2. reflexivity.
Qed.

Theorem rice_prog_nonhalting : forall pm w x g mu,
  g_beh (rice_prog pm w) x g mu -> MM2_HALTING pm.
Proof.
  intros [[p a] b] w x g mu (N & HtN & _).
  unfold MM2_HALTING. apply mm2_termination_guest_iff.
  set (cq := {| gc_pc := 5; gc_mu := 0; gc_g := {| gr0 := a; gr1 := b; gr2 := x; gr3 := 0 |} |}).
  assert (Hc : crel (mm2_guest_config (1, (a, b))) cq) by (unfold crel; cbn; lia).
  set (N' := Nat.max N 4).
  assert (HN' : g_run N' (rice_prog (p, a, b) w) (g_input x) = g_run N (rice_prog (p, a, b) w) (g_input x))
    by (apply g_run_terminal_after; [exact HtN|lia]).
  replace N' with (4 + (N' - 4)) in HN' by lia.
  rewrite g_run_add, rice_prefix_run in HN'. fold cq in HN'.
  set (T := fun m => g_terminal (qprog p) (g_run m (qprog p) cq)).
  destruct (bounded_search T (fun m => g_terminal_dec _ _) (N' - 4)) as [(k & _ & Tk)|Hno].
  - destruct (cm2_compile_sound _ k _ _ Hc Tk) as (final & Hh & _). exists final. exact Hh.
  - exfalso.
    assert (Hlive : forall m, m < N' - 4 -> ~ g_terminal (qprog p) (g_run m (qprog p) cq))
      by (intros m Hm; apply (Hno m); lia).
    pose proof (reloc_run _ 4 (qprog p) (N' - 4) cq (rice_embeds_q p a b w) Hlive) as Hr.
    rewrite Hr in HN'. unfold g_terminal in HtN. rewrite <- HN', rice_prog_length in HtN.
    pose proof (Hno (N' - 4) ltac:(lia)) as Hnt. unfold T, g_terminal in Hnt.
    unfold rconf, rpc in HtN. cbn [gc_pc] in HtN.
    destruct (gc_pc (g_run (N' - 4) (qprog p) cq) <? length (qprog p)) eqn:E.
    + apply Nat.ltb_lt in E. lia.
    + apply Nat.ltb_ge in E. lia.
Qed.

