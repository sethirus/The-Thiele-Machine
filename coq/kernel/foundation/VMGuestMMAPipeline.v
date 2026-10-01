(** VMGuestMMAPipeline.v: the composite guest program that evaluates a
    one-input alternate Minsky program with exact semantics.

    Shape.  For a program [P] in the [MMA_computable] shape for one input
    (counters [S (S n)]), the pipeline is
      [g_mma_init n ++ reloc Li C ++ reloc (Li + Lc) g_exact_epilogue]
    where [C] is the three-counter guest compilation of the reduced and
    swapped program, [Li] and [Lc] are the lengths of the first two parts.
    Every instruction of the initializer and of the compiled part costs 0.
    The relocation clamps every out-of-range jump of [C] to the start of the
    epilogue, so no jump of [C] can land inside the epilogue.

    Exactness.  The compiled part reaches a terminal configuration if and
    only if [P] halts.  The reverse direction runs the guest simulation
    backwards (a terminal guest state is only reached after the three-counter
    program halts), undoes the counter swap, and pulls termination back
    through the vendored compilers ([compiler_t_term_equiv]) and through the
    output epilogue of [mma_with_output].  Determinism of the small-step
    semantics then pins the final pc, the final ledger (0) and register 0.

    Composition.  [g_pipeline_beh] states the pipeline's behaviour as the
    epilogue's behaviour on the output of [P]; divergence of [P] gives no
    behaviour at all. *)

From Coq Require Import Arith Lia List.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss
  compiler_correction.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs
  mma3_mma2_compiler.
From Kernel Require Import VMSelfGuest VMSelfRun VMSelfRice
  MMAOutputEpilogue VMMMA3GuestCompiler VMMMAReduction VMGuestMMAInit
  VMGuestExactEpilogue.

(** * 1. Generic facts about guest runs. *)

(** Behaviour from an arbitrary start configuration. *)
Definition g_beh_from (p : list GInstr) (c : GConf) (g : GRegs) (mu : nat)
    : Prop :=
  exists n, g_terminal p (g_run n p c) /\
            gc_g (g_run n p c) = g /\ gc_mu (g_run n p c) = mu.

Lemma g_beh_from_input : forall p x g mu,
  g_beh p x g mu <-> g_beh_from p (g_input x) g mu.
Proof. intros. reflexivity. Qed.

Lemma g_beh_from_shift : forall p c N g mu,
  g_beh_from p c g mu <-> g_beh_from p (g_run N p c) g mu.
Proof.
  intros p c N g mu. split.
  - intros (n & Ht & Hg & Hmu).
    assert (He : g_run (N + n) p c = g_run n p c)
      by (apply g_run_terminal_after; [exact Ht|lia]).
    exists n. rewrite <- g_run_add, He. auto.
  - intros (k & Ht & Hg & Hmu). exists (N + k). rewrite g_run_add. auto.
Qed.

Lemma g_beh_from_terminal : forall p c g mu,
  g_terminal p c -> (g_beh_from p c g mu <-> gc_g c = g /\ gc_mu c = mu).
Proof.
  intros p c g mu Ht. split.
  - intros (n & _ & Hg & Hmu).
    rewrite g_run_terminal in Hg, Hmu by exact Ht. auto.
  - intros [Hg Hmu]. exists 0. cbn [g_run]. auto.
Qed.

Lemma g_first_terminal : forall p c n,
  g_terminal p (g_run n p c) ->
  exists j, j <= n /\ g_run j p c = g_run n p c /\
            forall m, m < j -> ~ g_terminal p (g_run m p c).
Proof.
  intros p c n Ht.
  destruct (least_index (fun k => g_terminal p (g_run k p c))
              (fun k => g_terminal_dec p (g_run k p c)) n Ht)
    as (j & Hj & Tj & Hmin).
  exists j. split; [exact Hj|]. split; [|exact Hmin].
  symmetry. apply g_run_terminal_after; [exact Tj|exact Hj].
Qed.

(** A run that stays inside [p] is a run of [p ++ q]. *)
Lemma g_run_prefix : forall n p q c,
  (forall m, m < n -> ~ g_terminal p (g_run m p c)) ->
  g_run n (p ++ q) c = g_run n p c.
Proof.
  induction n as [|n IH]; intros p q c Hlive; [reflexivity|].
  assert (Hc : gc_pc c < length p).
  { pose proof (Hlive 0 ltac:(lia)) as H0. cbn [g_run] in H0.
    unfold g_terminal in H0. lia. }
  cbn [g_run].
  replace (g_step (p ++ q) c) with (g_step p c).
  - apply IH. intros m Hm. exact (Hlive (S m) ltac:(lia)).
  - unfold g_step. rewrite nth_error_app1 by exact Hc. reflexivity.
Qed.

Lemma rconf_terminal : forall K L c, L <= gc_pc c ->
  rconf K L c = {| gc_pc := K + L; gc_mu := gc_mu c; gc_g := gc_g c |}.
Proof.
  intros K L c H. unfold rconf, rpc. destruct (gc_pc c <? L) eqn:E.
  - apply Nat.ltb_lt in E. lia.
  - reflexivity.
Qed.

(** A relocated program that terminates leaves the host at its end address
    with the same ledger and registers. *)
Lemma reloc_reach_end : forall P K w c n,
  embeds P K w -> g_terminal w (g_run n w c) ->
  exists j, g_run j P (rconf K (length w) c) =
    {| gc_pc := K + length w; gc_mu := gc_mu (g_run n w c);
       gc_g := gc_g (g_run n w c) |}.
Proof.
  intros P K w c n Hemb Ht.
  destruct (g_first_terminal w c n Ht) as (j & _ & Hj & Hmin).
  exists j. rewrite (reloc_run P K w j c Hemb Hmin), Hj.
  apply rconf_terminal. exact Ht.
Qed.

Lemma reloc_live : forall P K w c n,
  embeds P K w -> (forall m, m <= n -> ~ g_terminal w (g_run m w c)) ->
  gc_pc (g_run n P (rconf K (length w) c)) < K + length w.
Proof.
  intros P K w c n Hemb Hlive.
  rewrite (reloc_run P K w n c Hemb) by (intros m Hm; apply Hlive; lia).
  pose proof (Hlive n (le_n n)) as Hn. unfold g_terminal in Hn.
  unfold rconf, rpc; cbn [gc_pc].
  destruct (gc_pc (g_run n w c) <? length w) eqn:E;
    [apply Nat.ltb_lt in E; lia|apply Nat.ltb_ge in E; lia].
Qed.

(** A host that terminates from the relocated start forces the relocated
    program to terminate. *)
Lemma reloc_beh_needs : forall P K w c g mu,
  embeds P K w -> K + length w <= length P ->
  g_beh_from P (rconf K (length w) c) g mu ->
  exists k, g_terminal w (g_run k w c).
Proof.
  intros P K w c g mu Hemb Hlen (n & Ht & _ & _).
  destruct (bounded_search (fun k => g_terminal w (g_run k w c))
              (fun k => g_terminal_dec w (g_run k w c)) n)
    as [(k & _ & Tk)|Hno].
  - exists k. exact Tk.
  - exfalso. pose proof (reloc_live P K w c n Hemb Hno) as H.
    unfold g_terminal in Ht. lia.
Qed.

Lemma reloc_tail_beh : forall P K w c g mu,
  embeds P K w -> length P = K + length w ->
  g_beh_from P (rconf K (length w) c) g mu <-> g_beh_from w c g mu.
Proof.
  intros P K w c g mu Hemb Hlen. split.
  - intros Hb.
    destruct (reloc_beh_needs P K w c g mu Hemb ltac:(lia) Hb) as (k & Tk).
    destruct (reloc_reach_end P K w c k Hemb Tk) as (j & Hj).
    rewrite (g_beh_from_shift P _ j), Hj in Hb.
    rewrite g_beh_from_terminal in Hb by (unfold g_terminal; cbn [gc_pc]; lia).
    cbn [gc_g gc_mu] in Hb. destruct Hb as [Hg Hmu].
    exists k. auto.
  - intros (k & Tk & Hg & Hmu).
    destruct (reloc_reach_end P K w c k Hemb Tk) as (j & Hj).
    exists j. rewrite Hj.
    split; [unfold g_terminal; cbn [gc_pc]; lia|cbn [gc_g gc_mu]; auto].
Qed.

(** Zero-cost programs never move the ledger. *)
Lemma g_next_mu : forall i pc mu g,
  snd (fst (g_next i pc mu g)) = mu + g_cost i.
Proof.
  intros i pc mu g. destruct i; cbn [g_next fst snd]; reflexivity.
Qed.

Lemma g_run_mu_cost0 : forall p n c,
  Forall (fun i => g_cost i = 0) p -> gc_mu (g_run n p c) = gc_mu c.
Proof.
  intros p n. induction n as [|n IH]; intros c H; [reflexivity|].
  cbn [g_run]. rewrite IH by exact H. unfold g_step.
  destruct (nth_error p (gc_pc c)) as [i|] eqn:E; [|reflexivity].
  pose proof (proj1 (Forall_forall _ _) H i (nth_error_In _ _ E)) as Hi.
  cbn beta in Hi.
  pose proof (g_next_mu i (gc_pc c) (gc_mu c) (gc_g c)) as Hm.
  destruct (g_next i (gc_pc c) (gc_mu c) (gc_g c)) as [[pc' mu'] g'].
  cbn [fst snd gc_mu] in *. lia.
Qed.

Lemma mma3_compile_aux_cost0 : forall p a len,
  Forall (fun i => g_cost i = 0) (mma3_compile_aux a len p).
Proof.
  induction p as [|i p IH]; intros a len; [constructor|].
  cbn [mma3_compile_aux]. apply Forall_app. split; [|apply IH].
  destruct i; cbn [mma3_block]; repeat constructor.
Qed.

Lemma mma3_compile_cost0 : forall p,
  Forall (fun i => g_cost i = 0) (mma3_compile p).
Proof. intro p. apply mma3_compile_aux_cost0. Qed.

Lemma reloc_cost0 : forall K q,
  Forall (fun i => g_cost i = 0) q -> Forall (fun i => g_cost i = 0) (reloc K q).
Proof.
  intros K q Hq. unfold reloc. apply Forall_map.
  eapply Forall_impl; [|exact Hq]. intros i Hi. destruct i; exact Hi.
Qed.

(** * 2. Termination facts for alternate Minsky machines. *)

(** A run that reaches an out-of-code state is a prefix of every longer run
    from the same start. *)
Lemma mma_steps_split : forall k (Q : nat * list (mm_instr (pos k))) j t t1,
  sss_steps (@mma_sss k) Q j t t1 ->
  forall m t', sss_steps (@mma_sss k) Q m t t' -> out_code (fst t') Q ->
  j <= m /\ sss_steps (@mma_sss k) Q (m - j) t1 t'.
Proof.
  intros k Q j t t1 H.
  induction H as [t|j t t2 t1 H12 H21 IH]; intros m t' Hm Hout.
  - split; [lia|]. rewrite Nat.sub_0_r. exact Hm.
  - inversion Hm as [t0 E1 E2|m' ta tb tc Hab Hbc E1 E2 E3]; subst.
    + exfalso. exact (sss_out_step_stall Hout H12).
    + rewrite (sss_step_fun (@mma_sss_fun k) H12 Hab) in *.
      destruct (IH m' t' Hbc Hout) as [Hle Hs].
      split; [lia|]. replace (S m' - S j) with (m' - j) by lia. exact Hs.
Qed.

(** Backward simulation: if every in-code source step is matched by at least
    one target step, target termination implies source termination. *)
Lemma mma_back_sim : forall a b (P : list (mm_instr (pos a)))
    (Q : list (mm_instr (pos b))) (R : mm_state a -> mm_state b -> Prop),
  (forall s t, R s t -> in_code (fst s) (1, P) ->
     exists s1 t1, sss_step (@mma_sss a) (1, P) s s1 /\
                   sss_progress (@mma_sss b) (1, Q) t t1 /\ R s1 t1) ->
  forall s t, R s t -> sss_terminates (@mma_sss b) (1, Q) t ->
  sss_terminates (@mma_sss a) (1, P) s.
Proof.
  intros a b P Q R Hsim s t HR (t' & (m & Hm) & Hout).
  revert s t HR Hm. induction m as [m IH] using lt_wf_ind.
  intros s t HR Hm.
  destruct (in_out_code_dec (fst s) (1, P)) as [Hin|Hoc].
  - destruct (Hsim s t HR Hin) as (s1 & t1 & Hst & (j & Hj & Hjs) & HR1).
    destruct (mma_steps_split b (1, Q) j t t1 Hjs m t' Hm Hout) as [Hle Hrest].
    destruct (IH (m - j) ltac:(lia) s1 t1 HR1 Hrest)
      as (s' & (q & Hq) & Hoc').
    exists s'. split; [exists (S q); exact (in_sss_steps_S Hst Hq)|exact Hoc'].
  - exists s. split; [exists 0; constructor|exact Hoc].
Qed.

Lemma mma_with_output_term : forall n (P : list (mm_instr (pos (S (S n))))) start,
  sss_terminates (@mma_sss (S (S n) + 1)) (1, @mma_with_output (S n) pos1 P)
    (1, mma_extend_vec start 0) ->
  sss_terminates (@mma_sss (S (S n))) (1, P) (1, start).
Proof.
  intros n P start H.
  refine (mma_back_sim (S (S n)) (S (S n) + 1) P (@mma_with_output (S n) pos1 P)
    (fun s t => t = (mma_exit_link (length P) (fst s), mma_extend_vec (snd s) 0))
    _ (1, start) (1, mma_extend_vec start 0) _ H).
  - intros [pc v] t -> Hin. cbn [fst snd] in *.
    unfold in_code, code_start, code_end in Hin. cbn [fst snd] in Hin.
    destruct pc as [|a]; [lia|].
    destruct (nth_error P a) as [i|] eqn:Hi;
      [|apply nth_error_None in Hi; lia].
    destruct (mma_sss_total i (S a, v)) as [s1 Hs1].
    exists s1, (mma_exit_link (length P) (fst s1), mma_extend_vec (snd s1) 0).
    assert (Hst : sss_step (@mma_sss (S (S n))) (1, P) (S a, v) s1)
      by exact (sss_step_from_nth _ _ (@mma_sss (S (S n))) P a i v s1 Hi Hs1).
    split; [exact Hst|]. split; [|reflexivity].
    rewrite mma_exit_link_inside by lia.
    exists 1. split; [lia|].
    apply (in_sss_steps_S (mma_with_output_main_step (S n) pos1 P (S a) v s1 0 Hst)).
    constructor.
  - cbn [fst snd]. rewrite mma_exit_link_one. reflexivity.
Qed.

Lemma mma_cast_term : forall a b (e : a = b) p start,
  sss_terminates (@mma_sss b) (1, mma_cast_program e p) (1, mma_cast_vec e start) ->
  sss_terminates (@mma_sss a) (1, p) (1, start).
Proof. intros a b e p start H. destruct e. exact H. Qed.

Lemma mma_reduce_all_term : forall n p start,
  sss_terminates (@mma_sss 3) (1, mma_reduce_all n p) (1, mma_pack_all n start) ->
  sss_terminates (@mma_sss (3 + n)) (1, p) (1, start).
Proof.
  induction n as [|n IH]; intros p start H; [exact H|].
  cbn [mma_reduce_all mma_pack_all] in H.
  apply IH in H.
  exact (proj2 (compiler_t_term_equiv (mma3_mma2_compiler (S n)) (1, p) 1 start
           (mma_pack_vec (S n) start) (mma_pack_vec_sim (S n) start)) H).
Qed.

Lemma mma3_swap_instr_involutive : forall i,
  mma3_swap_instr (mma3_swap_instr i) = i.
Proof.
  intros [x|x t]; cbn [mma3_swap_instr]; rewrite mma3_swap_pos_involutive;
    reflexivity.
Qed.

Lemma mma3_swap_program_involutive : forall p,
  mma3_swap_program (mma3_swap_program p) = p.
Proof.
  intro p. unfold mma3_swap_program. rewrite map_map.
  rewrite <- (map_id p) at 2. apply map_ext.
  intro i. apply mma3_swap_instr_involutive.
Qed.

Lemma mma3_swap_term : forall p v,
  sss_terminates (@mma_sss 3) (1, mma3_swap_program p) (1, mma3_swap_vec v) ->
  sss_terminates (@mma_sss 3) (1, p) (1, v).
Proof.
  intros p v ([pc w] & (k & Hk) & Hout).
  pose proof (mma3_swap_program_steps _ _ _ _ Hk) as Hs.
  rewrite mma3_swap_program_involutive in Hs.
  change (mma3_swap_state (1, mma3_swap_vec v))
    with (1, mma3_swap_vec (mma3_swap_vec v)) in Hs.
  rewrite mma3_swap_vec_involutive in Hs.
  exists (mma3_swap_state (pc, w)). split; [exists k; exact Hs|].
  unfold out_code, code_start, code_end in *. cbn [fst snd mma3_swap_state] in *.
  unfold mma3_swap_program in Hout. rewrite map_length in Hout. exact Hout.
Qed.

(** * 3. Backward guest simulation of the three-counter compiler. *)

Lemma mma3_guest_back : forall q fuel s gc,
  mma3_rel (length q) s gc ->
  g_terminal (mma3_compile q) (g_run fuel (mma3_compile q) gc) ->
  exists s', sss_output (@mma_sss 3) (1, q) s s' /\
             mma3_rel (length q) s' (g_run fuel (mma3_compile q) gc).
Proof.
  intros q fuel. induction fuel as [fuel IH] using lt_wf_ind.
  intros [pc v] gc Hrel Ht.
  pose proof Hrel as Hr. unfold mma3_rel in Hr. destruct Hr as (Hpc & _).
  assert (Hout_case : pc = 0 \/ S (length q) <= pc -> exists s',
            sss_output (@mma_sss 3) (1, q) (pc, v) s' /\
            mma3_rel (length q) s' (g_run fuel (mma3_compile q) gc)).
  { intro Hcase.
    assert (Hgt : g_terminal (mma3_compile q) gc).
    { unfold g_terminal. rewrite mma3_compile_length, Hpc. unfold mma3_addr.
      destruct (pc =? 0) eqn:E; [lia|apply Nat.eqb_neq in E; lia]. }
    rewrite (g_run_terminal fuel _ _ Hgt).
    exists (pc, v). split; [|exact Hrel].
    split; [exists 0; constructor|].
    unfold out_code, code_start, code_end; cbn [fst snd]. lia. }
  destruct pc as [|a]; [apply Hout_case; left; reflexivity|].
  destruct (le_lt_dec (length q) a) as [Hhi|Hlo];
    [apply Hout_case; right; lia|].
  destruct (nth_error q a) as [i|] eqn:Hi; [|apply nth_error_None in Hi; lia].
  destruct (mma_sss_total i (S a, v)) as [s1 Hs1].
  destruct (mma3_step_sim q a i v s1 gc Hi Hs1 Hrel) as (f1 & Hf1 & Hrel1).
  assert (Hstep : sss_step (@mma_sss 3) (1, q) (S a, v) s1)
    by exact (sss_step_from_nth _ _ (@mma_sss 3) q a i v s1 Hi Hs1).
  destruct (le_lt_dec f1 fuel) as [Hle|Hgt].
  - assert (Hsplit : g_run fuel (mma3_compile q) gc =
                     g_run (fuel - f1) (mma3_compile q) (g_run f1 (mma3_compile q) gc))
      by (rewrite <- g_run_add; f_equal; lia).
    rewrite Hsplit in Ht |- *.
    destruct (IH (fuel - f1) ltac:(lia) s1 _ Hrel1 Ht) as (s' & Hout & Hrel').
    exists s'. split; [|exact Hrel'].
    destruct Hout as ((k & Hk) & Hoc).
    split; [exists (S k); exact (in_sss_steps_S Hstep Hk)|exact Hoc].
  - assert (Heq : g_run f1 (mma3_compile q) gc = g_run fuel (mma3_compile q) gc)
      by (apply g_run_terminal_after; [exact Ht|lia]).
    rewrite Heq in Hrel1. exists s1. split; [|exact Hrel1].
    split; [exists 1; exact (in_sss_steps_S Hstep (in_sss_steps_0 _ _ _))|].
    destruct s1 as [pc1 v1]. unfold mma3_rel in Hrel1. destruct Hrel1 as (Hpc1 & _).
    unfold g_terminal in Ht. rewrite mma3_compile_length, Hpc1 in Ht.
    unfold mma3_addr in Ht.
    unfold out_code, code_start, code_end; cbn [fst snd].
    destruct (pc1 =? 0) eqn:E; [apply Nat.eqb_eq in E; lia|apply Nat.eqb_neq in E; lia].
Qed.

(** * 4. The compiled stage: exact in both directions. *)

Definition mma_pipe3 (n : nat) (P : list (mm_instr (Fin.t (S (S n)))))
    : list (mm_instr (Fin.t 3)) :=
  mma_reduce_all n (mma_cast_program (mma_dim_eq n) (@mma_with_output (S n) pos1 P)).

Definition mma_pipe_code (n : nat) (P : list (mm_instr (Fin.t (S (S n)))))
    : list GInstr :=
  mma3_compile (mma3_swap_program (mma_pipe3 n P)).

Definition mma_pipe_start (z n : nat) : GConf :=
  mma3_guest_start (mma3_swap_vec (mma_init_start3 z n)).

(** REVERSE: a terminal configuration of the compiled program is reached only
    after [P] halts, and it is then exact. *)
Theorem mma_pipe_reverse : forall n (P : list (mm_instr (Fin.t (S (S n))))) z fuel,
  g_terminal (mma_pipe_code n P)
    (g_run fuel (mma_pipe_code n P) (mma_pipe_start z n)) ->
  exists pc final,
    sss_output (@mma_sss (S (S n))) (1, P) (1, mma_init_start z n) (pc, final) /\
    gc_pc (g_run fuel (mma_pipe_code n P) (mma_pipe_start z n)) =
      length (mma_pipe_code n P) /\
    gc_mu (g_run fuel (mma_pipe_code n P) (mma_pipe_start z n)) = 0 /\
    gr0 (gc_g (g_run fuel (mma_pipe_code n P) (mma_pipe_start z n))) =
      vec_pos final pos0.
Proof.
  intros n P z fuel Ht. unfold mma_pipe_code in *.
  destruct (mma3_guest_back (mma3_swap_program (mma_pipe3 n P)) fuel
    (1, mma3_swap_vec (mma_init_start3 z n)) (mma_pipe_start z n)
    (mma3_guest_start_rel _ _) Ht) as (s' & Hq & Hrel).
  assert (H3 : sss_terminates (@mma_sss 3) (1, mma_pipe3 n P) (1, mma_init_start3 z n))
    by (apply mma3_swap_term; exists s'; exact Hq).
  unfold mma_pipe3, mma_init_start3 in H3.
  apply mma_reduce_all_term in H3.
  apply mma_cast_term in H3.
  apply mma_with_output_term in H3.
  destruct H3 as ([pc final] & Hout).
  exists pc, final. split; [exact Hout|].
  destruct (mma_output_to_three n P (mma_init_start z n) pc final Hout)
    as (target & Hthree & Hval).
  pose proof (mma3_swap_output _ _ _ _ Hthree) as Hsw.
  change (mma_reduce_all n (mma_cast_program (mma_dim_eq n)
            (@mma_with_output (S n) pos1 P))) with (mma_pipe3 n P) in Hsw.
  change (mma_pack_all n (mma_cast_vec (mma_dim_eq n)
            (mma_extend_vec (mma_init_start z n) 0))) with (mma_init_start3 z n) in Hsw.
  pose proof (sss_output_fun (@mma_sss_fun 3) Hq Hsw) as Es'. subst s'.
  unfold mma3_rel in Hrel. destruct Hrel as (Hpc & H0 & _ & _).
  split; [|split].
  - rewrite Hpc, mma3_compile_length.
    unfold mma3_swap_program. rewrite !map_length. unfold mma3_addr.
    replace (1 + length (mma_pipe3 n P) =? 0) with false by reflexivity. lia.
  - rewrite g_run_mu_cost0 by apply mma3_compile_cost0. reflexivity.
  - rewrite H0, mma3_swap_vec_lookup, (proj1 mma3_swap_pos_values). exact Hval.
Qed.

(** FORWARD: if [P] halts, the compiled program reaches exactly its end with
    ledger 0 and the output in register 0. *)
Theorem mma_pipe_forward : forall n (P : list (mm_instr (Fin.t (S (S n))))) z pc final,
  sss_output (@mma_sss (S (S n))) (1, P) (1, mma_init_start z n) (pc, final) ->
  exists fuel,
    g_terminal (mma_pipe_code n P)
      (g_run fuel (mma_pipe_code n P) (mma_pipe_start z n)) /\
    gc_pc (g_run fuel (mma_pipe_code n P) (mma_pipe_start z n)) =
      length (mma_pipe_code n P) /\
    gc_mu (g_run fuel (mma_pipe_code n P) (mma_pipe_start z n)) = 0 /\
    gr0 (gc_g (g_run fuel (mma_pipe_code n P) (mma_pipe_start z n))) =
      vec_pos final pos0.
Proof.
  intros n P z pc final Hout.
  destruct (mma_output_to_guest_r0 n P (mma_init_start z n) pc final Hout)
    as (fuel & Hres). cbn zeta in Hres. destruct Hres as [Ht _].
  exists fuel.
  assert (Ht' : g_terminal (mma_pipe_code n P)
                  (g_run fuel (mma_pipe_code n P) (mma_pipe_start z n)))
    by exact Ht.
  destruct (mma_pipe_reverse n P z fuel Ht')
    as (pc' & final' & Hout' & Hpc & Hmu & H0).
  pose proof (sss_output_fun (@mma_sss_fun _) Hout Hout') as E.
  injection E as _ Ef. subst final'.
  auto.
Qed.

(** * 5. The composite guest program. *)

Definition g_pipeline (n : nat) (P : list (mm_instr (Fin.t (S (S n)))))
    : list GInstr :=
  g_mma_init n ++ reloc (length (g_mma_init n)) (mma_pipe_code n P) ++
  reloc (length (g_mma_init n) + length (mma_pipe_code n P)) g_exact_epilogue.

Theorem g_pipeline_wf : forall n P, g_wf_program (g_pipeline n P).
Proof.
  intros n P. unfold g_pipeline, g_wf_program. apply Forall_app.
  split; [apply g_mma_init_wf|].
  apply Forall_app. split; apply reloc_wf;
    [apply mma3_compile_wf|apply g_exact_epilogue_wf].
Qed.

(** Every instruction before the epilogue costs 0. *)
Lemma g_pipeline_prefix_cost0 : forall n P,
  Forall (fun i => g_cost i = 0)
    (g_mma_init n ++ reloc (length (g_mma_init n)) (mma_pipe_code n P)).
Proof.
  intros n P. apply Forall_app. split; [apply g_mma_init_cost_zero|].
  apply reloc_cost0, mma3_compile_cost0.
Qed.

Lemma g_pipeline_length : forall n P,
  length (g_pipeline n P) =
  length (g_mma_init n) + length (mma_pipe_code n P) + length g_exact_epilogue.
Proof.
  intros n P. unfold g_pipeline. rewrite !app_length, !reloc_length. lia.
Qed.

Lemma g_pipeline_embeds_code : forall n P,
  embeds (g_pipeline n P) (length (g_mma_init n)) (mma_pipe_code n P).
Proof.
  intros n P i Hi. unfold g_pipeline.
  rewrite nth_error_app2 by lia.
  replace (length (g_mma_init n) + i - length (g_mma_init n)) with i by lia.
  rewrite nth_error_app1 by (rewrite reloc_length; exact Hi). reflexivity.
Qed.

Lemma g_pipeline_embeds_epi : forall n P,
  embeds (g_pipeline n P) (length (g_mma_init n) + length (mma_pipe_code n P))
    g_exact_epilogue.
Proof.
  intros n P i Hi. unfold g_pipeline. rewrite app_assoc.
  rewrite nth_error_app2 by (rewrite app_length, reloc_length; lia).
  rewrite app_length, reloc_length. f_equal. lia.
Qed.

(** The initializer hands over to the compiled stage at its start. *)
Lemma g_pipeline_init : forall n P z, exists N0,
  g_run N0 (g_pipeline n P) (g_input z) =
  rconf (length (g_mma_init n)) (length (mma_pipe_code n P)) (mma_pipe_start z n).
Proof.
  intros n P z. destruct (g_mma_init_run n z) as (fuel & Hrun).
  assert (Ht : g_terminal (g_mma_init n) (g_run fuel (g_mma_init n) (g_input z)))
    by (rewrite Hrun; unfold g_terminal; cbn [gc_pc]; lia).
  destruct (g_first_terminal _ _ _ Ht) as (j & _ & Hj & Hmin).
  exists j. unfold g_pipeline. rewrite g_run_prefix by exact Hmin.
  rewrite Hj, Hrun. unfold rconf, mma_pipe_start, mma3_guest_start.
  cbn [gc_pc gc_mu gc_g]. rewrite rpc_zero. reflexivity.
Qed.

(** * 6. The epilogue stage. *)

(** [epi_beh m g mu]: the epilogue started at pc 0 with ledger 0 and
    register 0 holding [m] terminates with registers [g] and ledger [mu]. *)
Definition epi_beh (m : nat) (g : GRegs) (mu : nat) : Prop :=
  g_beh g_exact_epilogue m g mu.

(** The epilogue overwrites registers 1..3 before reading them, so its
    behaviour depends only on register 0. *)
Lemma epi_from_any : forall m r1 r2 r3 g mu,
  g_beh_from g_exact_epilogue
    {| gc_pc := 0; gc_mu := 0;
       gc_g := {| gr0 := m; gr1 := r1; gr2 := r2; gr3 := r3 |} |} g mu <->
  epi_beh m g mu.
Proof.
  intros m r1 r2 r3 g mu. unfold epi_beh. rewrite g_beh_from_input.
  rewrite (g_beh_from_shift _ _ 3), (g_beh_from_shift _ (g_input m) 3).
  assert (E : g_run 3 g_exact_epilogue
                {| gc_pc := 0; gc_mu := 0;
                   gc_g := {| gr0 := m; gr1 := r1; gr2 := r2; gr3 := r3 |} |} =
              g_run 3 g_exact_epilogue (g_input m)) by reflexivity.
  rewrite E. reflexivity.
Qed.

Lemma epi_beh_pack : forall g' m' g mu,
  epi_beh (g_out_pack g' m') g mu <-> g = g' /\ mu = m'.
Proof.
  intros g' m' g mu. destruct (g_exact_epilogue_run g' m' 0 0 0 0) as (f & Hf).
  unfold epi_beh. rewrite g_beh_from_input, (g_beh_from_shift _ _ f).
  change (g_input (g_out_pack g' m')) with
    {| gc_pc := 0; gc_mu := 0;
       gc_g := {| gr0 := g_out_pack g' m'; gr1 := 0; gr2 := 0; gr3 := 0 |} |}.
  rewrite Hf, g_beh_from_terminal by (unfold g_terminal; cbn [gc_pc]; lia).
  cbn [gc_g gc_mu]. split; intros [H1 H2]; subst; split; reflexivity.
Qed.

(** * 7. Composition. *)

Lemma g_pipeline_beh_via : forall n P z k g mu,
  g_terminal (mma_pipe_code n P) (g_run k (mma_pipe_code n P) (mma_pipe_start z n)) ->
  (g_beh (g_pipeline n P) z g mu <->
   epi_beh (gr0 (gc_g (g_run k (mma_pipe_code n P) (mma_pipe_start z n)))) g mu).
Proof.
  intros n P z k g mu Ht.
  destruct (g_pipeline_init n P z) as (N0 & HN0).
  rewrite g_beh_from_input, (g_beh_from_shift _ _ N0), HN0.
  destruct (reloc_reach_end (g_pipeline n P) (length (g_mma_init n))
    (mma_pipe_code n P) (mma_pipe_start z n) k (g_pipeline_embeds_code n P) Ht)
    as (j & Hj).
  rewrite (g_beh_from_shift _ _ j), Hj.
  destruct (mma_pipe_reverse n P z k Ht) as (pc & final & _ & _ & Hmu & _).
  rewrite Hmu.
  destruct (gc_g (g_run k (mma_pipe_code n P) (mma_pipe_start z n)))
    as [r0 r1 r2 r3].
  cbn [gr0].
  replace {| gc_pc := length (g_mma_init n) + length (mma_pipe_code n P);
             gc_mu := 0;
             gc_g := {| gr0 := r0; gr1 := r1; gr2 := r2; gr3 := r3 |} |} with
    (rconf (length (g_mma_init n) + length (mma_pipe_code n P))
       (length g_exact_epilogue)
       {| gc_pc := 0; gc_mu := 0;
          gc_g := {| gr0 := r0; gr1 := r1; gr2 := r2; gr3 := r3 |} |})
    by (unfold rconf; cbn [gc_pc gc_mu gc_g]; rewrite rpc_zero; reflexivity).
  rewrite reloc_tail_beh by first [apply g_pipeline_embeds_epi|apply g_pipeline_length].
  apply epi_from_any.
Qed.

(** COMPOSITION: the pipeline's behaviour is exactly the epilogue's
    behaviour on the output of [P]. *)
Theorem g_pipeline_beh : forall n (P : list (mm_instr (Fin.t (S (S n))))) z g mu,
  g_beh (g_pipeline n P) z g mu <->
  exists pc final,
    sss_output (@mma_sss (S (S n))) (1, P) (1, mma_init_start z n) (pc, final) /\
    epi_beh (vec_pos final pos0) g mu.
Proof.
  intros n P z g mu. split.
  - intros Hb.
    destruct (g_pipeline_init n P z) as (N0 & HN0).
    pose proof Hb as Hb'.
    rewrite g_beh_from_input, (g_beh_from_shift _ _ N0), HN0 in Hb'.
    assert (Hle : length (g_mma_init n) + length (mma_pipe_code n P) <=
                  length (g_pipeline n P)) by (rewrite g_pipeline_length; lia).
    destruct (reloc_beh_needs (g_pipeline n P) (length (g_mma_init n))
      (mma_pipe_code n P) (mma_pipe_start z n) g mu
      (g_pipeline_embeds_code n P) Hle Hb') as (k & Hk).
    destruct (mma_pipe_reverse n P z k Hk) as (pc & final & Hout & _ & _ & H0).
    exists pc, final. split; [exact Hout|]. rewrite <- H0.
    apply (proj1 (g_pipeline_beh_via n P z k g mu Hk)). exact Hb.
  - intros (pc & final & Hout & He).
    destruct (mma_pipe_forward n P z pc final Hout) as (k & Hk & _ & _ & H0).
    apply (proj2 (g_pipeline_beh_via n P z k g mu Hk)). rewrite H0. exact He.
Qed.

(** Divergence: if [P] never halts from the input, the pipeline has no
    behaviour on it. *)
Corollary g_pipeline_diverges : forall n (P : list (mm_instr (Fin.t (S (S n))))) z,
  ~ sss_terminates (@mma_sss (S (S n))) (1, P) (1, mma_init_start z n) ->
  forall g mu, ~ g_beh (g_pipeline n P) z g mu.
Proof.
  intros n P z Hdiv g mu Hb.
  apply g_pipeline_beh in Hb. destruct Hb as (pc & final & Hout & _).
  apply Hdiv. exists (pc, final). exact Hout.
Qed.

(** With packed outputs the epilogue decodes the output exactly. *)
Corollary g_pipeline_beh_pack : forall n (P : list (mm_instr (Fin.t (S (S n))))) z g mu,
  (forall pc final,
     sss_output (@mma_sss (S (S n))) (1, P) (1, mma_init_start z n) (pc, final) ->
     exists g' mu', vec_pos final pos0 = g_out_pack g' mu') ->
  (g_beh (g_pipeline n P) z g mu <->
   exists pc final,
     sss_output (@mma_sss (S (S n))) (1, P) (1, mma_init_start z n) (pc, final) /\
     vec_pos final pos0 = g_out_pack g mu).
Proof.
  intros n P z g mu Hpack. rewrite g_pipeline_beh. split.
  - intros (pc & final & Hout & He). exists pc, final. split; [exact Hout|].
    destruct (Hpack pc final Hout) as (g' & mu' & Hv).
    rewrite Hv in He |- *. apply epi_beh_pack in He.
    destruct He as [-> ->]. reflexivity.
  - intros (pc & final & Hout & Hv). exists pc, final. split; [exact Hout|].
    rewrite Hv. apply epi_beh_pack. auto.
Qed.

(** Under packed outputs, halting is exact in both directions. *)
Corollary g_pipeline_halts_pack : forall n (P : list (mm_instr (Fin.t (S (S n))))) z,
  (forall pc final,
     sss_output (@mma_sss (S (S n))) (1, P) (1, mma_init_start z n) (pc, final) ->
     exists g' mu', vec_pos final pos0 = g_out_pack g' mu') ->
  ((exists g mu, g_beh (g_pipeline n P) z g mu) <->
   sss_terminates (@mma_sss (S (S n))) (1, P) (1, mma_init_start z n)).
Proof.
  intros n P z Hpack. split.
  - intros (g & mu & Hb). apply g_pipeline_beh in Hb.
    destruct Hb as (pc & final & Hout & _). exists (pc, final). exact Hout.
  - intros ([pc final] & Hout).
    destruct (Hpack pc final Hout) as (g & mu & Hv).
    exists g, mu. apply (proj2 (g_pipeline_beh_pack n P z g mu Hpack)).
    exists pc, final. auto.
Qed.

Print Assumptions g_pipeline_wf.
Print Assumptions g_pipeline_prefix_cost0.
Print Assumptions mma_pipe_reverse.
Print Assumptions mma_pipe_forward.
Print Assumptions epi_from_any.
Print Assumptions g_pipeline_beh.
Print Assumptions g_pipeline_diverges.
Print Assumptions g_pipeline_beh_pack.
Print Assumptions g_pipeline_halts_pack.
