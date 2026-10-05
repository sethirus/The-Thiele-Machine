Lemma cg_not_halted_before : forall m,
  rd (presented_run M s0 m) = true ->
  (forall m', m' < m -> rd (presented_run M s0 m') = false) ->
  forall h, h < m -> pm_next M (presented_run M s0 h) <> None.
Proof.
  intros m Hm Hb h Hh E.
  destruct (presented_halted_stable M s0 h m E ltac:(lia)) as [Hr _].
  rewrite Hr, (Hb h Hh) in Hm. discriminate.
Qed.

Lemma cg_latch_before : forall m,
  (forall m', m' < m -> rd (presented_run M s0 m') = false) ->
  forall m', m' < m -> mlatch M s0 m' = false.
Proof.
  intros m Hb m' Hm'. destruct (mlatch M s0 m') eqn:L; [| reflexivity].
  apply presented_mlatch_iff in L. destruct L as (k & Hk & Hr).
  rewrite (Hb k ltac:(lia)) in Hr. discriminate.
Qed.

(* At the first index m whose reading is yes, the guest reaches the image
   of NEW with the record unearned, the flag down, S holding the code of
   the state after m steps, and the fixed checker accepting. *)
Lemma cg_y_new : forall m,
  rd (presented_run M s0 m) = true ->
  (forall m', m' < m -> rd (presented_run M s0 m') = false) ->
  exists L ex a, G.pc (G.core_of (Yrun s0 L)) = lnk (cg_NEW M pc) /\
    cg_simul K (ex, a) (Yrun s0 L) /\ cg_a_earned a = false /\ cg_a_cert a = false /\
    ex 0 = sc (presented_run M s0 m) /\ cg_ueval (URun R) (cg_gk K ex) = true.
Proof.
  intros m Hm Hb. destruct m as [| m'].
  - destruct (cg_x_to_new M pc s0 0 (cg_e0 M s0) (cg_mkaux 0 false false)
                (cg_e0_rf M pc s0) Hm) as (ex & t & Hex & Hp & Hck).
    assert (Hx : sss_progress (cg_xstep K R) (1, SRC)
                   (1, (cg_e0 M s0, cg_mkaux 0 false false))
                   (cg_NEW M pc, (ex, cg_mkaux 0 false false))).
    { eapply sss_progress_trans; [| exact Hp].
      apply cg_x_dec0 with (x := 8); [exact (cg_sc_jmp0 M pc) |].
      rewrite (cg_e0_rf M pc s0). reflexivity. }
    destruct (cg_y_phase 1 _ _ _ _ Hx cg_ystart_simul (eq_sym (cg_link_start (1, SRC) 1)))
      as (q & w & _ & Hrun & Hpc & Hsim).
    exists q, ex, (cg_mkaux 0 false false). rewrite Hrun.
    split; [exact Hpc |]. split; [exact Hsim |]. split; [reflexivity |]. split; [reflexivity |].
    split; [rewrite Hex; reflexivity | exact Hck].
  - assert (Hnh := cg_not_halted_before (S m') Hm Hb).
    destruct (cg_y_head m' (fun h Hh => Hnh h ltac:(lia))) as (N & _ & [e a] & [He Ha] & Hpc & Hsim).
    cbn [fst snd] in He, Ha.
    destruct (pm_next M (presented_run M s0 m')) as [i |] eqn:E;
      [| exfalso; exact (Hnh m' ltac:(lia) E)].
    assert (Hl : mlatch M s0 m' = false) by (apply (cg_latch_before (S m') Hb); lia).
    rewrite Hl in He, Ha.
    destruct (cg_x_move M pc _ i 0 e a He E) as (e1 & He1 & H1).
    assert (Hrd : rd (cstep (presented_run M s0 m') i) = true).
    { rewrite presented_run_succ, E in Hm. exact Hm. }
    destruct (cg_x_to_new M pc _ _ e1 a He1 Hrd) as (ex & t & Hex & Hp & Hck).
    assert (Hx : sss_progress (cg_xstep K R) (1, SRC) (2, (e, a)) (cg_NEW M pc, (ex, a)))
      by (eapply sss_progress_trans; [exact H1 | exact Hp]).
    destruct (cg_y_phase 2 _ _ _ _ Hx Hsim Hpc) as (q & w & _ & Hrun & Hpc' & Hsim').
    exists (N + q), ex, a. rewrite cg_run_prog_add, Hrun.
    split; [exact Hpc' |]. split; [exact Hsim' |]. subst a.
    split; [reflexivity |]. split; [reflexivity |].
    split; [| exact Hck]. rewrite Hex. cbn. rewrite presented_run_succ, E. reflexivity.
Qed.

Theorem cg_guest_earned : forall N, G.cert (Yrun s0 N) = true ->
  P.pr_passing_checks cg_uprop_eqb cg_ueval
    (P.pr_trace_of cg_uprop_eqb cg_ueval N cg_guest (cg_ystart s0)) (cg_ystart s0) = 1 /\
  exists L m, L < N /\
    rd (presented_run M s0 m) = true /\
    (forall m', m' < m -> rd (presented_run M s0 m') = false) /\
    P.pr_next_instr cg_guest (G.core_of (Yrun s0 L)) = Some (P.CHECK (URun R) G.CB) /\
    G.check_ok cg_ueval (G.core_of (Yrun s0 L)) (URun R) G.CB = true /\
    pm_sdec M (cg_expo (qs 0) (G.cb (G.core_of (Yrun s0 L)))) = Some (presented_run M s0 m) /\
    (forall L', L' < N ->
       cg_passes_at cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) L' = 1 -> L' = L).
Proof.
  intros N HN.
  destruct (proj1 cg_guest_flag_iff (ex_intro _ N HN)) as [n Hn].
  destruct (cg_first_true n n (le_n n) Hn) as (m & Hm & Hb).
  destruct (cg_y_new m Hm Hb) as (L & ex & a & Hpc & Hsim & Hea & Hca & Hex0 & Hck).
  destruct Hsim as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
  cbn [cg_a_mu cg_a_cert cg_a_earned] in H4, H5, H7, H8.
  destruct (H7 Hea) as [Hf _].
  assert (Hnext : P.pr_next_instr cg_guest (G.core_of (Yrun s0 L)) = Some (P.CHECK (URun R) G.CB)).
  { unfold P.pr_next_instr. rewrite H6, Hpc, cg_fetch_new. reflexivity. }
  assert (Hok : G.check_ok cg_ueval (G.core_of (Yrun s0 L)) (URun R) G.CB = true).
  { unfold G.check_ok. rewrite H6, Hf. cbn [G.val]. rewrite H2, Hck. reflexivity. }
  assert (Hpass : cg_passes_at cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) L = 1).
  { unfold cg_passes_at. cbv zeta. rewrite Hnext. unfold P.pr_passes. rewrite Hok. reflexivity. }
  assert (HLN : L < N).
  { destruct (le_lt_dec N L) as [Hle | Hlt]; [| exact Hlt].
    pose proof (cg_cert_mono _ _ _ _ _ N L Hle HN) as C. rewrite H5, Hca in C. discriminate. }
  assert (Hup : cg_psum cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) N <= 1).
  { destruct (cg_cover N) as (N' & n' & [e' a'] & HN' & _ & Hsim').
    destruct Hsim' as (_ & _ & _ & _ & _ & _ & K7 & K8).
    pose proof (P.pr_facts_count_program cg_uprop_eqb cg_ueval N' cg_guest (cg_ystart s0)) as Hc.
    rewrite cg_passing_sum in Hc. cbn [cg_ystart G.start G.start_core G.core_of G.facts length] in Hc.
    assert (Hl1 : length (G.facts (G.core_of (Yrun s0 N'))) <= 1).
    { destruct (cg_a_earned a') eqn:Ea.
      - rewrite (proj2 (K8 eq_refl)). lia.
      - rewrite (proj1 (K7 eq_refl)). simpl. lia. }
    generalize (cg_psum_mono _ cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) N N' HN'). lia. }
  assert (Hlow := cg_psum_ge _ cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) N L HLN).
  split.
  { rewrite cg_passing_sum. lia. }
  exists L, m. split; [exact HLN |]. split; [exact Hm |]. split; [exact Hb |].
  split; [exact Hnext |]. split; [exact Hok |]. split.
  { rewrite H2, cg_expo_gk_zero by exact H3. rewrite Hex0. apply pm_sdec_scode. }
  intros L' HL' Hp'. destruct (Nat.eq_dec L' L) as [-> | Hne]; [reflexivity |].
  generalize (cg_psum_two _ cg_uprop_eqb cg_ueval cg_guest (cg_ystart s0) N L L' HLN HL'
                ltac:(congruence)). lia.
Qed.

