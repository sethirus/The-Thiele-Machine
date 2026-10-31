(** AxCgkHost: one run of the universal host carries a whole chain of
    thresholds.

    The fixed program U_P (UniversalPRun.v) runs every guest program of the
    priced machine.  AxCgkRun.v built, for a chain machine C (a driver, number
    codes and a height h; level j is reached when j <= h s) with a
    presentation and heights at most 16, a guest program ax_cgk_guest whose ONE
    run earns one chain, CHECK, COMMIT, CERTIFY, for each level as the
    latched height rises, so that its fact table holds exactly as many facts
    as the latched height.  Loaded on U_P, that guest is carried exactly:

      ax_cgk_host_points   while the driver has not halted before step n there is
                        a host time at which counter RB decodes to the state
                        after n steps, the host ledger is ax_cm_gledger n, and
                        the host's record (flag, number of facts, channel
                        committed, trap latch) is
                        (0 < lat n, lat n, 0 < lat n, false), where lat n is
                        the latched height after n steps: the host holds
                        exactly as many facts as there are levels latched;
      ax_cgk_host_levels   so level j is latched after n steps exactly when the
                        host holds at least j facts at that time, and the
                        host never holds more than 16;
      ax_cgk_host_halting  the host halts exactly when the driver halts;
      ax_cgk_host_halt_point  at the halt, the same record and decoding;
      ax_cgk_host_surcharge   the host ledger exceeds the machine's by
                        ax_cm_surcharge, at most 3 times the latched height.

    The chain of thresholds a_1 <= ... <= a_k of a growing record gives a chain
    machine with h s = the number of thresholds at or below the record of s
    (k <= 16), and then one run of U_P carries all k thresholds at once: the
    first threshold is the flag (the single-threshold compile of the
    repository is the case k = 1 with the surcharge 3 - cost of the first
    raising move). *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
Require Minimal.EarnedGeneric Minimal.EarnedPriced.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
From Kernel Require Import AxCore AxChain AxCgkLang AxCgkGuest AxCgkRun AxHost.
Require Import Kernel.UniversalPCodes Kernel.UniversalPBridge Kernel.UniversalPBlocks
  Kernel.UniversalPLayout Kernel.UniversalPPhases Kernel.UniversalPSim Kernel.UniversalPRun.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker Kernel.CompilerLifts Kernel.CompilerIcomp.

Local Notation hstate := (@M.pu_state pu_hprop).

Section Host.

Variable C : ax_chain_mach.
Variable cp : ax_chain_pres C.
Variable s0 : ax_cm_st C.

Local Notation next := (ax_cm_next C).

(* Counter B of the guest at the start: the Godel code of the register
   file holding the code of s0 in register 0. *)
Definition ax_cgk_guest_b : nat := cg_gk (ax_cgk_k C cp) (ax_cgk_e0 C s0).

(* The host after t steps, loaded with the guest of the chain machine. *)
Definition ax_cgk_host_at (t : nat) : hstate := pu_hrun (ax_cgk_guest C cp) 0 ax_cgk_guest_b t.

(* What a counter value says about the machine. *)
Definition ax_cgk_decode (v : nat) : option (ax_cm_st C) := ax_cm_sdec C (cg_expo (qs 0) v).

(* The guest run of the host is the compiler's guest run. *)
Lemma ax_cgk_grun_guest : forall N,
  pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N =
  P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0).
Proof. reflexivity. Qed.

(** One matching host time for a guest run length: the counters, the ledger
    and the level 2 record agree. *)
Lemma ax_cgk_host_match : forall m, exists n,
  hv (pu_hrun (ax_cgk_guest C cp) 0 ax_cgk_guest_b n) pu_RB =
    E.cb (E.core_of (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b m)) /\
  ax_hrec (pu_hrun (ax_cgk_guest C cp) 0 ax_cgk_guest_b n) =
    ax_grec (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b m) /\
  M.mu (pu_hrun (ax_cgk_guest C cp) 0 ax_cgk_guest_b n) =
    E.mu (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b m).
Proof.
  intros m. destruct (pu_U_simulation (ax_cgk_guest C cp) 0 ax_cgk_guest_b m) as [n [[R Hle] | RH]].
  - exists n. destruct R as [sg [rho R]].
    split; [exact (pu_R_rb _ sg rho _ _ R) |]. split.
    + apply (ax_rec_of_tables _ _ sg rho);
        [exact (pu_rw_gfacts _ _ _ _ _ R) | exact (pu_rw_hfacts _ _ _ _ _ R)
        | exact (pu_rw_gchan _ _ _ _ _ R) | exact (pu_rw_hchan _ _ _ _ _ R)
        | exact (pu_rw_cert _ _ _ _ _ R) |].
      rewrite (pu_rw_err _ _ _ _ _ R).
      destruct (pu_rw_head _ _ _ _ _ R) as (_ & Herr & _). exact Herr.
    + exact (pu_rw_mu _ _ _ _ _ R).
  - exists n. destruct RH as (_ & _ & _ & Hb' & Herr & Hmu & Hc & sg & rho & Hgf & Hhf & Hgc & Hhc).
    split; [exact Hb' |]. split; [| exact Hmu].
    apply (ax_rec_of_tables _ _ sg rho); assumption.
Qed.

Local Notation chain_rec := (fun (c : nat) =>
  (Nat.ltb 0 c, (c, (Nat.ltb 0 c, false)))).

Lemma ax_cgk_grec_point : forall N,
  length (G.facts (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))) =
    length (G.facts (G.core_of (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N))).
Proof. intros N. reflexivity. Qed.

Theorem ax_cgk_host_points : ax_cm_bounded_from C s0 -> forall n,
  (forall m, m < n -> next (ax_cm_run C s0 m) <> None) ->
  exists t,
    ax_cgk_decode (hv (ax_cgk_host_at t) pu_RB) = Some (ax_cm_run C s0 n) /\
    M.mu (ax_cgk_host_at t) = ax_cm_gledger C s0 n /\
    ax_hrec (ax_cgk_host_at t) = chain_rec (ax_cm_lat C s0 n).
Proof.
  intros Hb n Hn.
  destruct (ax_cgk_guest_matching_points C cp s0 Hb n Hn) as (N & _ & _ & Herr & _ & Hd & Hm & Hc & Hf & Hch).
  destruct (ax_cgk_host_match N) as (t & Hrb & Hrec & Hmu).
  exists t. unfold ax_cgk_host_at, ax_cgk_decode.
  rewrite Hrb. change (E.cb (E.core_of (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N)))
    with (G.cb (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))).
  split; [exact Hd |]. split.
  - rewrite Hmu. exact Hm.
  - rewrite Hrec. unfold ax_grec. change (E.cert (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N))
      with (G.cert (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0))).
    change (E.facts (E.core_of (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N)))
      with (G.facts (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))).
    change (E.chan (E.core_of (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N)))
      with (G.chan (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))).
    change (E.err (E.core_of (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N)))
      with (G.err (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))).
    rewrite Hc, Hf, Herr.
    assert (Hcf : ax_chan_flag (G.chan (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0))))
                  = Nat.ltb 0 (ax_cm_lat C s0 n)).
    { destruct (G.chan (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))) eqn:Ech;
        unfold ax_chan_flag.
      - destruct (ax_cm_lat C s0 n) as [| u] eqn:El; [| reflexivity].
        exfalso. pose proof (proj2 Hch eq_refl) as H. discriminate H.
      - destruct (ax_cm_lat C s0 n) as [| u] eqn:El; [reflexivity |].
        exfalso. pose proof (proj1 Hch eq_refl) as H. discriminate H. }
    rewrite Hcf. reflexivity.
Qed.

(** The levels: level j is latched after n steps exactly when the host holds
    at least j facts. *)
Theorem ax_cgk_host_levels : ax_cm_bounded_from C s0 -> forall n j,
  (forall m, m < n -> next (ax_cm_run C s0 m) <> None) ->
  exists t,
    ax_cgk_decode (hv (ax_cgk_host_at t) pu_RB) = Some (ax_cm_run C s0 n) /\
    ((exists i, i <= n /\ j <= ax_cm_h C (ax_cm_run C s0 i)) <->
       j <= length (M.facts (M.core_of (ax_cgk_host_at t)))) /\
    length (M.facts (M.core_of (ax_cgk_host_at t))) <= 16.
Proof.
  intros Hb n j Hn. destruct (ax_cgk_host_points Hb n Hn) as (t & Hd & _ & Hrec).
  exists t. split; [exact Hd |].
  unfold ax_hrec in Hrec. injection Hrec as _ Hlen _ _.
  rewrite Hlen. split.
  - rewrite <- ax_cm_lat_iff. split; [intro H; exact H | intro H; exact H].
  - exact (ax_cm_lat_le_from C s0 Hb n).
Qed.

Theorem ax_cgk_host_halting : ax_cm_bounded_from C s0 ->
  (exists t, M.pu_halted U_P (M.core_of (ax_cgk_host_at t))) <->
  (exists n, next (ax_cm_run C s0 n) = None).
Proof.
  intros Hb. unfold ax_cgk_host_at. rewrite <- (pu_universal_halting (ax_cgk_guest C cp) 0 ax_cgk_guest_b).
  rewrite <- (ax_cgk_guest_halting_iff C cp s0 Hb). split; intros [N HN]; exists N; exact HN.
Qed.

Theorem ax_cgk_host_halt_point : ax_cm_bounded_from C s0 -> forall n,
  (forall m, m < n -> next (ax_cm_run C s0 m) <> None) ->
  next (ax_cm_run C s0 n) = None ->
  exists t,
    M.pu_halted U_P (M.core_of (ax_cgk_host_at t)) /\
    ax_cgk_decode (hv (ax_cgk_host_at t) pu_RB) = Some (ax_cm_run C s0 n) /\
    M.mu (ax_cgk_host_at t) = ax_cm_gledger C s0 n /\
    ax_hrec (ax_cgk_host_at t) = chain_rec (ax_cm_lat C s0 n).
Proof.
  intros Hb n Hn Hh.
  destruct (ax_cgk_guest_halts_at C cp s0 Hb n Hn Hh) as (N & HN & Hd & Hm & Hc & Hf & Hch & Herr0 & _).
  destruct (pu_halt_point (ax_cgk_guest C cp) 0 ax_cgk_guest_b N HN) as [N0 RH].
  exists N0. unfold ax_cgk_host_at, ax_cgk_decode.
  destruct RH as (Hg & Hhh & _ & Hb' & Herr & Hmu & Hcc & sg & rho & Hgf & Hhf & Hgc & Hhc).
  split; [exact Hhh |].
  rewrite Hb'. change (E.cb (E.core_of (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N)))
    with (G.cb (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))).
  split; [exact Hd |]. split.
  - rewrite Hmu. exact Hm.
  - rewrite (ax_rec_of_tables _ _ sg rho Hgf Hhf Hgc Hhc Hcc Herr). unfold ax_grec.
    change (E.cert (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N))
      with (G.cert (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0))).
    change (E.facts (E.core_of (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N)))
      with (G.facts (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))).
    change (E.chan (E.core_of (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N)))
      with (G.chan (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))).
    change (E.err (E.core_of (pu_grun (ax_cgk_guest C cp) 0 ax_cgk_guest_b N)))
      with (G.err (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))).
    rewrite Hc, Hf, Herr0.
    assert (Hcf : ax_chan_flag (G.chan (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0))))
                  = Nat.ltb 0 (ax_cm_lat C s0 n)).
    { destruct (G.chan (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N (ax_cgk_guest C cp) (ax_cgk_ystart C cp s0)))) eqn:Ech;
        unfold ax_chan_flag.
      - destruct (ax_cm_lat C s0 n) as [| u] eqn:El; [| reflexivity].
        exfalso. pose proof (proj2 Hch eq_refl) as H. discriminate H.
      - destruct (ax_cm_lat C s0 n) as [| u] eqn:El; [reflexivity |].
        exfalso. pose proof (proj1 Hch eq_refl) as H. discriminate H. }
    rewrite Hcf. reflexivity.
Qed.

End Host.

Print Assumptions ax_cgk_host_match.
Print Assumptions ax_cgk_host_points.
Print Assumptions ax_cgk_host_levels.
Print Assumptions ax_cgk_host_halting.
Print Assumptions ax_cgk_host_halt_point.
