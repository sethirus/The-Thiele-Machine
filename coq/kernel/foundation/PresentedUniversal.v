(** PresentedUniversal.v: one fixed universal Thiele machine runs every
    computably presented Thiele machine.

    The host is the machine of EarnedMultiPriced.v with the one property
    PSlot of UniversalPCodes.v, whose checker is the fixed universal checker
    cg_ueval of CompilerChecker.v. The host program is the one fixed
    program U_P of UniversalPLayout.v. Neither depends on the machine being
    run.

    A computably presented machine is a presented machine M of Presented.v
    (a certification system with a driver and number codes for states and
    moves) together with a presentation pc : cg_presentation M of
    Presentation.v (four mu-recursive algorithms computing the driver, the
    step, the cost and the reading on codes). The compiler of
    CompilerGuest.v and CompilerGuestRun.v turns (M, pc) into a guest
    program cg_guest M pc of the priced machine of EarnedPriced.v over the
    property language cg_uprop, started from cg_ystart M pc s0 =
    G.start 0 b with b = pu_guest_b s0 the Godel code of the start state.

    Running U_P on the encoding of that guest (pu_host_at M pc s0 t is the
    host after t steps from hload (cg_guest M pc) 0 b):

      presented_universal_halting
          some host run halts exactly when the driver of M halts;
      presented_universal_points
          before M halts, for every step count n there is a host time at
          which counter RB decodes (the exponent of the first prime, then
          pm_sdec) to the state of M after n steps, the host ledger is
          M's ledger plus the surcharge, and the host flag is M's latch;
      presented_universal_halt_point
          when M first halts at step n, the host halts with the same
          decoding, ledger and flag;
      presented_universal_flag_iff
          the host flag rises exactly when M's reading is yes at some
          state of its driven run;
      presented_universal_earned
          when the host flag is up, the host's own trace contains its
          earned chain CHECK, COMMIT, CERTIFY on one slot of bank B, the
          slot holding at the CHECK the pair (code of URun r, v) for the
          one fixed routine code r of the guest; the universal checker
          accepts URun r at v; and v decodes to a state of M's driven run
          whose reading is yes;
      presented_universal
          the five together.

    The surcharge is the one of Presented.v: 0 while the latch is down;
    once it is up, 3 minus the cost of the first raising move. Corollaries:

      presented_universal_exact
          when the reading starts at no and the first raising move costs
          at least 3, the surcharge is 0 and the host ledger equals M's
          ledger at every matching point;
      presented_universal_surcharge_le_two
          when the reading starts at no, the host ledger exceeds M's ledger
          by at most 2 at every matching point;
      presented_universal_no_exact_below_three
          no run of the host machine from a clean start (U_P or any other
          program) can raise its flag with a ledger growth below 3, so a
          latch raised with ledger below 3 forces a surcharge; the
          surcharge is unavoidable.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, the compiler files, Presented.v and the UniversalP*.v files.
    No axioms, no Admitted.                                                 *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the presented universal machine of
   PresentedUniversal.v and imports only the Coq standard library, the
   vendored coq-undecidability library and the standard-library files under
   minimal/. Its link to the abstract record (the priced host as a
   CertificationSystem, the cost floor of its runs, and the undecidability
   of U_P's halting problem) lives in PricedHostLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
Require Import Kernel.UniversalPCodes Kernel.UniversalPBridge Kernel.UniversalPBlocks
  Kernel.UniversalPLayout Kernel.UniversalPPhases Kernel.UniversalPSim
  Kernel.UniversalPRun.
Require Minimal.ThieleComplete.
Require Import Minimal.Presented Kernel.Presentation.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker Kernel.CompilerGuest
  Kernel.CompilerGuestRun.
Module T := Minimal.ThieleComplete.

Local Notation hstate := (@M.pu_state pu_hprop).
Local Notation hrun_prog := (M.pu_run_prog pu_hprop_eqb pu_heval).
Local Notation hrun_l := (M.pu_run pu_hprop_eqb pu_heval).
Local Notation htrace := (M.pu_trace_of pu_hprop_eqb pu_heval).

(* ================================================================= *)
(* Guest traces.                                                      *)
(* ================================================================= *)

(* The instruction right after a prefix of a guest trace is the one the
   guest takes at that run length. *)
Lemma pu_trace_next : forall n Q (s : E.state) l1 i l2,
  E.trace_of n Q s = l1 ++ i :: l2 ->
  E.next_instr Q (E.core_of (E.run_prog (length l1) Q s)) = Some i /\ length l1 < n.
Proof.
  induction n as [| n IH]; intros Q s l1 i l2 H.
  - destruct l1; discriminate H.
  - cbn [P.pr_trace_of] in H.
    destruct (E.next_instr Q (E.core_of s)) as [a |] eqn:Hn; [| destruct l1; discriminate H].
    destruct l1 as [| b l1].
    + injection H as -> _. simpl. split; [exact Hn | lia].
    + injection H as -> H. cbn [length P.pr_run_prog]. unfold P.pr_step. rewrite Hn.
      destruct (IH Q _ l1 i l2 H) as [H1 H2]. split; [exact H1 | lia].
Qed.

(* ================================================================= *)
(* Matching host points for every guest run length.                   *)
(* ================================================================= *)

Lemma pu_host_match : forall (Q : list E.instr) x y m, exists t,
  hv (pu_hrun Q x y t) pu_RB = E.cb (E.core_of (pu_grun Q x y m)) /\
  M.mu (pu_hrun Q x y t) = E.mu (pu_grun Q x y m) /\
  M.cert (pu_hrun Q x y t) = E.cert (pu_grun Q x y m).
Proof.
  intros Q x y m. destruct (pu_sim_points Q x y m) as [N [sg [rho [[[R _] | RH] _]]]].
  - exists N. split; [exact (pu_R_rb Q sg rho _ _ R) |].
    split; [exact (pu_rw_mu _ _ _ _ _ R) | exact (pu_rw_cert _ _ _ _ _ R)].
  - exists N. destruct RH as [_ [_ [_ [Hb [_ [Hm [Hc _]]]]]]]. auto.
Qed.

(* ================================================================= *)
(* The composition.                                                   *)
(* ================================================================= *)

Section Composition.

Variable Mp : presented_machine.
Variable pc : cg_presentation Mp.

Local Notation st := (T.cs_state (pm_sys Mp)).
Local Notation ccost := (T.cs_cost (pm_sys Mp)).
Local Notation rd := (T.cs_cert (pm_sys Mp)).

(* Counter B of the guest at the start: the Godel code of the register
   file holding the code of s0 in register 0. *)
Definition pu_guest_b (s0 : st) : nat := cg_gk (cg_k Mp pc) (cg_e0 Mp s0).

(* The fixed host U_P, loaded with the compiled guest and its start. *)
Definition pu_host_start (s0 : st) : hstate := pu_hload (cg_guest Mp pc) 0 (pu_guest_b s0).

(* The host after t steps. *)
Definition pu_host_at (s0 : st) (t : nat) : hstate :=
  pu_hrun (cg_guest Mp pc) 0 (pu_guest_b s0) t.

(* What a counter value says about M: the exponent of the first prime,
   read back as a state of M. *)
Definition pu_decode (v : nat) : option st := pm_sdec Mp (cg_expo (qs 0) v).

(* The guest run of the universal host is the compiler's guest run. *)
Lemma pu_grun_guest : forall s0 N,
  pu_grun (cg_guest Mp pc) 0 (pu_guest_b s0) N =
  P.pr_run_prog cg_uprop_eqb cg_ueval N (cg_guest Mp pc) (cg_ystart Mp pc s0).
Proof. reflexivity. Qed.

Theorem presented_universal_halting : forall s0,
  (exists t, M.pu_halted U_P (M.core_of (pu_host_at s0 t))) <-> (exists n, mhalted Mp s0 n).
Proof.
  intros s0. unfold pu_host_at. rewrite <- pu_universal_halting.
  rewrite <- (cg_guest_halting_iff Mp pc s0). split; intros [N HN]; exists N; exact HN.
Qed.

Theorem presented_universal_points : forall s0 n,
  (forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None) ->
  exists t,
    pu_decode (hv (pu_host_at s0 t) pu_RB) = Some (presented_run Mp s0 n) /\
    M.mu (pu_host_at s0 t) = mledger Mp s0 n + surcharge Mp s0 n /\
    M.cert (pu_host_at s0 t) = mlatch Mp s0 n.
Proof.
  intros s0 n Hn.
  destruct (cg_guest_matching_points Mp pc s0 n Hn) as (N & _ & _ & _ & _ & Hd & Hm & Hc).
  destruct (pu_host_match (cg_guest Mp pc) 0 (pu_guest_b s0) N) as (t & Hb & Hmu & Hce).
  exists t. unfold pu_host_at, pu_decode. rewrite Hb, Hmu, Hce. auto.
Qed.

Theorem presented_universal_halt_point : forall s0 n,
  (forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None) ->
  pm_next Mp (presented_run Mp s0 n) = None ->
  exists t,
    M.pu_halted U_P (M.core_of (pu_host_at s0 t)) /\
    pu_decode (hv (pu_host_at s0 t) pu_RB) = Some (presented_run Mp s0 n) /\
    M.mu (pu_host_at s0 t) = mledger Mp s0 n + surcharge Mp s0 n /\
    M.cert (pu_host_at s0 t) = mlatch Mp s0 n.
Proof.
  intros s0 n Hn Hh.
  destruct (cg_guest_halts_at Mp pc s0 n Hn Hh) as (N & HN & Hd & Hm & Hc & _).
  destruct (proj1 (pu_universal_halting (cg_guest Mp pc) 0 (pu_guest_b s0))
              (ex_intro _ N HN)) as [t Ht].
  destruct (pu_universal_output (cg_guest Mp pc) 0 (pu_guest_b s0) N t HN Ht)
    as (_ & Hb & _ & Hmu & Hce).
  exists t. unfold pu_host_at, pu_decode. rewrite Hb, Hmu, Hce. auto.
Qed.

Theorem presented_universal_flag_iff : forall s0,
  (exists t, M.cert (pu_host_at s0 t) = true) <->
  (exists n, rd (presented_run Mp s0 n) = true).
Proof.
  intros s0. unfold pu_host_at. rewrite <- pu_universal_flag_iff.
  rewrite <- (cg_guest_flag_iff Mp pc s0). split; intros [N HN]; exists N; exact HN.
Qed.

Theorem presented_universal_earned : forall s0 t,
  M.cert (pu_host_at s0 t) = true ->
  exists k v m pre1 mid1 mid2 post,
    k < 16 /\
    htrace t U_P (pu_host_start s0) =
      pre1 ++ M.CHECK PSlot (pu_SLOT E.CB k) :: mid1 ++
      M.COMMIT PSlot (pu_SLOT E.CB k) :: mid2 ++ M.CERTIFY :: post /\
    M.pu_check_ok pu_heval (M.core_of (hrun_l pre1 (pu_host_start s0)))
      PSlot (pu_SLOT E.CB k) = true /\
    M.pu_commit_ok pu_hprop_eqb
      (M.core_of (hrun_l (pre1 ++ M.CHECK PSlot (pu_SLOT E.CB k) :: mid1)
                    (pu_host_start s0)))
      PSlot (pu_SLOT E.CB k) = true /\
    M.pu_certify_ok (M.core_of (hrun_l (pre1 ++ M.CHECK PSlot (pu_SLOT E.CB k) :: mid1 ++
                                     M.COMMIT PSlot (pu_SLOT E.CB k) :: mid2)
                                    (pu_host_start s0))) = true /\
    hver (hrun_l pre1 (pu_host_start s0)) (pu_SLOT E.CB k) =
      hver (hrun_l (pre1 ++ M.CHECK PSlot (pu_SLOT E.CB k) :: mid1) (pu_host_start s0))
        (pu_SLOT E.CB k) /\
    M.pu_untouched pu_hprop_eqb pu_heval
      (hrun_l (pre1 ++ [M.CHECK PSlot (pu_SLOT E.CB k)]) (pu_host_start s0))
      mid1 (pu_SLOT E.CB k) /\
    hv (hrun_l pre1 (pu_host_start s0)) (pu_SLOT E.CB k) =
      pu_pair (pu_pcode (URun (cg_r Mp pc))) v /\
    cg_ueval (URun (cg_r Mp pc)) v = true /\
    pu_decode v = Some (presented_run Mp s0 m) /\
    rd (presented_run Mp s0 m) = true.
Proof.
  intros s0 t Hc. unfold pu_host_at in Hc.
  set (Q := cg_guest Mp pc) in *. set (b := pu_guest_b s0) in *.
  destruct (pu_universal_earned Q 0 b t Hc)
    as (c & k & p & v & pre1 & mid1 & mid2 & post & Hk & Hlist & Hck & Hcm & Hok & Hv1 & Hun &
        Hval & Hholds & m' & gpre & gmid1 & gmid2 & gpost & Hglist & Hgck & _ & _ & _ & _ & Hgval).
  (* The guest flag is up at some run length. *)
  destruct (proj2 (pu_universal_flag_iff Q 0 b) (ex_intro _ t Hc)) as [mg Hmg].
  (* Where the guest chain's CHECK sits in the guest run. *)
  destruct (pu_trace_next m' Q (E.start 0 b) gpre (E.CHECK p c) _ Hglist) as [Hnext Hlt].
  assert (Hrun : E.run gpre (E.start 0 b) = E.run_prog (length gpre) Q (E.start 0 b))
    by exact (pu_gtrace_prefix m' Q (E.start 0 b) gpre _ Hglist).
  set (N := mg + m').
  assert (HN : G.cert (P.pr_run_prog cg_uprop_eqb cg_ueval N Q (cg_ystart Mp pc s0)) = true).
  { apply (cg_cert_mono _ _ _ Q (cg_ystart Mp pc s0) mg N); [unfold N; lia |]. exact Hmg. }
  destruct (cg_guest_earned Mp pc s0 N HN)
    as (_ & L & m & HL & Hrd & _ & HnL & HckL & HdL & Huniq).
  assert (HLe : length gpre = L).
  { apply Huniq; [unfold N; lia |]. unfold cg_passes_at. cbv zeta.
    change (P.pr_run_prog cg_uprop_eqb cg_ueval (length gpre) (cg_guest Mp pc)
              (cg_ystart Mp pc s0))
      with (E.run_prog (length gpre) Q (E.start 0 b)).
    fold Q. rewrite Hnext. cbn [P.pr_passes]. rewrite <- Hrun, Hgck. reflexivity. }
  subst L.
  change (P.pr_run_prog cg_uprop_eqb cg_ueval (length gpre) (cg_guest Mp pc)
            (cg_ystart Mp pc s0))
    with (E.run_prog (length gpre) Q (E.start 0 b)) in HnL, HdL.
  fold Q in HnL. rewrite HnL in Hnext. injection Hnext as Hp Hcc. subst p c.
  assert (Hcb : G.cb (G.core_of (E.run gpre (E.start 0 b))) = v) by exact Hgval.
  rewrite <- Hrun, Hcb in HdL.
  exists k, v, m, pre1, mid1, mid2, post.
  split; [exact Hk |]. split; [exact Hlist |]. split; [exact Hck |]. split; [exact Hcm |].
  split; [exact Hok |]. split; [exact Hv1 |]. split; [exact Hun |]. split; [exact Hval |].
  split; [apply cg_ueval_iff; exact Hholds |].
  split; [exact HdL | exact Hrd].
Qed.

(* The five together. *)
Theorem presented_universal : forall s0,
  ((exists t, M.pu_halted U_P (M.core_of (pu_host_at s0 t))) <-> (exists n, mhalted Mp s0 n)) /\
  (forall n, (forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None) ->
     exists t,
       pu_decode (hv (pu_host_at s0 t) pu_RB) = Some (presented_run Mp s0 n) /\
       M.mu (pu_host_at s0 t) = mledger Mp s0 n + surcharge Mp s0 n /\
       M.cert (pu_host_at s0 t) = mlatch Mp s0 n) /\
  (forall n, (forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None) ->
     pm_next Mp (presented_run Mp s0 n) = None ->
     exists t,
       M.pu_halted U_P (M.core_of (pu_host_at s0 t)) /\
       pu_decode (hv (pu_host_at s0 t) pu_RB) = Some (presented_run Mp s0 n) /\
       M.mu (pu_host_at s0 t) = mledger Mp s0 n + surcharge Mp s0 n /\
       M.cert (pu_host_at s0 t) = mlatch Mp s0 n) /\
  ((exists t, M.cert (pu_host_at s0 t) = true) <->
   (exists n, rd (presented_run Mp s0 n) = true)) /\
  (forall t, M.cert (pu_host_at s0 t) = true ->
     exists k v m pre1 mid1 mid2 post,
       k < 16 /\
       htrace t U_P (pu_host_start s0) =
         pre1 ++ M.CHECK PSlot (pu_SLOT E.CB k) :: mid1 ++
         M.COMMIT PSlot (pu_SLOT E.CB k) :: mid2 ++ M.CERTIFY :: post /\
       M.pu_check_ok pu_heval (M.core_of (hrun_l pre1 (pu_host_start s0)))
         PSlot (pu_SLOT E.CB k) = true /\
       M.pu_commit_ok pu_hprop_eqb
         (M.core_of (hrun_l (pre1 ++ M.CHECK PSlot (pu_SLOT E.CB k) :: mid1)
                       (pu_host_start s0)))
         PSlot (pu_SLOT E.CB k) = true /\
       M.pu_certify_ok (M.core_of (hrun_l (pre1 ++ M.CHECK PSlot (pu_SLOT E.CB k) :: mid1 ++
                                        M.COMMIT PSlot (pu_SLOT E.CB k) :: mid2)
                                       (pu_host_start s0))) = true /\
       hver (hrun_l pre1 (pu_host_start s0)) (pu_SLOT E.CB k) =
         hver (hrun_l (pre1 ++ M.CHECK PSlot (pu_SLOT E.CB k) :: mid1) (pu_host_start s0))
           (pu_SLOT E.CB k) /\
       M.pu_untouched pu_hprop_eqb pu_heval
         (hrun_l (pre1 ++ [M.CHECK PSlot (pu_SLOT E.CB k)]) (pu_host_start s0))
         mid1 (pu_SLOT E.CB k) /\
       hv (hrun_l pre1 (pu_host_start s0)) (pu_SLOT E.CB k) =
         pu_pair (pu_pcode (URun (cg_r Mp pc))) v /\
       cg_ueval (URun (cg_r Mp pc)) v = true /\
       pu_decode v = Some (presented_run Mp s0 m) /\
       rd (presented_run Mp s0 m) = true).
Proof.
  intros s0. split; [apply presented_universal_halting |].
  split; [apply presented_universal_points |].
  split; [apply presented_universal_halt_point |].
  split; [apply presented_universal_flag_iff | apply presented_universal_earned].
Qed.

(* ================================================================= *)
(* The surcharge.                                                     *)
(* ================================================================= *)

(* When the reading starts at no and the first raising move costs at
   least 3, the host ledger equals M's ledger at every matching point. *)
Theorem presented_universal_exact : forall s0,
  rd s0 = false ->
  (forall n i, first_raise Mp s0 n = Some i -> ccost i >= 3) ->
  forall n, (forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None) ->
  surcharge Mp s0 n = 0 /\
  exists t,
    pu_decode (hv (pu_host_at s0 t) pu_RB) = Some (presented_run Mp s0 n) /\
    M.mu (pu_host_at s0 t) = mledger Mp s0 n /\
    M.cert (pu_host_at s0 t) = mlatch Mp s0 n.
Proof.
  intros s0 H0 Hc n Hn.
  assert (Hs : surcharge Mp s0 n = 0).
  { unfold surcharge. destruct (mlatch Mp s0 n) eqn:Hl; [| reflexivity].
    destruct (presented_first_raise_spec Mp n s0 H0 Hl) as (m & i & _ & _ & _ & _ & Hf).
    unfold raise_cost. rewrite Hf. pose proof (Hc n i Hf). lia. }
  split; [exact Hs |].
  destruct (presented_universal_points s0 n Hn) as (t & Hd & Hm & Hce).
  exists t. rewrite Hs, Nat.add_0_r in Hm. auto.
Qed.

(* When the reading starts at no, the host pays at most 2 more than M. *)
Theorem presented_universal_surcharge_le_two : forall s0,
  rd s0 = false ->
  forall n, (forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None) ->
  exists t,
    pu_decode (hv (pu_host_at s0 t) pu_RB) = Some (presented_run Mp s0 n) /\
    mledger Mp s0 n <= M.mu (pu_host_at s0 t) <= mledger Mp s0 n + 2 /\
    M.cert (pu_host_at s0 t) = mlatch Mp s0 n.
Proof.
  intros s0 H0 n Hn.
  destruct (presented_universal_points s0 n Hn) as (t & Hd & Hm & Hce).
  pose proof (presented_surcharge_le_two Mp s0 n H0) as H2.
  exists t. split; [exact Hd |]. split; [lia | exact Hce].
Qed.

End Composition.

(* No run of the host machine from a clean start, U_P or any other
   program, raises its flag with a ledger growth below 3. So when M's
   latch is up after n steps with M's ledger below 3, no host run ends
   with its flag equal to the latch and its ledger grown by exactly M's
   ledger: the surcharge cannot be avoided. *)
Theorem presented_universal_no_exact_below_three :
  forall (Mp : presented_machine) (s0 : T.cs_state (pm_sys Mp)) (n : nat),
  mlatch Mp s0 n = true -> mledger Mp s0 n < 3 ->
  forall (h0 : hstate) (tr : list (@M.pu_instr pu_hprop)),
  M.pu_clean_start h0 ->
  ~ (M.cert (hrun_l tr h0) = mlatch Mp s0 n /\
     M.mu (hrun_l tr h0) = M.mu h0 + mledger Mp s0 n).
Proof.
  intros Mp s0 n Hl Hlt h0 tr H0 [Hc Hm]. rewrite Hl in Hc.
  destruct (M.pu_multi_certified_run_min_cost pu_hprop_eqb pu_hprop_eqb_eq pu_heval h0 tr H0 Hc)
    as [_ H3].
  lia.
Qed.

(* The same for U_P's own runs from the loaded host. *)
Corollary presented_universal_U_no_exact_below_three :
  forall (Mp : presented_machine) (pc : cg_presentation Mp) (s0 : T.cs_state (pm_sys Mp)) n t,
  mlatch Mp s0 n = true -> mledger Mp s0 n < 3 ->
  M.cert (pu_host_at Mp pc s0 t) = true -> M.mu (pu_host_at Mp pc s0 t) <> mledger Mp s0 n.
Proof.
  intros Mp pc s0 n t Hl Hlt Hc Hm.
  apply (presented_universal_no_exact_below_three Mp s0 n Hl Hlt (pu_host_start Mp pc s0)
           (htrace t U_P (pu_host_start Mp pc s0)) (M.pu_multi_start_clean _)).
  unfold pu_host_at, pu_hrun in Hc, Hm. fold (pu_host_start Mp pc s0) in Hc, Hm.
  rewrite <- (M.pu_multi_run_prog_trace pu_hprop_eqb pu_heval). split; [rewrite Hc, Hl; reflexivity |].
  rewrite Hm. reflexivity.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions pu_trace_next.
Print Assumptions pu_host_match.
Print Assumptions presented_universal_halting.
Print Assumptions presented_universal_points.
Print Assumptions presented_universal_halt_point.
Print Assumptions presented_universal_flag_iff.
Print Assumptions presented_universal_earned.
Print Assumptions presented_universal.
Print Assumptions presented_universal_exact.
Print Assumptions presented_universal_surcharge_le_two.
Print Assumptions presented_universal_no_exact_below_three.
Print Assumptions presented_universal_U_no_exact_below_three.
