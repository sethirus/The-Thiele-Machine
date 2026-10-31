(** UniversalPPhases.v: what the fixed host program U_P of UniversalPLayout.v
    does for one guest instruction.

    This file is the priced counterpart of UniversalPhases.v: the host is the
    machine of EarnedMultiPriced.v (with PAY), the guest is the priced
    machine of EarnedPriced.v over the universal property language
    cg_uprop (UniversalPCodes.v), every name carries the prefix pu_, and
    the host program is U_P.

    A host state is "at HEAD" for the guest program P when its pc is
    pu_L_HEAD (address 1), its trap latch is down, pu_PROG holds pu_prog_code P,
    and every scratch register pu_T0 .. pu_T9 holds 0. From such a state, with
    the guest pc in pu_GPC, each phase lemma runs U_P to the next state at HEAD,
    to the halt, or to a trap, and states exactly:

      the new values of pu_RA, pu_RB, pu_GPC, pu_NC c, pu_MP c k and pu_SLOT c k that change;
      that every other register returns to the value it had at HEAD (so
      every scratch register is 0 again);
      the versions of the registers from 48 on (the slots, pu_DEAD, and the
      unused registers above it): unchanged, except a bumped bank (each
      slot + 2) or the slot loaded by a CHECK (strictly larger);
      the fact table, the channel, the ledger mu, the flag and the trap
      latch.

    The host ledger goes up by exactly 1 in the CHECK, COMMIT, CERTIFY and
    PAY phases (one paid instruction each, pass or fail) and by 0 in every
    other phase.

      pu_phase_stop          guest pc 0, guest pc past the end, or HALT: the
                          host halts at pu_L_STOP, every register value as at
                          HEAD (corollaries pu_phase_pc0, pu_phase_out,
                          pu_phase_halt)
      pu_phase_decode        fetch and decode: the handler of the opcode is
                          reached with pu_T2 holding the operand
      pu_phase_inc           INC c
      pu_phase_dec_taken     DEC c j on a positive counter
      pu_phase_dec_zero      DEC c j on a zero counter
      pu_phase_check_pass    CHECK p c, slot pu_NC c < 16, the property holds and
                          the fact table has room
      pu_phase_check_fail    CHECK p c, slot pu_NC c < 16, the property fails or
                          the fact table is full: the host traps
      pu_phase_check_dead    CHECK p c with pu_NC c >= 16: CHECK PSlot pu_DEAD traps
      pu_phase_commit_pass   COMMIT p c, the first slot of bank c whose mirror
                          is pcode p + 1 carries a fact at its current
                          version: the channel holds that fact
      pu_phase_commit_stale  the same slot without that fact: the host traps
      pu_phase_commit_none   no mirror matches: COMMIT PSlot pu_DEAD traps
      pu_phase_certify_pass  CERTIFY with a full channel: the flag rises
      pu_phase_certify_fail  CERTIFY with an empty channel: the host traps
      pu_phase_pay           PAY: the host pays 1 at its own PAY, GPC goes up
                          by 1, nothing else moves

    Dependencies: the Coq standard library, the vendored coq-undecidability
    library, EarnedGeneric.v, EarnedPriced.v, EarnedMultiPriced.v, CompilerChecker.v,
    UniversalPCodes.v, UniversalPBridge.v, UniversalPBlocks.v and
    UniversalPLayout.v. No axioms, no Admitted.                            *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the universal interpreter U_P of UniversalPRun.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and files under minimal/. Its link to the abstract record (the
   host machine meeting thiele_complete of ThieleComplete.v, and every
   computably presented machine run on U_P) lives in UniversalPRun.v and
   PresentedUniversal.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import Vec.pos Vec.vec Code.subcode Code.sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.Util Require Import MMA_pairing.
Require Import Kernel.UniversalPCodes Kernel.UniversalPBridge Kernel.UniversalPBlocks
  Kernel.UniversalPLayout.

Local Notation hinstr := (@M.pu_instr pu_hprop).
Local Notation hstate := (@M.pu_state pu_hprop).
Local Notation hrun_prog := (M.pu_run_prog pu_hprop_eqb pu_heval).
Local Notation hexec := (M.pu_exec pu_hprop_eqb pu_heval).
Local Notation Hrun := (pu_hrun pu_hprop_eqb pu_heval).

(* ================================================================= *)
(* Frames given by a predicate.                                       *)
(* ================================================================= *)

(* Every register outside Q keeps its value. *)
Definition pu_vfr (Q : nat -> Prop) (s s' : hstate) : Prop :=
  forall r, ~ Q r -> hv s' r = hv s r.

(* Every register outside Q keeps its value and its version. *)
Definition pu_hfr (Q : nat -> Prop) (s s' : hstate) : Prop :=
  forall r, ~ Q r -> hv s' r = hv s r /\ hver s' r = hver s r.

Lemma pu_hframe_keep_vfr : forall rs (Q : nat -> Prop) (s s' : hstate),
  pu_hframe rs s s' -> (forall r, In r rs -> Q r \/ hv s' r = hv s r) -> pu_vfr Q s s'.
Proof.
  intros rs Q s s' F H r Hq. destruct (in_dec Nat.eq_dec r rs) as [Hin | Hn].
  - destruct (H r Hin) as [Hq' | E]; [contradiction | exact E].
  - apply F, Hn.
Qed.

Lemma pu_hframe_hfr : forall rs (Q : nat -> Prop) (s s' : hstate),
  pu_hframe rs s s' -> (forall r, In r rs -> Q r) -> pu_hfr Q s s'.
Proof. intros rs Q s s' F H r Hq. apply F. intro Hin. apply Hq, H, Hin. Qed.

Lemma pu_all_same_hframe : forall s s' : hstate,
  (forall d, hv s' d = hv s d /\ hver s' d = hver s d) -> pu_hframe [] s s'.
Proof. intros s s' H r _. apply H. Qed.

(* Markers: register r is not framed between s and s' by a given
   hypothesis (values / versions). *)
Inductive pu_skip_v (r : nat) (s s' : hstate) : Prop := skip_v_mark.
Inductive pu_skip_w (r : nat) (s s' : hstate) : Prop := skip_w_mark.

(* ================================================================= *)
(* Tactics.                                                           *)
(* ================================================================= *)

Ltac pu_unfold_regs :=
  unfold pu_RA, pu_RB, pu_PROG, pu_GPC, pu_T0, pu_T1, pu_T2, pu_T3, pu_T4, pu_T5, pu_T6, pu_T7, pu_T8, pu_T9,
    pu_greg, pu_NC, pu_MP, pu_SLOT, pu_DEAD, pu_scratch, pu_in_mp, pu_in_slots in *.

Ltac pu_ctr_bounds :=
  repeat match goal with
  | c : E.ctr |- _ =>
      lazymatch goal with
      | _ : pu_ccode c < 2 |- _ => fail
      | _ => pose proof (pu_ccode_lt c)
      end
  end.

(* Register arithmetic: membership, disequality, ranges. *)
Ltac pu_nreg := simpl in *; pu_unfold_regs; cbn [pu_ccode] in *; pu_ctr_bounds; lia.

(* Keep only the bound hypotheses of the form _ < 16. *)
Ltac pu_keep_bounds :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with
      | Prop => lazymatch T with
                | _ < 16 => fail
                | _ => clear H
                end
      end
  end.

Ltac pu_rneq := pu_keep_bounds; pu_nreg.

(* For register r, record the value and version equations of every frame
   hypothesis (hframe, hfr, vfr) that does not cover r. K names one
   hypothesis that carries what is known about r. *)
Ltac pu_track r K :=
  repeat match goal with
  | F : pu_hframe ?rs ?a ?b |- _ =>
      lazymatch goal with
      | _ : hver b r = hver a r |- _ => fail
      | _ : pu_skip_w r a b |- _ => fail
      | _ =>
          first
            [ let N := fresh "N" in
              assert (N : ~ In r rs) by (clear - K; pu_nreg);
              pose proof (proj1 (F r N));
              pose proof (proj2 (F r N)); clear N
            | assert (pu_skip_w r a b) by constructor ]
      end
  | F : pu_hfr ?Q ?a ?b |- _ =>
      lazymatch goal with
      | _ : hver b r = hver a r |- _ => fail
      | _ : pu_skip_w r a b |- _ => fail
      | _ =>
          first
            [ let N := fresh "N" in
              assert (N : ~ Q r) by (clear - K; pu_nreg);
              pose proof (proj1 (F r N)); pose proof (proj2 (F r N)); clear N
            | assert (pu_skip_w r a b) by constructor ]
      end
  | F : pu_vfr ?Q ?a ?b |- _ =>
      lazymatch goal with
      | _ : hv b r = hv a r |- _ => fail
      | _ : pu_skip_v r a b |- _ => fail
      | _ =>
          first
            [ let N := fresh "N" in
              assert (N : ~ Q r) by (clear - K; pu_nreg);
              pose proof (F r N); clear N
            | assert (pu_skip_v r a b) by constructor ]
      end
  end.

(* A vfr goal from an hframe hypothesis F: each register of F's list is
   either in Q or has an equation hv s' x = hv s x in the context. *)
Ltac pu_vfr_from F :=
  apply (pu_hframe_keep_vfr _ _ _ _ F);
  let r := fresh "r" in
  let Hin := fresh "Hin" in
  intros r Hin; simpl in Hin;
  repeat (destruct Hin as [<- | Hin]); try contradiction;
  first [ right; assumption
        | right; symmetry; assumption
        | left; cbv beta; repeat (first [left; reflexivity | right]); reflexivity ].

(* An hfr goal from an hframe hypothesis F whose list lies inside Q. *)
Ltac pu_hfr_from F :=
  apply (pu_hframe_hfr _ _ _ _ F);
  let r := fresh "r" in
  let Hin := fresh "Hin" in
  intros r Hin; simpl in Hin;
  repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbv beta; repeat (first [left; reflexivity | right]); try reflexivity.

(* A full frame goal hframe rs s s' along a chain. *)
Ltac pu_frame_goal :=
  let r := fresh "r" in
  let Hr := fresh "Hr" in
  intros r Hr; pu_track r Hr; split; congruence.

(* A vfr / hfr goal along a chain, by tracking a generic register. *)
Ltac pu_vfr_goal :=
  let r := fresh "r" in
  let Hr := fresh "Hr" in
  intros r Hr; pu_track r Hr; congruence.
Ltac pu_hfr_goal :=
  let r := fresh "r" in
  let Hr := fresh "Hr" in
  intros r Hr; pu_track r Hr; split; congruence.

(* ================================================================= *)
(* Distinct registers.                                                *)
(* ================================================================= *)

Lemma pu_nd_fetch : NoDup [pu_PROG; pu_GPC; pu_T0; pu_T1; pu_T2; pu_T3; pu_T4].
Proof. pu_unfold_regs. repeat constructor; simpl; intuition discriminate. Qed.

Lemma pu_nd_eqr : forall c k, NoDup [pu_MP c k; pu_T2; pu_T7; pu_T8; pu_T4].
Proof.
  intros c k. constructor; [simpl; pu_unfold_regs; lia |].
  pu_unfold_regs. repeat constructor; simpl; intuition discriminate.
Qed.

Lemma pu_cpick_nth : forall c (ta tb : nat), nth (pu_ccode c) [ta; tb] 0 = match c with E.CA => ta | E.CB => tb end.
Proof. intros []; reflexivity. Qed.

Lemma pu_nth_map_seq : forall (f : nat -> nat) n k, k < n -> nth k (map f (seq 0 n)) 0 = f k.
Proof.
  intros f n k Hk. rewrite (nth_indep _ 0 (f 0)) by (rewrite map_length, seq_length; exact Hk).
  rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.

(* ================================================================= *)
(* Reaching a state by running U_P.                                     *)
(* ================================================================= *)

Definition pu_hreach (s s' : hstate) : Prop := exists n, hrun_prog n U_P s = s'.

Lemma pu_Hrun_hreach : forall s s', Hrun U_P s s' -> pu_hreach s s'.
Proof. intros s s' [m [E _]]. exists m. exact E. Qed.

Lemma pu_hreach_trans : forall s1 s2 s3, pu_hreach s1 s2 -> pu_hreach s2 s3 -> pu_hreach s1 s3.
Proof.
  intros s1 s2 s3 [n E1] [m E2]. exists (n + m).
  rewrite (M.pu_multi_run_prog_add pu_hprop_eqb pu_heval), E1. exact E2.
Qed.

Lemma pu_hreach_one : forall s, pu_hreach s (hrun_prog 1 U_P s).
Proof. intro s. exists 1. reflexivity. Qed.

(* ================================================================= *)
(* Composite blocks, for any host program they are placed in.         *)
(* ================================================================= *)

Definition pu_cpick (c : E.ctr) (ta tb : nat) : nat := match c with E.CA => ta | E.CB => tb end.

(* Bank choice on pu_T2 = ccode c. *)
Lemma pu_hCD_spec : forall ta tb o Ph s c,
  subcode (o, pu_hCD ta tb o) (1, Ph) -> hpc s = o -> herr s = false -> hv s pu_T2 = pu_ccode c ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_cpick c ta tb /\ hv s' pu_T2 = 0 /\ hv s' pu_T4 = hv s pu_T4 /\
    pu_hframe [pu_T2; pu_T4] s s'.
Proof.
  intros ta tb o Ph s c Hsc Hpc He Hc. unfold pu_hCD in Hsc. pu_sc_split Hsc S0 S1.
  destruct (pu_hDISP_spec pu_T2 pu_T4 [ta; tb] o Ph s ltac:(pu_rneq) S0 Hpc He) as (s' & R & F & V4 & L & G).
  rewrite Hc in L. destruct (L ltac:(simpl; pose proof (pu_ccode_lt c); lia)) as [P2 V2].
  exists s'. split; [exact R |]. split; [rewrite P2, pu_cpick_nth; reflexivity |].
  split; [exact V2 |]. split; [exact V4 | exact F].
Qed.

(* Operand split and bank choice. *)
Lemma pu_hUCD_spec : forall ta tb o Ph s c x,
  subcode (o, pu_hUCD ta tb o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s pu_T2 = pu_pair (pu_ccode c) x ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_cpick c ta tb /\ hv s' pu_T2 = x /\ hv s' pu_T3 = 0 /\
    hv s' pu_T6 = 0 /\ hv s' pu_T4 = hv s pu_T4 /\ pu_hframe [pu_T3; pu_T2; pu_T6; pu_T4] s s'.
Proof.
  intros ta tb o Ph s c x Hsc Hpc He Hx. unfold pu_hUCD in Hsc.
  pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 S1 S2.
  destruct (pu_hUNPACK_spec pu_T3 pu_T2 pu_T6 (pu_ccode c) x o Ph s ltac:(pu_rneq) ltac:(pu_rneq) ltac:(pu_rneq) Hx S0
              Hpc He) as (s1 & R1 & P1 & V1x & V1y & V1a & F1).
  destruct (pu_hDISP_spec pu_T6 pu_T4 [ta; tb] (UNPACK_len + o) Ph s1 ltac:(pu_rneq) S1 P1 ltac:(pu_herr_tac))
    as (s2 & R2 & F2 & V4 & L & G).
  rewrite V1y in L. destruct (L ltac:(simpl; pose proof (pu_ccode_lt c); lia)) as [P2 V2].
  assert (KT : True) by exact I.
  exists s2. split; [pu_chain |]. split; [rewrite P2, pu_cpick_nth; reflexivity |].
  pu_track pu_T2 KT. pu_track pu_T3 KT. pu_track pu_T4 KT.
  split; [congruence |]. split; [congruence |]. split; [exact V2 |]. split; [congruence |].
  pu_frame_goal.
Qed.

(* BUMP of the slots k0 .. k0 + n - 1 of bank c. *)
Lemma pu_hBUMPS_gen : forall c n k0 o Ph s, k0 + n <= 16 ->
  subcode (o, pu_fam (fun k o' => pu_hBUMP (pu_SLOT c k) (pu_MP c k) o') pu_BUMP_len k0 n o) (1, Ph) ->
  hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = n * pu_BUMP_len + o /\
    (forall k, k0 <= k < k0 + n ->
       hv s' (pu_SLOT c k) = hv s (pu_SLOT c k) /\ hver s' (pu_SLOT c k) = 2 + hver s (pu_SLOT c k) /\
       hv s' (pu_MP c k) = 0) /\
    (forall r, (forall k, k0 <= k < k0 + n -> r <> pu_SLOT c k /\ r <> pu_MP c k) ->
       hv s' r = hv s r /\ hver s' r = hver s r) /\
    (forall r, (forall k, k0 <= k < k0 + n -> r <> pu_MP c k) -> hv s' r = hv s r).
Proof.
  intros c n. induction n as [| n IH]; intros k0 o Ph s Hb Hsc Hpc He.
  - exists s. split; [apply pu_hrun_refl |]. split; [exact Hpc |].
    split; [intros k Hk; lia |]. split; intros r _; [split |]; reflexivity.
  - cbn [pu_fam] in Hsc. pu_sc_split Hsc S0 S1.
    assert (Hne : pu_SLOT c k0 <> pu_MP c k0) by (unfold pu_SLOT, pu_MP; lia).
    destruct (pu_hBUMP_spec (pu_SLOT c k0) (pu_MP c k0) o Ph s Hne S0 Hpc He)
      as (s1 & R1 & P1 & V1 & W1 & M1 & F1).
    destruct (IH (S k0) (pu_BUMP_len + o) Ph s1 ltac:(lia) S1 P1 ltac:(pu_herr_tac))
      as (s2 & R2 & P2 & A2 & B2 & C2).
    exists s2. split; [pu_chain |]. split; [rewrite P2; simpl; lia |]. split; [| split].
    + intros k Hk. destruct (Nat.eq_dec k k0) as [-> | Hkn].
      * assert (X : forall q, S k0 <= q < S k0 + n -> pu_SLOT c k0 <> pu_SLOT c q /\ pu_SLOT c k0 <> pu_MP c q)
          by (intros q Hq; unfold pu_SLOT, pu_MP; lia).
        assert (Y : forall q, S k0 <= q < S k0 + n -> pu_MP c k0 <> pu_MP c q)
          by (intros q Hq; unfold pu_MP; lia).
        destruct (B2 _ X) as [E1 E2]. rewrite E1, E2, (C2 _ Y).
        split; [exact V1 | split; [exact W1 | exact M1]].
      * destruct (A2 k ltac:(lia)) as (E1 & E2 & E3).
        assert (N1 : ~ In (pu_SLOT c k) [pu_SLOT c k0; pu_MP c k0]) by (simpl; unfold pu_SLOT, pu_MP; lia).
        rewrite E1, E2, E3, (proj1 (F1 _ N1)), (proj2 (F1 _ N1)).
        repeat split.
    + intros r Hr.
      assert (N1 : ~ In r [pu_SLOT c k0; pu_MP c k0]).
      { destruct (Hr k0 ltac:(lia)) as [Ha Hb']. simpl. intuition congruence. }
      destruct (B2 r ltac:(intros q Hq; apply Hr; lia)) as [E1 E2]. rewrite E1, E2.
      exact (F1 r N1).
    + intros r Hr. rewrite (C2 r ltac:(intros q Hq; apply Hr; lia)).
      destruct (Nat.eq_dec r (pu_SLOT c k0)) as [-> | Hs].
      * exact V1.
      * apply (fun N => proj1 (F1 r N)). simpl. pose proof (Hr k0 ltac:(lia)). intuition congruence.
Qed.

Theorem pu_hBUMPS_spec : forall c o Ph s,
  subcode (o, pu_hBUMPS c o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_BUMPS_len + o /\
    (forall q, q < 16 -> hv s' (pu_SLOT c q) = hv s (pu_SLOT c q) /\
       hver s' (pu_SLOT c q) = 2 + hver s (pu_SLOT c q) /\ hv s' (pu_MP c q) = 0) /\
    pu_hfr (fun r => pu_in_mp c r \/ pu_in_slots c r) s s' /\ pu_vfr (pu_in_mp c) s s'.
Proof.
  intros c o Ph s Hsc Hpc He. unfold pu_hBUMPS in Hsc.
  destruct (pu_hBUMPS_gen c 16 0 o Ph s ltac:(lia) Hsc Hpc He) as (s' & R & P & A & B & C).
  exists s'. split; [exact R |]. split; [exact P |].
  split; [intros q Hq; apply A; lia |]. split.
  - intros r Hr. apply B. intros k Hk. unfold pu_in_mp, pu_in_slots, pu_SLOT, pu_MP in *. lia.
  - intros r Hr. apply C. intros k Hk. unfold pu_in_mp, pu_MP in *. lia.
Qed.

(* The 16-way comparison of the mirrors pu_MP c k with pu_T2. *)
Lemma pu_hEQRS_gen : forall c tgt n k0 o Ph s, k0 + n <= 16 ->
  subcode (o, pu_fam (fun k o' => pu_hEQR (pu_MP c k) pu_T2 pu_T7 pu_T8 pu_T4 (tgt k) o') pu_EQR_len k0 n o) (1, Ph) ->
  hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\
    ((hv s pu_T7 = 0 /\ hv s pu_T8 = 0 /\ hv s pu_T4 = 0) \/ 0 < n ->
       hv s' pu_T7 = 0 /\ hv s' pu_T8 = 0 /\ hv s' pu_T4 = 0) /\
    pu_vfr (fun r => r = pu_T7 \/ r = pu_T8 \/ r = pu_T4) s s' /\
    pu_hfr (fun r => r = pu_T7 \/ r = pu_T8 \/ r = pu_T4 \/ r = pu_T2 \/ pu_in_mp c r) s s' /\
    (forall j, k0 <= j < k0 + n -> hv s (pu_MP c j) = hv s pu_T2 ->
       (forall j', k0 <= j' < j -> hv s (pu_MP c j') <> hv s pu_T2) -> hpc s' = tgt j) /\
    ((forall j, k0 <= j < k0 + n -> hv s (pu_MP c j) <> hv s pu_T2) -> hpc s' = n * pu_EQR_len + o).
Proof.
  intros c tgt n. induction n as [| n IH]; intros k0 o Ph s Hb Hsc Hpc He.
  - exists s. split; [apply pu_hrun_refl |]. split; [intros [H | H]; [exact H | lia] |].
    split; [intros r _; reflexivity |]. split; [intros r _; auto |].
    split; [intros j Hj; lia | intros _; exact Hpc].
  - cbn [pu_fam] in Hsc. pu_sc_split Hsc S0 S1.
    destruct (pu_hEQR_spec (pu_MP c k0) pu_T2 pu_T7 pu_T8 pu_T4 (tgt k0) o Ph s (pu_nd_eqr c k0) S0 Hpc He)
      as (s1 & R1 & F1 & Vx & Vy & V7 & V8 & V4 & P1).
    assert (VF1 : pu_vfr (fun r => r = pu_T7 \/ r = pu_T8 \/ r = pu_T4) s s1) by pu_vfr_from F1.
    assert (HF1 : pu_hfr (fun r => r = pu_T7 \/ r = pu_T8 \/ r = pu_T4 \/ r = pu_T2 \/ pu_in_mp c r) s s1).
    { apply (pu_hframe_hfr _ _ _ _ F1). intros r Hin. simpl in Hin.
      destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]]; simpl; pu_unfold_regs; lia. }
    destruct (Nat.eqb_spec (hv s (pu_MP c k0)) (hv s pu_T2)) as [Heq | Hneq].
    + exists s1. split; [exact R1 |]. split; [intros _; repeat split; assumption |].
      split; [exact VF1 |]. split; [exact HF1 |]. split.
      * intros j Hj Hm Hfirst. destruct (Nat.eq_dec j k0) as [-> | Hjn]; [exact P1 |].
        exfalso. apply (Hfirst k0); [lia | exact Heq].
      * intros Hall. exfalso. apply (Hall k0); [lia | exact Heq].
    + destruct (IH (S k0) (pu_EQR_len + o) Ph s1 ltac:(lia) S1 P1 ltac:(pu_herr_tac))
        as (s2 & R2 & Z2 & VF2 & HF2 & M2 & N2).
      assert (EM : forall j, hv s1 (pu_MP c j) = hv s (pu_MP c j)).
      { intro j. apply VF1. unfold pu_T7, pu_T8, pu_T4, pu_MP. lia. }
      assert (ET : hv s1 pu_T2 = hv s pu_T2) by exact Vy.
      exists s2. split; [pu_chain |]. split; [intros _; apply Z2; left; repeat split; assumption |].
      split; [intros r Hr; rewrite (VF2 r Hr); apply VF1, Hr |].
      split.
      * intros r Hr. destruct (HF2 r Hr) as [A B]. destruct (HF1 r Hr) as [C D].
        split; congruence.
      * split.
        -- intros j Hj Hm Hfirst. destruct (Nat.eq_dec j k0) as [-> | Hjn]; [contradiction |].
           apply M2; [lia | congruence |]. intros j' Hj'. rewrite EM, ET. apply Hfirst. lia.
        -- intros Hall. rewrite N2; [simpl; lia |]. intros j Hj. rewrite EM, ET. apply Hall. lia.
Qed.

Theorem pu_hEQRS_spec : forall c tgt o Ph s,
  subcode (o, pu_hEQRS c tgt o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hv s' pu_T7 = 0 /\ hv s' pu_T8 = 0 /\ hv s' pu_T4 = 0 /\
    pu_vfr (fun r => r = pu_T7 \/ r = pu_T8 \/ r = pu_T4) s s' /\
    pu_hfr (fun r => r = pu_T7 \/ r = pu_T8 \/ r = pu_T4 \/ r = pu_T2 \/ pu_in_mp c r) s s' /\
    (forall j, j < 16 -> hv s (pu_MP c j) = hv s pu_T2 ->
       (forall j', j' < j -> hv s (pu_MP c j') <> hv s pu_T2) -> hpc s' = tgt j) /\
    ((forall j, j < 16 -> hv s (pu_MP c j) <> hv s pu_T2) -> hpc s' = 16 * pu_EQR_len + o).
Proof.
  intros c tgt o Ph s Hsc Hpc He. unfold pu_hEQRS in Hsc.
  destruct (pu_hEQRS_gen c tgt 16 0 o Ph s ltac:(lia) Hsc Hpc He)
    as (s' & R & Z & VF & HF & M & N).
  destruct (Z ltac:(right; lia)) as (Z7 & Z8 & Z4).
  exists s'. do 6 (split; [assumption |]). split.
  - intros j Hj Hm Hf. apply M; [lia | exact Hm |]. intros j' Hj'. apply Hf. lia.
  - intros Hall. apply N. intros j Hj. apply Hall. lia.
Qed.

(* The halt block: every scratch register to 0, then the HALT. *)
Lemma pu_hHALTB_spec : forall o Ph s,
  subcode (o, pu_hHALTB o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = 10 + o /\
    hv s' pu_T0 = 0 /\ hv s' pu_T1 = 0 /\ hv s' pu_T2 = 0 /\ hv s' pu_T3 = 0 /\ hv s' pu_T4 = 0 /\
    hv s' pu_T5 = 0 /\ hv s' pu_T6 = 0 /\ hv s' pu_T7 = 0 /\ hv s' pu_T8 = 0 /\ hv s' pu_T9 = 0 /\
    pu_hfr pu_scratch s s'.
Proof.
  intros o Ph s Hsc Hpc He. unfold pu_hHALTB in Hsc.
  pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 S1 Hsc2. pu_sc_split Hsc2 S2 Hsc3. pu_sc_split Hsc3 S3 Hsc4.
  pu_sc_split Hsc4 S4 Hsc5. pu_sc_split Hsc5 S5 Hsc6. pu_sc_split Hsc6 S6 Hsc7. pu_sc_split Hsc7 S7 Hsc8.
  pu_sc_split Hsc8 S8 Hsc9. pu_sc_split Hsc9 S9 S10.
  destruct (pu_hZERO_spec pu_T0 o Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & F1).
  destruct (pu_hZERO_spec pu_T1 (1 + o) Ph s1 S1 P1 ltac:(pu_herr_tac)) as (s2 & R2 & P2 & V2 & F2).
  destruct (pu_hZERO_spec pu_T2 (2 + o) Ph s2 S2 P2 ltac:(pu_herr_tac)) as (s3 & R3 & P3 & V3 & F3).
  destruct (pu_hZERO_spec pu_T3 (3 + o) Ph s3 S3 P3 ltac:(pu_herr_tac)) as (s4 & R4 & P4 & V4 & F4).
  destruct (pu_hZERO_spec pu_T4 (4 + o) Ph s4 S4 P4 ltac:(pu_herr_tac)) as (s5 & R5 & P5 & V5 & F5).
  destruct (pu_hZERO_spec pu_T5 (5 + o) Ph s5 S5 P5 ltac:(pu_herr_tac)) as (s6 & R6 & P6 & V6 & F6).
  destruct (pu_hZERO_spec pu_T6 (6 + o) Ph s6 S6 P6 ltac:(pu_herr_tac)) as (s7 & R7 & P7 & V7 & F7).
  destruct (pu_hZERO_spec pu_T7 (7 + o) Ph s7 S7 P7 ltac:(pu_herr_tac)) as (s8 & R8 & P8 & V8 & F8).
  destruct (pu_hZERO_spec pu_T8 (8 + o) Ph s8 S8 P8 ltac:(pu_herr_tac)) as (s9 & R9 & P9 & V9 & F9).
  destruct (pu_hZERO_spec pu_T9 (9 + o) Ph s9 S9 P9 ltac:(pu_herr_tac))
    as (s10 & R10 & P10 & V10 & F10).
  assert (KT : True) by exact I.
  exists s10. split; [pu_chain |]. split; [rewrite P10; reflexivity |].
  do 10 (split; [match goal with |- hv _ ?X = 0 => pu_track X KT; congruence end |]).
  pu_hfr_goal.
Qed.

(* HEAD: fetch, decode and dispatch, or leave for the halt. *)
Theorem pu_hHEAD_spec : forall (P : list E.instr) o Ph s,
  subcode (o, pu_hHEAD o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s pu_PROG = pu_prog_code P -> (forall r, pu_scratch r -> hv s r = 0) ->
  exists s1, Hrun Ph s s1 /\ pu_vfr pu_scratch s s1 /\
    pu_hfr (fun r => pu_scratch r \/ r = pu_PROG \/ r = pu_GPC) s s1 /\
    match E.fetch P (hv s pu_GPC) with
    | Some i => hpc s1 = pu_handler i /\ hv s1 pu_T2 = pu_arg_of i /\
        hv s1 pu_T0 = 0 /\ hv s1 pu_T1 = 0 /\ hv s1 pu_T3 = 0 /\ hv s1 pu_T4 = 0 /\ hv s1 pu_T5 = 0 /\
        hv s1 pu_T6 = 0 /\ hv s1 pu_T7 = 0 /\ hv s1 pu_T8 = 0 /\ hv s1 pu_T9 = 0
    | None => hpc s1 = pu_L_HALT
    end.
Proof.
  intros P o Ph s Hsc Hpc He Hp Hz. unfold pu_hHEAD in Hsc.
  pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 S1 Hsc2. pu_sc_split Hsc2 S2 Hsc3. pu_sc_split Hsc3 S3 S4.
  assert (KT : True) by exact I.
  destruct (hv s pu_GPC) as [| k] eqn:Hg.
  - destruct (pu_hFETCH_guest_pc0 P pu_PROG pu_GPC pu_T0 pu_T1 pu_T2 pu_T3 pu_T4 pu_L_HALT pu_L_HALT o Ph s pu_nd_fetch S0 Hpc He
                Hp Hg) as (s1 & R1 & F1 & Vp & Vg & Vt & P1).
    assert (Ep : hv s1 pu_PROG = hv s pu_PROG) by congruence.
    assert (Eg : hv s1 pu_GPC = hv s pu_GPC) by congruence.
    exists s1. split; [exact R1 |]. split.
    + apply (pu_hframe_keep_vfr _ _ _ _ F1). intros r Hin. simpl in Hin.
      destruct Hin as [<- | [<- | Hin]]; [right; exact Ep | right; exact Eg |].
      left. unfold pu_scratch. repeat (destruct Hin as [<- | Hin]); try contradiction; pu_unfold_regs; lia.
    + split; [| exact P1].
      apply (pu_hframe_hfr _ _ _ _ F1). intros r Hin. simpl in Hin.
      repeat (destruct Hin as [<- | Hin]); try contradiction; simpl; pu_unfold_regs; lia.
  - destruct (pu_hFETCH_guest P pu_PROG pu_GPC pu_T0 pu_T1 pu_T2 pu_T3 pu_T4 pu_L_HALT pu_L_HALT o Ph s k pu_nd_fetch S0 Hpc He
                Hp Hg) as (s1 & R1 & F1 & Vp & Vg & Vt & G).
    assert (Ep : hv s1 pu_PROG = hv s pu_PROG) by congruence.
    assert (Eg : hv s1 pu_GPC = hv s pu_GPC) by congruence.
    cbn [E.fetch]. destruct (nth_error P k) as [i |] eqn:Hn.
    + destruct G as (P1 & H1 & K1 & A1 & W1).
      destruct (pu_hZERO_spec pu_T0 (pu_FETCH_len + o) Ph s1 S1 P1 ltac:(pu_herr_tac))
        as (s2 & R2 & P2 & V2 & F2).
      assert (H2 : hv s2 pu_T2 = pu_pair (pu_op_of i) (pu_arg_of i)).
      { rewrite <- pu_icode_op_arg. pu_track pu_T2 KT. congruence. }
      destruct (pu_hUNPACK_spec pu_T3 pu_T2 pu_T5 (pu_op_of i) (pu_arg_of i) (1 + pu_FETCH_len + o) Ph s2
                  ltac:(pu_rneq) ltac:(pu_rneq) ltac:(pu_rneq) H2 S2 P2 ltac:(pu_herr_tac))
        as (s3 & R3 & P3 & V3x & V3y & V3a & F3).
      destruct (pu_hDISP_spec pu_T5 pu_T4 pu_handlers (1 + pu_FETCH_len + UNPACK_len + o) Ph s3 ltac:(pu_rneq) S3
                  P3 ltac:(pu_herr_tac)) as (s4 & R4 & F4 & V4 & L4 & G4).
      rewrite V3y in L4. destruct (L4 (pu_op_of_lt i)) as [P4 V5].
      exists s4. split; [pu_chain |].
      split; [| split; [| split; [exact P4 |]]].
      * intros r Hr. destruct (Nat.eq_dec r pu_PROG) as [-> | Hrp].
        { pu_track pu_PROG KT. congruence. }
        destruct (Nat.eq_dec r pu_GPC) as [-> | Hrg].
        { pu_track pu_GPC KT. congruence. }
        assert (K : ~ pu_scratch r /\ r <> pu_PROG /\ r <> pu_GPC) by (repeat split; assumption).
        pu_track r K. congruence.
      * intros r Hr. pu_track r Hr. split; congruence.
      * pose proof (Hz pu_T6 ltac:(pu_rneq)). pose proof (Hz pu_T7 ltac:(pu_rneq)).
        pose proof (Hz pu_T8 ltac:(pu_rneq)). pose proof (Hz pu_T9 ltac:(pu_rneq)).
        repeat split; match goal with |- hv _ ?X = _ => pu_track X KT; congruence end.
    + exists s1. split; [exact R1 |]. split.
      * apply (pu_hframe_keep_vfr _ _ _ _ F1). intros r Hin. simpl in Hin.
        destruct Hin as [<- | [<- | Hin]]; [right; exact Ep | right; exact Eg |].
        left. unfold pu_scratch. repeat (destruct Hin as [<- | Hin]); try contradiction; pu_unfold_regs; lia.
      * split; [| exact (proj1 G)].
        apply (pu_hframe_hfr _ _ _ _ F1). intros r Hin. simpl in Hin.
        repeat (destruct Hin as [<- | Hin]); try contradiction; simpl; pu_unfold_regs; lia.
Qed.


(* INC c: INC (greg c), bump bank c, INC pu_GPC, back to HEAD. *)
Theorem pu_hINCH_spec : forall c o Ph s,
  subcode (o, pu_hINCH c o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_L_HEAD /\
    hv s' (pu_greg c) = S (hv s (pu_greg c)) /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    (forall q, q < 16 -> hv s' (pu_SLOT c q) = hv s (pu_SLOT c q) /\
       hver s' (pu_SLOT c q) = 2 + hver s (pu_SLOT c q) /\ hv s' (pu_MP c q) = 0) /\
    pu_vfr (fun r => r = pu_greg c \/ r = pu_GPC \/ pu_in_mp c r) s s' /\
    pu_hfr (fun r => r = pu_greg c \/ r = pu_GPC \/ r = pu_T4 \/ pu_in_mp c r \/ pu_in_slots c r) s s'.
Proof.
  intros c o Ph s Hsc Hpc He. unfold pu_hINCH in Hsc.
  pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 S1 Hsc2. pu_sc_split Hsc2 S2 S3.
  destruct (pu_hINC_spec (pu_greg c) o Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & W1 & F1).
  destruct (pu_hBUMPS_spec c (1 + o) Ph s1 S1 P1 ltac:(pu_herr_tac)) as (s2 & R2 & P2 & B2 & HF2 & VF2).
  destruct (pu_hINC_spec pu_GPC (1 + pu_BUMPS_len + o) Ph s2 S2 P2 ltac:(pu_herr_tac))
    as (s3 & R3 & P3 & V3 & W3 & F3).
  destruct (pu_hJMP_spec pu_T4 pu_L_HEAD (2 + pu_BUMPS_len + o) Ph s3 S3 P3 ltac:(pu_herr_tac))
    as (s4 & R4 & P4 & V4 & F4).
  assert (KT : True) by exact I.
  exists s4. split; [pu_chain |]. split; [exact P4 |].
  split; [pu_track (pu_greg c) KT; congruence |].
  split; [pu_track pu_GPC KT; congruence |].
  split.
  - intros q Hq. destruct (B2 q Hq) as (E1 & E2 & E3).
    assert (K : q < 16) by exact Hq.
    pu_track (pu_SLOT c q) K. pu_track (pu_MP c q) K.
    split; [congruence |]. split; [lia | congruence].
  - split.
    + intros r Hr. destruct (Nat.eq_dec r pu_T4) as [-> | H4]; [pu_track pu_T4 KT; congruence |].
      assert (K : ~ (r = pu_greg c \/ r = pu_GPC \/ pu_in_mp c r) /\ r <> pu_T4) by (split; assumption).
      pu_track r K. congruence.
    + pu_hfr_goal.
Qed.

(* DEC c j on a zero counter: INC pu_GPC, clear pu_T2, back to HEAD. *)
Theorem pu_hDECH_zero : forall c o Ph s,
  subcode (o, pu_hDECH c o) (1, Ph) -> hpc s = o -> herr s = false -> hv s (pu_greg c) = 0 ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_L_HEAD /\ hv s' pu_GPC = S (hv s pu_GPC) /\ hv s' pu_T2 = 0 /\
    pu_vfr (fun r => r = pu_GPC \/ r = pu_T2) s s' /\
    pu_hfr (fun r => r = pu_greg c \/ r = pu_GPC \/ r = pu_T2 \/ r = pu_T4) s s'.
Proof.
  intros c o Ph s Hsc Hpc He Hz. unfold pu_hDECH in Hsc.
  pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 S1 Hsc2. pu_sc_split Hsc2 S2 Hsc3. pu_sc_split Hsc3 S3 Hsc4.
  destruct (pu_hDEC_spec (pu_greg c) (pu_DECH_taken o) o Ph s S0 Hpc He) as (s1 & R1 & F1 & D1).
  rewrite Hz in D1. destruct D1 as (P1 & V1 & W1).
  destruct (pu_hINC_spec pu_GPC (1 + o) Ph s1 S1 P1 ltac:(pu_herr_tac)) as (s2 & R2 & P2 & V2 & W2 & F2).
  destruct (pu_hZERO_spec pu_T2 (2 + o) Ph s2 S2 P2 ltac:(pu_herr_tac)) as (s3 & R3 & P3 & V3 & F3).
  destruct (pu_hJMP_spec pu_T4 pu_L_HEAD (3 + o) Ph s3 S3 P3 ltac:(pu_herr_tac)) as (s4 & R4 & P4 & V4 & F4).
  assert (KT : True) by exact I.
  exists s4. split; [pu_chain |]. split; [exact P4 |].
  split; [pu_track pu_GPC KT; congruence |]. split; [pu_track pu_T2 KT; congruence |]. split.
  - intros r Hr. destruct (Nat.eq_dec r pu_T4) as [-> | H4]; [pu_track pu_T4 KT; congruence |].
    destruct (Nat.eq_dec r (pu_greg c)) as [-> | Hg]; [pu_track (pu_greg c) KT; congruence |].
    assert (K : ~ (r = pu_GPC \/ r = pu_T2) /\ r <> pu_T4 /\ r <> pu_greg c) by (repeat split; assumption).
    pu_track r K. congruence.
  - pu_hfr_goal.
Qed.

(* DEC c j on a positive counter: decrement, bump bank c, pu_GPC := pu_T2. *)
Theorem pu_hDECH_taken : forall c o Ph s u,
  subcode (o, pu_hDECH c o) (1, Ph) -> hpc s = o -> herr s = false -> hv s (pu_greg c) = S u ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_L_HEAD /\ hv s' (pu_greg c) = u /\ hv s' pu_GPC = hv s pu_T2 /\
    hv s' pu_T2 = 0 /\
    (forall q, q < 16 -> hv s' (pu_SLOT c q) = hv s (pu_SLOT c q) /\
       hver s' (pu_SLOT c q) = 2 + hver s (pu_SLOT c q) /\ hv s' (pu_MP c q) = 0) /\
    pu_vfr (fun r => r = pu_greg c \/ r = pu_GPC \/ r = pu_T2 \/ pu_in_mp c r) s s' /\
    pu_hfr (fun r => r = pu_greg c \/ r = pu_GPC \/ r = pu_T2 \/ r = pu_T4 \/ pu_in_mp c r \/ pu_in_slots c r) s s'.
Proof.
  intros c o Ph s u Hsc Hpc He Hu. unfold pu_hDECH in Hsc.
  pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 X1 Hsc2. pu_sc_split Hsc2 X2 Hsc3. pu_sc_split Hsc3 X3 Hsc4.
  pu_sc_split Hsc4 S1 Hsc5. pu_sc_split Hsc5 S2 Hsc6. pu_sc_split Hsc6 S3 S4.
  destruct (pu_hDEC_spec (pu_greg c) (pu_DECH_taken o) o Ph s S0 Hpc He) as (s1 & R1 & F1 & D1).
  rewrite Hu in D1. destruct D1 as (P1 & V1 & W1).
  destruct (pu_hBUMPS_spec c (pu_DECH_taken o) Ph s1 S1 P1 ltac:(pu_herr_tac))
    as (s2 & R2 & P2 & B2 & HF2 & VF2).
  destruct (pu_hZERO_spec pu_GPC (pu_BUMPS_len + pu_DECH_taken o) Ph s2 S2 P2 ltac:(pu_herr_tac))
    as (s3 & R3 & P3 & V3 & F3).
  destruct (pu_hMOVE_spec pu_T2 pu_GPC (1 + pu_BUMPS_len + pu_DECH_taken o) Ph s3 ltac:(pu_rneq) S3 P3
              ltac:(pu_herr_tac)) as (s4 & R4 & P4 & V4y & V4x & F4).
  destruct (pu_hJMP_spec pu_T4 pu_L_HEAD (1 + MOVE_len + pu_BUMPS_len + pu_DECH_taken o) Ph s4 S4 P4
              ltac:(pu_herr_tac)) as (s5 & R5 & P5 & V5 & F5).
  assert (KT : True) by exact I.
  exists s5. split; [pu_chain |]. split; [exact P5 |].
  split; [pu_track (pu_greg c) KT; congruence |].
  split; [pu_track pu_GPC KT; pu_track pu_T2 KT; lia |].
  split; [pu_track pu_T2 KT; congruence |].
  split.
  - intros q Hq. destruct (B2 q Hq) as (E1 & E2 & E3).
    assert (K : q < 16) by exact Hq.
    pu_track (pu_SLOT c q) K. pu_track (pu_MP c q) K.
    split; [congruence |]. split; [lia | congruence].
  - split.
    + intros r Hr. destruct (Nat.eq_dec r pu_T4) as [-> | H4]; [pu_track pu_T4 KT; congruence |].
      assert (K : ~ (r = pu_greg c \/ r = pu_GPC \/ r = pu_T2 \/ pu_in_mp c r) /\ r <> pu_T4)
        by (split; assumption).
      pu_track r K. congruence.
    + pu_hfr_goal.
Qed.

(* CHECK, first part: copy pu_NC c and branch 17 ways on it. *)
Theorem pu_hCKH_disp : forall c o Ph s,
  subcode (o, pu_hCKH c o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hv s' pu_T4 = 0 /\
    pu_vfr (fun r => r = pu_T7 \/ r = pu_T4) s s' /\ pu_hframe [pu_NC c; pu_T7; pu_T4] s s' /\
    (hv s (pu_NC c) < 16 -> hpc s' = pu_CKS_at o (hv s (pu_NC c)) /\ hv s' pu_T7 = 0) /\
    (16 <= hv s (pu_NC c) -> hpc s' = pu_CKH_dead o /\ hv s' pu_T7 = hv s (pu_NC c) - 16).
Proof.
  intros c o Ph s Hsc Hpc He. unfold pu_hCKH in Hsc. pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 S1 Hsc2.
  destruct (pu_hCOPY_spec (pu_NC c) pu_T7 pu_T4 o Ph s ltac:(pu_rneq) ltac:(pu_rneq) ltac:(pu_rneq) S0 Hpc He)
    as (s1 & R1 & P1 & V1x & V1y & V1t & F1).
  destruct (pu_hDISP_spec pu_T7 pu_T4 (map (pu_CKS_at o) (seq 0 16)) (pu_COPY_len + o) Ph s1 ltac:(pu_rneq) S1 P1
              ltac:(pu_herr_tac)) as (s2 & R2 & F2 & V4 & L & G).
  rewrite map_length, seq_length, V1y in L, G.
  assert (KT : True) by exact I.
  exists s2. split; [pu_chain |]. split; [congruence |].
  split.
  - intros r Hr. destruct (Nat.eq_dec r (pu_NC c)) as [-> | Hn]; [pu_track (pu_NC c) KT; congruence |].
    assert (K : ~ (r = pu_T7 \/ r = pu_T4) /\ r <> pu_NC c) by (split; assumption).
    pu_track r K. congruence.
  - split; [pu_frame_goal |]. split.
    + intros Hl. destruct (L Hl) as [P2 Z2]. split; [| exact Z2].
      rewrite P2. apply pu_nth_map_seq. exact Hl.
    + intros Hl. destruct (G Hl) as [P2 Z2]. split; [| exact Z2].
      rewrite P2. unfold pu_CKH_dead. lia.
Qed.

(* CHECK on slot k, first part: load (code, value) into the slot. *)
Theorem pu_hCKS_pre : forall c k o Ph s,
  subcode (o, pu_hCKS c k o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_CKS_chk o /\
    hv s' (pu_SLOT c k) = hv s (pu_SLOT c k) + pu_pair (hv s pu_T2) (hv s (pu_greg c)) /\
    hver s (pu_SLOT c k) < hver s' (pu_SLOT c k) /\
    hv s' pu_T2 = hv s pu_T2 /\ hv s' pu_T3 = 0 /\ hv s' pu_T4 = 0 /\ hv s' pu_T8 = 0 /\ hv s' pu_T9 = 0 /\
    pu_vfr (fun r => r = pu_SLOT c k \/ r = pu_T3 \/ r = pu_T4 \/ r = pu_T8 \/ r = pu_T9) s s' /\
    pu_hframe [pu_greg c; pu_T8; pu_T4; pu_T2; pu_T9; pu_T3; pu_SLOT c k] s s'.
Proof.
  intros c k o Ph s Hsc Hpc He. unfold pu_hCKS in Hsc.
  pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 S1 Hsc2. pu_sc_split Hsc2 S2 Hsc3. pu_sc_split Hsc3 S3 Hsc4.
  destruct (pu_hCOPY_spec (pu_greg c) pu_T8 pu_T4 o Ph s ltac:(pu_rneq) ltac:(pu_rneq) ltac:(pu_rneq) S0 Hpc He)
    as (s1 & R1 & P1 & V1x & V1y & V1t & F1).
  destruct (pu_hCOPY_spec pu_T2 pu_T9 pu_T4 (pu_COPY_len + o) Ph s1 ltac:(pu_rneq) ltac:(pu_rneq) ltac:(pu_rneq) S1 P1
              ltac:(pu_herr_tac)) as (s2 & R2 & P2 & V2x & V2y & V2t & F2).
  destruct (pu_hPACK_spec pu_T3 pu_T8 pu_T9 (2 * pu_COPY_len + o) Ph s2 ltac:(pu_rneq) ltac:(pu_rneq) ltac:(pu_rneq) S2 P2
              ltac:(pu_herr_tac)) as (s3 & R3 & P3 & V3x & V3y & V3a & F3).
  destruct (pu_hMOVE_spec pu_T8 (pu_SLOT c k) (2 * pu_COPY_len + PACK_len + o) Ph s3 ltac:(pu_rneq) S3 P3
              ltac:(pu_herr_tac)) as (s4 & R4 & P4 & V4y & V4x & F4).
  assert (KT : True) by exact I.
  assert (ES : hv s4 (pu_SLOT c k) = hv s (pu_SLOT c k) + pu_pair (hv s pu_T2) (hv s (pu_greg c))).
  { pu_track (pu_SLOT c k) KT. pu_track pu_T8 KT. pu_track pu_T9 KT. pu_track pu_T2 KT. pu_track (pu_greg c) KT. congruence. }
  assert (R : Hrun Ph s s4) by pu_chain.
  exists s4. split; [exact R |]. split; [exact P4 |]. split; [exact ES |].
  split.
  { apply (pu_hrun_val_moved pu_hprop_eqb pu_heval Ph s s4 R). rewrite ES.
    pose proof (pu_pair_pos (hv s pu_T2) (hv s (pu_greg c))). lia. }
  split; [pu_track pu_T2 KT; congruence |]. split; [pu_track pu_T3 KT; congruence |].
  split; [pu_track pu_T4 KT; congruence |]. split; [pu_track pu_T8 KT; congruence |].
  split; [pu_track pu_T9 KT; congruence |]. split.
  - intros r Hr. destruct (Nat.eq_dec r pu_T2) as [-> | H2]; [pu_track pu_T2 KT; congruence |].
    destruct (Nat.eq_dec r (pu_greg c)) as [-> | Hg]; [pu_track (pu_greg c) KT; congruence |].
    assert (K : ~ (r = pu_SLOT c k \/ r = pu_T3 \/ r = pu_T4 \/ r = pu_T8 \/ r = pu_T9) /\ r <> pu_T2 /\
                r <> pu_greg c) by (repeat split; assumption).
    pu_track r K. congruence.
  - pu_frame_goal.
Qed.

(* CHECK on slot k, last part (after a passing CHECK): set the mirror to
   code + 1, INC pu_NC c, INC pu_GPC, back to HEAD. *)
Theorem pu_hCKS_post : forall c k o Ph s,
  subcode (o, pu_hCKS c k o) (1, Ph) -> hpc s = 1 + pu_CKS_chk o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_L_HEAD /\
    hv s' (pu_MP c k) = S (hv s pu_T2) /\ hv s' pu_T2 = 0 /\ hv s' (pu_NC c) = S (hv s (pu_NC c)) /\
    hv s' pu_GPC = S (hv s pu_GPC) /\ hv s' pu_T4 = hv s pu_T4 /\
    pu_vfr (fun r => r = pu_MP c k \/ r = pu_T2 \/ r = pu_NC c \/ r = pu_GPC) s s' /\
    pu_hframe [pu_MP c k; pu_T2; pu_NC c; pu_GPC; pu_T4] s s'.
Proof.
  intros c k o Ph s Hsc Hpc He. unfold pu_hCKS in Hsc.
  pu_sc_split Hsc X0 Hsc1. pu_sc_split Hsc1 X1 Hsc2. pu_sc_split Hsc2 X2 Hsc3. pu_sc_split Hsc3 X3 Hsc4.
  pu_sc_split Hsc4 X4 Hsc5. pu_sc_split Hsc5 S0 Hsc6. pu_sc_split Hsc6 S1 Hsc7. pu_sc_split Hsc7 S2 Hsc8.
  pu_sc_split Hsc8 S3 Hsc9. pu_sc_split Hsc9 S4 S5.
  destruct (pu_hZERO_spec (pu_MP c k) (1 + pu_CKS_chk o) Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & F1).
  destruct (pu_hMOVE_spec pu_T2 (pu_MP c k) (2 + pu_CKS_chk o) Ph s1 ltac:(pu_rneq) S1 P1 ltac:(pu_herr_tac))
    as (s2 & R2 & P2 & V2y & V2x & F2).
  destruct (pu_hINC_spec (pu_MP c k) (2 + MOVE_len + pu_CKS_chk o) Ph s2 S2 P2 ltac:(pu_herr_tac))
    as (s3 & R3 & P3 & V3 & W3 & F3).
  destruct (pu_hINC_spec (pu_NC c) (3 + MOVE_len + pu_CKS_chk o) Ph s3 S3 P3 ltac:(pu_herr_tac))
    as (s4 & R4 & P4 & V4 & W4 & F4).
  destruct (pu_hINC_spec pu_GPC (4 + MOVE_len + pu_CKS_chk o) Ph s4 S4 P4 ltac:(pu_herr_tac))
    as (s5 & R5 & P5 & V5 & W5 & F5).
  destruct (pu_hJMP_spec pu_T4 pu_L_HEAD (5 + MOVE_len + pu_CKS_chk o) Ph s5 S5 P5 ltac:(pu_herr_tac))
    as (s6 & R6 & P6 & V6 & F6).
  assert (KT : True) by exact I.
  exists s6. split; [pu_chain |]. split; [exact P6 |].
  split; [pu_track (pu_MP c k) KT; pu_track pu_T2 KT; lia |].
  split; [pu_track pu_T2 KT; congruence |].
  split; [pu_track (pu_NC c) KT; congruence |].
  split; [pu_track pu_GPC KT; congruence |].
  split; [pu_track pu_T4 KT; congruence |].
  split.
  - intros r Hr. destruct (Nat.eq_dec r pu_T4) as [-> | H4]; [pu_track pu_T4 KT; congruence |].
    assert (K : ~ (r = pu_MP c k \/ r = pu_T2 \/ r = pu_NC c \/ r = pu_GPC) /\ r <> pu_T4)
      by (split; assumption).
    pu_track r K. congruence.
  - pu_frame_goal.
Qed.

(* COMMIT, first part: pu_T2 := code + 1, then compare it with the mirrors
   of bank c in order. *)
Theorem pu_hCMH_search : forall c o Ph s,
  subcode (o, pu_hCMH c o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hv s' pu_T2 = S (hv s pu_T2) /\ hv s' pu_T7 = 0 /\ hv s' pu_T8 = 0 /\
    hv s' pu_T4 = 0 /\
    pu_vfr (fun r => r = pu_T2 \/ r = pu_T7 \/ r = pu_T8 \/ r = pu_T4) s s' /\
    pu_hfr (fun r => r = pu_T7 \/ r = pu_T8 \/ r = pu_T4 \/ r = pu_T2 \/ pu_in_mp c r) s s' /\
    (forall j, j < 16 -> hv s (pu_MP c j) = S (hv s pu_T2) ->
       (forall j', j' < j -> hv s (pu_MP c j') <> S (hv s pu_T2)) -> hpc s' = pu_CMS_at o j) /\
    ((forall j, j < 16 -> hv s (pu_MP c j) <> S (hv s pu_T2)) -> hpc s' = pu_CMH_dead o).
Proof.
  intros c o Ph s Hsc Hpc He. unfold pu_hCMH in Hsc. pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 S1 Hsc2.
  destruct (pu_hINC_spec pu_T2 o Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & W1 & F1).
  destruct (pu_hEQRS_spec c (pu_CMS_at o) (1 + o) Ph s1 S1 P1 ltac:(pu_herr_tac))
    as (s2 & R2 & Z7 & Z8 & Z4 & VF2 & HF2 & M2 & N2).
  assert (EM : forall j, hv s1 (pu_MP c j) = hv s (pu_MP c j)).
  { intro j. apply (fun N => proj1 (F1 (pu_MP c j) N)). simpl. pu_unfold_regs. lia. }
  assert (KT : True) by exact I.
  exists s2. split; [pu_chain |]. split; [pu_track pu_T2 KT; congruence |].
  split; [exact Z7 |]. split; [exact Z8 |]. split; [exact Z4 |].
  split; [pu_vfr_goal |]. split; [pu_hfr_goal |]. split.
  - intros j Hj Hm Hf. apply M2; [exact Hj | rewrite EM, V1; exact Hm |].
    intros j' Hj'. rewrite EM, V1. apply Hf, Hj'.
  - intros Hall. rewrite N2; [unfold pu_CMH_dead; lia |].
    intros j Hj. rewrite EM, V1. apply Hall, Hj.
Qed.

(* COMMIT, last part (after a passing COMMIT): clear pu_T2, INC pu_GPC, back
   to HEAD. *)
Theorem pu_hCMS_post : forall sl o Ph s,
  subcode (o, pu_hCMS sl o) (1, Ph) -> hpc s = 1 + o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_L_HEAD /\ hv s' pu_T2 = 0 /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    hv s' pu_T4 = hv s pu_T4 /\ pu_hframe [pu_T2; pu_GPC; pu_T4] s s'.
Proof.
  intros sl o Ph s Hsc Hpc He. unfold pu_hCMS in Hsc.
  pu_sc_split Hsc X0 Hsc1. pu_sc_split Hsc1 S0 Hsc2. pu_sc_split Hsc2 S1 S2.
  destruct (pu_hZERO_spec pu_T2 (1 + o) Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & F1).
  destruct (pu_hINC_spec pu_GPC (2 + o) Ph s1 S1 P1 ltac:(pu_herr_tac)) as (s2 & R2 & P2 & V2 & W2 & F2).
  destruct (pu_hJMP_spec pu_T4 pu_L_HEAD (3 + o) Ph s2 S2 P2 ltac:(pu_herr_tac)) as (s3 & R3 & P3 & V3 & F3).
  assert (KT : True) by exact I.
  exists s3. split; [pu_chain |]. split; [exact P3 |].
  split; [pu_track pu_T2 KT; congruence |]. split; [pu_track pu_GPC KT; congruence |].
  split; [pu_track pu_T4 KT; congruence |]. pu_frame_goal.
Qed.

(* CERTIFY, last part (after a passing CERTIFY): INC pu_GPC, back to HEAD. *)
Theorem pu_hCERTH_post : forall o Ph s,
  subcode (o, pu_hCERTH o) (1, Ph) -> hpc s = 1 + o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_L_HEAD /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    hv s' pu_T4 = hv s pu_T4 /\ pu_hframe [pu_GPC; pu_T4] s s'.
Proof.
  intros o Ph s Hsc Hpc He. unfold pu_hCERTH in Hsc.
  pu_sc_split Hsc X0 Hsc1. pu_sc_split Hsc1 S0 S1.
  destruct (pu_hINC_spec pu_GPC (1 + o) Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & W1 & F1).
  destruct (pu_hJMP_spec pu_T4 pu_L_HEAD (2 + o) Ph s1 S1 P1 ltac:(pu_herr_tac)) as (s2 & R2 & P2 & V2 & F2).
  assert (KT : True) by exact I.
  exists s2. split; [pu_chain |]. split; [exact P2 |].
  split; [pu_track pu_GPC KT; congruence |]. split; [pu_track pu_T4 KT; congruence |]. pu_frame_goal.
Qed.

(* Close an equation about a state reached along a chain by rewriting
   each value, version, latch, table, channel, ledger and flag of a later
   state with the equation that relates it to an earlier state (all such
   equations point from later states to earlier ones), then reflexivity,
   an assumption, or linear arithmetic. *)
Ltac pu_cc :=
  repeat match goal with
  | H : hv ?b ?r = _ |- context [hv ?b ?r] => rewrite H
  | H : hver ?b ?r = _ |- context [hver ?b ?r] => rewrite H
  | H : M.err (M.core_of ?b) = _ |- context [M.err (M.core_of ?b)] => rewrite H
  | H : M.facts (M.core_of ?b) = _ |- context [M.facts (M.core_of ?b)] => rewrite H
  | H : M.chan (M.core_of ?b) = _ |- context [M.chan (M.core_of ?b)] => rewrite H
  | H : M.mu ?b = _ |- context [M.mu ?b] => rewrite H
  | H : M.cert ?b = _ |- context [M.cert ?b] => rewrite H
  end;
  first [ reflexivity | assumption | lia ].

(* ================================================================= *)
(* The record moves of U_P.                                             *)
(* ================================================================= *)

Lemma pu_U_CHK : forall c k, k < 16 ->
  subcode (pu_CKS_chk (pu_CKS_at (pu_L_CKH c) k), pu_hCHECK (pu_SLOT c k) (pu_CKS_chk (pu_CKS_at (pu_L_CKH c) k))) (1, U_P).
Proof.
  intros c k Hk. pose proof (pu_U_CKS c k Hk) as H. unfold pu_hCKS in H.
  pu_sc_split H H1 H2. pu_sc_split H2 H3 H4. pu_sc_split H4 H5 H6. pu_sc_split H6 H7 H8.
  pu_sc_split H8 H9 H10. exact H9.
Qed.

Lemma pu_U_CMT : forall c k, k < 16 ->
  subcode (pu_CMS_at (pu_L_CMH c) k, pu_hCOMMIT (pu_SLOT c k) (pu_CMS_at (pu_L_CMH c) k)) (1, U_P).
Proof.
  intros c k Hk. pose proof (pu_U_CMS c k Hk) as H. unfold pu_hCMS in H. pu_sc_split H H1 H2. exact H1.
Qed.

Lemma pu_U_CERT : subcode (pu_L_CERT, pu_hCERTIFY pu_L_CERT) (1, U_P).
Proof. pose proof pu_U_CERTH as H. unfold pu_hCERTH in H. pu_sc_split H H1 H2. exact H1. Qed.

Lemma pu_halted_at_stop : forall s : hstate,
  herr s = false -> hpc s = pu_L_STOP -> M.pu_halted U_P (M.core_of s).
Proof.
  intros s He Hp. unfold M.pu_halted, M.pu_next_instr. rewrite He, Hp, pu_U_fetch_stop. reflexivity.
Qed.

(* ================================================================= *)
(* States at HEAD.                                                    *)
(* ================================================================= *)

Definition pu_at_head (P : list E.instr) (s : hstate) : Prop :=
  hpc s = pu_L_HEAD /\ herr s = false /\ hv s pu_PROG = pu_prog_code P /\
  (forall r, pu_scratch r -> hv s r = 0).

Lemma pu_scratch_dec : forall r, pu_scratch r \/ ~ pu_scratch r.
Proof. intro r. unfold pu_scratch. lia. Qed.

Lemma pu_scratch_all : forall s : hstate,
  hv s pu_T0 = 0 -> hv s pu_T1 = 0 -> hv s pu_T2 = 0 -> hv s pu_T3 = 0 -> hv s pu_T4 = 0 ->
  hv s pu_T5 = 0 -> hv s pu_T6 = 0 -> hv s pu_T7 = 0 -> hv s pu_T8 = 0 -> hv s pu_T9 = 0 ->
  forall r, pu_scratch r -> hv s r = 0.
Proof.
  intros s H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 r Hr.
  destruct (pu_scratch_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    assumption.
Qed.

Lemma pu_at_head_zero : forall P s, pu_at_head P s ->
  hv s pu_T0 = 0 /\ hv s pu_T1 = 0 /\ hv s pu_T2 = 0 /\ hv s pu_T3 = 0 /\ hv s pu_T4 = 0 /\
  hv s pu_T5 = 0 /\ hv s pu_T6 = 0 /\ hv s pu_T7 = 0 /\ hv s pu_T8 = 0 /\ hv s pu_T9 = 0.
Proof.
  intros P s (_ & _ & _ & Hz).
  repeat split; apply Hz; unfold pu_scratch; pu_unfold_regs; lia.
Qed.

Ltac pu_zero_goal K := match goal with |- hv _ ?X = 0 => pu_track X K; pu_cc end.

(* Close an pu_at_head goal: pc, latch, program code, and the ten scratch
   registers, each tracked along the chain. *)
Ltac pu_head_goal Hpc K :=
  unfold pu_at_head; split; [exact Hpc |]; split; [pu_herr_tac |];
  split; [pu_track pu_PROG K; pu_cc |];
  apply pu_scratch_all; pu_zero_goal K.

(* ================================================================= *)
(* Fetch and decode.                                                  *)
(* ================================================================= *)

Theorem pu_phase_decode : forall P s i, pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some i ->
  exists s1, Hrun U_P s s1 /\ herr s1 = false /\ hpc s1 = pu_handler i /\ hv s1 pu_T2 = pu_arg_of i /\
    hv s1 pu_T0 = 0 /\ hv s1 pu_T1 = 0 /\ hv s1 pu_T3 = 0 /\ hv s1 pu_T4 = 0 /\ hv s1 pu_T5 = 0 /\
    hv s1 pu_T6 = 0 /\ hv s1 pu_T7 = 0 /\ hv s1 pu_T8 = 0 /\ hv s1 pu_T9 = 0 /\
    pu_vfr pu_scratch s s1 /\ pu_hfr (fun r => pu_scratch r \/ r = pu_PROG \/ r = pu_GPC) s s1.
Proof.
  intros P s i (Hpc & He & Hp & Hz) Hf.
  destruct (pu_hHEAD_spec P pu_L_HEAD U_P s pu_U_HEAD Hpc He Hp Hz) as (s1 & R1 & V1 & F1 & G).
  rewrite Hf in G. destruct G as (P1 & A1 & Z0 & Z1 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  exists s1. split; [exact R1 |]. split; [pu_herr_tac |].
  repeat (split; [assumption |]). exact F1.
Qed.

(* ================================================================= *)
(* Guest pc 0, guest pc past the end, guest HALT: the host halts.     *)
(* ================================================================= *)

Theorem pu_phase_stop : forall P s, pu_at_head P s ->
  E.fetch P (hv s pu_GPC) = None \/ E.fetch P (hv s pu_GPC) = Some E.HALT ->
  exists s', pu_hreach s s' /\ hpc s' = pu_L_STOP /\ herr s' = false /\ M.pu_halted U_P (M.core_of s') /\
    (forall r, hv s' r = hv s r) /\
    (forall r, ~ pu_scratch r -> r <> pu_PROG -> r <> pu_GPC -> hver s' r = hver s r) /\
    pu_same_sub s s'.
Proof.
  intros P s Hh Hf. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_hHEAD_spec P pu_L_HEAD U_P s pu_U_HEAD Hpc He Hp Hz) as (s1 & R1 & V1 & F1 & G).
  assert (P1 : hpc s1 = pu_L_HALT).
  { destruct Hf as [Hf | Hf]; rewrite Hf in G; [exact G | exact (proj1 G)]. }
  destruct (pu_hHALTB_spec pu_L_HALT U_P s1 pu_U_HALTB P1 ltac:(pu_herr_tac))
    as (s2 & R2 & P2 & Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & F2).
  assert (R : Hrun U_P s s2) by pu_chain.
  assert (P2' : hpc s2 = pu_L_STOP) by (rewrite P2; reflexivity).
  exists s2. split; [apply pu_Hrun_hreach, R |]. split; [exact P2' |].
  split; [pu_herr_tac |]. split; [apply pu_halted_at_stop; [pu_herr_tac | exact P2'] |].
  split; [| split].
  - intros r. destruct (pu_scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs). apply (pu_scratch_all s2); assumption.
    + pu_track r Hs. pu_cc.
  - intros r H1 H2 H3. assert (K : ~ pu_scratch r /\ r <> pu_PROG /\ r <> pu_GPC) by (repeat split; assumption).
    pu_track r K. pu_cc.
  - apply (pu_hrun_same_sub _ _ _ _ _ R).
Qed.

Corollary pu_phase_pc0 : forall P s, pu_at_head P s -> hv s pu_GPC = 0 ->
  exists s', pu_hreach s s' /\ hpc s' = pu_L_STOP /\ herr s' = false /\ M.pu_halted U_P (M.core_of s') /\
    (forall r, hv s' r = hv s r) /\
    (forall r, ~ pu_scratch r -> r <> pu_PROG -> r <> pu_GPC -> hver s' r = hver s r) /\
    pu_same_sub s s'.
Proof. intros P s Hh Hg. apply (pu_phase_stop P s Hh). left. rewrite Hg. reflexivity. Qed.

Corollary pu_phase_out : forall P s k, pu_at_head P s -> hv s pu_GPC = S k -> nth_error P k = None ->
  exists s', pu_hreach s s' /\ hpc s' = pu_L_STOP /\ herr s' = false /\ M.pu_halted U_P (M.core_of s') /\
    (forall r, hv s' r = hv s r) /\
    (forall r, ~ pu_scratch r -> r <> pu_PROG -> r <> pu_GPC -> hver s' r = hver s r) /\
    pu_same_sub s s'.
Proof. intros P s k Hh Hg Hn. apply (pu_phase_stop P s Hh). left. rewrite Hg. exact Hn. Qed.

Corollary pu_phase_halt : forall P s, pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some E.HALT ->
  exists s', pu_hreach s s' /\ hpc s' = pu_L_STOP /\ herr s' = false /\ M.pu_halted U_P (M.core_of s') /\
    (forall r, hv s' r = hv s r) /\
    (forall r, ~ pu_scratch r -> r <> pu_PROG -> r <> pu_GPC -> hver s' r = hver s r) /\
    pu_same_sub s s'.
Proof. intros P s Hh Hf. apply (pu_phase_stop P s Hh). right. exact Hf. Qed.

(* ================================================================= *)
(* INC and DEC.                                                       *)
(* ================================================================= *)

Theorem pu_phase_inc : forall P s c,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.INC c) ->
  exists s', pu_hreach s s' /\ pu_at_head P s' /\
    hv s' (pu_greg c) = S (hv s (pu_greg c)) /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    (forall q, q < 16 -> hv s' (pu_MP c q) = 0 /\ hv s' (pu_SLOT c q) = hv s (pu_SLOT c q) /\
       hver s' (pu_SLOT c q) = 2 + hver s (pu_SLOT c q)) /\
    (forall r, r <> pu_greg c -> r <> pu_GPC -> ~ pu_in_mp c r -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> ~ pu_in_slots c r -> hver s' r = hver s r) /\
    pu_same_sub s s'.
Proof.
  intros P s c Hh Hf. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_phase_decode P s (E.INC c) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (pu_handler (E.INC c)) with pu_L_INC in P1. change (pu_arg_of (E.INC c)) with (pu_ccode c) in A1.
  destruct (pu_hCD_spec (pu_L_INCH E.CA) (pu_L_INCH E.CB) pu_L_INC U_P s1 c pu_U_INCD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & F2).
  assert (P2' : hpc s2 = pu_L_INCH c) by (rewrite P2; destruct c; reflexivity).
  destruct (pu_hINCH_spec c (pu_L_INCH c) U_P s2 (pu_U_INCH c) P2' ltac:(pu_herr_tac))
    as (s3 & R3 & P3 & G3 & C3 & B3 & VF3 & HF3).
  assert (R : Hrun U_P s s3) by pu_chain.
  assert (KT : True) by exact I.
  assert (AH : pu_at_head P s3) by pu_head_goal P3 KT.
  exists s3. split; [apply pu_Hrun_hreach, R |]. split; [exact AH |].
  split; [pu_track (pu_greg c) KT; pu_cc |].
  split; [pu_track pu_GPC KT; pu_cc |].
  split; [| split; [| split]].
  - intros q Hq. destruct (B3 q Hq) as (E1' & E2' & E3').
    assert (K : q < 16) by exact Hq. pu_track (pu_SLOT c q) K.
    split; [exact E3' |]. split; [pu_cc | lia].
  - intros r H1 H2 H3. destruct (pu_scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : ~ pu_scratch r /\ r <> pu_greg c /\ r <> pu_GPC /\ ~ pu_in_mp c r)
        by (repeat split; assumption).
      pu_track r K. pu_cc.
  - intros r H1 H2. assert (K : 48 <= r /\ ~ pu_in_slots c r) by (split; assumption).
    pu_track r K. pu_cc.
  - apply (pu_hrun_same_sub _ _ _ _ _ R).
Qed.

Theorem pu_phase_dec_taken : forall P s c j u,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.DEC c j) -> hv s (pu_greg c) = S u ->
  exists s', pu_hreach s s' /\ pu_at_head P s' /\ hv s' (pu_greg c) = u /\ hv s' pu_GPC = j /\
    (forall q, q < 16 -> hv s' (pu_MP c q) = 0 /\ hv s' (pu_SLOT c q) = hv s (pu_SLOT c q) /\
       hver s' (pu_SLOT c q) = 2 + hver s (pu_SLOT c q)) /\
    (forall r, r <> pu_greg c -> r <> pu_GPC -> ~ pu_in_mp c r -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> ~ pu_in_slots c r -> hver s' r = hver s r) /\
    pu_same_sub s s'.
Proof.
  intros P s c j u Hh Hf Hu. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_phase_decode P s (E.DEC c j) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (pu_handler (E.DEC c j)) with pu_L_DEC in P1.
  change (pu_arg_of (E.DEC c j)) with (pu_pair (pu_ccode c) j) in A1.
  destruct (pu_hUCD_spec (pu_L_DECH E.CA) (pu_L_DECH E.CB) pu_L_DEC U_P s1 c j pu_U_DECD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & X2 & Q2 & F2).
  assert (P2' : hpc s2 = pu_L_DECH c) by (rewrite P2; destruct c; reflexivity).
  assert (KT : True) by exact I.
  assert (G2 : hv s2 (pu_greg c) = S u) by (pu_track (pu_greg c) KT; pu_cc).
  destruct (pu_hDECH_taken c (pu_L_DECH c) U_P s2 u (pu_U_DECH c) P2' ltac:(pu_herr_tac) G2)
    as (s3 & R3 & P3 & G3 & C3 & Z3 & B3 & VF3 & HF3).
  assert (R : Hrun U_P s s3) by pu_chain.
  assert (AH : pu_at_head P s3) by pu_head_goal P3 KT.
  exists s3. split; [apply pu_Hrun_hreach, R |]. split; [exact AH |].
  split; [exact G3 |]. split; [pu_cc |].
  split; [| split; [| split]].
  - intros q Hq. destruct (B3 q Hq) as (E1' & E2' & E3').
    assert (K : q < 16) by exact Hq. pu_track (pu_SLOT c q) K.
    split; [exact E3' |]. split; [pu_cc | lia].
  - intros r H1 H2 H3. destruct (pu_scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : ~ pu_scratch r /\ r <> pu_greg c /\ r <> pu_GPC /\ ~ pu_in_mp c r)
        by (repeat split; assumption).
      pu_track r K. pu_cc.
  - intros r H1 H2. assert (K : 48 <= r /\ ~ pu_in_slots c r) by (split; assumption).
    pu_track r K. pu_cc.
  - apply (pu_hrun_same_sub _ _ _ _ _ R).
Qed.

Theorem pu_phase_dec_zero : forall P s c j,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.DEC c j) -> hv s (pu_greg c) = 0 ->
  exists s', pu_hreach s s' /\ pu_at_head P s' /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    (forall r, r <> pu_GPC -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r) /\
    pu_same_sub s s'.
Proof.
  intros P s c j Hh Hf Hu. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_phase_decode P s (E.DEC c j) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (pu_handler (E.DEC c j)) with pu_L_DEC in P1.
  change (pu_arg_of (E.DEC c j)) with (pu_pair (pu_ccode c) j) in A1.
  destruct (pu_hUCD_spec (pu_L_DECH E.CA) (pu_L_DECH E.CB) pu_L_DEC U_P s1 c j pu_U_DECD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & X2 & Q2 & F2).
  assert (P2' : hpc s2 = pu_L_DECH c) by (rewrite P2; destruct c; reflexivity).
  assert (KT : True) by exact I.
  assert (G2 : hv s2 (pu_greg c) = 0) by (pu_track (pu_greg c) KT; pu_cc).
  destruct (pu_hDECH_zero c (pu_L_DECH c) U_P s2 (pu_U_DECH c) P2' ltac:(pu_herr_tac) G2)
    as (s3 & R3 & P3 & C3 & Z3 & VF3 & HF3).
  assert (R : Hrun U_P s s3) by pu_chain.
  assert (AH : pu_at_head P s3) by pu_head_goal P3 KT.
  exists s3. split; [apply pu_Hrun_hreach, R |]. split; [exact AH |].
  split; [pu_track pu_GPC KT; pu_cc |].
  split; [| split].
  - intros r H1. destruct (pu_scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + destruct (Nat.eq_dec r (pu_greg c)) as [-> | Hg].
      * pu_track (pu_greg c) KT. pu_cc.
      * assert (K : ~ pu_scratch r /\ r <> pu_GPC /\ r <> pu_greg c) by (repeat split; assumption).
        pu_track r K. pu_cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. pu_track r K. pu_cc.
  - apply (pu_hrun_same_sub _ _ _ _ _ R).
Qed.

(* ================================================================= *)
(* CHECK.                                                             *)
(* ================================================================= *)

(* From HEAD to the CHECK of slot j = pu_NC c < 16, with the slot loaded. *)
Lemma pu_check_to_slot : forall P s p c j,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.CHECK p c) ->
  hv s (pu_NC c) = j -> j < 16 ->
  exists s4, Hrun U_P s s4 /\ herr s4 = false /\ hpc s4 = pu_CKS_chk (pu_CKS_at (pu_L_CKH c) j) /\
    hv s4 (pu_SLOT c j) = hv s (pu_SLOT c j) + pu_pair (pu_pcode p) (hv s (pu_greg c)) /\
    hver s (pu_SLOT c j) < hver s4 (pu_SLOT c j) /\
    hv s4 pu_T2 = pu_pcode p /\
    hv s4 pu_T0 = 0 /\ hv s4 pu_T1 = 0 /\ hv s4 pu_T3 = 0 /\ hv s4 pu_T4 = 0 /\ hv s4 pu_T5 = 0 /\
    hv s4 pu_T6 = 0 /\ hv s4 pu_T7 = 0 /\ hv s4 pu_T8 = 0 /\ hv s4 pu_T9 = 0 /\
    pu_vfr (fun r => pu_scratch r \/ r = pu_SLOT c j) s s4 /\
    pu_hfr (fun r => pu_scratch r \/ r = pu_PROG \/ r = pu_GPC \/ r = pu_NC c \/ r = pu_greg c \/ r = pu_SLOT c j) s s4.
Proof.
  intros P s p c j Hh Hf Hn Hj. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_phase_decode P s (E.CHECK p c) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (pu_handler (E.CHECK p c)) with pu_L_CHECK in P1.
  change (pu_arg_of (E.CHECK p c)) with (pu_pair (pu_ccode c) (pu_pcode p)) in A1.
  destruct (pu_hUCD_spec (pu_L_CKH E.CA) (pu_L_CKH E.CB) pu_L_CHECK U_P s1 c (pu_pcode p) pu_U_CKD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & X2 & Q2 & F2).
  assert (P2' : hpc s2 = pu_L_CKH c) by (rewrite P2; destruct c; reflexivity).
  destruct (pu_hCKH_disp c (pu_L_CKH c) U_P s2 (pu_U_CKH c) P2' ltac:(pu_herr_tac))
    as (s3 & R3 & Z3 & VF3 & F3 & L3 & G3).
  assert (KT : True) by exact I.
  assert (N2 : hv s2 (pu_NC c) = j) by (pu_track (pu_NC c) KT; pu_cc).
  rewrite N2 in L3. destruct (L3 Hj) as [P3 T73].
  destruct (pu_hCKS_pre c j (pu_CKS_at (pu_L_CKH c) j) U_P s3 (pu_U_CKS c j Hj) P3 ltac:(pu_herr_tac))
    as (s4 & R4 & P4 & S4 & W4 & T24 & T34 & T44 & T84 & T94 & VF4 & F4).
  assert (R : Hrun U_P s s4) by pu_chain.
  assert (KJ : j < 16) by exact Hj.
  exists s4. split; [exact R |]. split; [pu_herr_tac |]. split; [exact P4 |].
  split.
  { rewrite S4. pu_track (pu_SLOT c j) KJ. pu_track pu_T2 KT. pu_track (pu_greg c) KT. pu_cc. }
  split.
  { pu_track (pu_SLOT c j) KJ. lia. }
  split; [pu_track pu_T2 KT; pu_cc |].
  repeat (split; [pu_zero_goal KT |]).
  split.
  - intros r Hr. assert (K : ~ (pu_scratch r \/ r = pu_SLOT c j)) by exact Hr.
    pu_track r K. pu_cc.
  - intros r Hr. assert (K : j < 16 /\ ~ (pu_scratch r \/ r = pu_PROG \/ r = pu_GPC \/ r = pu_NC c \/
                                         r = pu_greg c \/ r = pu_SLOT c j)) by (split; assumption).
    pu_track r K. split; pu_cc.
Qed.

Theorem pu_phase_check_pass : forall P s p c j,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.CHECK p c) ->
  hv s (pu_NC c) = j -> j < 16 -> hv s (pu_SLOT c j) = 0 ->
  E.holds p (hv s (pu_greg c)) -> length (M.facts (M.core_of s)) < M.pu_fact_cap ->
  exists s', pu_hreach s s' /\ pu_at_head P s' /\
    hv s' pu_GPC = S (hv s pu_GPC) /\ hv s' (pu_NC c) = S j /\ hv s' (pu_MP c j) = S (pu_pcode p) /\
    hv s' (pu_SLOT c j) = pu_pair (pu_pcode p) (hv s (pu_greg c)) /\
    hver s (pu_SLOT c j) < hver s' (pu_SLOT c j) /\
    M.facts (M.core_of s') =
      M.mkfact PSlot (pu_SLOT c j) (hver s' (pu_SLOT c j)) :: M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    (forall r, r <> pu_GPC -> r <> pu_NC c -> r <> pu_MP c j -> r <> pu_SLOT c j -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> r <> pu_SLOT c j -> hver s' r = hver s r).
Proof.
  intros P s p c j Hh Hf Hn Hj Hs0 Hholds Hcap. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_check_to_slot P s p c j Hh Hf Hn Hj)
    as (s4 & R4 & E4 & P4 & S4 & W4 & T24 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & VF4 & HF4).
  rewrite Hs0, Nat.add_0_l in S4.
  destruct (pu_hrun_same_sub _ _ _ _ _ R4) as (Fa4 & Ch4 & Er4 & Mu4 & Ce4).
  destruct (pu_hCHECK_pass_fields (pu_SLOT c j) (pu_CKS_chk (pu_CKS_at (pu_L_CKH c) j)) U_P s4 p (hv s (pu_greg c))
              (pu_U_CHK c j Hj) P4 E4 S4 Hholds ltac:(rewrite Fa4; exact Hcap))
    as (Fa5 & Ch5 & P5 & E5 & Mu5 & Ce5 & All5).
  set (s5 := hrun_prog 1 U_P s4) in *.
  pose proof (pu_all_same_hframe s4 s5 All5) as F5.
  destruct (pu_hCKS_post c j (pu_CKS_at (pu_L_CKH c) j) U_P s5 (pu_U_CKS c j Hj) P5 E5)
    as (s6 & R6 & P6 & M6 & Z6 & N6 & G6 & W6 & VF6 & F6).
  destruct (pu_hrun_same_sub _ _ _ _ _ R6) as (Fa6 & Ch6 & Er6 & Mu6 & Ce6).
  assert (KT : True) by exact I.
  assert (KJ : j < 16) by exact Hj.
  assert (AH : pu_at_head P s6).
  { unfold pu_at_head. split; [exact P6 |]. split; [pu_cc |].
    split; [pu_track pu_PROG KT; pu_cc |]. apply pu_scratch_all; pu_zero_goal KT. }
  assert (EW : hver s6 (pu_SLOT c j) = hver s4 (pu_SLOT c j)) by (pu_track (pu_SLOT c j) KJ; pu_cc).
  exists s6. split.
  { apply (pu_hreach_trans s s4 s6); [apply pu_Hrun_hreach, R4 |].
    apply (pu_hreach_trans s4 s5 s6); [apply pu_hreach_one | apply pu_Hrun_hreach, R6]. }
  split; [exact AH |].
  split; [pu_track pu_GPC KT; pu_cc |].
  split; [pu_track (pu_NC c) KJ; pu_cc |].
  split; [pu_track (pu_MP c j) KJ; pu_track pu_T2 KT; pu_cc |].
  split; [pu_track (pu_SLOT c j) KJ; pu_cc |].
  split; [lia |].
  split; [rewrite Fa6, Fa5, EW, Fa4; reflexivity |].
  split; [pu_cc |]. split; [lia |]. split; [pu_cc |]. split.
  - intros r H1 H2 H3 H4. destruct (pu_scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : j < 16 /\ ~ pu_scratch r /\ r <> pu_GPC /\ r <> pu_NC c /\ r <> pu_MP c j /\ r <> pu_SLOT c j)
        by (repeat split; assumption).
      pu_track r K. pu_cc.
  - intros r H1 H2. assert (K : j < 16 /\ 48 <= r /\ r <> pu_SLOT c j) by (repeat split; assumption).
    pu_track r K. pu_cc.
Qed.

Theorem pu_phase_check_fail : forall P s p c j,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.CHECK p c) ->
  hv s (pu_NC c) = j -> j < 16 -> hv s (pu_SLOT c j) = 0 ->
  ~ E.holds p (hv s (pu_greg c)) \/ M.pu_fact_cap <= length (M.facts (M.core_of s)) ->
  exists s', pu_hreach s s' /\ herr s' = true /\ hpc s' = pu_CKS_chk (pu_CKS_at (pu_L_CKH c) j) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    hv s' (pu_SLOT c j) = pu_pair (pu_pcode p) (hv s (pu_greg c)) /\ hv s' pu_T2 = pu_pcode p /\
    (forall r, r <> pu_T2 -> r <> pu_SLOT c j -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> r <> pu_SLOT c j -> hver s' r = hver s r).
Proof.
  intros P s p c j Hh Hf Hn Hj Hs0 Hbad. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_check_to_slot P s p c j Hh Hf Hn Hj)
    as (s4 & R4 & E4 & P4 & S4 & W4 & T24 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & VF4 & HF4).
  rewrite Hs0, Nat.add_0_l in S4.
  destruct (pu_hrun_same_sub _ _ _ _ _ R4) as (Fa4 & Ch4 & Er4 & Mu4 & Ce4).
  assert (Hs5 : hrun_prog 1 U_P s4 = M.mkst (M.pu_trap (M.core_of s4)) (M.mu s4 + 1) (M.cert s4)).
  { destruct Hbad as [Hbad | Hbad].
    - apply (pu_hCHECK_fail_holds (pu_SLOT c j) (pu_CKS_chk (pu_CKS_at (pu_L_CKH c) j)) U_P s4 p (hv s (pu_greg c))
               (pu_U_CHK c j Hj) P4 E4 S4 Hbad).
    - apply (pu_hCHECK_fail_cap (pu_SLOT c j) (pu_CKS_chk (pu_CKS_at (pu_L_CKH c) j)) U_P s4
               (pu_U_CHK c j Hj) P4 E4). rewrite Fa4. exact Hbad. }
  exists (hrun_prog 1 U_P s4). split.
  { apply (pu_hreach_trans s s4); [apply pu_Hrun_hreach, R4 | apply pu_hreach_one]. }
  rewrite Hs5. cbn [M.core_of M.mu M.cert M.pu_trap M.vals M.vers M.pc M.err M.facts M.chan].
  split; [reflexivity |]. split; [exact P4 |]. split; [exact Fa4 |]. split; [exact Ch4 |].
  split; [lia |]. split; [exact Ce4 |]. split; [exact S4 |]. split; [exact T24 |].
  assert (KT : True) by exact I.
  assert (KJ : j < 16) by exact Hj.
  split.
  - intros r H1 H2. destruct (pu_scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs).
      destruct (pu_scratch_cases r Hs) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        first [contradiction | assumption].
    + assert (K : ~ (pu_scratch r \/ r = pu_SLOT c j)) by tauto. pu_track r K. pu_cc.
  - intros r H1 H2. assert (K : j < 16 /\ 48 <= r /\ r <> pu_SLOT c j) by (repeat split; assumption).
    pu_track r K. pu_cc.
Qed.

Theorem pu_phase_check_dead : forall P s p c,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.CHECK p c) ->
  16 <= hv s (pu_NC c) -> hv s pu_DEAD = 0 ->
  exists s', pu_hreach s s' /\ herr s' = true /\ hpc s' = pu_CKH_dead (pu_L_CKH c) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    hv s' pu_T2 = pu_pcode p /\ hv s' pu_T7 = hv s (pu_NC c) - 16 /\
    (forall r, r <> pu_T2 -> r <> pu_T7 -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s p c Hh Hf Hn Hd. pose proof Hh as (Hpc & He & Hp & Hz).
  pose proof (pu_at_head_zero P s Hh) as (Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  destruct (pu_phase_decode P s (E.CHECK p c) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (pu_handler (E.CHECK p c)) with pu_L_CHECK in P1.
  change (pu_arg_of (E.CHECK p c)) with (pu_pair (pu_ccode c) (pu_pcode p)) in A1.
  destruct (pu_hUCD_spec (pu_L_CKH E.CA) (pu_L_CKH E.CB) pu_L_CHECK U_P s1 c (pu_pcode p) pu_U_CKD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & X2 & Q2 & F2).
  assert (P2' : hpc s2 = pu_L_CKH c) by (rewrite P2; destruct c; reflexivity).
  destruct (pu_hCKH_disp c (pu_L_CKH c) U_P s2 (pu_U_CKH c) P2' ltac:(pu_herr_tac))
    as (s3 & R3 & Z43 & VF3 & F3 & L3 & G3).
  assert (KT : True) by exact I.
  assert (N2 : hv s2 (pu_NC c) = hv s (pu_NC c)) by (pu_track (pu_NC c) KT; pu_cc).
  rewrite N2 in G3. destruct (G3 Hn) as [P3 T73].
  assert (R : Hrun U_P s s3) by pu_chain.
  destruct (pu_hrun_same_sub _ _ _ _ _ R) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (D3 : hv s3 pu_DEAD = 0) by (pu_track pu_DEAD KT; pu_cc).
  pose proof (pu_hCHECK_fail_zero pu_DEAD (pu_CKH_dead (pu_L_CKH c)) U_P s3 (pu_U_CKH_dead c) P3
                ltac:(pu_herr_tac) D3) as Hs4.
  exists (hrun_prog 1 U_P s3). split.
  { apply (pu_hreach_trans s s3); [apply pu_Hrun_hreach, R | apply pu_hreach_one]. }
  rewrite Hs4. cbn [M.core_of M.mu M.cert M.pu_trap M.vals M.vers M.pc M.err M.facts M.chan].
  split; [reflexivity |]. split; [exact P3 |]. split; [exact Fa3 |]. split; [exact Ch3 |].
  split; [lia |]. split; [exact Ce3 |]. split; [pu_track pu_T2 KT; pu_cc |].
  split; [exact T73 |].
  split.
  - intros r H1 H2. destruct (pu_scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs).
      destruct (pu_scratch_cases r Hs) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        first [contradiction | pu_zero_goal KT].
    + assert (K : ~ pu_scratch r) by exact Hs. pu_track r K. pu_cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. pu_track r K. pu_cc.
Qed.

(* ================================================================= *)
(* COMMIT.                                                            *)
(* ================================================================= *)

(* From HEAD through the search of bank c. *)
Lemma pu_commit_search : forall P s p c,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.COMMIT p c) ->
  exists s3, Hrun U_P s s3 /\ herr s3 = false /\
    hv s3 pu_T2 = S (pu_pcode p) /\
    hv s3 pu_T0 = 0 /\ hv s3 pu_T1 = 0 /\ hv s3 pu_T3 = 0 /\ hv s3 pu_T4 = 0 /\ hv s3 pu_T5 = 0 /\
    hv s3 pu_T6 = 0 /\ hv s3 pu_T7 = 0 /\ hv s3 pu_T8 = 0 /\ hv s3 pu_T9 = 0 /\
    pu_vfr pu_scratch s s3 /\
    pu_hfr (fun r => pu_scratch r \/ r = pu_PROG \/ r = pu_GPC \/ pu_in_mp c r) s s3 /\
    (forall j, j < 16 -> hv s (pu_MP c j) = S (pu_pcode p) ->
       (forall j', j' < j -> hv s (pu_MP c j') <> S (pu_pcode p)) -> hpc s3 = pu_CMS_at (pu_L_CMH c) j) /\
    ((forall j, j < 16 -> hv s (pu_MP c j) <> S (pu_pcode p)) -> hpc s3 = pu_CMH_dead (pu_L_CMH c)).
Proof.
  intros P s p c Hh Hf. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_phase_decode P s (E.COMMIT p c) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (pu_handler (E.COMMIT p c)) with pu_L_COMMIT in P1.
  change (pu_arg_of (E.COMMIT p c)) with (pu_pair (pu_ccode c) (pu_pcode p)) in A1.
  destruct (pu_hUCD_spec (pu_L_CMH E.CA) (pu_L_CMH E.CB) pu_L_COMMIT U_P s1 c (pu_pcode p) pu_U_CMD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & X2 & Q2 & F2).
  assert (P2' : hpc s2 = pu_L_CMH c) by (rewrite P2; destruct c; reflexivity).
  destruct (pu_hCMH_search c (pu_L_CMH c) U_P s2 (pu_U_CMH c) P2' ltac:(pu_herr_tac))
    as (s3 & R3 & T23 & Z73 & Z83 & Z43 & VF3 & HF3 & M3 & N3).
  assert (KT : True) by exact I.
  assert (EM : forall j, hv s2 (pu_MP c j) = hv s (pu_MP c j)).
  { intro j. assert (K : True) by exact I. pu_track (pu_MP c j) K. pu_cc. }
  assert (R : Hrun U_P s s3) by pu_chain.
  exists s3. split; [exact R |]. split; [pu_herr_tac |].
  split; [pu_cc |].
  repeat (split; [pu_zero_goal KT |]).
  split; [pu_vfr_goal |]. split; [pu_hfr_goal |]. split.
  - intros j Hj Hm Hfst. apply M3; [exact Hj | rewrite EM, V2; exact Hm |].
    intros j' Hj'. rewrite EM, V2. apply Hfst, Hj'.
  - intros Hall. apply N3. intros j Hj. rewrite EM, V2. apply Hall, Hj.
Qed.

Theorem pu_phase_commit_pass : forall P s p c j,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.COMMIT p c) ->
  j < 16 -> hv s (pu_MP c j) = S (pu_pcode p) ->
  (forall j', j' < j -> hv s (pu_MP c j') <> S (pu_pcode p)) ->
  In (M.mkfact PSlot (pu_SLOT c j) (hver s (pu_SLOT c j))) (M.facts (M.core_of s)) ->
  exists s', pu_hreach s s' /\ pu_at_head P s' /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = Some (M.mkfact PSlot (pu_SLOT c j) (hver s (pu_SLOT c j))) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    (forall r, r <> pu_GPC -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s p c j Hh Hf Hj Hm Hfst Hin. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_commit_search P s p c Hh Hf)
    as (s3 & R3 & E3 & T23 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & VF3 & HF3 & M3 & N3).
  pose proof (M3 j Hj Hm Hfst) as P3.
  destruct (pu_hrun_same_sub _ _ _ _ _ R3) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (KJ : j < 16) by exact Hj.
  assert (WS : hver s3 (pu_SLOT c j) = hver s (pu_SLOT c j)) by (pu_track (pu_SLOT c j) KJ; pu_cc).
  destruct (pu_hCOMMIT_pass_fields (pu_SLOT c j) (pu_CMS_at (pu_L_CMH c) j) U_P s3 (pu_U_CMT c j Hj) P3 E3
              ltac:(rewrite WS, Fa3; exact Hin))
    as (Fa4 & Ch4 & P4 & E4 & Mu4 & Ce4 & All4).
  set (s4 := hrun_prog 1 U_P s3) in *.
  pose proof (pu_all_same_hframe s3 s4 All4) as F4.
  destruct (pu_hCMS_post (pu_SLOT c j) (pu_CMS_at (pu_L_CMH c) j) U_P s4 (pu_U_CMS c j Hj) P4 E4)
    as (s5 & R5 & P5 & Z5 & G5 & W5 & F5).
  destruct (pu_hrun_same_sub _ _ _ _ _ R5) as (Fa5 & Ch5 & Er5 & Mu5 & Ce5).
  assert (KT : True) by exact I.
  assert (AH : pu_at_head P s5).
  { unfold pu_at_head. split; [exact P5 |]. split; [pu_cc |].
    split; [pu_track pu_PROG KT; pu_cc |]. apply pu_scratch_all; pu_zero_goal KT. }
  exists s5. split.
  { apply (pu_hreach_trans s s3 s5); [apply pu_Hrun_hreach, R3 |].
    apply (pu_hreach_trans s3 s4 s5); [apply pu_hreach_one | apply pu_Hrun_hreach, R5]. }
  split; [exact AH |].
  split; [pu_track pu_GPC KT; pu_cc |].
  split; [pu_cc |].
  split; [rewrite Ch5, Ch4, WS; reflexivity |].
  split; [lia |]. split; [pu_cc |]. split.
  - intros r H1. destruct (pu_scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : ~ pu_scratch r /\ r <> pu_GPC) by (split; assumption). pu_track r K. pu_cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. pu_track r K. pu_cc.
Qed.

Theorem pu_phase_commit_stale : forall P s p c j,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.COMMIT p c) ->
  j < 16 -> hv s (pu_MP c j) = S (pu_pcode p) ->
  (forall j', j' < j -> hv s (pu_MP c j') <> S (pu_pcode p)) ->
  ~ In (M.mkfact PSlot (pu_SLOT c j) (hver s (pu_SLOT c j))) (M.facts (M.core_of s)) ->
  exists s', pu_hreach s s' /\ herr s' = true /\ hpc s' = pu_CMS_at (pu_L_CMH c) j /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    hv s' pu_T2 = S (pu_pcode p) /\
    (forall r, r <> pu_T2 -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s p c j Hh Hf Hj Hm Hfst Hin. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_commit_search P s p c Hh Hf)
    as (s3 & R3 & E3 & T23 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & VF3 & HF3 & M3 & N3).
  pose proof (M3 j Hj Hm Hfst) as P3.
  destruct (pu_hrun_same_sub _ _ _ _ _ R3) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (KJ : j < 16) by exact Hj.
  assert (WS : hver s3 (pu_SLOT c j) = hver s (pu_SLOT c j)) by (pu_track (pu_SLOT c j) KJ; pu_cc).
  pose proof (pu_hCOMMIT_fail (pu_SLOT c j) (pu_CMS_at (pu_L_CMH c) j) U_P s3 (pu_U_CMT c j Hj) P3 E3
                ltac:(rewrite WS, Fa3; exact Hin)) as Hs4.
  exists (hrun_prog 1 U_P s3). split.
  { apply (pu_hreach_trans s s3); [apply pu_Hrun_hreach, R3 | apply pu_hreach_one]. }
  rewrite Hs4. cbn [M.core_of M.mu M.cert M.pu_trap M.vals M.vers M.pc M.err M.facts M.chan].
  split; [reflexivity |]. split; [exact P3 |]. split; [exact Fa3 |]. split; [exact Ch3 |].
  split; [lia |]. split; [exact Ce3 |]. split; [exact T23 |].
  assert (KT : True) by exact I.
  split.
  - intros r H1. destruct (pu_scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs).
      destruct (pu_scratch_cases r Hs) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        first [contradiction | assumption].
    + pu_track r Hs. pu_cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. pu_track r K. pu_cc.
Qed.

Theorem pu_phase_commit_none : forall P s p c,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some (E.COMMIT p c) ->
  (forall j, j < 16 -> hv s (pu_MP c j) <> S (pu_pcode p)) ->
  ~ In (M.mkfact PSlot pu_DEAD (hver s pu_DEAD)) (M.facts (M.core_of s)) ->
  exists s', pu_hreach s s' /\ herr s' = true /\ hpc s' = pu_CMH_dead (pu_L_CMH c) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    hv s' pu_T2 = S (pu_pcode p) /\
    (forall r, r <> pu_T2 -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s p c Hh Hf Hnone Hin. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_commit_search P s p c Hh Hf)
    as (s3 & R3 & E3 & T23 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & VF3 & HF3 & M3 & N3).
  pose proof (N3 Hnone) as P3.
  destruct (pu_hrun_same_sub _ _ _ _ _ R3) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (KT : True) by exact I.
  assert (WD : hver s3 pu_DEAD = hver s pu_DEAD) by (pu_track pu_DEAD KT; pu_cc).
  pose proof (pu_hCOMMIT_fail pu_DEAD (pu_CMH_dead (pu_L_CMH c)) U_P s3 (pu_U_CMH_dead c) P3 E3
                ltac:(rewrite WD, Fa3; exact Hin)) as Hs4.
  exists (hrun_prog 1 U_P s3). split.
  { apply (pu_hreach_trans s s3); [apply pu_Hrun_hreach, R3 | apply pu_hreach_one]. }
  rewrite Hs4. cbn [M.core_of M.mu M.cert M.pu_trap M.vals M.vers M.pc M.err M.facts M.chan].
  split; [reflexivity |]. split; [exact P3 |]. split; [exact Fa3 |]. split; [exact Ch3 |].
  split; [lia |]. split; [exact Ce3 |]. split; [exact T23 |].
  split.
  - intros r H1. destruct (pu_scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs).
      destruct (pu_scratch_cases r Hs) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        first [contradiction | assumption].
    + pu_track r Hs. pu_cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. pu_track r K. pu_cc.
Qed.

(* ================================================================= *)
(* CERTIFY.                                                           *)
(* ================================================================= *)

Theorem pu_phase_certify_pass : forall P s f,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some E.CERTIFY -> M.chan (M.core_of s) = Some f ->
  exists s', pu_hreach s s' /\ pu_at_head P s' /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = true /\
    (forall r, r <> pu_GPC -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s f Hh Hf Hc. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_phase_decode P s E.CERTIFY Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (pu_handler E.CERTIFY) with pu_L_CERT in P1. change (pu_arg_of E.CERTIFY) with 0 in A1.
  destruct (pu_hrun_same_sub _ _ _ _ _ R1) as (Fa1 & Ch1 & Er1 & Mu1 & Ce1).
  pose proof (pu_hCERTIFY_pass pu_L_CERT U_P s1 f pu_U_CERT P1 E1 ltac:(rewrite Ch1; exact Hc)) as Hs2.
  set (s2 := hrun_prog 1 U_P s1) in *.
  assert (F2 : pu_hframe [] s1 s2) by (apply pu_all_same_hframe; intro d; rewrite Hs2; split; reflexivity).
  assert (P2 : hpc s2 = 1 + pu_L_CERT) by (rewrite Hs2; reflexivity).
  assert (Er2 : herr s2 = false) by (rewrite Hs2; exact E1).
  destruct (pu_hCERTH_post pu_L_CERT U_P s2 pu_U_CERTH P2 Er2) as (s3 & R3 & P3 & G3 & W3 & F3).
  destruct (pu_hrun_same_sub _ _ _ _ _ R3) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (KT : True) by exact I.
  assert (AH : pu_at_head P s3).
  { unfold pu_at_head. split; [exact P3 |]. split; [pu_cc |].
    split; [pu_track pu_PROG KT; pu_cc |]. apply pu_scratch_all; pu_zero_goal KT. }
  exists s3. split.
  { apply (pu_hreach_trans s s1 s3); [apply pu_Hrun_hreach, R1 |].
    apply (pu_hreach_trans s1 s2 s3); [apply pu_hreach_one | apply pu_Hrun_hreach, R3]. }
  split; [exact AH |]. split; [pu_track pu_GPC KT; pu_cc |].
  rewrite Hs2 in Fa3, Ch3, Mu3, Ce3. cbn [M.core_of M.mu M.cert M.pu_goto M.facts M.chan] in Fa3, Ch3, Mu3, Ce3.
  split; [pu_cc |]. split; [pu_cc |]. split; [lia |]. split; [exact Ce3 |]. split.
  - intros r H1. destruct (pu_scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : ~ pu_scratch r /\ r <> pu_GPC) by (split; assumption). pu_track r K. pu_cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. pu_track r K. pu_cc.
Qed.

Theorem pu_phase_certify_fail : forall P s,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some E.CERTIFY -> M.chan (M.core_of s) = None ->
  exists s', pu_hreach s s' /\ herr s' = true /\ hpc s' = pu_L_CERT /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    (forall r, hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s Hh Hf Hc. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_phase_decode P s E.CERTIFY Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (pu_handler E.CERTIFY) with pu_L_CERT in P1. change (pu_arg_of E.CERTIFY) with 0 in A1.
  destruct (pu_hrun_same_sub _ _ _ _ _ R1) as (Fa1 & Ch1 & Er1 & Mu1 & Ce1).
  pose proof (pu_hCERTIFY_fail pu_L_CERT U_P s1 pu_U_CERT P1 E1 ltac:(rewrite Ch1; exact Hc)) as Hs2.
  exists (hrun_prog 1 U_P s1). split.
  { apply (pu_hreach_trans s s1); [apply pu_Hrun_hreach, R1 | apply pu_hreach_one]. }
  rewrite Hs2. cbn [M.core_of M.mu M.cert M.pu_trap M.vals M.vers M.pc M.err M.facts M.chan].
  split; [reflexivity |]. split; [exact P1 |]. split; [exact Fa1 |]. split; [exact Ch1 |].
  split; [lia |]. split; [exact Ce1 |].
  split.
  - intros r. destruct (pu_scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs).
      destruct (pu_scratch_cases r Hs) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        assumption.
    + apply V1, Hs.
  - intros r H1. assert (K : 48 <= r) by exact H1. pu_track r K. pu_cc.
Qed.

(* ================================================================= *)
(* PAY.                                                               *)
(* ================================================================= *)

(* PAY, last part (after the paid step): INC GPC, back to HEAD. *)
Theorem pu_hPAYH_post : forall o Ph s,
  subcode (o, pu_hPAYH o) (1, Ph) -> hpc s = 1 + o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_L_HEAD /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    hv s' pu_T4 = hv s pu_T4 /\ pu_hframe [pu_GPC; pu_T4] s s'.
Proof.
  intros o Ph s Hsc Hpc He. unfold pu_hPAYH in Hsc.
  pu_sc_split Hsc X0 Hsc1. pu_sc_split Hsc1 S0 S1.
  destruct (pu_hINC_spec pu_GPC (1 + o) Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & W1 & F1).
  destruct (pu_hJMP_spec pu_T4 pu_L_HEAD (2 + o) Ph s1 S1 P1 ltac:(pu_herr_tac))
    as (s2 & R2 & P2 & V2 & F2).
  assert (KT : True) by exact I.
  exists s2. split; [pu_chain |]. split; [exact P2 |].
  split; [pu_track pu_GPC KT; congruence |]. split; [pu_track pu_T4 KT; congruence |].
  pu_frame_goal.
Qed.

Lemma pu_U_PAY : subcode (pu_L_PAY, pu_hPAY pu_L_PAY) (1, U_P).
Proof. pose proof pu_U_PAYH as H. unfold pu_hPAYH in H. pu_sc_split H H1 H2. exact H1. Qed.

(* A guest PAY: the host pays 1 at its own PAY and goes back to HEAD with
   GPC one higher; nothing else moves. *)
Theorem pu_phase_pay : forall P s,
  pu_at_head P s -> E.fetch P (hv s pu_GPC) = Some E.PAY ->
  exists s', pu_hreach s s' /\ pu_at_head P s' /\ hv s' pu_GPC = S (hv s pu_GPC) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    (forall r, r <> pu_GPC -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s Hh Hf. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (pu_phase_decode P s E.PAY Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (pu_handler E.PAY) with pu_L_PAY in P1. change (pu_arg_of E.PAY) with 0 in A1.
  destruct (pu_hrun_same_sub _ _ _ _ _ R1) as (Fa1 & Ch1 & Er1 & Mu1 & Ce1).
  pose proof (pu_hPAY_pass pu_L_PAY U_P s1 pu_U_PAY P1 E1) as Hs2.
  set (s2 := hrun_prog 1 U_P s1) in *.
  assert (F2 : pu_hframe [] s1 s2)
    by (apply pu_all_same_hframe; intro d; rewrite Hs2; split; reflexivity).
  assert (P2 : hpc s2 = 1 + pu_L_PAY) by (rewrite Hs2; reflexivity).
  assert (Er2 : herr s2 = false) by (rewrite Hs2; exact E1).
  destruct (pu_hPAYH_post pu_L_PAY U_P s2 pu_U_PAYH P2 Er2) as (s3 & R3 & P3 & G3 & W3 & F3).
  destruct (pu_hrun_same_sub _ _ _ _ _ R3) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (KT : True) by exact I.
  assert (AH : pu_at_head P s3).
  { unfold pu_at_head. split; [exact P3 |]. split; [pu_cc |].
    split; [pu_track pu_PROG KT; pu_cc |]. apply pu_scratch_all; pu_zero_goal KT. }
  exists s3. split.
  { apply (pu_hreach_trans s s1 s3); [apply pu_Hrun_hreach, R1 |].
    apply (pu_hreach_trans s1 s2 s3); [apply pu_hreach_one | apply pu_Hrun_hreach, R3]. }
  split; [exact AH |]. split; [pu_track pu_GPC KT; pu_cc |].
  rewrite Hs2 in Fa3, Ch3, Mu3, Ce3.
  cbn [M.core_of M.mu M.cert M.pu_goto M.facts M.chan] in Fa3, Ch3, Mu3, Ce3.
  split; [pu_cc |]. split; [pu_cc |]. split; [lia |]. split; [pu_cc |]. split.
  - intros r H1. destruct (pu_scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : ~ pu_scratch r /\ r <> pu_GPC) by (split; assumption). pu_track r K. pu_cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. pu_track r K. pu_cc.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions pu_hCD_spec.
Print Assumptions pu_hUCD_spec.
Print Assumptions pu_hBUMPS_spec.
Print Assumptions pu_hEQRS_spec.
Print Assumptions pu_hHALTB_spec.
Print Assumptions pu_hHEAD_spec.
Print Assumptions pu_hINCH_spec.
Print Assumptions pu_hDECH_zero.
Print Assumptions pu_hDECH_taken.
Print Assumptions pu_hCKH_disp.
Print Assumptions pu_hCKS_pre.
Print Assumptions pu_hCKS_post.
Print Assumptions pu_hCMH_search.
Print Assumptions pu_hCMS_post.
Print Assumptions pu_hCERTH_post.
Print Assumptions pu_phase_decode.
Print Assumptions pu_phase_stop.
Print Assumptions pu_phase_pc0.
Print Assumptions pu_phase_out.
Print Assumptions pu_phase_halt.
Print Assumptions pu_phase_inc.
Print Assumptions pu_phase_dec_taken.
Print Assumptions pu_phase_dec_zero.
Print Assumptions pu_check_to_slot.
Print Assumptions pu_phase_check_pass.
Print Assumptions pu_phase_check_fail.
Print Assumptions pu_phase_check_dead.
Print Assumptions pu_commit_search.
Print Assumptions pu_phase_commit_pass.
Print Assumptions pu_phase_commit_stale.
Print Assumptions pu_phase_commit_none.
Print Assumptions pu_phase_certify_pass.
Print Assumptions pu_phase_certify_fail.
Print Assumptions pu_hPAYH_post.
Print Assumptions pu_phase_pay.
