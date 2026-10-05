(** UniversalPhases.v: what the fixed host program U of UniversalLayout.v
    does for one guest instruction.

    A host state is "at HEAD" for the guest program P when its pc is
    L_HEAD (address 1), its trap latch is down, PROG holds prog_code P,
    and every scratch register T0 .. T9 holds 0. From such a state, with
    the guest pc in GPC, each phase lemma runs U to the next state at HEAD,
    to the halt, or to a trap, and states exactly:

      the new values of RA, RB, GPC, NC c, MP c k and SLOT c k that change;
      that every other register returns to the value it had at HEAD (so
      every scratch register is 0 again);
      the versions of the registers from 48 on (the slots, DEAD, and the
      unused registers above it): unchanged, except a bumped bank (each
      slot + 2) or the slot loaded by a CHECK (strictly larger);
      the fact table, the channel, the ledger mu, the flag and the trap
      latch.

    The host ledger goes up by exactly 1 in the CHECK, COMMIT and CERTIFY
    phases (one paid instruction each, pass or fail) and by 0 in every
    other phase.

      phase_stop          guest pc 0, guest pc past the end, or HALT: the
                          host halts at L_STOP, every register value as at
                          HEAD (corollaries phase_pc0, phase_out,
                          phase_halt)
      phase_decode        fetch and decode: the handler of the opcode is
                          reached with T2 holding the operand
      phase_inc           INC c
      phase_dec_taken     DEC c j on a positive counter
      phase_dec_zero      DEC c j on a zero counter
      phase_check_pass    CHECK p c, slot NC c < 16, the property holds and
                          the fact table has room
      phase_check_fail    CHECK p c, slot NC c < 16, the property fails or
                          the fact table is full: the host traps
      phase_check_dead    CHECK p c with NC c >= 16: CHECK PSlot DEAD traps
      phase_commit_pass   COMMIT p c, the first slot of bank c whose mirror
                          is pcode p + 1 carries a fact at its current
                          version: the channel holds that fact
      phase_commit_stale  the same slot without that fact: the host traps
      phase_commit_none   no mirror matches: COMMIT PSlot DEAD traps
      phase_certify_pass  CERTIFY with a full channel: the flag rises
      phase_certify_fail  CERTIFY with an empty channel: the host traps

    Dependencies: the Coq standard library, the vendored coq-undecidability
    library, EarnedCore.v, EarnedGeneric.v, EarnedMulti.v,
    UniversalCodes.v, UniversalBridge.v, UniversalBlocks.v and
    UniversalLayout.v. No axioms, no Admitted.                            *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import Vec.pos Vec.vec Code.subcode Code.sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.Util Require Import MMA_pairing.
Require Import Minimal.UniversalCodes Minimal.UniversalBridge Minimal.UniversalBlocks
  Minimal.UniversalLayout.

Local Notation hinstr := (@M.instr hprop).
Local Notation hstate := (@M.state hprop).
Local Notation hrun_prog := (M.run_prog hprop_eqb heval).
Local Notation hexec := (M.exec hprop_eqb heval).
Local Notation Hrun := (hrun hprop_eqb heval).

(* ================================================================= *)
(* Frames given by a predicate.                                       *)
(* ================================================================= *)

(* Every register outside Q keeps its value. *)
Definition vfr (Q : nat -> Prop) (s s' : hstate) : Prop :=
  forall r, ~ Q r -> hv s' r = hv s r.

(* Every register outside Q keeps its value and its version. *)
Definition hfr (Q : nat -> Prop) (s s' : hstate) : Prop :=
  forall r, ~ Q r -> hv s' r = hv s r /\ hver s' r = hver s r.

Lemma hframe_keep_vfr : forall rs (Q : nat -> Prop) (s s' : hstate),
  hframe rs s s' -> (forall r, In r rs -> Q r \/ hv s' r = hv s r) -> vfr Q s s'.
Proof.
  intros rs Q s s' F H r Hq. destruct (in_dec Nat.eq_dec r rs) as [Hin | Hn].
  - destruct (H r Hin) as [Hq' | E]; [contradiction | exact E].
  - apply F, Hn.
Qed.

Lemma hframe_hfr : forall rs (Q : nat -> Prop) (s s' : hstate),
  hframe rs s s' -> (forall r, In r rs -> Q r) -> hfr Q s s'.
Proof. intros rs Q s s' F H r Hq. apply F. intro Hin. apply Hq, H, Hin. Qed.

Lemma all_same_hframe : forall s s' : hstate,
  (forall d, hv s' d = hv s d /\ hver s' d = hver s d) -> hframe [] s s'.
Proof. intros s s' H r _. apply H. Qed.

(* Markers: register r is not framed between s and s' by a given
   hypothesis (values / versions). *)
Definition skip_v (r : nat) (s s' : hstate) : Prop := True.
Definition skip_w (r : nat) (s s' : hstate) : Prop := True.

(* ================================================================= *)
(* Tactics.                                                           *)
(* ================================================================= *)

Ltac unfold_regs :=
  unfold RA, RB, PROG, GPC, T0, T1, T2, T3, T4, T5, T6, T7, T8, T9,
    greg, NC, MP, SLOT, DEAD, scratch, in_mp, in_slots in *.

Ltac ctr_bounds :=
  repeat match goal with
  | c : E.ctr |- _ =>
      lazymatch goal with
      | _ : ccode c < 2 |- _ => fail
      | _ => pose proof (ccode_lt c)
      end
  end.

(* Register arithmetic: membership, disequality, ranges. *)
Ltac nreg := simpl in *; unfold_regs; cbn [ccode] in *; ctr_bounds; lia.

(* Keep only the bound hypotheses of the form _ < 16. *)
Ltac keep_bounds :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with
      | Prop => lazymatch T with
                | _ < 16 => fail
                | _ => clear H
                end
      end
  end.

Ltac rneq := keep_bounds; nreg.

(* For register r, record the value and version equations of every frame
   hypothesis (hframe, hfr, vfr) that does not cover r. K names one
   hypothesis that carries what is known about r. *)
Ltac track r K :=
  repeat match goal with
  | F : hframe ?rs ?a ?b |- _ =>
      lazymatch goal with
      | _ : hver b r = hver a r |- _ => fail
      | _ : skip_w r a b |- _ => fail
      | _ =>
          first
            [ let N := fresh "N" in
              assert (N : ~ In r rs) by (clear - K; nreg);
              pose proof (hframe_v rs a b r F N);
              pose proof (hframe_ver rs a b r F N); clear N
            | assert (skip_w r a b) by exact I ]
      end
  | F : hfr ?Q ?a ?b |- _ =>
      lazymatch goal with
      | _ : hver b r = hver a r |- _ => fail
      | _ : skip_w r a b |- _ => fail
      | _ =>
          first
            [ let N := fresh "N" in
              assert (N : ~ Q r) by (clear - K; nreg);
              pose proof (proj1 (F r N)); pose proof (proj2 (F r N)); clear N
            | assert (skip_w r a b) by exact I ]
      end
  | F : vfr ?Q ?a ?b |- _ =>
      lazymatch goal with
      | _ : hv b r = hv a r |- _ => fail
      | _ : skip_v r a b |- _ => fail
      | _ =>
          first
            [ let N := fresh "N" in
              assert (N : ~ Q r) by (clear - K; nreg);
              pose proof (F r N); clear N
            | assert (skip_v r a b) by exact I ]
      end
  end.

(* A vfr goal from an hframe hypothesis F: each register of F's list is
   either in Q or has an equation hv s' x = hv s x in the context. *)
Ltac vfr_from F :=
  apply (hframe_keep_vfr _ _ _ _ F);
  let r := fresh "r" in
  let Hin := fresh "Hin" in
  intros r Hin; simpl in Hin;
  repeat (destruct Hin as [<- | Hin]); try contradiction;
  first [ right; assumption
        | right; symmetry; assumption
        | left; cbv beta; repeat (first [left; reflexivity | right]); reflexivity ].

(* An hfr goal from an hframe hypothesis F whose list lies inside Q. *)
Ltac hfr_from F :=
  apply (hframe_hfr _ _ _ _ F);
  let r := fresh "r" in
  let Hin := fresh "Hin" in
  intros r Hin; simpl in Hin;
  repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbv beta; repeat (first [left; reflexivity | right]); try reflexivity.

(* A full frame goal hframe rs s s' along a chain. *)
Ltac frame_goal :=
  let r := fresh "r" in
  let Hr := fresh "Hr" in
  intros r Hr; track r Hr; split; congruence.

(* A vfr / hfr goal along a chain, by tracking a generic register. *)
Ltac vfr_goal :=
  let r := fresh "r" in
  let Hr := fresh "Hr" in
  intros r Hr; track r Hr; congruence.
Ltac hfr_goal :=
  let r := fresh "r" in
  let Hr := fresh "Hr" in
  intros r Hr; track r Hr; split; congruence.

(* ================================================================= *)
(* Distinct registers.                                                *)
(* ================================================================= *)

Lemma nd_fetch : NoDup [PROG; GPC; T0; T1; T2; T3; T4].
Proof. unfold_regs. repeat constructor; simpl; intuition discriminate. Qed.

Lemma nd_eqr : forall c k, NoDup [MP c k; T2; T7; T8; T4].
Proof.
  intros c k. constructor; [simpl; unfold_regs; lia |].
  unfold_regs. repeat constructor; simpl; intuition discriminate.
Qed.

Lemma cpick_nth : forall c (ta tb : nat), nth (ccode c) [ta; tb] 0 = match c with E.CA => ta | E.CB => tb end.
Proof. intros []; reflexivity. Qed.

Lemma nth_map_seq : forall (f : nat -> nat) n k, k < n -> nth k (map f (seq 0 n)) 0 = f k.
Proof.
  intros f n k Hk. rewrite (nth_indep _ 0 (f 0)) by (rewrite map_length, seq_length; exact Hk).
  rewrite map_nth, seq_nth by exact Hk. reflexivity.
Qed.

(* ================================================================= *)
(* Reaching a state by running U.                                     *)
(* ================================================================= *)

Definition hreach (s s' : hstate) : Prop := exists n, hrun_prog n U s = s'.

Lemma Hrun_hreach : forall s s', Hrun U s s' -> hreach s s'.
Proof. intros s s' [m [E _]]. exists m. exact E. Qed.

Lemma hreach_trans : forall s1 s2 s3, hreach s1 s2 -> hreach s2 s3 -> hreach s1 s3.
Proof.
  intros s1 s2 s3 [n E1] [m E2]. exists (n + m).
  rewrite (M.multi_run_prog_add hprop_eqb heval), E1. exact E2.
Qed.

Lemma hreach_one : forall s, hreach s (hrun_prog 1 U s).
Proof. intro s. exists 1. reflexivity. Qed.

(* ================================================================= *)
(* Composite blocks, for any host program they are placed in.         *)
(* ================================================================= *)

Definition cpick (c : E.ctr) (ta tb : nat) : nat := match c with E.CA => ta | E.CB => tb end.

(* Bank choice on T2 = ccode c. *)
Lemma hCD_spec : forall ta tb o Ph s c,
  subcode (o, hCD ta tb o) (1, Ph) -> hpc s = o -> herr s = false -> hv s T2 = ccode c ->
  exists s', Hrun Ph s s' /\ hpc s' = cpick c ta tb /\ hv s' T2 = 0 /\ hv s' T4 = hv s T4 /\
    hframe [T2; T4] s s'.
Proof.
  intros ta tb o Ph s c Hsc Hpc He Hc. unfold hCD in Hsc. sc_split Hsc S0 S1.
  destruct (hDISP_spec T2 T4 [ta; tb] o Ph s ltac:(rneq) S0 Hpc He) as (s' & R & F & V4 & L & G).
  rewrite Hc in L. destruct (L ltac:(simpl; pose proof (ccode_lt c); lia)) as [P2 V2].
  exists s'. split; [exact R |]. split; [rewrite P2, cpick_nth; reflexivity |].
  split; [exact V2 |]. split; [exact V4 | exact F].
Qed.

(* Operand split and bank choice. *)
Lemma hUCD_spec : forall ta tb o Ph s c x,
  subcode (o, hUCD ta tb o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s T2 = pair (ccode c) x ->
  exists s', Hrun Ph s s' /\ hpc s' = cpick c ta tb /\ hv s' T2 = x /\ hv s' T3 = 0 /\
    hv s' T6 = 0 /\ hv s' T4 = hv s T4 /\ hframe [T3; T2; T6; T4] s s'.
Proof.
  intros ta tb o Ph s c x Hsc Hpc He Hx. unfold hUCD in Hsc.
  sc_split Hsc S0 Hsc1. sc_split Hsc1 S1 S2.
  destruct (hUNPACK_spec T3 T2 T6 (ccode c) x o Ph s ltac:(rneq) ltac:(rneq) ltac:(rneq) Hx S0
              Hpc He) as (s1 & R1 & P1 & V1x & V1y & V1a & F1).
  destruct (hDISP_spec T6 T4 [ta; tb] (UNPACK_len + o) Ph s1 ltac:(rneq) S1 P1 ltac:(herr_tac))
    as (s2 & R2 & F2 & V4 & L & G).
  rewrite V1y in L. destruct (L ltac:(simpl; pose proof (ccode_lt c); lia)) as [P2 V2].
  assert (KT : True) by exact I.
  exists s2. split; [chain |]. split; [rewrite P2, cpick_nth; reflexivity |].
  track T2 KT. track T3 KT. track T4 KT.
  split; [congruence |]. split; [congruence |]. split; [exact V2 |]. split; [congruence |].
  frame_goal.
Qed.

(* BUMP of the slots k0 .. k0 + n - 1 of bank c. *)
Lemma hBUMPS_gen : forall c n k0 o Ph s, k0 + n <= 16 ->
  subcode (o, fam (fun k o' => hBUMP (SLOT c k) (MP c k) o') BUMP_len k0 n o) (1, Ph) ->
  hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = n * BUMP_len + o /\
    (forall k, k0 <= k < k0 + n ->
       hv s' (SLOT c k) = hv s (SLOT c k) /\ hver s' (SLOT c k) = 2 + hver s (SLOT c k) /\
       hv s' (MP c k) = 0) /\
    (forall r, (forall k, k0 <= k < k0 + n -> r <> SLOT c k /\ r <> MP c k) ->
       hv s' r = hv s r /\ hver s' r = hver s r) /\
    (forall r, (forall k, k0 <= k < k0 + n -> r <> MP c k) -> hv s' r = hv s r).
Proof.
  intros c n. induction n as [| n IH]; intros k0 o Ph s Hb Hsc Hpc He.
  - exists s. split; [apply hrun_refl |]. split; [exact Hpc |].
    split; [intros k Hk; lia |]. split; intros r _; [split |]; reflexivity.
  - cbn [fam] in Hsc. sc_split Hsc S0 S1.
    assert (Hne : SLOT c k0 <> MP c k0) by (unfold SLOT, MP; lia).
    destruct (hBUMP_spec (SLOT c k0) (MP c k0) o Ph s Hne S0 Hpc He)
      as (s1 & R1 & P1 & V1 & W1 & M1 & F1).
    destruct (IH (S k0) (BUMP_len + o) Ph s1 ltac:(lia) S1 P1 ltac:(herr_tac))
      as (s2 & R2 & P2 & A2 & B2 & C2).
    exists s2. split; [chain |]. split; [rewrite P2; simpl; lia |]. split; [| split].
    + intros k Hk. destruct (Nat.eq_dec k k0) as [-> | Hkn].
      * assert (X : forall q, S k0 <= q < S k0 + n -> SLOT c k0 <> SLOT c q /\ SLOT c k0 <> MP c q)
          by (intros q Hq; unfold SLOT, MP; lia).
        assert (Y : forall q, S k0 <= q < S k0 + n -> MP c k0 <> MP c q)
          by (intros q Hq; unfold MP; lia).
        destruct (B2 _ X) as [E1 E2]. rewrite E1, E2, (C2 _ Y).
        split; [exact V1 | split; [exact W1 | exact M1]].
      * destruct (A2 k ltac:(lia)) as (E1 & E2 & E3).
        assert (N1 : ~ In (SLOT c k) [SLOT c k0; MP c k0]) by (simpl; unfold SLOT, MP; lia).
        rewrite E1, E2, E3, (hframe_v _ _ _ _ F1 N1), (hframe_ver _ _ _ _ F1 N1).
        repeat split.
    + intros r Hr.
      assert (N1 : ~ In r [SLOT c k0; MP c k0]).
      { destruct (Hr k0 ltac:(lia)) as [Ha Hb']. simpl. intuition congruence. }
      destruct (B2 r ltac:(intros q Hq; apply Hr; lia)) as [E1 E2]. rewrite E1, E2.
      exact (F1 r N1).
    + intros r Hr. rewrite (C2 r ltac:(intros q Hq; apply Hr; lia)).
      destruct (Nat.eq_dec r (SLOT c k0)) as [-> | Hs].
      * exact V1.
      * apply (hframe_v _ _ _ _ F1). simpl. pose proof (Hr k0 ltac:(lia)). intuition congruence.
Qed.

Theorem hBUMPS_spec : forall c o Ph s,
  subcode (o, hBUMPS c o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = BUMPS_len + o /\
    (forall q, q < 16 -> hv s' (SLOT c q) = hv s (SLOT c q) /\
       hver s' (SLOT c q) = 2 + hver s (SLOT c q) /\ hv s' (MP c q) = 0) /\
    hfr (fun r => in_mp c r \/ in_slots c r) s s' /\ vfr (in_mp c) s s'.
Proof.
  intros c o Ph s Hsc Hpc He. unfold hBUMPS in Hsc.
  destruct (hBUMPS_gen c 16 0 o Ph s ltac:(lia) Hsc Hpc He) as (s' & R & P & A & B & C).
  exists s'. split; [exact R |]. split; [exact P |].
  split; [intros q Hq; apply A; lia |]. split.
  - intros r Hr. apply B. intros k Hk. unfold in_mp, in_slots, SLOT, MP in *. lia.
  - intros r Hr. apply C. intros k Hk. unfold in_mp, MP in *. lia.
Qed.

(* The 16-way comparison of the mirrors MP c k with T2. *)
Lemma hEQRS_gen : forall c tgt n k0 o Ph s, k0 + n <= 16 ->
  subcode (o, fam (fun k o' => hEQR (MP c k) T2 T7 T8 T4 (tgt k) o') EQR_len k0 n o) (1, Ph) ->
  hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\
    ((hv s T7 = 0 /\ hv s T8 = 0 /\ hv s T4 = 0) \/ 0 < n ->
       hv s' T7 = 0 /\ hv s' T8 = 0 /\ hv s' T4 = 0) /\
    vfr (fun r => r = T7 \/ r = T8 \/ r = T4) s s' /\
    hfr (fun r => r = T7 \/ r = T8 \/ r = T4 \/ r = T2 \/ in_mp c r) s s' /\
    (forall j, k0 <= j < k0 + n -> hv s (MP c j) = hv s T2 ->
       (forall j', k0 <= j' < j -> hv s (MP c j') <> hv s T2) -> hpc s' = tgt j) /\
    ((forall j, k0 <= j < k0 + n -> hv s (MP c j) <> hv s T2) -> hpc s' = n * EQR_len + o).
Proof.
  intros c tgt n. induction n as [| n IH]; intros k0 o Ph s Hb Hsc Hpc He.
  - exists s. split; [apply hrun_refl |]. split; [intros [H | H]; [exact H | lia] |].
    split; [intros r _; reflexivity |]. split; [intros r _; auto |].
    split; [intros j Hj; lia | intros _; exact Hpc].
  - cbn [fam] in Hsc. sc_split Hsc S0 S1.
    destruct (hEQR_spec (MP c k0) T2 T7 T8 T4 (tgt k0) o Ph s (nd_eqr c k0) S0 Hpc He)
      as (s1 & R1 & F1 & Vx & Vy & V7 & V8 & V4 & P1).
    assert (VF1 : vfr (fun r => r = T7 \/ r = T8 \/ r = T4) s s1) by vfr_from F1.
    assert (HF1 : hfr (fun r => r = T7 \/ r = T8 \/ r = T4 \/ r = T2 \/ in_mp c r) s s1).
    { apply (hframe_hfr _ _ _ _ F1). intros r Hin. simpl in Hin.
      destruct Hin as [<- | [<- | [<- | [<- | [<- | []]]]]]; simpl; unfold_regs; lia. }
    destruct (Nat.eqb_spec (hv s (MP c k0)) (hv s T2)) as [Heq | Hneq].
    + exists s1. split; [exact R1 |]. split; [intros _; repeat split; assumption |].
      split; [exact VF1 |]. split; [exact HF1 |]. split.
      * intros j Hj Hm Hfirst. destruct (Nat.eq_dec j k0) as [-> | Hjn]; [exact P1 |].
        exfalso. apply (Hfirst k0); [lia | exact Heq].
      * intros Hall. exfalso. apply (Hall k0); [lia | exact Heq].
    + destruct (IH (S k0) (EQR_len + o) Ph s1 ltac:(lia) S1 P1 ltac:(herr_tac))
        as (s2 & R2 & Z2 & VF2 & HF2 & M2 & N2).
      assert (EM : forall j, hv s1 (MP c j) = hv s (MP c j)).
      { intro j. apply VF1. unfold T7, T8, T4, MP. lia. }
      assert (ET : hv s1 T2 = hv s T2) by exact Vy.
      exists s2. split; [chain |]. split; [intros _; apply Z2; left; repeat split; assumption |].
      split; [intros r Hr; rewrite (VF2 r Hr); apply VF1, Hr |].
      split.
      * intros r Hr. destruct (HF2 r Hr) as [A B]. destruct (HF1 r Hr) as [C D].
        split; congruence.
      * split.
        -- intros j Hj Hm Hfirst. destruct (Nat.eq_dec j k0) as [-> | Hjn]; [contradiction |].
           apply M2; [lia | congruence |]. intros j' Hj'. rewrite EM, ET. apply Hfirst. lia.
        -- intros Hall. rewrite N2; [simpl; lia |]. intros j Hj. rewrite EM, ET. apply Hall. lia.
Qed.

Theorem hEQRS_spec : forall c tgt o Ph s,
  subcode (o, hEQRS c tgt o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hv s' T7 = 0 /\ hv s' T8 = 0 /\ hv s' T4 = 0 /\
    vfr (fun r => r = T7 \/ r = T8 \/ r = T4) s s' /\
    hfr (fun r => r = T7 \/ r = T8 \/ r = T4 \/ r = T2 \/ in_mp c r) s s' /\
    (forall j, j < 16 -> hv s (MP c j) = hv s T2 ->
       (forall j', j' < j -> hv s (MP c j') <> hv s T2) -> hpc s' = tgt j) /\
    ((forall j, j < 16 -> hv s (MP c j) <> hv s T2) -> hpc s' = 16 * EQR_len + o).
Proof.
  intros c tgt o Ph s Hsc Hpc He. unfold hEQRS in Hsc.
  destruct (hEQRS_gen c tgt 16 0 o Ph s ltac:(lia) Hsc Hpc He)
    as (s' & R & Z & VF & HF & M & N).
  destruct (Z ltac:(right; lia)) as (Z7 & Z8 & Z4).
  exists s'. do 6 (split; [assumption |]). split.
  - intros j Hj Hm Hf. apply M; [lia | exact Hm |]. intros j' Hj'. apply Hf. lia.
  - intros Hall. apply N. intros j Hj. apply Hall. lia.
Qed.

(* The halt block: every scratch register to 0, then the HALT. *)
Lemma hHALTB_spec : forall o Ph s,
  subcode (o, hHALTB o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = 10 + o /\
    hv s' T0 = 0 /\ hv s' T1 = 0 /\ hv s' T2 = 0 /\ hv s' T3 = 0 /\ hv s' T4 = 0 /\
    hv s' T5 = 0 /\ hv s' T6 = 0 /\ hv s' T7 = 0 /\ hv s' T8 = 0 /\ hv s' T9 = 0 /\
    hfr scratch s s'.
Proof.
  intros o Ph s Hsc Hpc He. unfold hHALTB in Hsc.
  sc_split Hsc S0 Hsc1. sc_split Hsc1 S1 Hsc2. sc_split Hsc2 S2 Hsc3. sc_split Hsc3 S3 Hsc4.
  sc_split Hsc4 S4 Hsc5. sc_split Hsc5 S5 Hsc6. sc_split Hsc6 S6 Hsc7. sc_split Hsc7 S7 Hsc8.
  sc_split Hsc8 S8 Hsc9. sc_split Hsc9 S9 S10.
  destruct (hZERO_spec T0 o Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & F1).
  destruct (hZERO_spec T1 (1 + o) Ph s1 S1 P1 ltac:(herr_tac)) as (s2 & R2 & P2 & V2 & F2).
  destruct (hZERO_spec T2 (2 + o) Ph s2 S2 P2 ltac:(herr_tac)) as (s3 & R3 & P3 & V3 & F3).
  destruct (hZERO_spec T3 (3 + o) Ph s3 S3 P3 ltac:(herr_tac)) as (s4 & R4 & P4 & V4 & F4).
  destruct (hZERO_spec T4 (4 + o) Ph s4 S4 P4 ltac:(herr_tac)) as (s5 & R5 & P5 & V5 & F5).
  destruct (hZERO_spec T5 (5 + o) Ph s5 S5 P5 ltac:(herr_tac)) as (s6 & R6 & P6 & V6 & F6).
  destruct (hZERO_spec T6 (6 + o) Ph s6 S6 P6 ltac:(herr_tac)) as (s7 & R7 & P7 & V7 & F7).
  destruct (hZERO_spec T7 (7 + o) Ph s7 S7 P7 ltac:(herr_tac)) as (s8 & R8 & P8 & V8 & F8).
  destruct (hZERO_spec T8 (8 + o) Ph s8 S8 P8 ltac:(herr_tac)) as (s9 & R9 & P9 & V9 & F9).
  destruct (hZERO_spec T9 (9 + o) Ph s9 S9 P9 ltac:(herr_tac))
    as (s10 & R10 & P10 & V10 & F10).
  assert (KT : True) by exact I.
  exists s10. split; [chain |]. split; [rewrite P10; reflexivity |].
  do 10 (split; [match goal with |- hv _ ?X = 0 => track X KT; congruence end |]).
  hfr_goal.
Qed.

(* HEAD: fetch, decode and dispatch, or leave for the halt. *)
Theorem hHEAD_spec : forall (P : list E.instr) o Ph s,
  subcode (o, hHEAD o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s PROG = prog_code P -> (forall r, scratch r -> hv s r = 0) ->
  exists s1, Hrun Ph s s1 /\ vfr scratch s s1 /\
    hfr (fun r => scratch r \/ r = PROG \/ r = GPC) s s1 /\
    match E.fetch P (hv s GPC) with
    | Some i => hpc s1 = handler i /\ hv s1 T2 = arg_of i /\
        hv s1 T0 = 0 /\ hv s1 T1 = 0 /\ hv s1 T3 = 0 /\ hv s1 T4 = 0 /\ hv s1 T5 = 0 /\
        hv s1 T6 = 0 /\ hv s1 T7 = 0 /\ hv s1 T8 = 0 /\ hv s1 T9 = 0
    | None => hpc s1 = L_HALT
    end.
Proof.
  intros P o Ph s Hsc Hpc He Hp Hz. unfold hHEAD in Hsc.
  sc_split Hsc S0 Hsc1. sc_split Hsc1 S1 Hsc2. sc_split Hsc2 S2 Hsc3. sc_split Hsc3 S3 S4.
  assert (KT : True) by exact I.
  destruct (hv s GPC) as [| k] eqn:Hg.
  - destruct (hFETCH_guest_pc0 P PROG GPC T0 T1 T2 T3 T4 L_HALT L_HALT o Ph s nd_fetch S0 Hpc He
                Hp Hg) as (s1 & R1 & F1 & Vp & Vg & Vt & P1).
    assert (Ep : hv s1 PROG = hv s PROG) by congruence.
    assert (Eg : hv s1 GPC = hv s GPC) by congruence.
    exists s1. split; [exact R1 |]. split.
    + apply (hframe_keep_vfr _ _ _ _ F1). intros r Hin. simpl in Hin.
      destruct Hin as [<- | [<- | Hin]]; [right; exact Ep | right; exact Eg |].
      left. unfold scratch. repeat (destruct Hin as [<- | Hin]); try contradiction; unfold_regs; lia.
    + split; [| exact P1].
      apply (hframe_hfr _ _ _ _ F1). intros r Hin. simpl in Hin.
      repeat (destruct Hin as [<- | Hin]); try contradiction; simpl; unfold_regs; lia.
  - destruct (hFETCH_guest P PROG GPC T0 T1 T2 T3 T4 L_HALT L_HALT o Ph s k nd_fetch S0 Hpc He
                Hp Hg) as (s1 & R1 & F1 & Vp & Vg & Vt & G).
    assert (Ep : hv s1 PROG = hv s PROG) by congruence.
    assert (Eg : hv s1 GPC = hv s GPC) by congruence.
    cbn [E.fetch]. destruct (nth_error P k) as [i |] eqn:Hn.
    + destruct G as (P1 & H1 & K1 & A1 & W1).
      destruct (hZERO_spec T0 (FETCH_len + o) Ph s1 S1 P1 ltac:(herr_tac))
        as (s2 & R2 & P2 & V2 & F2).
      assert (H2 : hv s2 T2 = pair (op_of i) (arg_of i)).
      { rewrite <- icode_op_arg. track T2 KT. congruence. }
      destruct (hUNPACK_spec T3 T2 T5 (op_of i) (arg_of i) (1 + FETCH_len + o) Ph s2
                  ltac:(rneq) ltac:(rneq) ltac:(rneq) H2 S2 P2 ltac:(herr_tac))
        as (s3 & R3 & P3 & V3x & V3y & V3a & F3).
      destruct (hDISP_spec T5 T4 handlers (1 + FETCH_len + UNPACK_len + o) Ph s3 ltac:(rneq) S3
                  P3 ltac:(herr_tac)) as (s4 & R4 & F4 & V4 & L4 & G4).
      rewrite V3y in L4. destruct (L4 (op_of_lt i)) as [P4 V5].
      exists s4. split; [chain |].
      split; [| split; [| split; [exact P4 |]]].
      * intros r Hr. destruct (Nat.eq_dec r PROG) as [-> | Hrp].
        { track PROG KT. congruence. }
        destruct (Nat.eq_dec r GPC) as [-> | Hrg].
        { track GPC KT. congruence. }
        assert (K : ~ scratch r /\ r <> PROG /\ r <> GPC) by (repeat split; assumption).
        track r K. congruence.
      * intros r Hr. track r Hr. split; congruence.
      * pose proof (Hz T6 ltac:(rneq)). pose proof (Hz T7 ltac:(rneq)).
        pose proof (Hz T8 ltac:(rneq)). pose proof (Hz T9 ltac:(rneq)).
        repeat split; match goal with |- hv _ ?X = _ => track X KT; congruence end.
    + exists s1. split; [exact R1 |]. split.
      * apply (hframe_keep_vfr _ _ _ _ F1). intros r Hin. simpl in Hin.
        destruct Hin as [<- | [<- | Hin]]; [right; exact Ep | right; exact Eg |].
        left. unfold scratch. repeat (destruct Hin as [<- | Hin]); try contradiction; unfold_regs; lia.
      * split; [| exact (proj1 G)].
        apply (hframe_hfr _ _ _ _ F1). intros r Hin. simpl in Hin.
        repeat (destruct Hin as [<- | Hin]); try contradiction; simpl; unfold_regs; lia.
Qed.


(* INC c: INC (greg c), bump bank c, INC GPC, back to HEAD. *)
Theorem hINCH_spec : forall c o Ph s,
  subcode (o, hINCH c o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = L_HEAD /\
    hv s' (greg c) = S (hv s (greg c)) /\ hv s' GPC = S (hv s GPC) /\
    (forall q, q < 16 -> hv s' (SLOT c q) = hv s (SLOT c q) /\
       hver s' (SLOT c q) = 2 + hver s (SLOT c q) /\ hv s' (MP c q) = 0) /\
    vfr (fun r => r = greg c \/ r = GPC \/ in_mp c r) s s' /\
    hfr (fun r => r = greg c \/ r = GPC \/ r = T4 \/ in_mp c r \/ in_slots c r) s s'.
Proof.
  intros c o Ph s Hsc Hpc He. unfold hINCH in Hsc.
  sc_split Hsc S0 Hsc1. sc_split Hsc1 S1 Hsc2. sc_split Hsc2 S2 S3.
  destruct (hINC_spec (greg c) o Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & W1 & F1).
  destruct (hBUMPS_spec c (1 + o) Ph s1 S1 P1 ltac:(herr_tac)) as (s2 & R2 & P2 & B2 & HF2 & VF2).
  destruct (hINC_spec GPC (1 + BUMPS_len + o) Ph s2 S2 P2 ltac:(herr_tac))
    as (s3 & R3 & P3 & V3 & W3 & F3).
  destruct (hJMP_spec T4 L_HEAD (2 + BUMPS_len + o) Ph s3 S3 P3 ltac:(herr_tac))
    as (s4 & R4 & P4 & V4 & F4).
  assert (KT : True) by exact I.
  exists s4. split; [chain |]. split; [exact P4 |].
  split; [track (greg c) KT; congruence |].
  split; [track GPC KT; congruence |].
  split.
  - intros q Hq. destruct (B2 q Hq) as (E1 & E2 & E3).
    assert (K : q < 16) by exact Hq.
    track (SLOT c q) K. track (MP c q) K.
    split; [congruence |]. split; [lia | congruence].
  - split.
    + intros r Hr. destruct (Nat.eq_dec r T4) as [-> | H4]; [track T4 KT; congruence |].
      assert (K : ~ (r = greg c \/ r = GPC \/ in_mp c r) /\ r <> T4) by (split; assumption).
      track r K. congruence.
    + hfr_goal.
Qed.

(* DEC c j on a zero counter: INC GPC, clear T2, back to HEAD. *)
Theorem hDECH_zero : forall c o Ph s,
  subcode (o, hDECH c o) (1, Ph) -> hpc s = o -> herr s = false -> hv s (greg c) = 0 ->
  exists s', Hrun Ph s s' /\ hpc s' = L_HEAD /\ hv s' GPC = S (hv s GPC) /\ hv s' T2 = 0 /\
    vfr (fun r => r = GPC \/ r = T2) s s' /\
    hfr (fun r => r = greg c \/ r = GPC \/ r = T2 \/ r = T4) s s'.
Proof.
  intros c o Ph s Hsc Hpc He Hz. unfold hDECH in Hsc.
  sc_split Hsc S0 Hsc1. sc_split Hsc1 S1 Hsc2. sc_split Hsc2 S2 Hsc3. sc_split Hsc3 S3 Hsc4.
  destruct (hDEC_spec (greg c) (DECH_taken o) o Ph s S0 Hpc He) as (s1 & R1 & F1 & D1).
  rewrite Hz in D1. destruct D1 as (P1 & V1 & W1).
  destruct (hINC_spec GPC (1 + o) Ph s1 S1 P1 ltac:(herr_tac)) as (s2 & R2 & P2 & V2 & W2 & F2).
  destruct (hZERO_spec T2 (2 + o) Ph s2 S2 P2 ltac:(herr_tac)) as (s3 & R3 & P3 & V3 & F3).
  destruct (hJMP_spec T4 L_HEAD (3 + o) Ph s3 S3 P3 ltac:(herr_tac)) as (s4 & R4 & P4 & V4 & F4).
  assert (KT : True) by exact I.
  exists s4. split; [chain |]. split; [exact P4 |].
  split; [track GPC KT; congruence |]. split; [track T2 KT; congruence |]. split.
  - intros r Hr. destruct (Nat.eq_dec r T4) as [-> | H4]; [track T4 KT; congruence |].
    destruct (Nat.eq_dec r (greg c)) as [-> | Hg]; [track (greg c) KT; congruence |].
    assert (K : ~ (r = GPC \/ r = T2) /\ r <> T4 /\ r <> greg c) by (repeat split; assumption).
    track r K. congruence.
  - hfr_goal.
Qed.

(* DEC c j on a positive counter: decrement, bump bank c, GPC := T2. *)
Theorem hDECH_taken : forall c o Ph s u,
  subcode (o, hDECH c o) (1, Ph) -> hpc s = o -> herr s = false -> hv s (greg c) = S u ->
  exists s', Hrun Ph s s' /\ hpc s' = L_HEAD /\ hv s' (greg c) = u /\ hv s' GPC = hv s T2 /\
    hv s' T2 = 0 /\
    (forall q, q < 16 -> hv s' (SLOT c q) = hv s (SLOT c q) /\
       hver s' (SLOT c q) = 2 + hver s (SLOT c q) /\ hv s' (MP c q) = 0) /\
    vfr (fun r => r = greg c \/ r = GPC \/ r = T2 \/ in_mp c r) s s' /\
    hfr (fun r => r = greg c \/ r = GPC \/ r = T2 \/ r = T4 \/ in_mp c r \/ in_slots c r) s s'.
Proof.
  intros c o Ph s u Hsc Hpc He Hu. unfold hDECH in Hsc.
  sc_split Hsc S0 Hsc1. sc_split Hsc1 X1 Hsc2. sc_split Hsc2 X2 Hsc3. sc_split Hsc3 X3 Hsc4.
  sc_split Hsc4 S1 Hsc5. sc_split Hsc5 S2 Hsc6. sc_split Hsc6 S3 S4.
  destruct (hDEC_spec (greg c) (DECH_taken o) o Ph s S0 Hpc He) as (s1 & R1 & F1 & D1).
  rewrite Hu in D1. destruct D1 as (P1 & V1 & W1).
  destruct (hBUMPS_spec c (DECH_taken o) Ph s1 S1 P1 ltac:(herr_tac))
    as (s2 & R2 & P2 & B2 & HF2 & VF2).
  destruct (hZERO_spec GPC (BUMPS_len + DECH_taken o) Ph s2 S2 P2 ltac:(herr_tac))
    as (s3 & R3 & P3 & V3 & F3).
  destruct (hMOVE_spec T2 GPC (1 + BUMPS_len + DECH_taken o) Ph s3 ltac:(rneq) S3 P3
              ltac:(herr_tac)) as (s4 & R4 & P4 & V4y & V4x & F4).
  destruct (hJMP_spec T4 L_HEAD (1 + MOVE_len + BUMPS_len + DECH_taken o) Ph s4 S4 P4
              ltac:(herr_tac)) as (s5 & R5 & P5 & V5 & F5).
  assert (KT : True) by exact I.
  exists s5. split; [chain |]. split; [exact P5 |].
  split; [track (greg c) KT; congruence |].
  split; [track GPC KT; track T2 KT; lia |].
  split; [track T2 KT; congruence |].
  split.
  - intros q Hq. destruct (B2 q Hq) as (E1 & E2 & E3).
    assert (K : q < 16) by exact Hq.
    track (SLOT c q) K. track (MP c q) K.
    split; [congruence |]. split; [lia | congruence].
  - split.
    + intros r Hr. destruct (Nat.eq_dec r T4) as [-> | H4]; [track T4 KT; congruence |].
      assert (K : ~ (r = greg c \/ r = GPC \/ r = T2 \/ in_mp c r) /\ r <> T4)
        by (split; assumption).
      track r K. congruence.
    + hfr_goal.
Qed.

(* CHECK, first part: copy NC c and branch 17 ways on it. *)
Theorem hCKH_disp : forall c o Ph s,
  subcode (o, hCKH c o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hv s' T4 = 0 /\
    vfr (fun r => r = T7 \/ r = T4) s s' /\ hframe [NC c; T7; T4] s s' /\
    (hv s (NC c) < 16 -> hpc s' = CKS_at o (hv s (NC c)) /\ hv s' T7 = 0) /\
    (16 <= hv s (NC c) -> hpc s' = CKH_dead o /\ hv s' T7 = hv s (NC c) - 16).
Proof.
  intros c o Ph s Hsc Hpc He. unfold hCKH in Hsc. sc_split Hsc S0 Hsc1. sc_split Hsc1 S1 Hsc2.
  destruct (hCOPY_spec (NC c) T7 T4 o Ph s ltac:(rneq) ltac:(rneq) ltac:(rneq) S0 Hpc He)
    as (s1 & R1 & P1 & V1x & V1y & V1t & F1).
  destruct (hDISP_spec T7 T4 (map (CKS_at o) (seq 0 16)) (COPY_len + o) Ph s1 ltac:(rneq) S1 P1
              ltac:(herr_tac)) as (s2 & R2 & F2 & V4 & L & G).
  rewrite map_length, seq_length, V1y in L, G.
  assert (KT : True) by exact I.
  exists s2. split; [chain |]. split; [congruence |].
  split.
  - intros r Hr. destruct (Nat.eq_dec r (NC c)) as [-> | Hn]; [track (NC c) KT; congruence |].
    assert (K : ~ (r = T7 \/ r = T4) /\ r <> NC c) by (split; assumption).
    track r K. congruence.
  - split; [frame_goal |]. split.
    + intros Hl. destruct (L Hl) as [P2 Z2]. split; [| exact Z2].
      rewrite P2. apply nth_map_seq. exact Hl.
    + intros Hl. destruct (G Hl) as [P2 Z2]. split; [| exact Z2].
      rewrite P2. unfold CKH_dead. lia.
Qed.

(* CHECK on slot k, first part: load (code, value) into the slot. *)
Theorem hCKS_pre : forall c k o Ph s,
  subcode (o, hCKS c k o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = CKS_chk o /\
    hv s' (SLOT c k) = hv s (SLOT c k) + pair (hv s T2) (hv s (greg c)) /\
    hver s (SLOT c k) < hver s' (SLOT c k) /\
    hv s' T2 = hv s T2 /\ hv s' T3 = 0 /\ hv s' T4 = 0 /\ hv s' T8 = 0 /\ hv s' T9 = 0 /\
    vfr (fun r => r = SLOT c k \/ r = T3 \/ r = T4 \/ r = T8 \/ r = T9) s s' /\
    hframe [greg c; T8; T4; T2; T9; T3; SLOT c k] s s'.
Proof.
  intros c k o Ph s Hsc Hpc He. unfold hCKS in Hsc.
  sc_split Hsc S0 Hsc1. sc_split Hsc1 S1 Hsc2. sc_split Hsc2 S2 Hsc3. sc_split Hsc3 S3 Hsc4.
  destruct (hCOPY_spec (greg c) T8 T4 o Ph s ltac:(rneq) ltac:(rneq) ltac:(rneq) S0 Hpc He)
    as (s1 & R1 & P1 & V1x & V1y & V1t & F1).
  destruct (hCOPY_spec T2 T9 T4 (COPY_len + o) Ph s1 ltac:(rneq) ltac:(rneq) ltac:(rneq) S1 P1
              ltac:(herr_tac)) as (s2 & R2 & P2 & V2x & V2y & V2t & F2).
  destruct (hPACK_spec T3 T8 T9 (2 * COPY_len + o) Ph s2 ltac:(rneq) ltac:(rneq) ltac:(rneq) S2 P2
              ltac:(herr_tac)) as (s3 & R3 & P3 & V3x & V3y & V3a & F3).
  destruct (hMOVE_spec T8 (SLOT c k) (2 * COPY_len + PACK_len + o) Ph s3 ltac:(rneq) S3 P3
              ltac:(herr_tac)) as (s4 & R4 & P4 & V4y & V4x & F4).
  assert (KT : True) by exact I.
  assert (ES : hv s4 (SLOT c k) = hv s (SLOT c k) + pair (hv s T2) (hv s (greg c))).
  { track (SLOT c k) KT. track T8 KT. track T9 KT. track T2 KT. track (greg c) KT. congruence. }
  assert (R : Hrun Ph s s4) by chain.
  exists s4. split; [exact R |]. split; [exact P4 |]. split; [exact ES |].
  split.
  { apply (hrun_val_moved hprop_eqb heval Ph s s4 R). rewrite ES.
    pose proof (pair_pos (hv s T2) (hv s (greg c))). lia. }
  split; [track T2 KT; congruence |]. split; [track T3 KT; congruence |].
  split; [track T4 KT; congruence |]. split; [track T8 KT; congruence |].
  split; [track T9 KT; congruence |]. split.
  - intros r Hr. destruct (Nat.eq_dec r T2) as [-> | H2]; [track T2 KT; congruence |].
    destruct (Nat.eq_dec r (greg c)) as [-> | Hg]; [track (greg c) KT; congruence |].
    assert (K : ~ (r = SLOT c k \/ r = T3 \/ r = T4 \/ r = T8 \/ r = T9) /\ r <> T2 /\
                r <> greg c) by (repeat split; assumption).
    track r K. congruence.
  - frame_goal.
Qed.

(* CHECK on slot k, last part (after a passing CHECK): set the mirror to
   code + 1, INC NC c, INC GPC, back to HEAD. *)
Theorem hCKS_post : forall c k o Ph s,
  subcode (o, hCKS c k o) (1, Ph) -> hpc s = 1 + CKS_chk o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = L_HEAD /\
    hv s' (MP c k) = S (hv s T2) /\ hv s' T2 = 0 /\ hv s' (NC c) = S (hv s (NC c)) /\
    hv s' GPC = S (hv s GPC) /\ hv s' T4 = hv s T4 /\
    vfr (fun r => r = MP c k \/ r = T2 \/ r = NC c \/ r = GPC) s s' /\
    hframe [MP c k; T2; NC c; GPC; T4] s s'.
Proof.
  intros c k o Ph s Hsc Hpc He. unfold hCKS in Hsc.
  sc_split Hsc X0 Hsc1. sc_split Hsc1 X1 Hsc2. sc_split Hsc2 X2 Hsc3. sc_split Hsc3 X3 Hsc4.
  sc_split Hsc4 X4 Hsc5. sc_split Hsc5 S0 Hsc6. sc_split Hsc6 S1 Hsc7. sc_split Hsc7 S2 Hsc8.
  sc_split Hsc8 S3 Hsc9. sc_split Hsc9 S4 S5.
  destruct (hZERO_spec (MP c k) (1 + CKS_chk o) Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & F1).
  destruct (hMOVE_spec T2 (MP c k) (2 + CKS_chk o) Ph s1 ltac:(rneq) S1 P1 ltac:(herr_tac))
    as (s2 & R2 & P2 & V2y & V2x & F2).
  destruct (hINC_spec (MP c k) (2 + MOVE_len + CKS_chk o) Ph s2 S2 P2 ltac:(herr_tac))
    as (s3 & R3 & P3 & V3 & W3 & F3).
  destruct (hINC_spec (NC c) (3 + MOVE_len + CKS_chk o) Ph s3 S3 P3 ltac:(herr_tac))
    as (s4 & R4 & P4 & V4 & W4 & F4).
  destruct (hINC_spec GPC (4 + MOVE_len + CKS_chk o) Ph s4 S4 P4 ltac:(herr_tac))
    as (s5 & R5 & P5 & V5 & W5 & F5).
  destruct (hJMP_spec T4 L_HEAD (5 + MOVE_len + CKS_chk o) Ph s5 S5 P5 ltac:(herr_tac))
    as (s6 & R6 & P6 & V6 & F6).
  assert (KT : True) by exact I.
  exists s6. split; [chain |]. split; [exact P6 |].
  split; [track (MP c k) KT; track T2 KT; lia |].
  split; [track T2 KT; congruence |].
  split; [track (NC c) KT; congruence |].
  split; [track GPC KT; congruence |].
  split; [track T4 KT; congruence |].
  split.
  - intros r Hr. destruct (Nat.eq_dec r T4) as [-> | H4]; [track T4 KT; congruence |].
    assert (K : ~ (r = MP c k \/ r = T2 \/ r = NC c \/ r = GPC) /\ r <> T4)
      by (split; assumption).
    track r K. congruence.
  - frame_goal.
Qed.

(* COMMIT, first part: T2 := code + 1, then compare it with the mirrors
   of bank c in order. *)
Theorem hCMH_search : forall c o Ph s,
  subcode (o, hCMH c o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hv s' T2 = S (hv s T2) /\ hv s' T7 = 0 /\ hv s' T8 = 0 /\
    hv s' T4 = 0 /\
    vfr (fun r => r = T2 \/ r = T7 \/ r = T8 \/ r = T4) s s' /\
    hfr (fun r => r = T7 \/ r = T8 \/ r = T4 \/ r = T2 \/ in_mp c r) s s' /\
    (forall j, j < 16 -> hv s (MP c j) = S (hv s T2) ->
       (forall j', j' < j -> hv s (MP c j') <> S (hv s T2)) -> hpc s' = CMS_at o j) /\
    ((forall j, j < 16 -> hv s (MP c j) <> S (hv s T2)) -> hpc s' = CMH_dead o).
Proof.
  intros c o Ph s Hsc Hpc He. unfold hCMH in Hsc. sc_split Hsc S0 Hsc1. sc_split Hsc1 S1 Hsc2.
  destruct (hINC_spec T2 o Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & W1 & F1).
  destruct (hEQRS_spec c (CMS_at o) (1 + o) Ph s1 S1 P1 ltac:(herr_tac))
    as (s2 & R2 & Z7 & Z8 & Z4 & VF2 & HF2 & M2 & N2).
  assert (EM : forall j, hv s1 (MP c j) = hv s (MP c j)).
  { intro j. apply (hframe_v _ _ _ _ F1). simpl. unfold_regs. lia. }
  assert (KT : True) by exact I.
  exists s2. split; [chain |]. split; [track T2 KT; congruence |].
  split; [exact Z7 |]. split; [exact Z8 |]. split; [exact Z4 |].
  split; [vfr_goal |]. split; [hfr_goal |]. split.
  - intros j Hj Hm Hf. apply M2; [exact Hj | rewrite EM, V1; exact Hm |].
    intros j' Hj'. rewrite EM, V1. apply Hf, Hj'.
  - intros Hall. rewrite N2; [unfold CMH_dead; lia |].
    intros j Hj. rewrite EM, V1. apply Hall, Hj.
Qed.

(* COMMIT, last part (after a passing COMMIT): clear T2, INC GPC, back
   to HEAD. *)
Theorem hCMS_post : forall sl o Ph s,
  subcode (o, hCMS sl o) (1, Ph) -> hpc s = 1 + o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = L_HEAD /\ hv s' T2 = 0 /\ hv s' GPC = S (hv s GPC) /\
    hv s' T4 = hv s T4 /\ hframe [T2; GPC; T4] s s'.
Proof.
  intros sl o Ph s Hsc Hpc He. unfold hCMS in Hsc.
  sc_split Hsc X0 Hsc1. sc_split Hsc1 S0 Hsc2. sc_split Hsc2 S1 S2.
  destruct (hZERO_spec T2 (1 + o) Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & F1).
  destruct (hINC_spec GPC (2 + o) Ph s1 S1 P1 ltac:(herr_tac)) as (s2 & R2 & P2 & V2 & W2 & F2).
  destruct (hJMP_spec T4 L_HEAD (3 + o) Ph s2 S2 P2 ltac:(herr_tac)) as (s3 & R3 & P3 & V3 & F3).
  assert (KT : True) by exact I.
  exists s3. split; [chain |]. split; [exact P3 |].
  split; [track T2 KT; congruence |]. split; [track GPC KT; congruence |].
  split; [track T4 KT; congruence |]. frame_goal.
Qed.

(* CERTIFY, last part (after a passing CERTIFY): INC GPC, back to HEAD. *)
Theorem hCERTH_post : forall o Ph s,
  subcode (o, hCERTH o) (1, Ph) -> hpc s = 1 + o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = L_HEAD /\ hv s' GPC = S (hv s GPC) /\
    hv s' T4 = hv s T4 /\ hframe [GPC; T4] s s'.
Proof.
  intros o Ph s Hsc Hpc He. unfold hCERTH in Hsc.
  sc_split Hsc X0 Hsc1. sc_split Hsc1 S0 S1.
  destruct (hINC_spec GPC (1 + o) Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & W1 & F1).
  destruct (hJMP_spec T4 L_HEAD (2 + o) Ph s1 S1 P1 ltac:(herr_tac)) as (s2 & R2 & P2 & V2 & F2).
  assert (KT : True) by exact I.
  exists s2. split; [chain |]. split; [exact P2 |].
  split; [track GPC KT; congruence |]. split; [track T4 KT; congruence |]. frame_goal.
Qed.

(* Close an equation about a state reached along a chain by rewriting
   each value, version, latch, table, channel, ledger and flag of a later
   state with the equation that relates it to an earlier state (all such
   equations point from later states to earlier ones), then reflexivity,
   an assumption, or linear arithmetic. *)
Ltac cc :=
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
(* The record moves of U.                                             *)
(* ================================================================= *)

Lemma U_CHK : forall c k, k < 16 ->
  subcode (CKS_chk (CKS_at (L_CKH c) k), hCHECK (SLOT c k) (CKS_chk (CKS_at (L_CKH c) k))) (1, U).
Proof.
  intros c k Hk. pose proof (U_CKS c k Hk) as H. unfold hCKS in H.
  sc_split H H1 H2. sc_split H2 H3 H4. sc_split H4 H5 H6. sc_split H6 H7 H8.
  sc_split H8 H9 H10. exact H9.
Qed.

Lemma U_CMT : forall c k, k < 16 ->
  subcode (CMS_at (L_CMH c) k, hCOMMIT (SLOT c k) (CMS_at (L_CMH c) k)) (1, U).
Proof.
  intros c k Hk. pose proof (U_CMS c k Hk) as H. unfold hCMS in H. sc_split H H1 H2. exact H1.
Qed.

Lemma U_CERT : subcode (L_CERT, hCERTIFY L_CERT) (1, U).
Proof. pose proof U_CERTH as H. unfold hCERTH in H. sc_split H H1 H2. exact H1. Qed.

Lemma halted_at_stop : forall s : hstate,
  herr s = false -> hpc s = L_STOP -> M.halted U (M.core_of s).
Proof.
  intros s He Hp. unfold M.halted, M.next_instr. rewrite He, Hp, U_fetch_stop. reflexivity.
Qed.

(* ================================================================= *)
(* States at HEAD.                                                    *)
(* ================================================================= *)

Definition at_head (P : list E.instr) (s : hstate) : Prop :=
  hpc s = L_HEAD /\ herr s = false /\ hv s PROG = prog_code P /\
  (forall r, scratch r -> hv s r = 0).

Lemma scratch_dec : forall r, scratch r \/ ~ scratch r.
Proof. intro r. unfold scratch. lia. Qed.

Lemma scratch_all : forall s : hstate,
  hv s T0 = 0 -> hv s T1 = 0 -> hv s T2 = 0 -> hv s T3 = 0 -> hv s T4 = 0 ->
  hv s T5 = 0 -> hv s T6 = 0 -> hv s T7 = 0 -> hv s T8 = 0 -> hv s T9 = 0 ->
  forall r, scratch r -> hv s r = 0.
Proof.
  intros s H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 r Hr.
  destruct (scratch_cases r Hr) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
    assumption.
Qed.

Lemma at_head_zero : forall P s, at_head P s ->
  hv s T0 = 0 /\ hv s T1 = 0 /\ hv s T2 = 0 /\ hv s T3 = 0 /\ hv s T4 = 0 /\
  hv s T5 = 0 /\ hv s T6 = 0 /\ hv s T7 = 0 /\ hv s T8 = 0 /\ hv s T9 = 0.
Proof.
  intros P s (_ & _ & _ & Hz).
  repeat split; apply Hz; unfold scratch; unfold_regs; lia.
Qed.

Ltac zero_goal K := match goal with |- hv _ ?X = 0 => track X K; cc end.

(* Close an at_head goal: pc, latch, program code, and the ten scratch
   registers, each tracked along the chain. *)
Ltac head_goal Hpc K :=
  unfold at_head; split; [exact Hpc |]; split; [herr_tac |];
  split; [track PROG K; cc |];
  apply scratch_all; zero_goal K.

(* ================================================================= *)
(* Fetch and decode.                                                  *)
(* ================================================================= *)

Theorem phase_decode : forall P s i, at_head P s -> E.fetch P (hv s GPC) = Some i ->
  exists s1, Hrun U s s1 /\ herr s1 = false /\ hpc s1 = handler i /\ hv s1 T2 = arg_of i /\
    hv s1 T0 = 0 /\ hv s1 T1 = 0 /\ hv s1 T3 = 0 /\ hv s1 T4 = 0 /\ hv s1 T5 = 0 /\
    hv s1 T6 = 0 /\ hv s1 T7 = 0 /\ hv s1 T8 = 0 /\ hv s1 T9 = 0 /\
    vfr scratch s s1 /\ hfr (fun r => scratch r \/ r = PROG \/ r = GPC) s s1.
Proof.
  intros P s i (Hpc & He & Hp & Hz) Hf.
  destruct (hHEAD_spec P L_HEAD U s U_HEAD Hpc He Hp Hz) as (s1 & R1 & V1 & F1 & G).
  rewrite Hf in G. destruct G as (P1 & A1 & Z0 & Z1 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  exists s1. split; [exact R1 |]. split; [herr_tac |].
  repeat (split; [assumption |]). exact F1.
Qed.

(* ================================================================= *)
(* Guest pc 0, guest pc past the end, guest HALT: the host halts.     *)
(* ================================================================= *)

Theorem phase_stop : forall P s, at_head P s ->
  E.fetch P (hv s GPC) = None \/ E.fetch P (hv s GPC) = Some E.HALT ->
  exists s', hreach s s' /\ hpc s' = L_STOP /\ herr s' = false /\ M.halted U (M.core_of s') /\
    (forall r, hv s' r = hv s r) /\
    (forall r, ~ scratch r -> r <> PROG -> r <> GPC -> hver s' r = hver s r) /\
    same_sub s s'.
Proof.
  intros P s Hh Hf. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (hHEAD_spec P L_HEAD U s U_HEAD Hpc He Hp Hz) as (s1 & R1 & V1 & F1 & G).
  assert (P1 : hpc s1 = L_HALT).
  { destruct Hf as [Hf | Hf]; rewrite Hf in G; [exact G | exact (proj1 G)]. }
  destruct (hHALTB_spec L_HALT U s1 U_HALTB P1 ltac:(herr_tac))
    as (s2 & R2 & P2 & Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & F2).
  assert (R : Hrun U s s2) by chain.
  assert (P2' : hpc s2 = L_STOP) by (rewrite P2; reflexivity).
  exists s2. split; [apply Hrun_hreach, R |]. split; [exact P2' |].
  split; [herr_tac |]. split; [apply halted_at_stop; [herr_tac | exact P2'] |].
  split; [| split].
  - intros r. destruct (scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs). apply (scratch_all s2); assumption.
    + track r Hs. cc.
  - intros r H1 H2 H3. assert (K : ~ scratch r /\ r <> PROG /\ r <> GPC) by (repeat split; assumption).
    track r K. cc.
  - apply (hrun_same_sub _ _ _ _ _ R).
Qed.

Corollary phase_pc0 : forall P s, at_head P s -> hv s GPC = 0 ->
  exists s', hreach s s' /\ hpc s' = L_STOP /\ herr s' = false /\ M.halted U (M.core_of s') /\
    (forall r, hv s' r = hv s r) /\
    (forall r, ~ scratch r -> r <> PROG -> r <> GPC -> hver s' r = hver s r) /\
    same_sub s s'.
Proof. intros P s Hh Hg. apply (phase_stop P s Hh). left. rewrite Hg. reflexivity. Qed.

Corollary phase_out : forall P s k, at_head P s -> hv s GPC = S k -> nth_error P k = None ->
  exists s', hreach s s' /\ hpc s' = L_STOP /\ herr s' = false /\ M.halted U (M.core_of s') /\
    (forall r, hv s' r = hv s r) /\
    (forall r, ~ scratch r -> r <> PROG -> r <> GPC -> hver s' r = hver s r) /\
    same_sub s s'.
Proof. intros P s k Hh Hg Hn. apply (phase_stop P s Hh). left. rewrite Hg. exact Hn. Qed.

Corollary phase_halt : forall P s, at_head P s -> E.fetch P (hv s GPC) = Some E.HALT ->
  exists s', hreach s s' /\ hpc s' = L_STOP /\ herr s' = false /\ M.halted U (M.core_of s') /\
    (forall r, hv s' r = hv s r) /\
    (forall r, ~ scratch r -> r <> PROG -> r <> GPC -> hver s' r = hver s r) /\
    same_sub s s'.
Proof. intros P s Hh Hf. apply (phase_stop P s Hh). right. exact Hf. Qed.

(* ================================================================= *)
(* INC and DEC.                                                       *)
(* ================================================================= *)

Theorem phase_inc : forall P s c,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.INC c) ->
  exists s', hreach s s' /\ at_head P s' /\
    hv s' (greg c) = S (hv s (greg c)) /\ hv s' GPC = S (hv s GPC) /\
    (forall q, q < 16 -> hv s' (MP c q) = 0 /\ hv s' (SLOT c q) = hv s (SLOT c q) /\
       hver s' (SLOT c q) = 2 + hver s (SLOT c q)) /\
    (forall r, r <> greg c -> r <> GPC -> ~ in_mp c r -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> ~ in_slots c r -> hver s' r = hver s r) /\
    same_sub s s'.
Proof.
  intros P s c Hh Hf. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (phase_decode P s (E.INC c) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (handler (E.INC c)) with L_INC in P1. change (arg_of (E.INC c)) with (ccode c) in A1.
  destruct (hCD_spec (L_INCH E.CA) (L_INCH E.CB) L_INC U s1 c U_INCD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & F2).
  assert (P2' : hpc s2 = L_INCH c) by (rewrite P2; destruct c; reflexivity).
  destruct (hINCH_spec c (L_INCH c) U s2 (U_INCH c) P2' ltac:(herr_tac))
    as (s3 & R3 & P3 & G3 & C3 & B3 & VF3 & HF3).
  assert (R : Hrun U s s3) by chain.
  assert (KT : True) by exact I.
  assert (AH : at_head P s3) by head_goal P3 KT.
  exists s3. split; [apply Hrun_hreach, R |]. split; [exact AH |].
  split; [track (greg c) KT; cc |].
  split; [track GPC KT; cc |].
  split; [| split; [| split]].
  - intros q Hq. destruct (B3 q Hq) as (E1' & E2' & E3').
    assert (K : q < 16) by exact Hq. track (SLOT c q) K.
    split; [exact E3' |]. split; [cc | lia].
  - intros r H1 H2 H3. destruct (scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : ~ scratch r /\ r <> greg c /\ r <> GPC /\ ~ in_mp c r)
        by (repeat split; assumption).
      track r K. cc.
  - intros r H1 H2. assert (K : 48 <= r /\ ~ in_slots c r) by (split; assumption).
    track r K. cc.
  - apply (hrun_same_sub _ _ _ _ _ R).
Qed.

Theorem phase_dec_taken : forall P s c j u,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.DEC c j) -> hv s (greg c) = S u ->
  exists s', hreach s s' /\ at_head P s' /\ hv s' (greg c) = u /\ hv s' GPC = j /\
    (forall q, q < 16 -> hv s' (MP c q) = 0 /\ hv s' (SLOT c q) = hv s (SLOT c q) /\
       hver s' (SLOT c q) = 2 + hver s (SLOT c q)) /\
    (forall r, r <> greg c -> r <> GPC -> ~ in_mp c r -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> ~ in_slots c r -> hver s' r = hver s r) /\
    same_sub s s'.
Proof.
  intros P s c j u Hh Hf Hu. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (phase_decode P s (E.DEC c j) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (handler (E.DEC c j)) with L_DEC in P1.
  change (arg_of (E.DEC c j)) with (pair (ccode c) j) in A1.
  destruct (hUCD_spec (L_DECH E.CA) (L_DECH E.CB) L_DEC U s1 c j U_DECD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & X2 & Q2 & F2).
  assert (P2' : hpc s2 = L_DECH c) by (rewrite P2; destruct c; reflexivity).
  assert (KT : True) by exact I.
  assert (G2 : hv s2 (greg c) = S u) by (track (greg c) KT; cc).
  destruct (hDECH_taken c (L_DECH c) U s2 u (U_DECH c) P2' ltac:(herr_tac) G2)
    as (s3 & R3 & P3 & G3 & C3 & Z3 & B3 & VF3 & HF3).
  assert (R : Hrun U s s3) by chain.
  assert (AH : at_head P s3) by head_goal P3 KT.
  exists s3. split; [apply Hrun_hreach, R |]. split; [exact AH |].
  split; [exact G3 |]. split; [cc |].
  split; [| split; [| split]].
  - intros q Hq. destruct (B3 q Hq) as (E1' & E2' & E3').
    assert (K : q < 16) by exact Hq. track (SLOT c q) K.
    split; [exact E3' |]. split; [cc | lia].
  - intros r H1 H2 H3. destruct (scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : ~ scratch r /\ r <> greg c /\ r <> GPC /\ ~ in_mp c r)
        by (repeat split; assumption).
      track r K. cc.
  - intros r H1 H2. assert (K : 48 <= r /\ ~ in_slots c r) by (split; assumption).
    track r K. cc.
  - apply (hrun_same_sub _ _ _ _ _ R).
Qed.

Theorem phase_dec_zero : forall P s c j,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.DEC c j) -> hv s (greg c) = 0 ->
  exists s', hreach s s' /\ at_head P s' /\ hv s' GPC = S (hv s GPC) /\
    (forall r, r <> GPC -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r) /\
    same_sub s s'.
Proof.
  intros P s c j Hh Hf Hu. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (phase_decode P s (E.DEC c j) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (handler (E.DEC c j)) with L_DEC in P1.
  change (arg_of (E.DEC c j)) with (pair (ccode c) j) in A1.
  destruct (hUCD_spec (L_DECH E.CA) (L_DECH E.CB) L_DEC U s1 c j U_DECD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & X2 & Q2 & F2).
  assert (P2' : hpc s2 = L_DECH c) by (rewrite P2; destruct c; reflexivity).
  assert (KT : True) by exact I.
  assert (G2 : hv s2 (greg c) = 0) by (track (greg c) KT; cc).
  destruct (hDECH_zero c (L_DECH c) U s2 (U_DECH c) P2' ltac:(herr_tac) G2)
    as (s3 & R3 & P3 & C3 & Z3 & VF3 & HF3).
  assert (R : Hrun U s s3) by chain.
  assert (AH : at_head P s3) by head_goal P3 KT.
  exists s3. split; [apply Hrun_hreach, R |]. split; [exact AH |].
  split; [track GPC KT; cc |].
  split; [| split].
  - intros r H1. destruct (scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + destruct (Nat.eq_dec r (greg c)) as [-> | Hg].
      * track (greg c) KT. cc.
      * assert (K : ~ scratch r /\ r <> GPC /\ r <> greg c) by (repeat split; assumption).
        track r K. cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. track r K. cc.
  - apply (hrun_same_sub _ _ _ _ _ R).
Qed.

(* ================================================================= *)
(* CHECK.                                                             *)
(* ================================================================= *)

(* From HEAD to the CHECK of slot j = NC c < 16, with the slot loaded. *)
Lemma check_to_slot : forall P s p c j,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.CHECK p c) ->
  hv s (NC c) = j -> j < 16 ->
  exists s4, Hrun U s s4 /\ herr s4 = false /\ hpc s4 = CKS_chk (CKS_at (L_CKH c) j) /\
    hv s4 (SLOT c j) = hv s (SLOT c j) + pair (pcode p) (hv s (greg c)) /\
    hver s (SLOT c j) < hver s4 (SLOT c j) /\
    hv s4 T2 = pcode p /\
    hv s4 T0 = 0 /\ hv s4 T1 = 0 /\ hv s4 T3 = 0 /\ hv s4 T4 = 0 /\ hv s4 T5 = 0 /\
    hv s4 T6 = 0 /\ hv s4 T7 = 0 /\ hv s4 T8 = 0 /\ hv s4 T9 = 0 /\
    vfr (fun r => scratch r \/ r = SLOT c j) s s4 /\
    hfr (fun r => scratch r \/ r = PROG \/ r = GPC \/ r = NC c \/ r = greg c \/ r = SLOT c j) s s4.
Proof.
  intros P s p c j Hh Hf Hn Hj. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (phase_decode P s (E.CHECK p c) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (handler (E.CHECK p c)) with L_CHECK in P1.
  change (arg_of (E.CHECK p c)) with (pair (ccode c) (pcode p)) in A1.
  destruct (hUCD_spec (L_CKH E.CA) (L_CKH E.CB) L_CHECK U s1 c (pcode p) U_CKD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & X2 & Q2 & F2).
  assert (P2' : hpc s2 = L_CKH c) by (rewrite P2; destruct c; reflexivity).
  destruct (hCKH_disp c (L_CKH c) U s2 (U_CKH c) P2' ltac:(herr_tac))
    as (s3 & R3 & Z3 & VF3 & F3 & L3 & G3).
  assert (KT : True) by exact I.
  assert (N2 : hv s2 (NC c) = j) by (track (NC c) KT; cc).
  rewrite N2 in L3. destruct (L3 Hj) as [P3 T73].
  destruct (hCKS_pre c j (CKS_at (L_CKH c) j) U s3 (U_CKS c j Hj) P3 ltac:(herr_tac))
    as (s4 & R4 & P4 & S4 & W4 & T24 & T34 & T44 & T84 & T94 & VF4 & F4).
  assert (R : Hrun U s s4) by chain.
  assert (KJ : j < 16) by exact Hj.
  exists s4. split; [exact R |]. split; [herr_tac |]. split; [exact P4 |].
  split.
  { rewrite S4. track (SLOT c j) KJ. track T2 KT. track (greg c) KT. cc. }
  split.
  { track (SLOT c j) KJ. lia. }
  split; [track T2 KT; cc |].
  repeat (split; [zero_goal KT |]).
  split.
  - intros r Hr. assert (K : ~ (scratch r \/ r = SLOT c j)) by exact Hr.
    track r K. cc.
  - intros r Hr. assert (K : j < 16 /\ ~ (scratch r \/ r = PROG \/ r = GPC \/ r = NC c \/
                                         r = greg c \/ r = SLOT c j)) by (split; assumption).
    track r K. split; cc.
Qed.

Theorem phase_check_pass : forall P s p c j,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.CHECK p c) ->
  hv s (NC c) = j -> j < 16 -> hv s (SLOT c j) = 0 ->
  E.holds p (hv s (greg c)) -> length (M.facts (M.core_of s)) < M.fact_cap ->
  exists s', hreach s s' /\ at_head P s' /\
    hv s' GPC = S (hv s GPC) /\ hv s' (NC c) = S j /\ hv s' (MP c j) = S (pcode p) /\
    hv s' (SLOT c j) = pair (pcode p) (hv s (greg c)) /\
    hver s (SLOT c j) < hver s' (SLOT c j) /\
    M.facts (M.core_of s') =
      M.mkfact PSlot (SLOT c j) (hver s' (SLOT c j)) :: M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    (forall r, r <> GPC -> r <> NC c -> r <> MP c j -> r <> SLOT c j -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> r <> SLOT c j -> hver s' r = hver s r).
Proof.
  intros P s p c j Hh Hf Hn Hj Hs0 Hholds Hcap. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (check_to_slot P s p c j Hh Hf Hn Hj)
    as (s4 & R4 & E4 & P4 & S4 & W4 & T24 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & VF4 & HF4).
  rewrite Hs0, Nat.add_0_l in S4.
  destruct (hrun_same_sub _ _ _ _ _ R4) as (Fa4 & Ch4 & Er4 & Mu4 & Ce4).
  destruct (hCHECK_pass_fields (SLOT c j) (CKS_chk (CKS_at (L_CKH c) j)) U s4 p (hv s (greg c))
              (U_CHK c j Hj) P4 E4 S4 Hholds ltac:(rewrite Fa4; exact Hcap))
    as (Fa5 & Ch5 & P5 & E5 & Mu5 & Ce5 & All5).
  set (s5 := hrun_prog 1 U s4) in *.
  pose proof (all_same_hframe s4 s5 All5) as F5.
  destruct (hCKS_post c j (CKS_at (L_CKH c) j) U s5 (U_CKS c j Hj) P5 E5)
    as (s6 & R6 & P6 & M6 & Z6 & N6 & G6 & W6 & VF6 & F6).
  destruct (hrun_same_sub _ _ _ _ _ R6) as (Fa6 & Ch6 & Er6 & Mu6 & Ce6).
  assert (KT : True) by exact I.
  assert (KJ : j < 16) by exact Hj.
  assert (AH : at_head P s6).
  { unfold at_head. split; [exact P6 |]. split; [cc |].
    split; [track PROG KT; cc |]. apply scratch_all; zero_goal KT. }
  assert (EW : hver s6 (SLOT c j) = hver s4 (SLOT c j)) by (track (SLOT c j) KJ; cc).
  exists s6. split.
  { apply (hreach_trans s s4 s6); [apply Hrun_hreach, R4 |].
    apply (hreach_trans s4 s5 s6); [apply hreach_one | apply Hrun_hreach, R6]. }
  split; [exact AH |].
  split; [track GPC KT; cc |].
  split; [track (NC c) KJ; cc |].
  split; [track (MP c j) KJ; track T2 KT; cc |].
  split; [track (SLOT c j) KJ; cc |].
  split; [lia |].
  split; [rewrite Fa6, Fa5, EW, Fa4; reflexivity |].
  split; [cc |]. split; [lia |]. split; [cc |]. split.
  - intros r H1 H2 H3 H4. destruct (scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : j < 16 /\ ~ scratch r /\ r <> GPC /\ r <> NC c /\ r <> MP c j /\ r <> SLOT c j)
        by (repeat split; assumption).
      track r K. cc.
  - intros r H1 H2. assert (K : j < 16 /\ 48 <= r /\ r <> SLOT c j) by (repeat split; assumption).
    track r K. cc.
Qed.

Theorem phase_check_fail : forall P s p c j,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.CHECK p c) ->
  hv s (NC c) = j -> j < 16 -> hv s (SLOT c j) = 0 ->
  ~ E.holds p (hv s (greg c)) \/ M.fact_cap <= length (M.facts (M.core_of s)) ->
  exists s', hreach s s' /\ herr s' = true /\ hpc s' = CKS_chk (CKS_at (L_CKH c) j) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    hv s' (SLOT c j) = pair (pcode p) (hv s (greg c)) /\ hv s' T2 = pcode p /\
    (forall r, r <> T2 -> r <> SLOT c j -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> r <> SLOT c j -> hver s' r = hver s r).
Proof.
  intros P s p c j Hh Hf Hn Hj Hs0 Hbad. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (check_to_slot P s p c j Hh Hf Hn Hj)
    as (s4 & R4 & E4 & P4 & S4 & W4 & T24 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & VF4 & HF4).
  rewrite Hs0, Nat.add_0_l in S4.
  destruct (hrun_same_sub _ _ _ _ _ R4) as (Fa4 & Ch4 & Er4 & Mu4 & Ce4).
  assert (Hs5 : hrun_prog 1 U s4 = M.mkst (M.trap (M.core_of s4)) (M.mu s4 + 1) (M.cert s4)).
  { destruct Hbad as [Hbad | Hbad].
    - apply (hCHECK_fail_holds (SLOT c j) (CKS_chk (CKS_at (L_CKH c) j)) U s4 p (hv s (greg c))
               (U_CHK c j Hj) P4 E4 S4 Hbad).
    - apply (hCHECK_fail_cap (SLOT c j) (CKS_chk (CKS_at (L_CKH c) j)) U s4
               (U_CHK c j Hj) P4 E4). rewrite Fa4. exact Hbad. }
  exists (hrun_prog 1 U s4). split.
  { apply (hreach_trans s s4); [apply Hrun_hreach, R4 | apply hreach_one]. }
  rewrite Hs5. cbn [M.core_of M.mu M.cert M.trap M.vals M.vers M.pc M.err M.facts M.chan].
  split; [reflexivity |]. split; [exact P4 |]. split; [exact Fa4 |]. split; [exact Ch4 |].
  split; [lia |]. split; [exact Ce4 |]. split; [exact S4 |]. split; [exact T24 |].
  assert (KT : True) by exact I.
  assert (KJ : j < 16) by exact Hj.
  split.
  - intros r H1 H2. destruct (scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs).
      destruct (scratch_cases r Hs) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        first [contradiction | assumption].
    + assert (K : ~ (scratch r \/ r = SLOT c j)) by tauto. track r K. cc.
  - intros r H1 H2. assert (K : j < 16 /\ 48 <= r /\ r <> SLOT c j) by (repeat split; assumption).
    track r K. cc.
Qed.

Theorem phase_check_dead : forall P s p c,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.CHECK p c) ->
  16 <= hv s (NC c) -> hv s DEAD = 0 ->
  exists s', hreach s s' /\ herr s' = true /\ hpc s' = CKH_dead (L_CKH c) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    hv s' T2 = pcode p /\ hv s' T7 = hv s (NC c) - 16 /\
    (forall r, r <> T2 -> r <> T7 -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s p c Hh Hf Hn Hd. pose proof Hh as (Hpc & He & Hp & Hz).
  pose proof (at_head_zero P s Hh) as (Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  destruct (phase_decode P s (E.CHECK p c) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (handler (E.CHECK p c)) with L_CHECK in P1.
  change (arg_of (E.CHECK p c)) with (pair (ccode c) (pcode p)) in A1.
  destruct (hUCD_spec (L_CKH E.CA) (L_CKH E.CB) L_CHECK U s1 c (pcode p) U_CKD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & X2 & Q2 & F2).
  assert (P2' : hpc s2 = L_CKH c) by (rewrite P2; destruct c; reflexivity).
  destruct (hCKH_disp c (L_CKH c) U s2 (U_CKH c) P2' ltac:(herr_tac))
    as (s3 & R3 & Z43 & VF3 & F3 & L3 & G3).
  assert (KT : True) by exact I.
  assert (N2 : hv s2 (NC c) = hv s (NC c)) by (track (NC c) KT; cc).
  rewrite N2 in G3. destruct (G3 Hn) as [P3 T73].
  assert (R : Hrun U s s3) by chain.
  destruct (hrun_same_sub _ _ _ _ _ R) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (D3 : hv s3 DEAD = 0) by (track DEAD KT; cc).
  pose proof (hCHECK_fail_zero DEAD (CKH_dead (L_CKH c)) U s3 (U_CKH_dead c) P3
                ltac:(herr_tac) D3) as Hs4.
  exists (hrun_prog 1 U s3). split.
  { apply (hreach_trans s s3); [apply Hrun_hreach, R | apply hreach_one]. }
  rewrite Hs4. cbn [M.core_of M.mu M.cert M.trap M.vals M.vers M.pc M.err M.facts M.chan].
  split; [reflexivity |]. split; [exact P3 |]. split; [exact Fa3 |]. split; [exact Ch3 |].
  split; [lia |]. split; [exact Ce3 |]. split; [track T2 KT; cc |].
  split; [exact T73 |].
  split.
  - intros r H1 H2. destruct (scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs).
      destruct (scratch_cases r Hs) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        first [contradiction | zero_goal KT].
    + assert (K : ~ scratch r) by exact Hs. track r K. cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. track r K. cc.
Qed.

(* ================================================================= *)
(* COMMIT.                                                            *)
(* ================================================================= *)

(* From HEAD through the search of bank c. *)
Lemma commit_search : forall P s p c,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.COMMIT p c) ->
  exists s3, Hrun U s s3 /\ herr s3 = false /\
    hv s3 T2 = S (pcode p) /\
    hv s3 T0 = 0 /\ hv s3 T1 = 0 /\ hv s3 T3 = 0 /\ hv s3 T4 = 0 /\ hv s3 T5 = 0 /\
    hv s3 T6 = 0 /\ hv s3 T7 = 0 /\ hv s3 T8 = 0 /\ hv s3 T9 = 0 /\
    vfr scratch s s3 /\
    hfr (fun r => scratch r \/ r = PROG \/ r = GPC \/ in_mp c r) s s3 /\
    (forall j, j < 16 -> hv s (MP c j) = S (pcode p) ->
       (forall j', j' < j -> hv s (MP c j') <> S (pcode p)) -> hpc s3 = CMS_at (L_CMH c) j) /\
    ((forall j, j < 16 -> hv s (MP c j) <> S (pcode p)) -> hpc s3 = CMH_dead (L_CMH c)).
Proof.
  intros P s p c Hh Hf. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (phase_decode P s (E.COMMIT p c) Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (handler (E.COMMIT p c)) with L_COMMIT in P1.
  change (arg_of (E.COMMIT p c)) with (pair (ccode c) (pcode p)) in A1.
  destruct (hUCD_spec (L_CMH E.CA) (L_CMH E.CB) L_COMMIT U s1 c (pcode p) U_CMD P1 E1 A1)
    as (s2 & R2 & P2 & V2 & W2 & X2 & Q2 & F2).
  assert (P2' : hpc s2 = L_CMH c) by (rewrite P2; destruct c; reflexivity).
  destruct (hCMH_search c (L_CMH c) U s2 (U_CMH c) P2' ltac:(herr_tac))
    as (s3 & R3 & T23 & Z73 & Z83 & Z43 & VF3 & HF3 & M3 & N3).
  assert (KT : True) by exact I.
  assert (EM : forall j, hv s2 (MP c j) = hv s (MP c j)).
  { intro j. assert (K : True) by exact I. track (MP c j) K. cc. }
  assert (R : Hrun U s s3) by chain.
  exists s3. split; [exact R |]. split; [herr_tac |].
  split; [cc |].
  repeat (split; [zero_goal KT |]).
  split; [vfr_goal |]. split; [hfr_goal |]. split.
  - intros j Hj Hm Hfst. apply M3; [exact Hj | rewrite EM, V2; exact Hm |].
    intros j' Hj'. rewrite EM, V2. apply Hfst, Hj'.
  - intros Hall. apply N3. intros j Hj. rewrite EM, V2. apply Hall, Hj.
Qed.

Theorem phase_commit_pass : forall P s p c j,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.COMMIT p c) ->
  j < 16 -> hv s (MP c j) = S (pcode p) ->
  (forall j', j' < j -> hv s (MP c j') <> S (pcode p)) ->
  In (M.mkfact PSlot (SLOT c j) (hver s (SLOT c j))) (M.facts (M.core_of s)) ->
  exists s', hreach s s' /\ at_head P s' /\ hv s' GPC = S (hv s GPC) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = Some (M.mkfact PSlot (SLOT c j) (hver s (SLOT c j))) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    (forall r, r <> GPC -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s p c j Hh Hf Hj Hm Hfst Hin. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (commit_search P s p c Hh Hf)
    as (s3 & R3 & E3 & T23 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & VF3 & HF3 & M3 & N3).
  pose proof (M3 j Hj Hm Hfst) as P3.
  destruct (hrun_same_sub _ _ _ _ _ R3) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (KJ : j < 16) by exact Hj.
  assert (WS : hver s3 (SLOT c j) = hver s (SLOT c j)) by (track (SLOT c j) KJ; cc).
  destruct (hCOMMIT_pass_fields (SLOT c j) (CMS_at (L_CMH c) j) U s3 (U_CMT c j Hj) P3 E3
              ltac:(rewrite WS, Fa3; exact Hin))
    as (Fa4 & Ch4 & P4 & E4 & Mu4 & Ce4 & All4).
  set (s4 := hrun_prog 1 U s3) in *.
  pose proof (all_same_hframe s3 s4 All4) as F4.
  destruct (hCMS_post (SLOT c j) (CMS_at (L_CMH c) j) U s4 (U_CMS c j Hj) P4 E4)
    as (s5 & R5 & P5 & Z5 & G5 & W5 & F5).
  destruct (hrun_same_sub _ _ _ _ _ R5) as (Fa5 & Ch5 & Er5 & Mu5 & Ce5).
  assert (KT : True) by exact I.
  assert (AH : at_head P s5).
  { unfold at_head. split; [exact P5 |]. split; [cc |].
    split; [track PROG KT; cc |]. apply scratch_all; zero_goal KT. }
  exists s5. split.
  { apply (hreach_trans s s3 s5); [apply Hrun_hreach, R3 |].
    apply (hreach_trans s3 s4 s5); [apply hreach_one | apply Hrun_hreach, R5]. }
  split; [exact AH |].
  split; [track GPC KT; cc |].
  split; [cc |].
  split; [rewrite Ch5, Ch4, WS; reflexivity |].
  split; [lia |]. split; [cc |]. split.
  - intros r H1. destruct (scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : ~ scratch r /\ r <> GPC) by (split; assumption). track r K. cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. track r K. cc.
Qed.

Theorem phase_commit_stale : forall P s p c j,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.COMMIT p c) ->
  j < 16 -> hv s (MP c j) = S (pcode p) ->
  (forall j', j' < j -> hv s (MP c j') <> S (pcode p)) ->
  ~ In (M.mkfact PSlot (SLOT c j) (hver s (SLOT c j))) (M.facts (M.core_of s)) ->
  exists s', hreach s s' /\ herr s' = true /\ hpc s' = CMS_at (L_CMH c) j /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    hv s' T2 = S (pcode p) /\
    (forall r, r <> T2 -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s p c j Hh Hf Hj Hm Hfst Hin. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (commit_search P s p c Hh Hf)
    as (s3 & R3 & E3 & T23 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & VF3 & HF3 & M3 & N3).
  pose proof (M3 j Hj Hm Hfst) as P3.
  destruct (hrun_same_sub _ _ _ _ _ R3) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (KJ : j < 16) by exact Hj.
  assert (WS : hver s3 (SLOT c j) = hver s (SLOT c j)) by (track (SLOT c j) KJ; cc).
  pose proof (hCOMMIT_fail (SLOT c j) (CMS_at (L_CMH c) j) U s3 (U_CMT c j Hj) P3 E3
                ltac:(rewrite WS, Fa3; exact Hin)) as Hs4.
  exists (hrun_prog 1 U s3). split.
  { apply (hreach_trans s s3); [apply Hrun_hreach, R3 | apply hreach_one]. }
  rewrite Hs4. cbn [M.core_of M.mu M.cert M.trap M.vals M.vers M.pc M.err M.facts M.chan].
  split; [reflexivity |]. split; [exact P3 |]. split; [exact Fa3 |]. split; [exact Ch3 |].
  split; [lia |]. split; [exact Ce3 |]. split; [exact T23 |].
  assert (KT : True) by exact I.
  split.
  - intros r H1. destruct (scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs).
      destruct (scratch_cases r Hs) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        first [contradiction | assumption].
    + track r Hs. cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. track r K. cc.
Qed.

Theorem phase_commit_none : forall P s p c,
  at_head P s -> E.fetch P (hv s GPC) = Some (E.COMMIT p c) ->
  (forall j, j < 16 -> hv s (MP c j) <> S (pcode p)) ->
  ~ In (M.mkfact PSlot DEAD (hver s DEAD)) (M.facts (M.core_of s)) ->
  exists s', hreach s s' /\ herr s' = true /\ hpc s' = CMH_dead (L_CMH c) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    hv s' T2 = S (pcode p) /\
    (forall r, r <> T2 -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s p c Hh Hf Hnone Hin. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (commit_search P s p c Hh Hf)
    as (s3 & R3 & E3 & T23 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & VF3 & HF3 & M3 & N3).
  pose proof (N3 Hnone) as P3.
  destruct (hrun_same_sub _ _ _ _ _ R3) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (KT : True) by exact I.
  assert (WD : hver s3 DEAD = hver s DEAD) by (track DEAD KT; cc).
  pose proof (hCOMMIT_fail DEAD (CMH_dead (L_CMH c)) U s3 (U_CMH_dead c) P3 E3
                ltac:(rewrite WD, Fa3; exact Hin)) as Hs4.
  exists (hrun_prog 1 U s3). split.
  { apply (hreach_trans s s3); [apply Hrun_hreach, R3 | apply hreach_one]. }
  rewrite Hs4. cbn [M.core_of M.mu M.cert M.trap M.vals M.vers M.pc M.err M.facts M.chan].
  split; [reflexivity |]. split; [exact P3 |]. split; [exact Fa3 |]. split; [exact Ch3 |].
  split; [lia |]. split; [exact Ce3 |]. split; [exact T23 |].
  split.
  - intros r H1. destruct (scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs).
      destruct (scratch_cases r Hs) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        first [contradiction | assumption].
    + track r Hs. cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. track r K. cc.
Qed.

(* ================================================================= *)
(* CERTIFY.                                                           *)
(* ================================================================= *)

Theorem phase_certify_pass : forall P s f,
  at_head P s -> E.fetch P (hv s GPC) = Some E.CERTIFY -> M.chan (M.core_of s) = Some f ->
  exists s', hreach s s' /\ at_head P s' /\ hv s' GPC = S (hv s GPC) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = true /\
    (forall r, r <> GPC -> hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s f Hh Hf Hc. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (phase_decode P s E.CERTIFY Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (handler E.CERTIFY) with L_CERT in P1. change (arg_of E.CERTIFY) with 0 in A1.
  destruct (hrun_same_sub _ _ _ _ _ R1) as (Fa1 & Ch1 & Er1 & Mu1 & Ce1).
  pose proof (hCERTIFY_pass L_CERT U s1 f U_CERT P1 E1 ltac:(rewrite Ch1; exact Hc)) as Hs2.
  set (s2 := hrun_prog 1 U s1) in *.
  assert (F2 : hframe [] s1 s2) by (apply all_same_hframe; intro d; rewrite Hs2; split; reflexivity).
  assert (P2 : hpc s2 = 1 + L_CERT) by (rewrite Hs2; reflexivity).
  assert (Er2 : herr s2 = false) by (rewrite Hs2; exact E1).
  destruct (hCERTH_post L_CERT U s2 U_CERTH P2 Er2) as (s3 & R3 & P3 & G3 & W3 & F3).
  destruct (hrun_same_sub _ _ _ _ _ R3) as (Fa3 & Ch3 & Er3 & Mu3 & Ce3).
  assert (KT : True) by exact I.
  assert (AH : at_head P s3).
  { unfold at_head. split; [exact P3 |]. split; [cc |].
    split; [track PROG KT; cc |]. apply scratch_all; zero_goal KT. }
  exists s3. split.
  { apply (hreach_trans s s1 s3); [apply Hrun_hreach, R1 |].
    apply (hreach_trans s1 s2 s3); [apply hreach_one | apply Hrun_hreach, R3]. }
  split; [exact AH |]. split; [track GPC KT; cc |].
  rewrite Hs2 in Fa3, Ch3, Mu3, Ce3. cbn [M.core_of M.mu M.cert M.goto M.facts M.chan] in Fa3, Ch3, Mu3, Ce3.
  split; [cc |]. split; [cc |]. split; [lia |]. split; [exact Ce3 |]. split.
  - intros r H1. destruct (scratch_dec r) as [Hs | Hs].
    + destruct AH as (_ & _ & _ & Hz'). rewrite (Hz' r Hs), (Hz r Hs). reflexivity.
    + assert (K : ~ scratch r /\ r <> GPC) by (split; assumption). track r K. cc.
  - intros r H1. assert (K : 48 <= r) by exact H1. track r K. cc.
Qed.

Theorem phase_certify_fail : forall P s,
  at_head P s -> E.fetch P (hv s GPC) = Some E.CERTIFY -> M.chan (M.core_of s) = None ->
  exists s', hreach s s' /\ herr s' = true /\ hpc s' = L_CERT /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
    (forall r, hv s' r = hv s r) /\
    (forall r, 48 <= r -> hver s' r = hver s r).
Proof.
  intros P s Hh Hf Hc. pose proof Hh as (Hpc & He & Hp & Hz).
  destruct (phase_decode P s E.CERTIFY Hh Hf)
    as (s1 & R1 & E1 & P1 & A1 & Y0 & Y1 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & V1 & F1).
  change (handler E.CERTIFY) with L_CERT in P1. change (arg_of E.CERTIFY) with 0 in A1.
  destruct (hrun_same_sub _ _ _ _ _ R1) as (Fa1 & Ch1 & Er1 & Mu1 & Ce1).
  pose proof (hCERTIFY_fail L_CERT U s1 U_CERT P1 E1 ltac:(rewrite Ch1; exact Hc)) as Hs2.
  exists (hrun_prog 1 U s1). split.
  { apply (hreach_trans s s1); [apply Hrun_hreach, R1 | apply hreach_one]. }
  rewrite Hs2. cbn [M.core_of M.mu M.cert M.trap M.vals M.vers M.pc M.err M.facts M.chan].
  split; [reflexivity |]. split; [exact P1 |]. split; [exact Fa1 |]. split; [exact Ch1 |].
  split; [lia |]. split; [exact Ce1 |].
  split.
  - intros r. destruct (scratch_dec r) as [Hs | Hs].
    + rewrite (Hz r Hs).
      destruct (scratch_cases r Hs) as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]];
        assumption.
    + apply V1, Hs.
  - intros r H1. assert (K : 48 <= r) by exact H1. track r K. cc.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions hCD_spec.
Print Assumptions hUCD_spec.
Print Assumptions hBUMPS_spec.
Print Assumptions hEQRS_spec.
Print Assumptions hHALTB_spec.
Print Assumptions hHEAD_spec.
Print Assumptions hINCH_spec.
Print Assumptions hDECH_zero.
Print Assumptions hDECH_taken.
Print Assumptions hCKH_disp.
Print Assumptions hCKS_pre.
Print Assumptions hCKS_post.
Print Assumptions hCMH_search.
Print Assumptions hCMS_post.
Print Assumptions hCERTH_post.
Print Assumptions phase_decode.
Print Assumptions phase_stop.
Print Assumptions phase_pc0.
Print Assumptions phase_out.
Print Assumptions phase_halt.
Print Assumptions phase_inc.
Print Assumptions phase_dec_taken.
Print Assumptions phase_dec_zero.
Print Assumptions check_to_slot.
Print Assumptions phase_check_pass.
Print Assumptions phase_check_fail.
Print Assumptions phase_check_dead.
Print Assumptions commit_search.
Print Assumptions phase_commit_pass.
Print Assumptions phase_commit_stale.
Print Assumptions phase_commit_none.
Print Assumptions phase_certify_pass.
Print Assumptions phase_certify_fail.
