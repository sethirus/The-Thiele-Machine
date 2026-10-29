(** SmLoops3.v: the commit loop, the certify loop and the closing check.

    Continues SmLoops2.v.

      sm2_commit_loop   body COMMIT PSlot rs. Given that the table already
                        holds the claim about rs at its current version, it
                        commits to that claim n times: the channel holds the
                        claim when n is positive, the ledger grows by n.
      sm2_certify_loop  body CERTIFY. Given a full channel, it raises the
                        flag when n is positive; the ledger grows by n.
      sm2_trapg         [DEC fe; INC Z; DEC Z; CHECK PSlot rd]: when fe holds
                        0 it falls out without a trace; when fe holds a
                        positive number it checks rd, a register that holds 0
                        and so never passes, and traps, paying 1.

    Dependencies: Coq standard library, EarnedMulti.v, UniversalCodes.v,
    SmHostBlocks.v, SmLoops.v and SmLoops2.v. No axioms and no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here the COMMIT loop, the CERTIFY loop and the closing check on the host machine of EarnedMulti.v.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmLoops Minimal.SmLoops2.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hexec := (M.exec UC.hprop_eqb UC.heval).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).

(* ================================================================= *)
(* The commit loop.                                                   *)
(* ================================================================= *)

Theorem sm2_commit_loop : forall Q o r Z rs,
  sm2_inQ Q o (sm2_whilel o r Z [M.COMMIT UC.PSlot rs]) ->
  r <> Z -> rs <> r -> rs <> Z ->
  forall n s, M.pc (M.core_of s) = o + 1 -> M.err (M.core_of s) = false ->
  M.vals (M.core_of s) r = n ->
  (1 <= n -> In (M.mkfact UC.PSlot rs (M.vers (M.core_of s) rs)) (M.facts (M.core_of s))) ->
  exists s', sm2_RR Q s s' /\ M.pc (M.core_of s') = o + 7 /\ M.err (M.core_of s') = false /\
    M.vals (M.core_of s') r = 0 /\ M.vals (M.core_of s') Z = M.vals (M.core_of s) Z /\
    (forall q, q <> r -> M.vals (M.core_of s') q = M.vals (M.core_of s) q) /\
    (forall q, q <> r -> q <> Z -> M.vers (M.core_of s') q = M.vers (M.core_of s) q) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    (n = 0 -> M.chan (M.core_of s') = M.chan (M.core_of s)) /\
    (1 <= n -> M.chan (M.core_of s') = Some (M.mkfact UC.PSlot rs (M.vers (M.core_of s) rs))) /\
    M.mu s' = M.mu s + n /\ M.cert s' = M.cert s.
Proof.
  intros Q o r Z rs Hin HrZ Hrs1 Hrs2 n s Hp He Hv Hcl.
  destruct (sm2_whilel_fetch Q o r Z _ Hin) as (F1 & F2 & F3 & F4 & F5 & Fb).
  simpl length in F3, F4, F5, Fb.
  set (cl := M.mkfact UC.PSlot rs (M.vers (M.core_of s) rs)).
  set (Inv := fun (j : nat) (t : hstate) =>
    (forall q, q <> r -> M.vals (M.core_of t) q = M.vals (M.core_of s) q) /\
    (forall q, q <> r -> q <> Z -> M.vers (M.core_of t) q = M.vers (M.core_of s) q) /\
    M.facts (M.core_of t) = M.facts (M.core_of s) /\
    (j = 0 -> M.chan (M.core_of t) = M.chan (M.core_of s)) /\
    (1 <= j -> M.chan (M.core_of t) = Some cl) /\
    M.err (M.core_of t) = false /\
    M.mu t = M.mu s + j /\ M.cert t = M.cert s).
  assert (Hirr : forall j t t', sm2_loose r Z t t' -> Inv j t -> Inv j t').
  { intros j t t' (A & B & (C1 & C2 & C3 & C4 & C5)) (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8).
    unfold Inv. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    - intros q Hq. rewrite <- (A q Hq). apply I1, Hq.
    - intros q H1 H2. rewrite <- (B q H1 H2). apply I2; assumption.
    - rewrite <- C1. exact I3.
    - intro Hj. rewrite <- C2. apply I4, Hj.
    - intro Hj. rewrite <- C2. apply I5, Hj.
    - rewrite <- C3. exact I6.
    - rewrite <- C4. exact I7.
    - rewrite <- C5. exact I8. }
  assert (Hbody : forall j t, j < n -> Inv j t -> M.pc (M.core_of t) = o + 4 ->
    M.err (M.core_of t) = false ->
    exists s1 : hstate, sm2_RR Q t s1 /\ M.pc (M.core_of s1) = o + 4 + 1 /\
      M.err (M.core_of s1) = false /\ Inv (S j) s1 /\
      M.vals (M.core_of s1) r = M.vals (M.core_of t) r /\
      M.vals (M.core_of s1) Z = M.vals (M.core_of t) Z).
  { intros j t Hj (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8) Hpt Het.
    assert (Hfe : M.fetch Q (M.pc (M.core_of t)) = Some (M.COMMIT UC.PSlot rs)).
    { rewrite Hpt. pose proof (Fb 0 ltac:(simpl; lia)) as Hf0. rewrite Nat.add_0_r in Hf0.
      rewrite Hf0. reflexivity. }
    assert (Hw1 : M.vers (M.core_of t) rs = M.vers (M.core_of s) rs) by (apply I2; congruence).
    assert (Hin1 : In (M.mkfact UC.PSlot rs (M.vers (M.core_of t) rs)) (M.facts (M.core_of t))).
    { rewrite Hw1, I3. apply Hcl. lia. }
    destruct (sm2_step_commit_ok Q t rs Het Hfe Hin1)
      as (N1 & P1 & V1 & W1 & Fa1 & C1 & E1 & Mu1 & Ce1).
    exists (hstep Q t). refine (conj _ (conj _ (conj E1 (conj _ (conj _ _))))).
    - eapply sm2_RR_one. exact N1.
    - rewrite P1, Hpt. lia.
    - unfold Inv. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj E1 (conj _ _))))))).
      + intros q Hq. rewrite V1. apply I1, Hq.
      + intros q H1 H2. rewrite W1. apply I2; assumption.
      + rewrite Fa1. exact I3.
      + intro Hz. discriminate Hz.
      + intros _. rewrite C1, Hw1. reflexivity.
      + rewrite Mu1, I7. lia.
      + rewrite Ce1. exact I8.
    - rewrite V1. reflexivity.
    - rewrite V1. reflexivity. }
  pose proof (sm2_while Q o r Z 1 n Inv HrZ F1 F2 F3 F4 F5 Hirr Hbody) as Hw.
  specialize (Hw n 0 s ltac:(lia)).
  assert (HI0 : Inv 0 s).
  { unfold Inv. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); try reflexivity.
    - intro Hz. exfalso. lia.
    - exact He.
    - lia. }
  destruct (Hw HI0 Hp He Hv) as (s' & R & P & E & V0 & (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8) & VZ).
  exists s'.
  refine (conj R (conj _ (conj E (conj V0 (conj VZ (conj J1 (conj J2 (conj J3 (conj _ (conj _ (conj _ J8))))))))))).
  - rewrite P. lia.
  - intro Hn0. apply J4. lia.
  - intro Hn1. apply J5. lia.
  - rewrite J7. lia.
Qed.

(* ================================================================= *)
(* The certify loop.                                                  *)
(* ================================================================= *)

Theorem sm2_certify_loop : forall Q o r Z,
  sm2_inQ Q o (sm2_whilel o r Z [M.CERTIFY]) ->
  r <> Z ->
  forall n s, M.pc (M.core_of s) = o + 1 -> M.err (M.core_of s) = false ->
  M.vals (M.core_of s) r = n -> (1 <= n -> M.chan (M.core_of s) <> None) ->
  exists s', sm2_RR Q s s' /\ M.pc (M.core_of s') = o + 7 /\ M.err (M.core_of s') = false /\
    M.vals (M.core_of s') r = 0 /\ M.vals (M.core_of s') Z = M.vals (M.core_of s) Z /\
    (forall q, q <> r -> M.vals (M.core_of s') q = M.vals (M.core_of s) q) /\
    (forall q, q <> r -> q <> Z -> M.vers (M.core_of s') q = M.vers (M.core_of s) q) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + n /\
    (n = 0 -> M.cert s' = M.cert s) /\ (1 <= n -> M.cert s' = true).
Proof.
  intros Q o r Z Hin HrZ n s Hp He Hv Hch.
  destruct (sm2_whilel_fetch Q o r Z _ Hin) as (F1 & F2 & F3 & F4 & F5 & Fb).
  simpl length in F3, F4, F5, Fb.
  set (Inv := fun (j : nat) (t : hstate) =>
    (forall q, q <> r -> M.vals (M.core_of t) q = M.vals (M.core_of s) q) /\
    (forall q, q <> r -> q <> Z -> M.vers (M.core_of t) q = M.vers (M.core_of s) q) /\
    M.facts (M.core_of t) = M.facts (M.core_of s) /\
    M.chan (M.core_of t) = M.chan (M.core_of s) /\
    M.err (M.core_of t) = false /\
    M.mu t = M.mu s + j /\
    (j = 0 -> M.cert t = M.cert s) /\ (1 <= j -> M.cert t = true)).
  assert (Hirr : forall j t t', sm2_loose r Z t t' -> Inv j t -> Inv j t').
  { intros j t t' (A & B & (C1 & C2 & C3 & C4 & C5)) (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8).
    unfold Inv. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    - intros q Hq. rewrite <- (A q Hq). apply I1, Hq.
    - intros q H1 H2. rewrite <- (B q H1 H2). apply I2; assumption.
    - rewrite <- C1. exact I3.
    - rewrite <- C2. exact I4.
    - rewrite <- C3. exact I5.
    - rewrite <- C4. exact I6.
    - intro Hj. rewrite <- C5. apply I7, Hj.
    - intro Hj. rewrite <- C5. apply I8, Hj. }
  assert (Hbody : forall j t, j < n -> Inv j t -> M.pc (M.core_of t) = o + 4 ->
    M.err (M.core_of t) = false ->
    exists s1 : hstate, sm2_RR Q t s1 /\ M.pc (M.core_of s1) = o + 4 + 1 /\
      M.err (M.core_of s1) = false /\ Inv (S j) s1 /\
      M.vals (M.core_of s1) r = M.vals (M.core_of t) r /\
      M.vals (M.core_of s1) Z = M.vals (M.core_of t) Z).
  { intros j t Hj (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8) Hpt Het.
    assert (Hfe : M.fetch Q (M.pc (M.core_of t)) = Some M.CERTIFY).
    { rewrite Hpt. pose proof (Fb 0 ltac:(simpl; lia)) as Hf0. rewrite Nat.add_0_r in Hf0.
      rewrite Hf0. reflexivity. }
    assert (Hch1 : M.chan (M.core_of t) <> None) by (rewrite I4; apply Hch; lia).
    destruct (sm2_step_certify_ok Q t Het Hfe Hch1)
      as (N1 & P1 & V1 & W1 & Fa1 & C1 & E1 & Mu1 & Ce1).
    exists (hstep Q t). refine (conj _ (conj _ (conj E1 (conj _ (conj _ _))))).
    - eapply sm2_RR_one. exact N1.
    - rewrite P1, Hpt. lia.
    - unfold Inv. refine (conj _ (conj _ (conj _ (conj _ (conj E1 (conj _ (conj _ _))))))).
      + intros q Hq. rewrite V1. apply I1, Hq.
      + intros q H1 H2. rewrite W1. apply I2; assumption.
      + rewrite Fa1. exact I3.
      + rewrite C1. exact I4.
      + rewrite Mu1, I6. lia.
      + intro Hz. discriminate Hz.
      + intros _. exact Ce1.
    - rewrite V1. reflexivity.
    - rewrite V1. reflexivity. }
  pose proof (sm2_while Q o r Z 1 n Inv HrZ F1 F2 F3 F4 F5 Hirr Hbody) as Hw.
  specialize (Hw n 0 s ltac:(lia)).
  assert (HI0 : Inv 0 s).
  { unfold Inv. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); try reflexivity.
    - exact He.
    - lia.
    - intro Hz. exfalso. lia. }
  destruct (Hw HI0 Hp He Hv) as (s' & R & P & E & V0 & (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8) & VZ).
  exists s'.
  refine (conj R (conj _ (conj E (conj V0 (conj VZ (conj J1 (conj J2 (conj J3 (conj J4 (conj _ (conj _ _))))))))))).
  - rewrite P. lia.
  - rewrite J6. lia.
  - intro Hn0. apply J7. lia.
  - intro Hn1. apply J8. lia.
Qed.

(* ================================================================= *)
(* The closing check.                                                 *)
(* ================================================================= *)

Definition sm2_trapg (o fe Z rd : nat) : list hinstr :=
  [M.DEC fe (o + 4); M.INC Z; M.DEC Z (o + 5); M.CHECK UC.PSlot rd].

Lemma sm2_trapg_length : forall o fe Z rd, length (sm2_trapg o fe Z rd) = 4.
Proof. reflexivity. Qed.

Theorem sm2_trap_zero : forall Q o fe Z rd, sm2_inQ Q o (sm2_trapg o fe Z rd) ->
  fe <> Z ->
  forall s, M.pc (M.core_of s) = o + 1 -> M.err (M.core_of s) = false ->
  M.vals (M.core_of s) fe = 0 ->
  exists s', sm2_RR Q s s' /\ M.pc (M.core_of s') = o + 5 /\ M.err (M.core_of s') = false /\
    (forall q, M.vals (M.core_of s') q = M.vals (M.core_of s) q) /\ sm2_pfe s s'.
Proof.
  intros Q o fe Z rd Hin HfZ s Hp He Hv.
  unfold sm2_inQ in Hin.
  assert (F1 : M.fetch Q (o + 1) = Some (M.DEC fe (o + 4))) by (rewrite (Hin 1) by (simpl; lia); reflexivity).
  assert (F2 : M.fetch Q (o + 2) = Some (M.INC Z)) by (rewrite (Hin 2) by (simpl; lia); reflexivity).
  assert (F3 : M.fetch Q (o + 3) = Some (M.DEC Z (o + 5))) by (rewrite (Hin 3) by (simpl; lia); reflexivity).
  assert (F1' : M.fetch Q (M.pc (M.core_of s)) = Some (M.DEC fe (o + 4))) by (rewrite Hp; exact F1).
  destruct (sm2_step_dec_zero Q s fe (o + 4) He F1' Hv) as (N1 & P1 & V1 & W1 & E1).
  set (s1 := hstep Q s) in *.
  assert (He1 : M.err (M.core_of s1) = false) by (destruct E1 as (_ & _ & C & _); rewrite <- C; exact He).
  assert (F2' : M.fetch Q (M.pc (M.core_of s1)) = Some (M.INC Z))
    by (rewrite P1, Hp; replace (S (o + 1)) with (o + 2) by lia; exact F2).
  destruct (sm2_step_inc Q s1 Z He1 F2') as (N2 & P2 & V2 & W2 & E2).
  set (s2 := hstep Q s1) in *.
  assert (He2 : M.err (M.core_of s2) = false) by (destruct E2 as (_ & _ & C & _); rewrite <- C; exact He1).
  assert (F3' : M.fetch Q (M.pc (M.core_of s2)) = Some (M.DEC Z (o + 5))).
  { rewrite P2, P1, Hp. replace (S (S (o + 1))) with (o + 3) by lia. exact F3. }
  assert (HZ2 : M.vals (M.core_of s2) Z = S (M.vals (M.core_of s) Z)).
  { rewrite V2, Nat.eqb_refl, V1. reflexivity. }
  destruct (sm2_step_dec_pos Q s2 Z (o + 5) (M.vals (M.core_of s) Z) He2 F3' HZ2)
    as (N3 & P3 & V3 & W3 & E3).
  exists (hstep Q s2). refine (conj _ (conj P3 (conj _ (conj _ _)))).
  - eapply sm2_RR_step; [exact N1 |]. eapply sm2_RR_step; [exact N2 |].
    eapply sm2_RR_step; [exact N3 |]. apply sm2_RR_refl.
  - destruct E3 as (_ & _ & C & _). rewrite <- C. exact He2.
  - intro q. rewrite V3. destruct (Nat.eqb_spec q Z) as [-> | Hz].
    + reflexivity.
    + rewrite V2. destruct (Nat.eqb_spec q Z); [congruence |]. rewrite V1. reflexivity.
  - eapply sm2_pfe_trans; [exact E1 |]. eapply sm2_pfe_trans; [exact E2 | exact E3].
Qed.

Theorem sm2_trap_pos : forall Q o fe Z rd, sm2_inQ Q o (sm2_trapg o fe Z rd) ->
  forall s m, M.pc (M.core_of s) = o + 1 -> M.err (M.core_of s) = false ->
  M.vals (M.core_of s) fe = S m -> M.vals (M.core_of s) rd = 0 -> rd <> fe ->
  exists s', sm2_RR Q s s' /\ M.err (M.core_of s') = true /\
    (forall q, q <> fe -> M.vals (M.core_of s') q = M.vals (M.core_of s) q) /\
    M.facts (M.core_of s') = M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s.
Proof.
  intros Q o fe Z rd Hin s m Hp He Hv Hrd Hne.
  unfold sm2_inQ in Hin.
  assert (F1 : M.fetch Q (o + 1) = Some (M.DEC fe (o + 4))) by (rewrite (Hin 1) by (simpl; lia); reflexivity).
  assert (F4 : M.fetch Q (o + 4) = Some (M.CHECK UC.PSlot rd)) by (rewrite (Hin 4) by (simpl; lia); reflexivity).
  assert (F1' : M.fetch Q (M.pc (M.core_of s)) = Some (M.DEC fe (o + 4))) by (rewrite Hp; exact F1).
  destruct (sm2_step_dec_pos Q s fe (o + 4) m He F1' Hv) as (N1 & P1 & V1 & W1 & E1).
  set (s1 := hstep Q s) in *.
  assert (He1 : M.err (M.core_of s1) = false) by (destruct E1 as (_ & _ & C & _); rewrite <- C; exact He).
  assert (F4' : M.fetch Q (M.pc (M.core_of s1)) = Some (M.CHECK UC.PSlot rd)) by (rewrite P1; exact F4).
  assert (Hrd1 : M.vals (M.core_of s1) rd = 0).
  { rewrite V1. destruct (Nat.eqb_spec rd fe); [congruence | exact Hrd]. }
  destruct (sm2_step_check_fail Q s1 rd He1 F4' Hrd1) as (N2 & V2 & Fa2 & C2 & E2 & Mu2 & Ce2).
  exists (hstep Q s1). refine (conj _ (conj E2 (conj _ (conj _ (conj _ (conj _ _)))))).
  - eapply sm2_RR_step; [exact N1 |]. eapply sm2_RR_step; [exact N2 |]. apply sm2_RR_refl.
  - intros q Hq. rewrite V2, V1. destruct (Nat.eqb_spec q fe); [congruence | reflexivity].
  - rewrite Fa2. destruct E1 as (A & _). symmetry. exact A.
  - rewrite C2. destruct E1 as (_ & B & _). symmetry. exact B.
  - rewrite Mu2. destruct E1 as (_ & _ & _ & D & _). rewrite <- D. reflexivity.
  - rewrite Ce2. destruct E1 as (_ & _ & _ & _ & E). symmetry. exact E.
Qed.

Print Assumptions sm2_commit_loop.
Print Assumptions sm2_certify_loop.
Print Assumptions sm2_trap_zero.
Print Assumptions sm2_trap_pos.
