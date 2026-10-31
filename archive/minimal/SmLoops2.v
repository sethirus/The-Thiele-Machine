(** SmLoops2.v: the loops of the replay, and its last instruction.

    The counting loop of SmLoops.v with four kinds of body.

      sm2_fan_spec      the body is a row of INC instructions. Every unit in
                        the counter r is moved to the registers of the row:
                        register q gains n times the number of times the row
                        names it. Used to copy a number into several
                        registers and to move a result into register 0.
      sm2_check_loop    the body is CHECK PSlot rs. It records n facts about
                        register rs at its current version, and pays n.
      sm2_commit_loop   the body is COMMIT PSlot rs. It commits to the claim
                        about rs at its current version n times, and pays n.
      sm2_certify_loop  the body is CERTIFY. It raises the flag (when n is
                        positive) and pays n.

    The last gadget [sm2_trapg] is the closing check: if its counter is 1, it
    runs CHECK PSlot rd on a register that holds 0, which never satisfies the
    property, so the host traps and the ledger goes up by 1; if the counter
    is 0, it does nothing.

    In every statement the counter register r, the jump register Z and the
    slot register rs are three different registers, and a register that the
    body does not name keeps its value; the versions of every register but
    r and Z are kept as well.

    Dependencies: Coq standard library, EarnedMulti.v, UniversalCodes.v,
    SmHostBlocks.v and SmLoops.v. No axioms and no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here the fan loop and the CHECK loop on the host machine of EarnedMulti.v.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmLoops.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hexec := (M.exec UC.hprop_eqb UC.heval).
Local Notation hcexec := (M.cexec UC.hprop_eqb UC.heval).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).

(* ================================================================= *)
(* The lines of a loop.                                               *)
(* ================================================================= *)

Lemma sm2_nth_tail : forall (A : Type) (a b c : list A) k,
  nth_error (a ++ b ++ c) (length a + length b + k) = nth_error c k.
Proof.
  intros A a b c k. rewrite nth_error_app2 by lia.
  replace (length a + length b + k - length a) with (length b + k) by lia.
  rewrite nth_error_app2 by lia.
  replace (length b + k - length b) with k by lia. reflexivity.
Qed.

Lemma sm2_nth_mid : forall (A : Type) (a b c : list A) i,
  i < length b -> nth_error (a ++ b ++ c) (length a + i) = nth_error b i.
Proof.
  intros A a b c i Hi. rewrite nth_error_app2 by lia.
  replace (length a + i - length a) with i by lia.
  rewrite nth_error_app1 by exact Hi. reflexivity.
Qed.

Lemma sm2_whilel_fetch : forall Q o r Z body,
  sm2_inQ Q o (sm2_whilel o r Z body) ->
  M.fetch Q (o + 1) = Some (M.DEC r (o + 4)) /\
  M.fetch Q (o + 2) = Some (M.INC Z) /\
  M.fetch Q (o + 3) = Some (M.DEC Z (o + 6 + length body)) /\
  M.fetch Q (o + 4 + length body) = Some (M.INC Z) /\
  M.fetch Q (o + 5 + length body) = Some (M.DEC Z (o + 1)) /\
  (forall i, i < length body -> M.fetch Q (o + 4 + i) = nth_error body i).
Proof.
  intros Q o r Z body H. unfold sm2_inQ in H. rewrite sm2_whilel_length in H.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
  - rewrite (H 1) by lia. reflexivity.
  - rewrite (H 2) by lia. reflexivity.
  - rewrite (H 3) by lia. reflexivity.
  - replace (o + 4 + length body) with (o + (4 + length body)) by lia.
    rewrite (H (4 + length body)) by lia.
    unfold sm2_whilel.
    replace (4 + length body) with (S (length (sm2_whead o r Z (length body)) + length body + 0))
      by (unfold sm2_whead; simpl; lia).
    change (nth_error (sm2_whead o r Z (length body) ++ body ++ sm2_wtail o Z)
              (length (sm2_whead o r Z (length body)) + length body + 0) = Some (M.INC Z)).
    rewrite sm2_nth_tail. reflexivity.
  - replace (o + 5 + length body) with (o + (5 + length body)) by lia.
    rewrite (H (5 + length body)) by lia.
    unfold sm2_whilel.
    replace (5 + length body) with (S (length (sm2_whead o r Z (length body)) + length body + 1))
      by (unfold sm2_whead; simpl; lia).
    change (nth_error (sm2_whead o r Z (length body) ++ body ++ sm2_wtail o Z)
              (length (sm2_whead o r Z (length body)) + length body + 1) = Some (M.DEC Z (o + 1))).
    rewrite sm2_nth_tail. reflexivity.
  - intros i Hi. replace (o + 4 + i) with (o + (4 + i)) by lia.
    rewrite (H (4 + i)) by lia.
    unfold sm2_whilel.
    replace (4 + i) with (S (length (sm2_whead o r Z (length body)) + i))
      by (unfold sm2_whead; simpl; lia).
    change (nth_error (sm2_whead o r Z (length body) ++ body ++ sm2_wtail o Z)
              (length (sm2_whead o r Z (length body)) + i) = nth_error body i).
    apply sm2_nth_mid. exact Hi.
Qed.

Lemma sm2_count_nil : forall ds q, ~ In q ds -> count_occ Nat.eq_dec ds q = 0.
Proof. intros ds q H. apply count_occ_not_In. exact H. Qed.

(* ================================================================= *)
(* The fan: a loop whose body is a row of INC instructions.           *)
(* ================================================================= *)

Definition sm2_fan (o r Z : nat) (ds : list nat) : list hinstr :=
  sm2_whilel o r Z (map M.INC ds).

Theorem sm2_fan_spec : forall Q o r Z ds, sm2_inQ Q o (sm2_fan o r Z ds) ->
  r <> Z -> ~ In r ds -> ~ In Z ds ->
  forall n s, M.pc (M.core_of s) = o + 1 -> M.err (M.core_of s) = false ->
  M.vals (M.core_of s) r = n ->
  exists s', sm2_RR Q s s' /\ M.pc (M.core_of s') = o + 6 + length ds /\
    M.err (M.core_of s') = false /\
    M.vals (M.core_of s') r = 0 /\ M.vals (M.core_of s') Z = M.vals (M.core_of s) Z /\
    (forall q, q <> r -> M.vals (M.core_of s') q =
                M.vals (M.core_of s) q + n * count_occ Nat.eq_dec ds q) /\
    (forall q, q <> r -> q <> Z -> count_occ Nat.eq_dec ds q = 0 ->
               M.vers (M.core_of s') q = M.vers (M.core_of s) q) /\
    sm2_pfe s s'.
Proof.
  intros Q o r Z ds Hin HrZ Hr Hz n s Hp He Hv.
  destruct (sm2_whilel_fetch Q o r Z _ Hin) as (F1 & F2 & F3 & F4 & F5 & Fb).
  rewrite map_length in F3, F4, F5, Fb.
  set (Inv := fun (j : nat) (t : hstate) =>
    (forall q, q <> r -> M.vals (M.core_of t) q = M.vals (M.core_of s) q + j * count_occ Nat.eq_dec ds q) /\
    (forall q, q <> r -> q <> Z -> count_occ Nat.eq_dec ds q = 0 ->
               M.vers (M.core_of t) q = M.vers (M.core_of s) q) /\
    sm2_pfe s t).
  assert (Hirr : forall j t t', sm2_loose r Z t t' -> Inv j t -> Inv j t').
  { intros j t t' (A & B & C) (I1 & I2 & I3). unfold Inv. split; [| split].
    - intros q Hq. rewrite <- (A q Hq). apply I1, Hq.
    - intros q H1 H2 H3. rewrite <- (B q H1 H2). apply I2; assumption.
    - eapply sm2_pfe_trans; [exact I3 | exact C]. }
  assert (Hr0 : count_occ Nat.eq_dec ds r = 0) by (apply sm2_count_nil; exact Hr).
  assert (Hz0 : count_occ Nat.eq_dec ds Z = 0) by (apply sm2_count_nil; exact Hz).
  assert (Hbody : forall j t, j < n -> Inv j t -> M.pc (M.core_of t) = o + 4 ->
    M.err (M.core_of t) = false ->
    exists s1 : hstate, sm2_RR Q t s1 /\ M.pc (M.core_of s1) = o + 4 + length ds /\
      M.err (M.core_of s1) = false /\ Inv (S j) s1 /\
      M.vals (M.core_of s1) r = M.vals (M.core_of t) r /\
      M.vals (M.core_of s1) Z = M.vals (M.core_of t) Z).
  { intros j t _ (I1 & I2 & I3) Hpt Het.
    destruct (sm2_incs_chain ds Q t Het) as (t1 & R1 & P1 & E1 & V1 & W1 & PF1).
    { intros i Hi. rewrite Hpt. rewrite (Fb i Hi).
      rewrite nth_error_map. exact (f_equal (option_map M.INC) (nth_error_nth' ds 0 Hi)). }
    exists t1. refine (conj R1 (conj _ (conj E1 (conj _ (conj _ _))))).
    - rewrite P1, Hpt. reflexivity.
    - unfold Inv. refine (conj _ (conj _ _)).
      + intros q Hq. rewrite V1, (I1 q Hq). nia.
      + intros q Hq1 Hq2 Hq3. rewrite (W1 q Hq3). apply I2; assumption.
      + eapply sm2_pfe_trans; [exact I3 | exact PF1].
    - rewrite V1, Hr0. lia.
    - rewrite V1, Hz0. lia. }
  pose proof (sm2_while Q o r Z (length ds) n Inv HrZ F1 F2 F3 F4 F5 Hirr Hbody) as Hw.
  specialize (Hw n 0 s ltac:(lia)).
  assert (HI0 : Inv 0 s).
  { unfold Inv. refine (conj _ (conj _ _)).
    - intros q Hq. lia.
    - intros q _ _ _. reflexivity.
    - apply sm2_pfe_refl. }
  destruct (Hw HI0 Hp He Hv) as (s' & R & P & E & V0 & (J1 & J2 & J3) & VZ).
  exists s'. rewrite Nat.add_0_l in J1.
  refine (conj R (conj P (conj E (conj V0 (conj VZ (conj J1 (conj J2 J3))))))).
Qed.

(* ================================================================= *)
(* One effect instruction.                                            *)
(* ================================================================= *)

Lemma sm2_step_check_ok : forall Q s rs,
  M.err (M.core_of s) = false -> M.fetch Q (M.pc (M.core_of s)) = Some (M.CHECK UC.PSlot rs) ->
  UC.heval UC.PSlot (M.vals (M.core_of s) rs) = true ->
  length (M.facts (M.core_of s)) < 16 ->
  M.next_instr Q (M.core_of s) <> None /\
  M.pc (M.core_of (hstep Q s)) = S (M.pc (M.core_of s)) /\
  (forall q, M.vals (M.core_of (hstep Q s)) q = M.vals (M.core_of s) q) /\
  (forall q, M.vers (M.core_of (hstep Q s)) q = M.vers (M.core_of s) q) /\
  M.facts (M.core_of (hstep Q s)) = M.mkfact UC.PSlot rs (M.vers (M.core_of s) rs) :: M.facts (M.core_of s) /\
  M.chan (M.core_of (hstep Q s)) = M.chan (M.core_of s) /\
  M.err (M.core_of (hstep Q s)) = false /\
  M.mu (hstep Q s) = M.mu s + 1 /\ M.cert (hstep Q s) = M.cert s.
Proof.
  intros Q s rs He Hf Hh Hl.
  destruct (sm2_fetch_next Q s (M.CHECK UC.PSlot rs) He Hf ltac:(discriminate)) as [Hn Hst].
  rewrite Hst. split; [rewrite Hn; discriminate |].
  assert (Hok : M.check_ok UC.heval (M.core_of s) UC.PSlot rs = true).
  { unfold M.check_ok. rewrite He, Hh. simpl. apply Nat.ltb_lt. exact Hl. }
  assert (Hc : M.core_of (hexec s (M.CHECK UC.PSlot rs)) =
               M.record_fact (M.core_of s) (M.claim (M.core_of s) UC.PSlot rs)).
  { unfold hexec, M.exec, M.cexec. cbn [M.core_of]. rewrite He, Hok. reflexivity. }
  rewrite Hc.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); try reflexivity.
  - exact He.
  - unfold hexec, M.exec. cbn [M.cert]. simpl. destruct (M.cert s); reflexivity.
Qed.

Lemma sm2_step_commit_ok : forall Q s rs,
  M.err (M.core_of s) = false -> M.fetch Q (M.pc (M.core_of s)) = Some (M.COMMIT UC.PSlot rs) ->
  In (M.mkfact UC.PSlot rs (M.vers (M.core_of s) rs)) (M.facts (M.core_of s)) ->
  M.next_instr Q (M.core_of s) <> None /\
  M.pc (M.core_of (hstep Q s)) = S (M.pc (M.core_of s)) /\
  (forall q, M.vals (M.core_of (hstep Q s)) q = M.vals (M.core_of s) q) /\
  (forall q, M.vers (M.core_of (hstep Q s)) q = M.vers (M.core_of s) q) /\
  M.facts (M.core_of (hstep Q s)) = M.facts (M.core_of s) /\
  M.chan (M.core_of (hstep Q s)) = Some (M.mkfact UC.PSlot rs (M.vers (M.core_of s) rs)) /\
  M.err (M.core_of (hstep Q s)) = false /\
  M.mu (hstep Q s) = M.mu s + 1 /\ M.cert (hstep Q s) = M.cert s.
Proof.
  intros Q s rs He Hf Hin.
  destruct (sm2_fetch_next Q s (M.COMMIT UC.PSlot rs) He Hf ltac:(discriminate)) as [Hn Hst].
  rewrite Hst. split; [rewrite Hn; discriminate |].
  assert (Hok : M.commit_ok UC.hprop_eqb (M.core_of s) UC.PSlot rs = true).
  { unfold M.commit_ok. rewrite He. simpl. apply existsb_exists. exists (M.claim (M.core_of s) UC.PSlot rs).
    split; [exact Hin |]. apply (proj2 (M.multi_fact_eqb_eq UC.hprop_eqb UC.hprop_eqb_eq _ _)). reflexivity. }
  assert (Hc : M.core_of (hexec s (M.COMMIT UC.PSlot rs)) =
               M.commit_to (M.core_of s) (M.claim (M.core_of s) UC.PSlot rs)).
  { unfold hexec, M.exec, M.cexec. cbn [M.core_of]. rewrite He, Hok. reflexivity. }
  rewrite Hc.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); try reflexivity.
  - exact He.
  - unfold hexec, M.exec. cbn [M.cert]. simpl. destruct (M.cert s); reflexivity.
Qed.

Lemma sm2_step_certify_ok : forall Q s,
  M.err (M.core_of s) = false -> M.fetch Q (M.pc (M.core_of s)) = Some M.CERTIFY ->
  M.chan (M.core_of s) <> None ->
  M.next_instr Q (M.core_of s) <> None /\
  M.pc (M.core_of (hstep Q s)) = S (M.pc (M.core_of s)) /\
  (forall q, M.vals (M.core_of (hstep Q s)) q = M.vals (M.core_of s) q) /\
  (forall q, M.vers (M.core_of (hstep Q s)) q = M.vers (M.core_of s) q) /\
  M.facts (M.core_of (hstep Q s)) = M.facts (M.core_of s) /\
  M.chan (M.core_of (hstep Q s)) = M.chan (M.core_of s) /\
  M.err (M.core_of (hstep Q s)) = false /\
  M.mu (hstep Q s) = M.mu s + 1 /\ M.cert (hstep Q s) = true.
Proof.
  intros Q s He Hf Hch.
  destruct (sm2_fetch_next Q s M.CERTIFY He Hf ltac:(discriminate)) as [Hn Hst].
  rewrite Hst. split; [rewrite Hn; discriminate |].
  assert (Hok : M.certify_ok (M.core_of s) = true).
  { unfold M.certify_ok. rewrite He. simpl. destruct (M.chan (M.core_of s)); [reflexivity | congruence]. }
  assert (Hc : M.core_of (hexec s M.CERTIFY) = M.goto (M.core_of s) (S (M.pc (M.core_of s)))).
  { unfold hexec, M.exec, M.cexec. cbn [M.core_of]. rewrite He, Hok. reflexivity. }
  rewrite Hc.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); try reflexivity.
  - exact He.
  - unfold hexec, M.exec. cbn [M.cert M.fires]. rewrite Hok. destruct (M.cert s); reflexivity.
Qed.

Lemma sm2_step_check_fail : forall Q s rd,
  M.err (M.core_of s) = false -> M.fetch Q (M.pc (M.core_of s)) = Some (M.CHECK UC.PSlot rd) ->
  M.vals (M.core_of s) rd = 0 ->
  M.next_instr Q (M.core_of s) <> None /\
  (forall q, M.vals (M.core_of (hstep Q s)) q = M.vals (M.core_of s) q) /\
  M.facts (M.core_of (hstep Q s)) = M.facts (M.core_of s) /\
  M.chan (M.core_of (hstep Q s)) = M.chan (M.core_of s) /\
  M.err (M.core_of (hstep Q s)) = true /\
  M.mu (hstep Q s) = M.mu s + 1 /\ M.cert (hstep Q s) = M.cert s.
Proof.
  intros Q s rd He Hf Hz.
  destruct (sm2_fetch_next Q s (M.CHECK UC.PSlot rd) He Hf ltac:(discriminate)) as [Hn Hst].
  rewrite Hst. split; [rewrite Hn; discriminate |].
  assert (Hok : M.check_ok UC.heval (M.core_of s) UC.PSlot rd = false).
  { unfold M.check_ok. rewrite He, Hz. simpl. reflexivity. }
  assert (Hc : M.core_of (hexec s (M.CHECK UC.PSlot rd)) = M.trap (M.core_of s)).
  { unfold hexec, M.exec, M.cexec. cbn [M.core_of]. rewrite He, Hok. reflexivity. }
  rewrite Hc.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))); try reflexivity.
  - unfold hexec, M.exec. cbn [M.cert]. simpl. destruct (M.cert s); reflexivity.
Qed.

(* ================================================================= *)
(* The check loop.                                                    *)
(* ================================================================= *)

Theorem sm2_check_loop : forall Q o r Z rs,
  sm2_inQ Q o (sm2_whilel o r Z [M.CHECK UC.PSlot rs]) ->
  r <> Z -> rs <> r -> rs <> Z ->
  forall n s, M.pc (M.core_of s) = o + 1 -> M.err (M.core_of s) = false ->
  M.vals (M.core_of s) r = n ->
  UC.heval UC.PSlot (M.vals (M.core_of s) rs) = true ->
  length (M.facts (M.core_of s)) + n <= 16 ->
  exists s', sm2_RR Q s s' /\ M.pc (M.core_of s') = o + 7 /\ M.err (M.core_of s') = false /\
    M.vals (M.core_of s') r = 0 /\ M.vals (M.core_of s') Z = M.vals (M.core_of s) Z /\
    (forall q, q <> r -> M.vals (M.core_of s') q = M.vals (M.core_of s) q) /\
    (forall q, q <> r -> q <> Z -> M.vers (M.core_of s') q = M.vers (M.core_of s) q) /\
    M.facts (M.core_of s') = repeat (M.mkfact UC.PSlot rs (M.vers (M.core_of s) rs)) n
                             ++ M.facts (M.core_of s) /\
    M.chan (M.core_of s') = M.chan (M.core_of s) /\
    M.mu s' = M.mu s + n /\ M.cert s' = M.cert s.
Proof.
  intros Q o r Z rs Hin HrZ Hrs1 Hrs2 n s Hp He Hv Hh Hl.
  destruct (sm2_whilel_fetch Q o r Z _ Hin) as (F1 & F2 & F3 & F4 & F5 & Fb).
  simpl length in F3, F4, F5, Fb.
  set (cl := M.mkfact UC.PSlot rs (M.vers (M.core_of s) rs)).
  set (Inv := fun (j : nat) (t : hstate) =>
    (forall q, q <> r -> M.vals (M.core_of t) q = M.vals (M.core_of s) q) /\
    (forall q, q <> r -> q <> Z -> M.vers (M.core_of t) q = M.vers (M.core_of s) q) /\
    M.facts (M.core_of t) = repeat cl j ++ M.facts (M.core_of s) /\
    M.chan (M.core_of t) = M.chan (M.core_of s) /\ M.err (M.core_of t) = false /\
    M.mu t = M.mu s + j /\ M.cert t = M.cert s).
  assert (Hirr : forall j t t', sm2_loose r Z t t' -> Inv j t -> Inv j t').
  { intros j t t' (A & B & (C1 & C2 & C3 & C4 & C5)) (I1 & I2 & I3 & I4 & I5 & I6 & I7).
    unfold Inv. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
    - intros q Hq. rewrite <- (A q Hq). apply I1, Hq.
    - intros q H1 H2. rewrite <- (B q H1 H2). apply I2; assumption.
    - rewrite <- C1. exact I3.
    - rewrite <- C2. exact I4.
    - rewrite <- C3. exact I5.
    - rewrite <- C4. exact I6.
    - rewrite <- C5. exact I7. }
  assert (Hbody : forall j t, j < n -> Inv j t -> M.pc (M.core_of t) = o + 4 ->
    M.err (M.core_of t) = false ->
    exists s1 : hstate, sm2_RR Q t s1 /\ M.pc (M.core_of s1) = o + 4 + 1 /\
      M.err (M.core_of s1) = false /\ Inv (S j) s1 /\
      M.vals (M.core_of s1) r = M.vals (M.core_of t) r /\
      M.vals (M.core_of s1) Z = M.vals (M.core_of t) Z).
  { intros j t Hj (I1 & I2 & I3 & I4 & I5 & I6 & I7) Hpt Het.
    assert (Hfe : M.fetch Q (M.pc (M.core_of t)) = Some (M.CHECK UC.PSlot rs)).
    { rewrite Hpt. pose proof (Fb 0 ltac:(simpl; lia)) as Hf0. rewrite Nat.add_0_r in Hf0. rewrite Hf0. reflexivity. }
    assert (Hv1 : M.vals (M.core_of t) rs = M.vals (M.core_of s) rs) by (apply I1; congruence).
    assert (Hl1 : length (M.facts (M.core_of t)) < 16).
    { rewrite I3, app_length, repeat_length. lia. }
    destruct (sm2_step_check_ok Q t rs Het Hfe ltac:(rewrite Hv1; exact Hh) Hl1)
      as (N1 & P1 & V1 & W1 & Fa1 & C1 & E1 & Mu1 & Ce1).
    exists (hstep Q t). refine (conj _ (conj _ (conj E1 (conj _ (conj _ _))))).
    - eapply sm2_RR_one. exact N1.
    - rewrite P1, Hpt. lia.
    - unfold Inv. refine (conj _ (conj _ (conj _ (conj _ (conj E1 (conj _ _)))))).
      + intros q Hq. rewrite V1. apply I1, Hq.
      + intros q H1 H2. rewrite W1. apply I2; assumption.
      + rewrite Fa1, I3. simpl repeat.
        assert (Hw1 : M.vers (M.core_of t) rs = M.vers (M.core_of s) rs) by (apply I2; congruence).
        rewrite Hw1. reflexivity.
      + rewrite C1. exact I4.
      + rewrite Mu1, I6. lia.
      + rewrite Ce1. exact I7.
    - rewrite V1. reflexivity.
    - rewrite V1. reflexivity. }
  pose proof (sm2_while Q o r Z 1 n Inv HrZ F1 F2 F3 F4 F5 Hirr Hbody) as Hw.
  specialize (Hw n 0 s ltac:(lia)).
  assert (HI0 : Inv 0 s).
  { unfold Inv. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); try reflexivity.
    - exact He.
    - lia. }
  destruct (Hw HI0 Hp He Hv) as (s' & R & P & E & V0 & (J1 & J2 & J3 & J4 & J5 & J6 & J7) & VZ).
  exists s'. simpl in J3.
  refine (conj R (conj _ (conj E (conj V0 (conj VZ (conj J1 (conj J2 (conj J3 (conj J4 (conj _ J7)))))))))).
  - rewrite P. lia.
  - rewrite J6. lia.
Qed.

Print Assumptions sm2_fan_spec.
Print Assumptions sm2_check_loop.
