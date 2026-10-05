(** SmLoops.v: runs of host programs, and counting loops with instructions
    in their bodies.

    This file works on the host machine (EarnedMulti.v with the property
    PSlot of UniversalCodes.v), with a program given as a list of host
    instructions and a position in it given by absolute line numbers.

    [sm2_RR Q s s'] says the program Q, started in state s, reaches s' by a
    run in which every state before s' still has a next instruction. It is
    reflexive and transitive, so a long run is a chain of short ones, and a
    run of this kind never stops early.

    One-step lemmas for INC and DEC give every field of the state after the
    step. Then the counting loop

      line o+1        DEC r (o+4)       counter r positive: take one, go to the body
      line o+2        INC Z             counter zero: set up an unconditional jump
      line o+3        DEC Z (o+6+L)     jump out, past the loop
      lines o+4 ..    the body, L lines
      line o+4+L      INC Z
      line o+5+L      DEC Z (o+1)       unconditional jump back to the test

    runs its body once for every unit in register r, whatever the body is,
    provided the body leaves the registers r and Z alone and the invariant
    that describes what the body has done so far does not read the counter,
    the jump register or the program counter [sm2_while]. The jump pair
    INC Z, DEC Z is a jump that costs nothing and changes no value.

    A body made of a row of INC instructions [sm2_incs_chain], and the effect
    of the whole loop on every register [sm2_fan_loop].

    Dependencies: Coq standard library, EarnedMulti.v, UniversalCodes.v and
    SmHostBlocks.v. No axioms, no Admitted.                                *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Sm.SmHostBlocks.
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
(* Runs in which no state before the last one has stopped.            *)
(* ================================================================= *)

Inductive sm2_RR (Q : list hinstr) : hstate -> hstate -> Prop :=
| sm2_RR_refl : forall s, sm2_RR Q s s
| sm2_RR_step : forall s s'',
    M.next_instr Q (M.core_of s) <> None ->
    sm2_RR Q (hstep Q s) s'' -> sm2_RR Q s s''.

Lemma sm2_RR_trans : forall Q s s' s'', sm2_RR Q s s' -> sm2_RR Q s' s'' -> sm2_RR Q s s''.
Proof.
  intros Q s s' s'' H. induction H as [s | s s' Hn H IH]; intro H2;
    [exact H2 | eapply sm2_RR_step; [exact Hn | apply IH, H2]].
Qed.

Lemma sm2_RR_one : forall Q s, M.next_instr Q (M.core_of s) <> None -> sm2_RR Q s (hstep Q s).
Proof. intros Q s Hn. eapply sm2_RR_step; [exact Hn | apply sm2_RR_refl]. Qed.

Lemma sm2_RR_run : forall Q s s', sm2_RR Q s s' -> exists n, hrun_prog n Q s = s'.
Proof.
  intros Q s s' H. induction H as [s | s s'' Hn H IH].
  - exists 0. reflexivity.
  - destruct IH as [n Hn']. exists (S n). exact Hn'.
Qed.

(* The same run, as a number of steps with every earlier state running. *)
Lemma sm2_RR_steps : forall Q s s', sm2_RR Q s s' ->
  exists n, hrun_prog n Q s = s' /\
            forall m, m < n -> M.next_instr Q (M.core_of (hrun_prog m Q s)) <> None.
Proof.
  intros Q s s' H. induction H as [s | s s'' Hn H IH].
  - exists 0. split; [reflexivity | intros m Hm; lia].
  - destruct IH as [n [Hr Hall]]. exists (S n). split; [exact Hr |].
    intros m Hm. destruct m as [| m].
    + exact Hn.
    + simpl. apply Hall. lia.
Qed.

(* A run that stops in a state that has a next instruction is not a run
   that has stopped. *)
Lemma sm2_RR_last : forall Q s s', sm2_RR Q s s' ->
  M.halted Q (M.core_of s) -> s' = s.
Proof.
  intros Q s s' H Hh. inversion H; subst; [reflexivity |].
  exfalso. unfold M.halted in Hh. contradiction.
Qed.

(* ================================================================= *)
(* Fields a plain step leaves alone.                                  *)
(* ================================================================= *)

Definition sm2_pfe (s s' : hstate) : Prop :=
  M.facts (M.core_of s) = M.facts (M.core_of s') /\
  M.chan (M.core_of s) = M.chan (M.core_of s') /\
  M.err (M.core_of s) = M.err (M.core_of s') /\
  M.mu s = M.mu s' /\ M.cert s = M.cert s'.

Lemma sm2_pfe_refl : forall s, sm2_pfe s s.
Proof. intro s. repeat split. Qed.

Lemma sm2_pfe_trans : forall s s' s'', sm2_pfe s s' -> sm2_pfe s' s'' -> sm2_pfe s s''.
Proof.
  intros s s' s'' (A & B & C & D & E) (A' & B' & C' & D' & E').
  repeat split; congruence.
Qed.

Lemma sm2_pfe_sym : forall s s', sm2_pfe s s' -> sm2_pfe s' s.
Proof. intros s s' (A & B & C & D & E). repeat split; congruence. Qed.

(* ================================================================= *)
(* One step of INC and DEC.                                           *)
(* ================================================================= *)

Lemma sm2_fetch_next : forall Q s i,
  M.err (M.core_of s) = false -> M.fetch Q (M.pc (M.core_of s)) = Some i -> i <> M.HALT ->
  M.next_instr Q (M.core_of s) = Some i /\ hstep Q s = hexec s i.
Proof.
  intros Q s i He Hf Hi.
  assert (Hn : M.next_instr Q (M.core_of s) = Some i) by (apply sm_next_intro; assumption).
  split; [exact Hn |]. unfold hstep, M.step. rewrite Hn. reflexivity.
Qed.

Lemma sm2_step_inc : forall Q s r,
  M.err (M.core_of s) = false -> M.fetch Q (M.pc (M.core_of s)) = Some (M.INC r) ->
  M.next_instr Q (M.core_of s) <> None /\
  M.pc (M.core_of (hstep Q s)) = S (M.pc (M.core_of s)) /\
  (forall q, M.vals (M.core_of (hstep Q s)) q =
             if Nat.eqb q r then S (M.vals (M.core_of s) r) else M.vals (M.core_of s) q) /\
  (forall q, q <> r -> M.vers (M.core_of (hstep Q s)) q = M.vers (M.core_of s) q) /\
  sm2_pfe s (hstep Q s).
Proof.
  intros Q s r He Hf.
  destruct (sm2_fetch_next Q s (M.INC r) He Hf ltac:(discriminate)) as [Hn Hst].
  rewrite Hst. split; [rewrite Hn; discriminate |].
  destruct (sm_plain_exec UC.hprop_eqb UC.heval s (M.INC r) eq_refl) as (A & B & C & D & E).
  assert (Hc : M.core_of (hexec s (M.INC r)) =
                M.write (M.core_of s) r (S (M.vals (M.core_of s) r)) (S (M.pc (M.core_of s)))).
  { unfold hexec, M.exec, M.cexec. cbn [M.core_of]. rewrite He. reflexivity. }
  rewrite Hc.
  refine (conj _ (conj _ (conj _ _))).
  - reflexivity.
  - intro q. rewrite M.multi_val_write. destruct (Nat.eqb_spec r q), (Nat.eqb_spec q r); subst; congruence.
  - intros q Hq. rewrite M.multi_ver_write. destruct (Nat.eqb_spec r q); [congruence | reflexivity].
  - unfold sm2_pfe. refine (conj _ (conj _ (conj _ (conj _ _)))); symmetry; assumption.
Qed.

Lemma sm2_step_dec_pos : forall Q s r j m,
  M.err (M.core_of s) = false -> M.fetch Q (M.pc (M.core_of s)) = Some (M.DEC r j) ->
  M.vals (M.core_of s) r = S m ->
  M.next_instr Q (M.core_of s) <> None /\
  M.pc (M.core_of (hstep Q s)) = j /\
  (forall q, M.vals (M.core_of (hstep Q s)) q =
             if Nat.eqb q r then m else M.vals (M.core_of s) q) /\
  (forall q, q <> r -> M.vers (M.core_of (hstep Q s)) q = M.vers (M.core_of s) q) /\
  sm2_pfe s (hstep Q s).
Proof.
  intros Q s r j m He Hf Hv.
  destruct (sm2_fetch_next Q s (M.DEC r j) He Hf ltac:(discriminate)) as [Hn Hst].
  rewrite Hst. split; [rewrite Hn; discriminate |].
  destruct (sm_plain_exec UC.hprop_eqb UC.heval s (M.DEC r j) eq_refl) as (A & B & C & D & E).
  assert (Hc : M.core_of (hexec s (M.DEC r j)) = M.write (M.core_of s) r m j).
  { unfold hexec, M.exec, M.cexec. cbn [M.core_of]. rewrite He, Hv. reflexivity. }
  rewrite Hc.
  refine (conj _ (conj _ (conj _ _))).
  - reflexivity.
  - intro q. rewrite M.multi_val_write. destruct (Nat.eqb_spec r q), (Nat.eqb_spec q r); subst; congruence.
  - intros q Hq. rewrite M.multi_ver_write. destruct (Nat.eqb_spec r q); [congruence | reflexivity].
  - unfold sm2_pfe. refine (conj _ (conj _ (conj _ (conj _ _)))); symmetry; assumption.
Qed.

Lemma sm2_step_dec_zero : forall Q s r j,
  M.err (M.core_of s) = false -> M.fetch Q (M.pc (M.core_of s)) = Some (M.DEC r j) ->
  M.vals (M.core_of s) r = 0 ->
  M.next_instr Q (M.core_of s) <> None /\
  M.pc (M.core_of (hstep Q s)) = S (M.pc (M.core_of s)) /\
  (forall q, M.vals (M.core_of (hstep Q s)) q = M.vals (M.core_of s) q) /\
  (forall q, M.vers (M.core_of (hstep Q s)) q = M.vers (M.core_of s) q) /\
  sm2_pfe s (hstep Q s).
Proof.
  intros Q s r j He Hf Hv.
  destruct (sm2_fetch_next Q s (M.DEC r j) He Hf ltac:(discriminate)) as [Hn Hst].
  rewrite Hst. split; [rewrite Hn; discriminate |].
  destruct (sm_plain_exec UC.hprop_eqb UC.heval s (M.DEC r j) eq_refl) as (A & B & C & D & E).
  assert (Hc : M.core_of (hexec s (M.DEC r j)) = M.goto (M.core_of s) (S (M.pc (M.core_of s)))).
  { unfold hexec, M.exec, M.cexec. cbn [M.core_of]. rewrite He, Hv. reflexivity. }
  rewrite Hc.
  refine (conj _ (conj _ (conj _ _))).
  - reflexivity.
  - intro q. reflexivity.
  - intro q. reflexivity.
  - unfold sm2_pfe. refine (conj _ (conj _ (conj _ (conj _ _)))); symmetry; assumption.
Qed.

(* ================================================================= *)
(* The counting loop.                                                 *)
(* ================================================================= *)

Definition sm2_whead (o r Z L : nat) : list hinstr :=
  [M.DEC r (o + 4); M.INC Z; M.DEC Z (o + 6 + L)].

Definition sm2_wtail (o Z : nat) : list hinstr := [M.INC Z; M.DEC Z (o + 1)].

Definition sm2_whilel (o r Z : nat) (body : list hinstr) : list hinstr :=
  sm2_whead o r Z (length body) ++ body ++ sm2_wtail o Z.

Lemma sm2_whilel_length : forall o r Z body, length (sm2_whilel o r Z body) = 5 + length body.
Proof. intros. unfold sm2_whilel. rewrite app_length, app_length. simpl. lia. Qed.

(* The lines of a block inside a program that holds it at offset o. *)
Definition sm2_inQ (Q : list hinstr) (o : nat) (g : list hinstr) : Prop :=
  forall p, 1 <= p <= length g -> M.fetch Q (o + p) = M.fetch g p.

Lemma sm2_inQ_app : forall L1 g L2, sm2_inQ (L1 ++ g ++ L2) (length L1) g.
Proof.
  intros L1 g L2 p Hp. destruct p as [| p]; [lia |].
  replace (length L1 + S p) with (S (length L1 + p)) by lia. simpl M.fetch.
  rewrite nth_error_app2 by lia. replace (length L1 + p - length L1) with p by lia.
  rewrite nth_error_app1 by lia. reflexivity.
Qed.

(* Two states that differ at most in the counter r, the jump register Z, the
   versions of those two, and the program counter. *)
Definition sm2_loose (r Z : nat) (s s' : hstate) : Prop :=
  (forall q, q <> r -> M.vals (M.core_of s) q = M.vals (M.core_of s') q) /\
  (forall q, q <> r -> q <> Z -> M.vers (M.core_of s) q = M.vers (M.core_of s') q) /\
  sm2_pfe s s'.

Lemma sm2_loose_trans : forall r Z s s' s'', sm2_loose r Z s s' -> sm2_loose r Z s' s'' ->
  sm2_loose r Z s s''.
Proof.
  intros r Z s s' s'' (A & B & C) (A' & B' & C'). split; [| split].
  - intros q Hq. rewrite A by exact Hq. apply A', Hq.
  - intros q H1 H2. rewrite B by assumption. apply B'; assumption.
  - eapply sm2_pfe_trans; eauto.
Qed.

Section While.

Variables (Q : list hinstr) (o r Z L N : nat).
Variable Inv : nat -> hstate -> Prop.
Hypothesis HrZ : r <> Z.
Hypothesis F1 : M.fetch Q (o + 1) = Some (M.DEC r (o + 4)).
Hypothesis F2 : M.fetch Q (o + 2) = Some (M.INC Z).
Hypothesis F3 : M.fetch Q (o + 3) = Some (M.DEC Z (o + 6 + L)).
Hypothesis F4 : M.fetch Q (o + 4 + L) = Some (M.INC Z).
Hypothesis F5 : M.fetch Q (o + 5 + L) = Some (M.DEC Z (o + 1)).
Hypothesis Hirr : forall j s s', sm2_loose r Z s s' -> Inv j s -> Inv j s'.
Hypothesis Hbody : forall j s, j < N -> Inv j s -> M.pc (M.core_of s) = o + 4 ->
  M.err (M.core_of s) = false ->
  exists s1, sm2_RR Q s s1 /\ M.pc (M.core_of s1) = o + 4 + L /\ M.err (M.core_of s1) = false /\
             Inv (S j) s1 /\ M.vals (M.core_of s1) r = M.vals (M.core_of s) r /\
             M.vals (M.core_of s1) Z = M.vals (M.core_of s) Z.

Lemma sm2_while_exit : forall j s, Inv j s -> M.pc (M.core_of s) = o + 1 ->
  M.err (M.core_of s) = false -> M.vals (M.core_of s) r = 0 ->
  exists s', sm2_RR Q s s' /\ M.pc (M.core_of s') = o + 6 + L /\ M.err (M.core_of s') = false /\
             M.vals (M.core_of s') r = 0 /\ Inv j s' /\ M.vals (M.core_of s') Z = M.vals (M.core_of s) Z.
Proof.
  intros j s HI Hp He Hv.
  assert (F1' : M.fetch Q (M.pc (M.core_of s)) = Some (M.DEC r (o + 4))) by (rewrite Hp; exact F1).
  destruct (sm2_step_dec_zero Q s r (o + 4) He F1' Hv) as (N1 & P1 & V1 & W1 & E1).
  set (s1 := hstep Q s) in *.
  assert (He1 : M.err (M.core_of s1) = false) by (destruct E1 as (_ & _ & C & _); rewrite <- C; exact He).
  assert (F2' : M.fetch Q (M.pc (M.core_of s1)) = Some (M.INC Z)) by (rewrite P1, Hp; replace (S (o + 1)) with (o + 2) by lia; exact F2).
  destruct (sm2_step_inc Q s1 Z He1 F2') as (N2 & P2 & V2 & W2 & E2).
  set (s2 := hstep Q s1) in *.
  assert (He2 : M.err (M.core_of s2) = false) by (destruct E2 as (_ & _ & C & _); rewrite <- C; exact He1).
  assert (F3' : M.fetch Q (M.pc (M.core_of s2)) = Some (M.DEC Z (o + 6 + L))).
  { rewrite P2, P1, Hp. replace (S (S (o + 1))) with (o + 3) by lia. exact F3. }
  assert (HZ2 : M.vals (M.core_of s2) Z = S (M.vals (M.core_of s) Z)).
  { rewrite V2, Nat.eqb_refl, V1. reflexivity. }
  destruct (sm2_step_dec_pos Q s2 Z (o + 6 + L) (M.vals (M.core_of s) Z) He2 F3' HZ2)
    as (N3 & P3 & V3 & W3 & E3).
  exists (hstep Q s2). split; [| split; [exact P3 | split]].
  - eapply sm2_RR_step; [exact N1 |]. eapply sm2_RR_step; [exact N2 |].
    eapply sm2_RR_step; [exact N3 |]. apply sm2_RR_refl.
  - destruct E3 as (_ & _ & C & _). rewrite <- C. exact He2.
  - split; [| split].
    + rewrite V3. destruct (Nat.eqb_spec r Z); [congruence |].
      rewrite V2. destruct (Nat.eqb_spec r Z); [congruence |]. rewrite V1. exact Hv.
    + eapply Hirr; [| exact HI]. split; [| split].
      * intros q Hq. rewrite V3. destruct (Nat.eqb_spec q Z) as [-> | Hz].
        -- reflexivity.
        -- rewrite V2. destruct (Nat.eqb_spec q Z); [congruence |]. rewrite V1. reflexivity.
      * intros q Hq1 Hq2. rewrite W3 by exact Hq2. rewrite W2 by exact Hq2. rewrite W1. reflexivity.
      * eapply sm2_pfe_trans; [exact E1 |]. eapply sm2_pfe_trans; [exact E2 | exact E3].
    + rewrite V3, Nat.eqb_refl. reflexivity.
Qed.

(* One pass: the counter is positive, the body runs, and the jump goes back. *)
Lemma sm2_while_trip : forall j m s, j < N -> Inv j s -> M.pc (M.core_of s) = o + 1 ->
  M.err (M.core_of s) = false -> M.vals (M.core_of s) r = S m ->
  exists s', sm2_RR Q s s' /\ M.pc (M.core_of s') = o + 1 /\ M.err (M.core_of s') = false /\
             M.vals (M.core_of s') r = m /\ Inv (S j) s' /\ M.vals (M.core_of s') Z = M.vals (M.core_of s) Z.
Proof.
  intros j m s HjN HI Hp He Hv.
  assert (F1' : M.fetch Q (M.pc (M.core_of s)) = Some (M.DEC r (o + 4))) by (rewrite Hp; exact F1).
  destruct (sm2_step_dec_pos Q s r (o + 4) m He F1' Hv) as (N1 & P1 & V1 & W1 & E1).
  set (sd := hstep Q s) in *.
  assert (Hed : M.err (M.core_of sd) = false) by (destruct E1 as (_ & _ & C & _); rewrite <- C; exact He).
  assert (HId : Inv j sd).
  { eapply Hirr; [| exact HI]. split; [| split; [| exact E1]].
    - intros q Hq. rewrite V1. destruct (Nat.eqb_spec q r); [congruence | reflexivity].
    - intros q Hq1 Hq2. rewrite W1 by exact Hq1. reflexivity. }
  destruct (Hbody j sd HjN HId P1 Hed) as (se & Rse & Pse & Ese & Ise & Vrse & VZse).
  assert (F4' : M.fetch Q (M.pc (M.core_of se)) = Some (M.INC Z)) by (rewrite Pse; exact F4).
  destruct (sm2_step_inc Q se Z Ese F4') as (N2 & P2 & V2 & W2 & E2).
  set (s2 := hstep Q se) in *.
  assert (He2 : M.err (M.core_of s2) = false) by (destruct E2 as (_ & _ & C & _); rewrite <- C; exact Ese).
  assert (F5' : M.fetch Q (M.pc (M.core_of s2)) = Some (M.DEC Z (o + 1))).
  { rewrite P2, Pse. replace (S (o + 4 + L)) with (o + 5 + L) by lia. exact F5. }
  assert (HZ2 : M.vals (M.core_of s2) Z = S (M.vals (M.core_of se) Z)).
  { rewrite V2, Nat.eqb_refl. reflexivity. }
  destruct (sm2_step_dec_pos Q s2 Z (o + 1) (M.vals (M.core_of se) Z) He2 F5' HZ2)
    as (N3 & P3 & V3 & W3 & E3).
  exists (hstep Q s2). split; [| split; [exact P3 | split]].
  - eapply sm2_RR_step; [exact N1 |].
    eapply sm2_RR_trans; [exact Rse |].
    eapply sm2_RR_step; [exact N2 |].
    eapply sm2_RR_step; [exact N3 |]. apply sm2_RR_refl.
  - destruct E3 as (_ & _ & C & _). rewrite <- C. exact He2.
  - split; [| split].
    + rewrite V3. destruct (Nat.eqb_spec r Z); [congruence |].
      rewrite V2. destruct (Nat.eqb_spec r Z); [congruence |].
      rewrite Vrse, V1, Nat.eqb_refl. reflexivity.
    + eapply Hirr; [| exact Ise]. split; [| split].
      * intros q Hq. rewrite V3. destruct (Nat.eqb_spec q Z) as [-> | Hz].
        -- reflexivity.
        -- rewrite V2. destruct (Nat.eqb_spec q Z); [congruence | reflexivity].
      * intros q Hq1 Hq2. rewrite W3 by exact Hq2. rewrite W2 by exact Hq2. reflexivity.
      * eapply sm2_pfe_trans; [exact E2 |]. exact E3.
    + rewrite V3, Nat.eqb_refl. rewrite VZse. rewrite V1.
      destruct (Nat.eqb_spec Z r); [congruence | reflexivity].
Qed.

Theorem sm2_while : forall n j s, j + n <= N -> Inv j s -> M.pc (M.core_of s) = o + 1 ->
  M.err (M.core_of s) = false -> M.vals (M.core_of s) r = n ->
  exists s', sm2_RR Q s s' /\ M.pc (M.core_of s') = o + 6 + L /\ M.err (M.core_of s') = false /\
             M.vals (M.core_of s') r = 0 /\ Inv (j + n) s' /\ M.vals (M.core_of s') Z = M.vals (M.core_of s) Z.
Proof.
  induction n as [| n IH]; intros j s HjN HI Hp He Hv.
  - destruct (sm2_while_exit j s HI Hp He Hv) as (s' & H1 & H2 & H3 & H4 & H5 & H6).
    exists s'. rewrite Nat.add_0_r. repeat split; assumption.
  - destruct (sm2_while_trip j n s ltac:(lia) HI Hp He Hv) as (s1 & R1 & P1 & E1 & V1 & I1 & Z1).
    destruct (IH (S j) s1 ltac:(lia) I1 P1 E1 V1) as (s' & R2 & P2 & E2 & V2 & I2 & Z2).
    exists s'. split; [eapply sm2_RR_trans; eauto |].
    repeat split; try assumption.
    + replace (j + S n) with (S j + n) by lia. exact I2.
    + rewrite Z2. exact Z1.
Qed.

End While.

(* ================================================================= *)
(* A body made of INC instructions.                                   *)
(* ================================================================= *)

Lemma sm2_incs_chain : forall ds Q s,
  M.err (M.core_of s) = false ->
  (forall i, i < length ds -> M.fetch Q (M.pc (M.core_of s) + i) = Some (M.INC (nth i ds 0))) ->
  exists s1, sm2_RR Q s s1 /\ M.pc (M.core_of s1) = M.pc (M.core_of s) + length ds /\
             M.err (M.core_of s1) = false /\
             (forall q, M.vals (M.core_of s1) q = M.vals (M.core_of s) q + count_occ Nat.eq_dec ds q) /\
             (forall q, count_occ Nat.eq_dec ds q = 0 -> M.vers (M.core_of s1) q = M.vers (M.core_of s) q) /\
             sm2_pfe s s1.
Proof.
  induction ds as [| d ds IH]; intros Q s He Hf.
  - exists s. refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + apply sm2_RR_refl.
    + simpl. lia.
    + exact He.
    + intro q. simpl. lia.
    + intros q _. reflexivity.
    + apply sm2_pfe_refl.
  - assert (Hf0 : M.fetch Q (M.pc (M.core_of s)) = Some (M.INC d)).
    { specialize (Hf 0 ltac:(simpl; lia)). simpl in Hf. rewrite Nat.add_0_r in Hf. exact Hf. }
    destruct (sm2_step_inc Q s d He Hf0) as (N1 & P1 & V1 & W1 & E1).
    set (s1 := hstep Q s) in *.
    assert (He1 : M.err (M.core_of s1) = false) by (destruct E1 as (_ & _ & C & _); rewrite <- C; exact He).
    destruct (IH Q s1 He1) as (s2 & R2 & P2 & E2 & V2 & W2 & PF2).
    + intros i Hi. rewrite P1. replace (S (M.pc (M.core_of s)) + i) with (M.pc (M.core_of s) + S i) by lia.
      specialize (Hf (S i) ltac:(simpl; lia)). simpl in Hf. exact Hf.
    + exists s2. split; [eapply sm2_RR_step; [exact N1 | exact R2] |].
      split; [rewrite P2, P1; simpl; lia |]. split; [exact E2 |]. split.
      * intro q. rewrite V2, V1. simpl. destruct (Nat.eq_dec d q) as [-> | Hne].
        -- rewrite Nat.eqb_refl. lia.
        -- destruct (Nat.eqb_spec q d); [congruence | lia].
      * split.
        -- intros q Hq. simpl in Hq. destruct (Nat.eq_dec d q) as [-> | Hne]; [discriminate |].
           rewrite W2 by exact Hq. apply W1. congruence.
        -- eapply sm2_pfe_trans; [exact E1 | exact PF2].
Qed.

Print Assumptions sm2_while.
Print Assumptions sm2_incs_chain.
