(** NeutralUnivDef.v: a NEUTRAL universal machine, stated without CHECK, COMMIT or
    CERTIFY, and the general facts about it.

    Built on UMachDef.v (guest classes [gclass], hosts with stored programs
    [host], runs [hr]/[hl], the book's clause (1) [clause1] and matching
    points [match_at]), UMachRegHost.v (register hosts [reg_host]) and
    NeutralComplete.v (neutral-complete machines).

    The definition [neutral_universal C H Obs obs K] (section 1):

      (N0) the host is neutral-complete, and its computing moves are
           exactly its counter moves;
      (N1) halting matched, and the halted host matches the guest's last
           state;
      (N2) the run passes IN ORDER (strictly increasing host times f m)
           through host states that decode to the guest's states, with the
           host's record equal to the guest's (latched) record and the
           host's ledger the guest's plus at most K;
      (N3) the rise is the program's: there is a set of program lines
           [raise], fixed with the program, such that every record move the
           program executes either traps or sets record := record || raise(line);
      (N4) register host: every move is INC/DEC/HALT at price 0 or a
           record move at price 1 that leaves the registers alone and
           advances or traps; the next move depends only on line and trap;
      (N5) clean load: one template [tpl], fixed with the program, gives the
           host's start from a register file (registers = the file, line
           fixed, no trap, record down); the guest enters only through the
           register file [code i]; the decode reads only registers.

    General facts proved here:
      naive_rise_free     the suggested neutral form of "earned again"
                          ("every rise of the host's record is made by one of
                          its own non-computing moves, at a point where the
                          guest's record rises, and never otherwise") follows
                          from (N1)+(N2) and a permanent host record alone;
      nr_determined       under (N3)+(N4) the line, the registers, the record
                          and the ledger of a run are determined by the line,
                          registers and record it starts from, whatever else
                          the state holds;
      toll_floor / surcharge_floor
                          lower bounds on the surcharge from the host's raise
                          floor;
      pay_needed          a guest that pays while its record is down forces
                          the host to execute a record move that does not
                          raise (a PAY in effect);
      chains_to_fun       decidable matching + finite increasing chains give
                          one strictly increasing matching function.        *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Logic.ConstructiveEpsilon.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Minimal.ThieleComplete.
Require Import Minimal.NeutralComplete.

(* ================================================================= *)
(* 0. Hosts as machines; kinds.                                       *)
(* ================================================================= *)

Definition hmach (H : host) : machine := mk_machine (hS H) (hI H) (hstep H) (hcost H) (hflag H).

Definition is_counter (k : rkind) : bool := match k with RRec => false | _ => true end.

(* ================================================================= *)
(* 1. The definition.                                                 *)
(* ================================================================= *)

Section Def.
Variable C : gclass.
Variable H : host.
Variable Obs : gi C -> Type.
Variable obs : forall i, gS C i -> Obs i.

(* (N0) *)
Definition host_nc (R : reg_host H) : Prop :=
  exists J : neutral_interface (hmach H),
    neutral_complete_with J /\ forall m, ni_isbase J m = is_counter (b_kind R m).

(* (N3) the rise is the program's. *)
Definition line_raise (R : reg_host H) (P : hP H) (raise : nat -> bool) : Prop :=
  forall s m, b_err R s = false -> hnext H P s = Some m -> b_kind R m = RRec ->
    b_err R (hstep H s m) = true \/
    hflag H (hstep H s m) = hflag H s || raise (b_pc R s).

(* (N5) the load template. *)
Definition clean_template (R : reg_host H) (tpl : (nat -> nat) -> hS H) : Prop :=
  (forall rho x, b_reg R (tpl rho) x = rho x) /\
  (forall rho rho', b_pc R (tpl rho) = b_pc R (tpl rho')) /\
  (forall rho, b_err R (tpl rho) = false) /\
  (forall rho, hflag H (tpl rho) = false).

(* (N1) halting matched, with the halted state matched. *)
Definition halt_clause (K : nat) (P : hP H) (h0 : hS H) (i : gi C)
  (decode : hS H -> Obs i) : Prop :=
  clause1 C H P h0 i /\
  forall m0, live_before i m0 -> gnext C i (grun i m0) = None ->
    exists n, hnext H P (hr P h0 n) = None /\ match_at C H Obs obs K P h0 i decode n m0.

(* (N2) in order. *)
Definition in_order (K : nat) (P : hP H) (h0 : hS H) (i : gi C)
  (decode : hS H -> Obs i) (f : nat -> nat) : Prop :=
  (forall m, live_before i (S m) -> f m < f (S m)) /\
  (forall m, live_before i m -> match_at C H Obs obs K P h0 i decode (f m) m).

Definition neutral_universal (K : nat) : Prop :=
  exists (P : hP H) (R : reg_host H) (raise : nat -> bool)
         (tpl : (nat -> nat) -> hS H) (code : gi C -> nat -> nat)
         (dec : forall i, (nat -> nat) -> Obs i),
    host_nc R /\ line_raise R P raise /\ clean_template R tpl /\
    forall i,
      halt_clause K P (tpl (code i)) i (fun h => dec i (b_reg R h)) /\
      exists f, in_order K P (tpl (code i)) i (fun h => dec i (b_reg R h)) f.

(* The same with the order dropped (one matching time per guest step). *)
Definition neutral_universal_weak (K : nat) : Prop :=
  exists (P : hP H) (R : reg_host H) (raise : nat -> bool)
         (tpl : (nat -> nat) -> hS H) (code : gi C -> nat -> nat)
         (dec : forall i, (nat -> nat) -> Obs i),
    host_nc R /\ line_raise R P raise /\ clean_template R tpl /\
    forall i,
      halt_clause K P (tpl (code i)) i (fun h => dec i (b_reg R h)) /\
      forall m, live_before i m -> exists n,
        match_at C H Obs obs K P (tpl (code i)) i (fun h => dec i (b_reg R h)) n m.

Theorem neutral_universal_weakens : forall K, neutral_universal K -> neutral_universal_weak K.
Proof.
  intros K (P & R & ra & tpl & code & dec & H0 & H3 & H5 & Hall).
  exists P, R, ra, tpl, code, dec. split; [exact H0 |]. split; [exact H3 |]. split; [exact H5 |].
  intros i. destruct (Hall i) as (H1 & f & _ & Hm). split; [exact H1 |].
  intros m Hl. exists (f m). apply Hm, Hl.
Qed.

End Def.

(* ================================================================= *)
(* 2. Run facts.                                                      *)
(* ================================================================= *)

Section RunFacts.
Variable H : host.
Variable P : hP H.
Hypothesis Hperm : forall s m, hflag H s = true -> hflag H (hstep H s m) = true.

Lemma hr_flag_mono : forall h a b, a <= b -> hflag H (hr P h a) = true -> hflag H (hr P h b) = true.
Proof.
  intros h a b Hab Ha. replace b with (a + (b - a)) by lia. rewrite hr_add.
  generalize (hr P h a) Ha. generalize (b - a). clear - Hperm. induction n as [| n IH]; intros s Hs; [exact Hs |].
  simpl. destruct (hnext H P s); [apply IH, Hperm, Hs | exact Hs].
Qed.

Lemma hl_mono : forall h a b, a <= b -> hl P h a <= hl P h b.
Proof.
  intros h a b Hab. replace b with (a + (b - a)) by lia. rewrite hl_add. lia.
Qed.

(* Discrete intermediate values: a flag down at a and up at b rose at some n in [a, b). *)
Lemma flag_rises_between : forall h a b, hflag H (hr P h a) = false -> hflag H (hr P h b) = true ->
  exists n, a <= n < b /\ hflag H (hr P h n) = false /\ hflag H (hr P h (S n)) = true.
Proof.
  intros h a b Ha Hb. destruct (le_lt_dec b a) as [Hle | Hlt].
  - exfalso. assert (b = a \/ b < a) as [-> | Hl] by lia; [congruence |].
    rewrite (hr_flag_mono h b a ltac:(lia) Hb) in Ha. discriminate.
  - replace b with (a + (b - a)) in * by lia. clear Hlt.
    remember (b - a) as d eqn:Hd. clear Hd b. revert Hb. induction d as [| d IH]; intros Hb.
    + rewrite Nat.add_0_r in Hb. congruence.
    + destruct (hflag H (hr P h (a + d))) eqn:E.
      * destruct (IH eq_refl) as (n & Hn & H1 & H2). exists n. split; [lia | auto].
      * exists (a + d). split; [lia |]. split; [exact E |]. replace (S (a + d)) with (a + S d) by lia. exact Hb.
Qed.

(* The toll on runs: a raised flag costs at least 1 from a lowered start. *)
Theorem toll_floor : forall h n, hflag H h = false -> hflag H (hr P h n) = true -> hl P h n >= 1.
Proof.
  intros h n. revert h. induction n as [| n IH]; intros h H0 H1; [simpl in H1; congruence |].
  simpl in H1 |- *. destruct (hnext H P h) as [m |] eqn:E; [| congruence].
  destruct (hflag H (hstep H h m)) eqn:F.
  - pose proof (htoll H h m H0 F). lia.
  - pose proof (IH _ F H1). lia.
Qed.

End RunFacts.

(* A guest whose reading is permanent has its latch equal to its reading. *)
Lemma glat_read : forall (C : gclass) (i : gi C),
  (forall s m, gread C i s = true -> gread C i (gstep C i s m) = true) ->
  forall m, glat i m = gread C i (grun i m).
Proof.
  intros C i Hp m. induction m as [| m IH]; [reflexivity |].
  unfold glat, grun in *.
  change (glatch (gstart C i) (S m)) with
    (glatch (gstart C i) m || gread C i (gr (gstart C i) (S m))).
  rewrite IH, (gr_succ C i m).
  destruct (gnext C i (gr (gstart C i) m)) as [j |].
  - destruct (gread C i (gr (gstart C i) m)) eqn:E; simpl; [rewrite (Hp _ j E) |]; reflexivity.
  - destruct (gread C i _); reflexivity.
Qed.

(* ================================================================= *)
(* 3. The suggested neutral "earned again" is automatic.              *)
(* ================================================================= *)

Section NaiveFree.
Variable C : gclass.
Variable H : host.
Variable Obs : gi C -> Type.
Variable obs : forall i, gS C i -> Obs i.
Variable K : nat.
Variable P : hP H.
Variable h0 : hS H.
Variable i : gi C.
Variable decode : hS H -> Obs i.
Variable f : nat -> nat.
Hypothesis Hperm : forall s m, hflag H s = true -> hflag H (hstep H s m) = true.
Hypothesis Hhalt : halt_clause C H Obs obs K P h0 i decode.
Hypothesis Hord : in_order C H Obs obs K P h0 i decode f.

Lemma live_down : forall a b, a <= b -> live_before i b -> live_before i a.
Proof. intros a b Hab Hl k Hk. apply Hl. lia. Qed.

(* Where a host time sits among the matching times. *)
Lemma locate : forall n M, live_before i M -> f 0 <= n < f M ->
  exists m, live_before i (S m) /\ S m <= M /\ f m <= n < f (S m).
Proof.
  intros n M. induction M as [| M IH]; intros Hl Hn; [lia |].
  destruct (le_lt_dec (f M) n) as [Hle | Hlt].
  - exists M. split; [exact Hl |]. lia.
  - destruct (IH (live_down M (S M) ltac:(lia) Hl) ltac:(lia)) as (m & H1 & H2 & H3).
    exists m. split; [exact H1 |]. split; [lia | exact H3].
Qed.

Lemma f_grows : forall m, live_before i m -> f 0 + m <= f m.
Proof.
  induction m as [| m IH]; intros Hm; [lia |].
  pose proof (proj1 Hord m Hm). pose proof (IH (live_down m (S m) ltac:(lia) Hm)). lia.
Qed.

(* Every rise of the host's record: made by a paid host move, and either
   before the first matching time with the guest's record already up at
   its start, or inside a matching interval in which the guest's record
   rises. *)
Theorem naive_rise_free : forall n,
  hflag H (hr P h0 n) = false -> hflag H (hr P h0 (S n)) = true ->
  (exists mv, hnext H P (hr P h0 n) = Some mv /\ hcost H mv >= 1) /\
  ((n < f 0 /\ glat i 0 = true) \/
   (exists m, live_before i (S m) /\ f m <= n < f (S m) /\ glat i m = false /\ glat i (S m) = true)).
Proof.
  intros n F0 F1. split; [exact (clause3_free H P h0 n F0 F1) |].
  assert (Hm0 : forall m, live_before i m -> hflag H (hr P h0 (f m)) = glat i m)
    by (intros m Hm; exact (proj1 (proj2 (proj2 Hord m Hm)))).
  destruct (le_lt_dec (f 0) n) as [Hle | Hlt].
  2:{ left. split; [exact Hlt |]. rewrite <- (Hm0 0 (fun k Hk => ltac:(lia))).
      apply (hr_flag_mono H P Hperm h0 (S n)); [lia | exact F1]. }
  right.
  destruct (live_or_stop_gen C i (S n)) as [Hl | (m0 & Hm0lt & Hs & Hl0)].
  - destruct (locate n (S n) Hl (conj Hle (Nat.lt_le_trans _ _ _ (Nat.lt_succ_diag_r n)
               (Nat.le_trans _ _ _ (Nat.le_add_l (S n) (f 0)) (f_grows (S n) Hl))))) as (m & Hlm & _ & Hin).
    exists m. split; [exact Hlm |]. split; [exact Hin |].
    split.
    + rewrite <- (Hm0 m (live_down m (S m) ltac:(lia) Hlm)).
      destruct (hflag H (hr P h0 (f m))) eqn:E; [| reflexivity].
      rewrite (hr_flag_mono H P Hperm h0 (f m) n ltac:(lia) E) in F0. discriminate.
    + rewrite <- (Hm0 (S m) Hlm). apply (hr_flag_mono H P Hperm h0 (S n)); [lia | exact F1].
  - (* the guest stopped at m0 <= n *)
    destruct (le_lt_dec (f m0) n) as [Hge | Hlt'].
    + exfalso. destruct (proj2 Hhalt m0 Hl0 Hs) as (nh & Hnh & _ & Hfl & _).
      pose proof (Hm0 m0 Hl0) as Ef.
      destruct (le_lt_dec nh n) as [Ha | Ha].
      * rewrite (hr_stopped_stays H P h0 nh n Ha Hnh) in F0.
        rewrite (hr_stopped_stays H P h0 nh (S n) ltac:(lia) Hnh) in F1. congruence.
      * rewrite <- Ef in Hfl.
        destruct (hflag H (hr P h0 (f m0))) eqn:E.
        { rewrite (hr_flag_mono H P Hperm h0 (f m0) n Hge E) in F0. discriminate. }
        rewrite (hr_flag_mono H P Hperm h0 (S n) nh ltac:(lia) F1) in Hfl. discriminate.
    + destruct (locate n m0 Hl0 (conj Hle Hlt')) as (m & Hlm & _ & Hin).
      exists m. split; [exact Hlm |]. split; [exact Hin |]. split.
      * rewrite <- (Hm0 m (live_down m (S m) ltac:(lia) Hlm)).
        destruct (hflag H (hr P h0 (f m))) eqn:E; [| reflexivity].
        rewrite (hr_flag_mono H P Hperm h0 (f m) n ltac:(lia) E) in F0. discriminate.
      * rewrite <- (Hm0 (S m) Hlm). apply (hr_flag_mono H P Hperm h0 (S n)); [lia | exact F1].
Qed.

(* And conversely: every rise of the guest's record has a host rise in its
   matching interval. *)
Theorem naive_rise_converse : forall m, live_before i (S m) ->
  glat i m = false -> glat i (S m) = true ->
  exists n, f m <= n < f (S m) /\ hflag H (hr P h0 n) = false /\ hflag H (hr P h0 (S n)) = true.
Proof.
  intros m Hl G0 G1.
  assert (A : hflag H (hr P h0 (f m)) = false)
    by (rewrite (proj1 (proj2 (proj2 Hord m (live_down m (S m) ltac:(lia) Hl)))); exact G0).
  assert (B : hflag H (hr P h0 (f (S m))) = true)
    by (rewrite (proj1 (proj2 (proj2 Hord (S m) Hl))); exact G1).
  exact (flag_rises_between H P Hperm h0 _ _ A B).
Qed.

End NaiveFree.

(* ================================================================= *)
(* 4. Under (N3)+(N4) the record is the register computation's.       *)
(* ================================================================= *)

Section Determined.
Variable H : host.
Variable R : reg_host H.
Variable P : hP H.
Variable raise : nat -> bool.
Hypothesis HL : line_raise H R P raise.

Definition fsame (s1 s2 : hS H) : Prop :=
  b_pc R s1 = b_pc R s2 /\ (forall x, b_reg R s1 x = b_reg R s2 x) /\ hflag H s1 = hflag H s2.

Lemma fone : forall s1 s2 m, fsame s1 s2 -> hnext H P s1 = Some m -> hnext H P s2 = Some m ->
  b_err R s1 = false -> b_err R s2 = false ->
  b_err R (hstep H s1 m) = false -> b_err R (hstep H s2 m) = false ->
  (forall s m, b_kind R m <> RRec -> hflag H (hstep H s m) = hflag H s) ->
  fsame (hstep H s1 m) (hstep H s2 m).
Proof.
  intros s1 s2 m [Hp [Hr Hf]] N1 N2 E1 E2 F1 F2 Hcf.
  assert (B : bsame H R (hstep H s1 m) (hstep H s2 m))
    by (apply (one H R s1 s2 m); auto; split; auto).
  destruct B as [Bp Br]. split; [exact Bp |]. split; [exact Br |].
  destruct (b_kind R m) eqn:K.
  - rewrite !Hcf by (rewrite K; discriminate). exact Hf.
  - rewrite !Hcf by (rewrite K; discriminate). exact Hf.
  - rewrite !Hcf by (rewrite K; discriminate). exact Hf.
  - destruct (HL s1 m E1 N1 K) as [T | A1]; [congruence |].
    destruct (HL s2 m E2 N2 K) as [T | A2]; [congruence |].
    rewrite A1, A2, Hf, Hp. reflexivity.
Qed.

(* Two runs of the program from states with the same line, registers and
   record have the same line, registers, record and ledger at every time
   before either traps, whatever else the two states hold. *)
Theorem nr_determined :
  (forall s m, b_kind R m <> RRec -> hflag H (hstep H s m) = hflag H s) ->
  forall n s1 s2, fsame s1 s2 ->
    b_err R (hr P s1 n) = false -> b_err R (hr P s2 n) = false ->
    fsame (hr P s1 n) (hr P s2 n) /\ hl P s1 n = hl P s2 n.
Proof.
  intros Hcf n. induction n as [| n IH]; intros s1 s2 B F1 F2; [split; [exact B | reflexivity] |].
  pose proof (err_back H R P (S n) s1 F1) as E1. pose proof (err_back H R P (S n) s2 F2) as E2.
  simpl in F1, F2 |- *.
  assert (N : hnext H P s1 = hnext H P s2)
    by (apply (b_next H R); [congruence | apply B]).
  rewrite <- N in F2 |- *.
  destruct (hnext H P s1) as [m |] eqn:Nm; [| split; [exact B | reflexivity]].
  destruct (IH (hstep H s1 m) (hstep H s2 m)) as [IH1 IH2]; [| exact F1 | exact F2 |].
  - apply fone; auto. exact (err_back H R P n _ F1). exact (err_back H R P n _ F2).
  - split; [exact IH1 | rewrite IH2; reflexivity].
Qed.

End Determined.

(* ================================================================= *)
(* 5. The surcharge floor and the need for a non-raising paid move.   *)
(* ================================================================= *)

Section Floor.
Variable C : gclass.
Variable H : host.
Variable Obs : gi C -> Type.
Variable obs : forall i, gS C i -> Obs i.
Variable K : nat.
Variable P : hP H.
Variable h0 : hS H.
Variable i : gi C.
Variable decode : hS H -> Obs i.

(* If every run of P from h0 that ends with the record up has ledger at
   least phi, then at every matching point with the guest's latch up the
   surcharge is at least phi minus the guest's ledger. *)
Theorem surcharge_floor : forall phi n m s,
  (forall t, hflag H (hr P h0 t) = true -> hl P h0 t >= phi) ->
  hflag H (hr P h0 n) = glat i m -> glat i m = true ->
  hl P h0 n = gledger i m + s -> s >= phi - gledger i m.
Proof.
  intros phi n m s Hphi Hf Hg Hl. rewrite Hg in Hf. pose proof (Hphi n Hf). lia.
Qed.

(* With a lowered start, phi = 1 for every host (the toll). *)
Corollary surcharge_floor_one : forall n m s,
  hflag H h0 = false -> hflag H (hr P h0 n) = glat i m -> glat i m = true ->
  hl P h0 n = gledger i m + s -> s >= 1 - gledger i m.
Proof.
  intros n m s H0 Hf Hg Hl. apply (surcharge_floor 1 n m s); auto.
  intros t Ht. exact (toll_floor H P h0 t H0 Ht).
Qed.

(* A guest that has paid while its record is down: the host has executed a
   record move after which its record is still down. *)
Theorem pay_needed : forall (R : reg_host H) n m s,
  (forall s m, hflag H s = true -> hflag H (hstep H s m) = true) ->
  hflag H (hr P h0 n) = glat i m -> glat i m = false ->
  hl P h0 n = gledger i m + s -> gledger i m >= 1 ->
  exists k mv, k < n /\ hnext H P (hr P h0 k) = Some mv /\ b_kind R mv = RRec /\
               hflag H (hr P h0 (S k)) = false.
Proof.
  intros R n m s Hperm Hf Hg Hl Hp.
  assert (Hpos : hl P h0 n >= 1) by lia.
  assert (Hex : forall t h, hl P h t >= 1 ->
            exists k mv, k < t /\ hnext H P (hr P h k) = Some mv /\ hcost H mv >= 1).
  { induction t as [| t IH]; intros h Hh; [simpl in Hh; lia |].
    simpl in Hh. destruct (hnext H P h) as [mv |] eqn:E; [| lia].
    destruct (hcost H mv) eqn:Ec.
    - destruct (IH (hstep H h mv) ltac:(lia)) as (k & mv' & Hk & Hn & Hc).
      exists (S k), mv'. split; [lia |]. simpl. rewrite E. auto.
    - exists 0, mv. split; [lia |]. simpl. split; [exact E | lia]. }
  destruct (Hex n h0 Hpos) as (k & mv & Hk & Hn & Hc).
  exists k, mv. split; [exact Hk |]. split; [exact Hn |]. split.
  - pose proof (b_cost H R mv) as Bc. destruct (b_kind R mv); [lia | lia | lia | reflexivity].
  - destruct (hflag H (hr P h0 (S k))) eqn:E; [| reflexivity].
    rewrite Hg in Hf. rewrite (hr_flag_mono H P Hperm h0 (S k) n ltac:(lia) E) in Hf. discriminate.
Qed.

End Floor.

(* ================================================================= *)
(* 6. From finite increasing chains to one increasing function.       *)
(* ================================================================= *)

Section Chains.
Variable D : nat -> nat -> Prop.
Hypothesis Ddec : forall m n, {D m n} + {~ D m n}.
Variable L : nat -> Prop.
Hypothesis Ldec : forall m, {L m} + {~ L m}.
Hypothesis Ldown : forall m, L (S m) -> L m.
Hypothesis chains : forall M, L M -> exists l : nat -> nat,
  (forall k, k < M -> l k < l (S k)) /\ (forall k, k <= M -> D k (l k)).

Definition chain_at (M : nat) (l : nat -> nat) : Prop :=
  (forall k, k < M -> l k < l (S k)) /\ (forall k, k <= M -> D k (l k)).

Definition Inv (m n : nat) : Prop :=
  L m -> D m n /\ forall M l, m <= M -> chain_at M l -> n <= l m.

Definition base : {n | Inv 0 n}.
Proof.
  destruct (Ldec 0) as [HL | HL].
  - assert (e : exists n, D 0 n).
    { destruct (chains 0 HL) as (l & _ & Hd). exists (l 0). apply Hd. lia. }
    destruct (epsilon_smallest (D 0) (Ddec 0) e) as (n & Hn & Hmin).
    exists n. intros _. split; [exact Hn |]. intros M l _ [_ Hd]. apply Hmin, Hd. lia.
  - exists 0. intros HL'. contradiction.
Defined.

Definition next (m : nat) (x : {n | Inv m n}) : {n | Inv (S m) n /\ (L (S m) -> proj1_sig x < n)}.
Proof.
  destruct x as [nm Im]. simpl.
  destruct (Ldec (S m)) as [HL | HL].
  - set (Q := fun n => nm < n /\ D (S m) n).
    assert (Qdec : forall n, {Q n} + {~ Q n}).
    { intros n. unfold Q. destruct (lt_dec nm n) as [a | a]; [| right; tauto].
      destruct (Ddec (S m) n) as [b | b]; [left; auto | right; tauto]. }
    assert (e : exists n, Q n).
    { destruct (chains (S m) HL) as (l & Hi & Hd).
      destruct (Im (Ldown m HL)) as [_ Hle].
      pose proof (Hle (S m) l ltac:(lia) (conj Hi Hd)) as A. pose proof (Hi m ltac:(lia)) as B.
      exists (l (S m)). split; [lia | apply Hd; lia]. }
    destruct (epsilon_smallest Q Qdec e) as (n & [Hlt Hn] & Hmin).
    exists n. split; [| intros _; exact Hlt].
    intros _. split; [exact Hn |]. intros M l HM [Hi Hd].
    destruct (Im (Ldown m HL)) as [_ Hle].
    pose proof (Hle M l ltac:(lia) (conj Hi Hd)) as A. pose proof (Hi m ltac:(lia)) as B.
    apply Hmin. split; [lia | apply Hd; lia].
  - exists 0. split; [intros HL'; contradiction | intros HL'; contradiction].
Defined.

Fixpoint fseq (m : nat) : {n | Inv m n} :=
  match m with
  | 0 => base
  | S m' => let y := next m' (fseq m') in exist _ (proj1_sig y) (proj1 (proj2_sig y))
  end.

Theorem chains_to_fun : exists f : nat -> nat,
  (forall m, L (S m) -> f m < f (S m)) /\ (forall m, L m -> D m (f m)).
Proof.
  exists (fun m => proj1_sig (fseq m)). split.
  - intros m HL. simpl. exact (proj2 (proj2_sig (next m (fseq m))) HL).
  - intros m HL. exact (proj1 (proj2_sig (fseq m) HL)).
Qed.

End Chains.

(* live_before is decidable. *)
Lemma live_before_dec : forall (C : gclass) (i : gi C) m, {live_before i m} + {~ live_before i m}.
Proof.
  intros C i m. induction m as [| m IH].
  - left. intros k Hk. lia.
  - destruct IH as [Hl | Hl].
    + destruct (gnext C i (grun i m)) eqn:E.
      * left. intros k Hk. destruct (Nat.eq_dec k m) as [Hk' | Hne]; [rewrite Hk'; unfold grun in E; rewrite E; discriminate |].
        apply Hl. lia.
      * right. intros Hl'. exact (Hl' m ltac:(lia) E).
    + right. intros Hl'. apply Hl. intros k Hk. apply Hl'. lia.
Defined.

Print Assumptions neutral_universal_weakens.
Print Assumptions toll_floor.
Print Assumptions naive_rise_free.
Print Assumptions naive_rise_converse.
Print Assumptions nr_determined.
Print Assumptions surcharge_floor.
Print Assumptions surcharge_floor_one.
Print Assumptions pay_needed.
Print Assumptions chains_to_fun.
