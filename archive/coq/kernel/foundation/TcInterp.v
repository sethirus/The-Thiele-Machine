(** TcInterp.v: an interpreter for the small machine, written over plain
    data, and the packed evaluators.

    The small machine (EarnedCore.v) keeps its state in a record. This file
    runs the same machine on plain data: the two counters, their versions,
    the program counter, the fact table as a list of (property code,
    (counter code, version)), the channel as an option of such a triple, and
    the trap latch as a boolean. It never reads the ledger or the flag,
    because the next core of the machine does not depend on them.

      tc_kstep P k       one step of the program P on the plain core k
      tc_kout n P a      run P on the input a (counter A holds a, B holds 0)
                         for n steps; if it has stopped, Some (counter A)

    What is proved: the plain core and the machine's core stay related, step
    for step, and one has stopped exactly when the other has [tc_krel_step,
    tc_krel_halted]; a program ends on the input a with a in counter A
    exactly when some number of steps of the interpreter gives Some a
    [tc_kout_ends]; more steps never change an answer [tc_kout_mono].

    The packed readings. A program computes y from x, [tc_pk], when started
    with 2^x in counter A and 0 in counter B it stops with exactly 2^y in
    counter A. [tc_klog] reads the exponent back. The evaluators

      tc_uev n x e       run the program numbered e on x
      tc_ev t n x c      run the program numbered t on the number of the
                         program specialised to c, then run the program
                         whose number comes out on x

    find y exactly when the program numbered e computes y from x
    [tc_uev_spec], respectively when some d is computed from tc_kspec c by
    the program numbered t and y from x by the program numbered d
    [tc_ev_spec].

    Every function here is a plain recursion over numbers, booleans, pairs,
    options and lists, so TcEvalL.v can turn it into a term of L.

    Dependencies: Coq standard library, EarnedCore.v, UniversalCodes.v,
    TcBlocks.v, TcCodes.v, TcRice.v. No axioms and no unfinished proofs.               *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore Minimal.UniversalCodes.
Require Import Minimal.TcBlocks Kernel.TcCodes Kernel.TcRice.
Module E := Minimal.EarnedCore.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

(* ================================================================= *)
(* The property checker and the fact table, on plain data.            *)
(* ================================================================= *)

Definition tc_keval (q v : nat) : bool :=
  match q with
  | 0 => Nat.eqb v 0
  | S q1 => match q1 with 0 => negb (snd (tc_hb v)) | S n => Nat.leb n v end
  end.

Lemma tc_keval_eq : forall q v, tc_keval q v = E.eval (UC.pdec q) v.
Proof.
  intros q v. destruct q as [| [| n]]; simpl; try reflexivity.
  rewrite tc_hb_spec. simpl. apply Nat.negb_odd.
Qed.

Definition tc_kfeq (f g : nat * (nat * nat)) : bool :=
  Nat.eqb (fst f) (fst g) && Nat.eqb (tc_cn (fst (snd f))) (tc_cn (fst (snd g))) &&
  Nat.eqb (snd (snd f)) (snd (snd g)).

Fixpoint tc_kmem (f : nat * (nat * nat)) (l : list (nat * (nat * nat))) : bool :=
  match l with
  | [] => false
  | g :: t => tc_kfeq f g || tc_kmem f t
  end.

Definition tc_tofact (f : nat * (nat * nat)) : E.fact :=
  E.mkfact (UC.pdec (fst f)) (tc_cdec (fst (snd f))) (snd (snd f)).

Lemma tc_kfeq_eq : forall f g, tc_kfeq f g = E.fact_eqb (tc_tofact f) (tc_tofact g).
Proof.
  intros [q [c v]] [q' [c' v']]. unfold tc_kfeq, tc_tofact, E.fact_eqb. simpl.
  assert (Hp : E.prop_eqb (UC.pdec q) (UC.pdec q') = Nat.eqb q q').
  { destruct (Nat.eqb_spec q q') as [-> | Hne].
    - destruct (UC.pdec q') eqn:E1; simpl; try reflexivity. apply Nat.eqb_refl.
    - destruct (E.prop_eqb (UC.pdec q) (UC.pdec q')) eqn:E1; [| reflexivity].
      exfalso. apply Hne. destruct (E.fact_eqb_eq (E.mkfact (UC.pdec q) E.CA 0) (E.mkfact (UC.pdec q') E.CA 0)) as [H1 _].
      assert (Hf : E.fact_eqb (E.mkfact (UC.pdec q) E.CA 0) (E.mkfact (UC.pdec q') E.CA 0) = true).
      { unfold E.fact_eqb. simpl. rewrite E1. simpl. reflexivity. }
      apply H1 in Hf. injection Hf as Hf. rewrite <- (UC.pcode_pdec q), <- (UC.pcode_pdec q'). f_equal. exact Hf. }
  assert (Hc : E.ctr_eqb (tc_cdec c) (tc_cdec c') = Nat.eqb (tc_cn c) (tc_cn c')).
  { unfold tc_cdec, tc_cn. destruct (Nat.eqb c 0), (Nat.eqb c' 0); reflexivity. }
  rewrite Hp, Hc. reflexivity.
Qed.

Lemma tc_kmem_eq : forall f l,
  existsb (E.fact_eqb (tc_tofact f)) (map tc_tofact l) = tc_kmem f l.
Proof.
  intros f l. induction l as [| g l IH]; [reflexivity |].
  simpl. rewrite IH, tc_kfeq_eq. reflexivity.
Qed.

(* ================================================================= *)
(* The plain machine.                                                 *)
(* ================================================================= *)

Definition tc_KC : Type :=
  (nat * (nat * (nat * (nat * (nat * (list (nat * (nat * nat)) * (option (nat * (nat * nat)) * bool)))))))%type.

Definition tc_kfetch (P : list tc_ki) (n : nat) : option tc_ki :=
  match n with 0 => None | S m => nth_error P m end.

Definition tc_kexec (i : tc_ki) (a b va vb pc : nat) (fs : list (nat * (nat * nat)))
    (ch : option (nat * (nat * nat))) (er : bool) : tc_KC :=
  match i with
  | tc_KHalt => (a, (b, (va, (vb, (pc, (fs, (ch, er)))))))
  | tc_KInc c =>
      if Nat.eqb c 0 then (S a, (b, (S va, (vb, (S pc, (fs, (ch, er)))))))
      else (a, (S b, (va, (S vb, (S pc, (fs, (ch, er)))))))
  | tc_KDec c j =>
      if Nat.eqb c 0 then
        match a with
        | 0 => (a, (b, (va, (vb, (S pc, (fs, (ch, er)))))))
        | S n => (n, (b, (S va, (vb, (j, (fs, (ch, er)))))))
        end
      else
        match b with
        | 0 => (a, (b, (va, (vb, (S pc, (fs, (ch, er)))))))
        | S n => (a, (n, (va, (S vb, (j, (fs, (ch, er)))))))
        end
  | tc_KCheck c q =>
      if tc_keval q (if Nat.eqb c 0 then a else b) && Nat.ltb (length fs) 16
      then (a, (b, (va, (vb, (S pc, ((q, (c, if Nat.eqb c 0 then va else vb)) :: fs, (ch, er)))))))
      else (a, (b, (va, (vb, (pc, (fs, (ch, true)))))))
  | tc_KCommit c q =>
      if tc_kmem (q, (c, if Nat.eqb c 0 then va else vb)) fs
      then (a, (b, (va, (vb, (S pc, (fs, (Some (q, (c, if Nat.eqb c 0 then va else vb)), er)))))))
      else (a, (b, (va, (vb, (pc, (fs, (ch, true)))))))
  | tc_KCertify =>
      match ch with
      | Some _ => (a, (b, (va, (vb, (S pc, (fs, (ch, er)))))))
      | None => (a, (b, (va, (vb, (pc, (fs, (ch, true)))))))
      end
  end.

(* Written with projections rather than a nested pattern, which the
   extraction tactic of TcEvalL.v handles. *)
Definition tc_kstep (P : list tc_ki) (k : tc_KC) : tc_KC :=
  if snd (snd (snd (snd (snd (snd (snd k)))))) then k else
  match tc_kfetch P (fst (snd (snd (snd (snd k))))) with
  | None => k
  | Some i => tc_kexec i (fst k) (fst (snd k)) (fst (snd (snd k))) (fst (snd (snd (snd k))))
                (fst (snd (snd (snd (snd k))))) (fst (snd (snd (snd (snd (snd k))))))
                (fst (snd (snd (snd (snd (snd (snd k))))))) (snd (snd (snd (snd (snd (snd (snd k)))))))
  end.

Definition tc_khalted (P : list tc_ki) (k : tc_KC) : bool :=
  if snd (snd (snd (snd (snd (snd (snd k)))))) then true else
  match tc_kfetch P (fst (snd (snd (snd (snd k))))) with
  | None => true
  | Some tc_KHalt => true
  | Some _ => false
  end.

Fixpoint tc_krun (n : nat) (P : list tc_ki) (k : tc_KC) : tc_KC :=
  match n with 0 => k | S m => tc_krun m P (tc_kstep P k) end.

Definition tc_kstart (a : nat) : tc_KC := (a, (0, (0, (0, (1, ([], (None, false))))))).

Definition tc_kout (fuel : nat) (P : list tc_ki) (a : nat) : option nat :=
  let k := tc_krun fuel P (tc_kstart a) in
  if tc_khalted P k then Some (fst k) else None.

(* ================================================================= *)
(* The plain machine is the small machine.                            *)
(* ================================================================= *)

Definition tc_krel (k : E.core) (t : tc_KC) : Prop :=
  match t with
  | (a, (b, (va, (vb, (pc, (fs, (ch, er))))))) =>
      E.ca k = a /\ E.cb k = b /\ E.va k = va /\ E.vb k = vb /\ E.pc k = pc /\
      E.facts k = map tc_tofact fs /\ E.chan k = option_map tc_tofact ch /\ E.err k = er
  end.

Lemma tc_fetch_of : forall P n, E.fetch (map tc_ofki P) n = option_map tc_ofki (tc_kfetch P n).
Proof. intros P [| n]; simpl; [reflexivity | apply nth_error_map]. Qed.

Lemma tc_krel_halted : forall P k t, tc_krel k t ->
  (E.halted (map tc_ofki P) k <-> tc_khalted P t = true).
Proof.
  intros P k [a [b [va [vb [pc [fs [ch er]]]]]]] (Ha & Hb & Hva & Hvb & Hp & Hf & Hc & He).
  unfold E.halted, E.next_instr, tc_khalted. cbn [fst snd]. rewrite He, Hp, tc_fetch_of.
  destruct er; [split; reflexivity |].
  destruct (tc_kfetch P pc) as [[] |]; simpl; split; intro H; congruence.
Qed.

Lemma tc_val_rel : forall k a b c, E.ca k = a -> E.cb k = b ->
  E.val k (tc_cdec c) = if Nat.eqb c 0 then a else b.
Proof. intros k a b c Ha Hb. unfold tc_cdec. destruct (Nat.eqb c 0); simpl; auto. Qed.

Lemma tc_ver_rel : forall k va vb c, E.va k = va -> E.vb k = vb ->
  E.ver k (tc_cdec c) = if Nat.eqb c 0 then va else vb.
Proof. intros k va vb c Ha Hb. unfold tc_cdec. destruct (Nat.eqb c 0); simpl; auto. Qed.

Lemma tc_krel_step : forall P k t, tc_krel k t -> tc_krel (E.core_step (map tc_ofki P) k) (tc_kstep P t).
Proof.
  intros P k [a [b [va [vb [pc [fs [ch er]]]]]]] Hrel.
  pose proof Hrel as (Ha & Hb & Hva & Hvb & Hp & Hf & Hc & He).
  unfold tc_kstep. cbn [fst snd]. destruct er.
  { assert (Hn : E.next_instr (map tc_ofki P) k = None)
      by (unfold E.next_instr; rewrite He; reflexivity).
    unfold E.core_step. rewrite Hn. exact Hrel. }
  destruct (tc_kfetch P pc) as [i |] eqn:Hi.
  2: { assert (Hn : E.next_instr (map tc_ofki P) k = None)
         by (unfold E.next_instr; rewrite He, Hp, tc_fetch_of, Hi; reflexivity).
       unfold E.core_step. rewrite Hn. exact Hrel. }
  destruct i as [c | c j | | c q | c q |] eqn:Ei.
  3: { assert (Hn : E.next_instr (map tc_ofki P) k = None)
         by (unfold E.next_instr; rewrite He, Hp, tc_fetch_of, Hi; reflexivity).
       unfold E.core_step. rewrite Hn. exact Hrel. }
  all: assert (Hn : E.next_instr (map tc_ofki P) k = Some (tc_ofki i))
         by (unfold E.next_instr; rewrite He, Hp, tc_fetch_of, Hi, Ei; reflexivity).
  all: unfold E.core_step; rewrite Hn, Ei; unfold E.cexec; rewrite He; cbn [tc_ofki tc_kexec].
  - (* INC *)
    unfold tc_cdec. destruct (Nat.eqb c 0); simpl;
      unfold E.write; simpl; rewrite ?Ha, ?Hb, ?Hva, ?Hvb, ?Hp; repeat split; auto.
  - (* DEC *)
    unfold tc_cdec. destruct (Nat.eqb c 0).
    + simpl. rewrite Ha. destruct a as [| n]; simpl.
      * unfold E.goto. simpl. rewrite Hp. repeat split; auto.
      * unfold E.write. simpl. rewrite ?Ha, ?Hb, ?Hva, ?Hvb, ?Hp. repeat split; auto.
    + simpl. rewrite Hb. destruct b as [| n]; simpl.
      * unfold E.goto. simpl. rewrite Hp. repeat split; auto.
      * unfold E.write. simpl. rewrite ?Ha, ?Hb, ?Hva, ?Hvb, ?Hp. repeat split; auto.
  - (* CHECK *)
    assert (Hok : E.check_ok k (UC.pdec q) (tc_cdec c) =
                  tc_keval q (if Nat.eqb c 0 then a else b) && Nat.ltb (length fs) 16).
    { unfold E.check_ok. rewrite He, (tc_val_rel k a b c Ha Hb), Hf, map_length, tc_keval_eq. reflexivity. }
    rewrite Hok. destruct (tc_keval q (if Nat.eqb c 0 then a else b) && Nat.ltb (length fs) 16).
    + unfold E.record_fact, E.claim. simpl. rewrite (tc_ver_rel k va vb c Hva Hvb), Hp, Hf.
      repeat split; auto.
    + unfold E.trap. simpl. rewrite Hp. repeat split; auto.
  - (* COMMIT *)
    assert (Hok : E.commit_ok k (UC.pdec q) (tc_cdec c) = tc_kmem (q, (c, if Nat.eqb c 0 then va else vb)) fs).
    { unfold E.commit_ok, E.claim. rewrite He, Hf, (tc_ver_rel k va vb c Hva Hvb), <- tc_kmem_eq.
      reflexivity. }
    rewrite Hok. destruct (tc_kmem (q, (c, if Nat.eqb c 0 then va else vb)) fs).
    + unfold E.commit_to, E.claim. simpl. rewrite (tc_ver_rel k va vb c Hva Hvb), Hp.
      repeat split; auto.
    + unfold E.trap. simpl. rewrite Hp. repeat split; auto.
  - (* CERTIFY *)
    assert (Hok : E.certify_ok k = match ch with Some _ => true | None => false end).
    { unfold E.certify_ok. rewrite He, Hc. destruct ch; reflexivity. }
    rewrite Hok. destruct ch as [f |].
    + unfold E.goto. simpl. rewrite Hp. repeat split; auto.
    + unfold E.trap. simpl. rewrite Hp. repeat split; auto.
Qed.

Lemma tc_krel_run : forall n P k t, tc_krel k t ->
  tc_krel (E.core_run n (map tc_ofki P) k) (tc_krun n P t).
Proof.
  induction n as [| n IH]; intros P k t H; [exact H |].
  simpl. apply IH, tc_krel_step, H.
Qed.

Lemma tc_krel_start : forall a, tc_krel (E.core_of (E.start a 0)) (tc_kstart a).
Proof. intro a. simpl. repeat split. Qed.

Theorem tc_kout_ends : forall P a z,
  (exists s, tc_ends a (map tc_ofki P) s /\ E.ca (E.core_of s) = z) <->
  exists n, tc_kout n P a = Some z.
Proof.
  intros P a z. split.
  - intros [s [[n [-> Hh]] Hy]]. exists n.
    pose proof (tc_krel_run n P _ _ (tc_krel_start a)) as Hr.
    rewrite <- E.core_run_prog in Hr.
    unfold tc_kout. rewrite (proj1 (tc_krel_halted P _ _ Hr) Hh).
    destruct (tc_krun n P (tc_kstart a)) as [a' [b [va [vb [pc [fs [ch er]]]]]]].
    destruct Hr as (Ha & _). simpl. rewrite <- Ha, Hy. reflexivity.
  - intros [n Hn]. unfold tc_kout in Hn.
    pose proof (tc_krel_run n P _ _ (tc_krel_start a)) as Hr.
    rewrite <- E.core_run_prog in Hr.
    destruct (tc_khalted P (tc_krun n P (tc_kstart a))) eqn:Hh; [| discriminate].
    injection Hn as <-.
    exists (E.run_prog n (map tc_ofki P) (E.start a 0)). split.
    + exists n. split; [reflexivity |]. apply (tc_krel_halted P _ _ Hr), Hh.
    + destruct (tc_krun n P (tc_kstart a)) as [a' [b [va [vb [pc [fs [ch er]]]]]]].
      destruct Hr as (Ha & _). apply Ha.
Qed.

(* ================================================================= *)
(* More steps never change an answer.                                 *)
(* ================================================================= *)

Lemma tc_kstep_halted : forall P k, tc_khalted P k = true -> tc_kstep P k = k.
Proof.
  intros P [a [b [va [vb [pc [fs [ch er]]]]]]] H. unfold tc_khalted in H. unfold tc_kstep.
  cbn [fst snd] in H |- *.
  destruct er; [reflexivity |].
  destruct (tc_kfetch P pc) as [[] |]; try discriminate; reflexivity.
Qed.

Lemma tc_krun_halted : forall n P k, tc_khalted P k = true -> tc_krun n P k = k.
Proof.
  induction n as [| n IH]; intros P k H; [reflexivity |].
  simpl. rewrite tc_kstep_halted by exact H. apply IH, H.
Qed.

Lemma tc_krun_add : forall a b P k, tc_krun (a + b) P k = tc_krun b P (tc_krun a P k).
Proof. induction a as [| a IH]; intros; simpl; [reflexivity | apply IH]. Qed.

Theorem tc_kout_mono : forall n n' P a z, n <= n' ->
  tc_kout n P a = Some z -> tc_kout n' P a = Some z.
Proof.
  intros n n' P a z Hle H. unfold tc_kout in *.
  destruct (tc_khalted P (tc_krun n P (tc_kstart a))) eqn:Hh; [| discriminate].
  replace n' with (n + (n' - n)) by lia. rewrite tc_krun_add.
  rewrite (tc_krun_halted (n' - n) P _ Hh), Hh. exact H.
Qed.

(* ================================================================= *)
(* The exponent, read back.                                           *)
(* ================================================================= *)

Fixpoint tc_klog_go (fuel a k : nat) : option nat :=
  match fuel with
  | 0 => None
  | S f => if Nat.eqb (2 ^ k) a then Some k else tc_klog_go f a (S k)
  end.

Definition tc_klog (a : nat) : option nat := tc_klog_go (S a) a 0.

Lemma tc_klog_go_sound : forall fuel a k z, tc_klog_go fuel a k = Some z -> 2 ^ z = a.
Proof.
  induction fuel as [| f IH]; intros a k z H; [discriminate |].
  simpl in H. destruct (Nat.eqb_spec (2 ^ k) a) as [E1 | E1].
  - injection H as <-. exact E1.
  - eapply IH. exact H.
Qed.

Lemma tc_lt_pow2 : forall y, y < 2 ^ y.
Proof.
  induction y as [| y IH]; [simpl; lia |].
  rewrite Nat.pow_succ_r'. lia.
Qed.

Lemma tc_klog_go_complete : forall fuel y k, k <= y -> y < k + fuel -> tc_klog_go fuel (2 ^ y) k = Some y.
Proof.
  induction fuel as [| f IH]; intros y k H1 H2; [lia |].
  simpl. destruct (Nat.eqb_spec (2 ^ k) (2 ^ y)) as [E1 | E1].
  - apply Nat.pow_inj_r in E1; [| lia]. subst k. reflexivity.
  - apply IH; [| lia]. destruct (Nat.eq_dec k y) as [-> | Hne]; [exfalso; apply E1; reflexivity | lia].
Qed.

Lemma tc_klog_pow : forall y, tc_klog (2 ^ y) = Some y.
Proof.
  intro y. unfold tc_klog. apply tc_klog_go_complete; [lia |].
  pose proof (tc_lt_pow2 y). lia.
Qed.

Lemma tc_klog_sound : forall a z, tc_klog a = Some z -> 2 ^ z = a.
Proof. intros a z H. exact (tc_klog_go_sound _ _ _ _ H). Qed.

(* the packed reading of a program *)
Definition tc_pk (P : list E.instr) (x y : nat) : Prop :=
  exists s, tc_ends (2 ^ x) P s /\ E.ca (E.core_of s) = 2 ^ y.

Definition tc_kpk (fuel : nat) (P : list tc_ki) (x : nat) : option nat :=
  match tc_kout fuel P (2 ^ x) with Some a => tc_klog a | None => None end.

Lemma tc_kpk_mono : forall n n' P x y, n <= n' -> tc_kpk n P x = Some y -> tc_kpk n' P x = Some y.
Proof.
  intros n n' P x y Hle H. unfold tc_kpk in *.
  destruct (tc_kout n P (2 ^ x)) as [a |] eqn:Ha; [| discriminate].
  rewrite (tc_kout_mono n n' _ _ a Hle Ha). exact H.
Qed.

Theorem tc_kpk_pk : forall P x y,
  tc_pk (map tc_ofki P) x y <-> exists n, tc_kpk n P x = Some y.
Proof.
  intros P x y. unfold tc_pk. split.
  - intros [s [Hs Hy]]. destruct (proj1 (tc_kout_ends P (2 ^ x) (2 ^ y)) (ex_intro _ s (conj Hs Hy))) as [n Hn].
    exists n. unfold tc_kpk. rewrite Hn. apply tc_klog_pow.
  - intros [n Hn]. unfold tc_kpk in Hn.
    destruct (tc_kout n P (2 ^ x)) as [a |] eqn:Ha; [| discriminate].
    apply tc_klog_sound in Hn. subst a.
    apply (proj2 (tc_kout_ends P (2 ^ x) (2 ^ y))). exists n. exact Ha.
Qed.

(* ================================================================= *)
(* The two evaluators.                                                *)
(* ================================================================= *)

Definition tc_uev (fuel x e : nat) : option nat := tc_kpk fuel (tc_kpdec e) x.

Theorem tc_uev_spec : forall x e y,
  (exists n, tc_uev n x e = Some y) <-> tc_pk (tc_pdec e) x y.
Proof. intros x e y. unfold tc_uev, tc_pdec. rewrite tc_kpk_pk. reflexivity. Qed.

Lemma tc_uev_mono : forall n n' x e, n <= n' ->
  forall y, tc_uev n x e = Some y -> tc_uev n' x e = Some y.
Proof. intros n n' x e Hle y H. eapply tc_kpk_mono; eauto. Qed.

Definition tc_ev (t fuel x c : nat) : option nat :=
  match tc_kpk fuel (tc_kpdec t) (tc_kspec c) with
  | Some d => tc_kpk fuel (tc_kpdec d) x
  | None => None
  end.

Lemma tc_ev_mono : forall t n n' x c y, n <= n' ->
  tc_ev t n x c = Some y -> tc_ev t n' x c = Some y.
Proof.
  intros t n n' x c y Hle H. unfold tc_ev in *.
  destruct (tc_kpk n (tc_kpdec t) (tc_kspec c)) as [d |] eqn:Hd; [| discriminate].
  rewrite (tc_kpk_mono n n' _ _ d Hle Hd). eapply tc_kpk_mono; eauto.
Qed.

Theorem tc_ev_spec : forall t x c y,
  (exists n, tc_ev t n x c = Some y) <->
  exists d, tc_pk (tc_pdec t) (tc_kspec c) d /\ tc_pk (tc_pdec d) x y.
Proof.
  intros t x c y. unfold tc_pdec. split.
  - intros [n Hn]. unfold tc_ev in Hn.
    destruct (tc_kpk n (tc_kpdec t) (tc_kspec c)) as [d |] eqn:Hd; [| discriminate].
    exists d. split; apply tc_kpk_pk; exists n; assumption.
  - intros [d [H1 H2]]. apply tc_kpk_pk in H1. apply tc_kpk_pk in H2.
    destruct H1 as [n1 H1]. destruct H2 as [n2 H2].
    exists (n1 + n2). unfold tc_ev.
    rewrite (tc_kpk_mono n1 (n1 + n2) _ _ d) by (lia || exact H1).
    apply (tc_kpk_mono n2); [lia | exact H2].
Qed.

Print Assumptions tc_kout_ends.
Print Assumptions tc_ev_spec.
Print Assumptions tc_uev_spec.
