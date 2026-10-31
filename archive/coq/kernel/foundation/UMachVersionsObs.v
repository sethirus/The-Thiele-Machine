(** UMachVersionsObs.v: the guest's version numbers, for U.

    A. obs_run: on the small machine, the version NUMBERS are not
       observable.  gobs s keeps the counters, the line, the trap, the
       ledger, the flag and, for every fact in the table and for the
       channel, its property, its counter and one bit: is it about the
       counter's current version?  Two states with the same gobs (and fact
       versions not ahead of their counters, which every reachable state
       satisfies) have the same gobs after every instruction sequence, so
       the same counters, line, trap, ledger, flag and the same pass/fail
       of every CHECK, COMMIT and CERTIFY forever.  So gobs is everything
       about a guest state that any run can show, and the literal version
       numbers are bookkeeping.

    B. U_obs_at_rel: at every matching point of U (rel_with) the host state
       determines gobs of the guest, by an explicit decode hobs (the
       property and bank of each host fact read off its slot register, and
       the current-bit read as "the host fact's version is the slot's
       version").

    C. U_meets_strong_obs: U meets the in-order rendering of
       the plain definition with the observation gobs (guarded at a trap)
       and decode hobs, surcharge 0.

    Whether U's state also determines the literal version numbers is not
    proved in this file.                                                   *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.UMachCheatSmall.
Require Import Kernel.UMachMeetsU.
Require Import Kernel.UMachInOrderGen.
Require Import Kernel.UMachInOrderU.
Require Import Minimal.UniversalCodes.
Require Import Kernel.UniversalBridge.
Require Import Kernel.UniversalLayout.
Require Import Kernel.UniversalPhases.
Require Import Kernel.UniversalSim.
Require Import Kernel.UniversalRun.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* A. The observable state of a small-machine state.                  *)
(* ================================================================= *)

Definition fobs (k : E.core) (f : E.fact) : E.prop * E.ctr * bool :=
  (E.f_prop f, E.f_ctr f, Nat.eqb (E.f_ver f) (E.ver k (E.f_ctr f))).

Definition GObs : Type :=
  (nat * nat * nat * bool * list (E.prop * E.ctr * bool) * option (E.prop * E.ctr * bool) * nat * bool)%type.

Definition gobs (s : E.state) : GObs :=
  let k := E.core_of s in
  (E.ca k, E.cb k, E.pc k, E.err k, map (fobs k) (E.facts k), option_map (fobs k) (E.chan k),
   E.mu s, E.cert s).

(* Fact versions are never ahead of their counters. *)
Definition vbounded (k : E.core) : Prop :=
  (forall f, In f (E.facts k) -> E.f_ver f <= E.ver k (E.f_ctr f)) /\
  (forall f, E.chan k = Some f -> E.f_ver f <= E.ver k (E.f_ctr f)).

Lemma vbounded_start : forall a b, vbounded (E.core_of (E.start a b)).
Proof. intros a b. split; [intros f [] | intros f H; discriminate]. Qed.

Lemma ver_write : forall k c n j d,
  E.ver (E.write k c n j) d = if E.ctr_eqb c d then S (E.ver k d) else E.ver k d.
Proof. intros k [] n j []; reflexivity. Qed.

Definition wobs (c : E.ctr) (o : E.prop * E.ctr * bool) : E.prop * E.ctr * bool :=
  let '(p, d, b) := o in (p, d, if E.ctr_eqb c d then false else b).

Lemma fobs_write : forall k c n j f, E.f_ver f <= E.ver k (E.f_ctr f) ->
  fobs (E.write k c n j) f = wobs c (fobs k f).
Proof.
  intros k c n j [p d v] H. unfold fobs, wobs. simpl in *. rewrite ver_write.
  destruct (E.ctr_eqb c d); [| reflexivity].
  f_equal. apply Nat.eqb_neq. lia.
Qed.

Lemma map_fobs_write : forall k c n j l, (forall f, In f l -> E.f_ver f <= E.ver k (E.f_ctr f)) ->
  map (fobs (E.write k c n j)) l = map (wobs c) (map (fobs k) l).
Proof.
  intros k c n j l H. induction l as [| f l IH]; [reflexivity |]. simpl.
  rewrite IH by (intros g Hg; apply H; right; exact Hg).
  rewrite fobs_write by (apply H; left; reflexivity). reflexivity.
Qed.

Lemma exists_claim : forall k p c,
  existsb (E.fact_eqb (E.claim k p c)) (E.facts k) =
  existsb (fun o => match o with (q, d, b) => E.prop_eqb p q && E.ctr_eqb c d && b end)
          (map (fobs k) (E.facts k)).
Proof.
  intros k p c. induction (E.facts k) as [| [q d v] l IH]; [reflexivity |]. simpl.
  rewrite IH. unfold E.fact_eqb, E.claim. simpl. f_equal.
  destruct (E.ctr_eqb c d) eqn:Hc; simpl; rewrite ?andb_false_r; [| reflexivity].
  assert (c = d) by (destruct c, d; simpl in Hc; congruence). subst d.
  rewrite (Nat.eqb_sym (E.ver k c) v). reflexivity.
Qed.

Lemma vb_write : forall k c n j, vbounded k -> vbounded (E.write k c n j).
Proof.
  intros k c n j [H1 H2]. split.
  - intros f Hf. rewrite ver_write. assert (Hf' : In f (E.facts k)) by (destruct c; exact Hf).
    specialize (H1 f Hf'). destruct (E.ctr_eqb c (E.f_ctr f)); lia.
  - intros f Hf. rewrite ver_write. assert (Hf' : E.chan k = Some f) by (destruct c; exact Hf).
    specialize (H2 f Hf'). destruct (E.ctr_eqb c (E.f_ctr f)); lia.
Qed.

Lemma vb_step : forall k i, vbounded k -> vbounded (E.cexec k i).
Proof.
  intros k i Hv. unfold E.cexec. destruct (E.err k); [exact Hv |].
  destruct i as [c | c j | | p c | p c |].
  - apply vb_write, Hv.
  - destruct (E.val k c); [exact Hv | apply vb_write, Hv].
  - exact Hv.
  - destruct (E.check_ok k p c); [| exact Hv]. destruct Hv as [H1 H2]. split; simpl.
    + intros f [<- | Hf]; [simpl; destruct c; simpl; lia | apply H1, Hf].
    + exact H2.
  - destruct (E.commit_ok k p c); [| exact Hv]. destruct Hv as [H1 H2]. split; simpl.
    + exact H1.
    + intros f Hf. injection Hf as <-. simpl. destruct c; simpl; lia.
  - destruct (E.certify_ok k); exact Hv.
Qed.

Lemma len_map_eq : forall {A B} (f g : A -> B) l1 l2, map f l1 = map g l2 -> length l1 = length l2.
Proof. intros A B f g l1 l2 H. rewrite <- (map_length f), <- (map_length g). congruence. Qed.

Lemma fobs_same : forall k1 k2, E.va k1 = E.va k2 -> E.vb k1 = E.vb k2 ->
  forall f, fobs k1 f = fobs k2 f.
Proof. intros k1 k2 Ha Hb [p [] v]; unfold fobs; simpl; congruence. Qed.

Definition core_obs (k : E.core) :=
  (E.ca k, E.cb k, E.pc k, E.err k, map (fobs k) (E.facts k), option_map (fobs k) (E.chan k)).

Lemma gobs_core : forall k m b, gobs (E.mkst k m b) = (core_obs k, m, b).
Proof. reflexivity. Qed.

Lemma core_obs_write : forall k k' c n j, vbounded k -> vbounded k' ->
  core_obs k = core_obs k' -> core_obs (E.write k c n j) = core_obs (E.write k' c n j).
Proof.
  intros k k' c n j [F1 C1] [F2 C2] H. unfold core_obs in *.
  assert (Ha : E.ca k = E.ca k') by congruence. assert (Hb : E.cb k = E.cb k') by congruence.
  assert (He : E.err k = E.err k') by congruence.
  assert (Hf : map (fobs k) (E.facts k) = map (fobs k') (E.facts k')) by congruence.
  assert (Hch : option_map (fobs k) (E.chan k) = option_map (fobs k') (E.chan k')) by congruence.
  assert (Ff : forall kk, E.facts (E.write kk c n j) = E.facts kk) by (destruct c; reflexivity).
  assert (Fc : forall kk, E.chan (E.write kk c n j) = E.chan kk) by (destruct c; reflexivity).
  rewrite !Ff, !Fc, (map_fobs_write k c n j _ F1), (map_fobs_write k' c n j _ F2), Hf.
  assert (Ch : option_map (fobs (E.write k c n j)) (E.chan k) =
               option_map (fobs (E.write k' c n j)) (E.chan k')).
  { destruct (E.chan k) as [g |] eqn:E1, (E.chan k') as [g' |] eqn:E2; cbn [option_map] in Hch |- *;
      try discriminate; [| reflexivity].
    assert (Hg : fobs k g = fobs k' g') by congruence.
    rewrite (fobs_write k c n j g (C1 g eq_refl)), (fobs_write k' c n j g' (C2 g' eq_refl)), Hg.
    reflexivity. }
  rewrite Ch. destruct c; simpl; rewrite ?Ha, ?Hb, ?He; reflexivity.
Qed.

Lemma map_fobs_same : forall k1 k2 l, E.va k1 = E.va k2 -> E.vb k1 = E.vb k2 ->
  map (fobs k1) l = map (fobs k2) l.
Proof. intros k1 k2 l Ha Hb. apply map_ext. apply fobs_same; assumption. Qed.

Lemma opt_fobs_same : forall k1 k2 o, E.va k1 = E.va k2 -> E.vb k1 = E.vb k2 ->
  option_map (fobs k1) o = option_map (fobs k2) o.
Proof. intros k1 k2 [f |] Ha Hb; simpl; [rewrite (fobs_same k1 k2 Ha Hb) |]; reflexivity. Qed.

Lemma obs_goto : forall k k' j, core_obs k = core_obs k' -> core_obs (E.goto k j) = core_obs (E.goto k' j).
Proof.
  intros k k' j H. unfold core_obs in *. unfold E.goto. simpl.
  rewrite (map_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k), (map_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k'),
    (opt_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k), (opt_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k')
    by reflexivity.
  congruence.
Qed.

Lemma obs_trap : forall k k', core_obs k = core_obs k' -> core_obs (E.trap k) = core_obs (E.trap k').
Proof.
  intros k k' H. unfold core_obs in *. unfold E.trap. simpl.
  rewrite (map_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k), (map_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k'),
    (opt_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k), (opt_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k')
    by reflexivity.
  congruence.
Qed.

Lemma obs_record : forall k k' p d, core_obs k = core_obs k' ->
  core_obs (E.record_fact k (E.claim k p d)) = core_obs (E.record_fact k' (E.claim k' p d)).
Proof.
  intros k k' p d H. unfold core_obs in *. unfold E.record_fact. simpl.
  rewrite (map_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k), (map_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k'),
    (opt_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k), (opt_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k')
    by reflexivity.
  assert (C : forall kk, fobs kk (E.claim kk p d) = (p, d, true))
    by (intros kk; unfold fobs, E.claim; simpl; rewrite Nat.eqb_refl; reflexivity).
  unfold fobs at 1 4. unfold E.claim. simpl. rewrite !Nat.eqb_refl.
  assert (Hm : map (fobs k) (E.facts k) = map (fobs k') (E.facts k')) by congruence.
  rewrite Hm. congruence.
Qed.

Lemma obs_commit : forall k k' p d, core_obs k = core_obs k' ->
  core_obs (E.commit_to k (E.claim k p d)) = core_obs (E.commit_to k' (E.claim k' p d)).
Proof.
  intros k k' p d H. unfold core_obs in *. unfold E.commit_to. simpl.
  rewrite (map_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k), (map_fobs_same (E.mkcore _ _ _ _ _ _ _ _) k')
    by reflexivity.
  unfold fobs at 2 4. unfold E.claim. simpl. rewrite !Nat.eqb_refl.
  assert (Hm : map (fobs k) (E.facts k) = map (fobs k') (E.facts k')) by congruence.
  rewrite Hm. congruence.
Qed.

Theorem obs_step : forall s t i, vbounded (E.core_of s) -> vbounded (E.core_of t) ->
  gobs s = gobs t -> gobs (E.exec s i) = gobs (E.exec t i).
Proof.
  intros [k mu c] [k' mu' c'] i Vs Vt H. simpl in Vs, Vt.
  rewrite !gobs_core in H.
  assert (Hk : core_obs k = core_obs k') by congruence.
  assert (Hmu : mu = mu') by congruence. assert (Hc : c = c') by congruence. subst mu' c'.
  assert (Ha : E.ca k = E.ca k') by (unfold core_obs in Hk; congruence).
  assert (Hb : E.cb k = E.cb k') by (unfold core_obs in Hk; congruence).
  assert (Hp : E.pc k = E.pc k') by (unfold core_obs in Hk; congruence).
  assert (He : E.err k = E.err k') by (unfold core_obs in Hk; congruence).
  assert (Hf : map (fobs k) (E.facts k) = map (fobs k') (E.facts k')) by (unfold core_obs in Hk; congruence).
  assert (Hch : option_map (fobs k) (E.chan k) = option_map (fobs k') (E.chan k'))
    by (unfold core_obs in Hk; congruence).
  assert (Hval : forall d, E.val k d = E.val k' d) by (intros []; simpl; congruence).
  assert (Hlen : length (E.facts k) = length (E.facts k')) by (eapply len_map_eq; exact Hf).
  assert (Hcs : (match E.chan k with Some _ => true | None => false end) =
                (match E.chan k' with Some _ => true | None => false end)).
  { destruct (E.chan k), (E.chan k'); simpl in Hch; congruence. }
  assert (Fire : E.fires k i = E.fires k' i).
  { destruct i; try reflexivity. unfold E.fires, E.certify_ok. rewrite He, Hcs. reflexivity. }
  unfold E.exec. simpl E.core_of; simpl E.mu; simpl E.cert. rewrite Fire, !gobs_core.
  f_equal. f_equal.
  unfold E.cexec. rewrite <- He. destruct (E.err k) eqn:Ek; [exact Hk |].
  destruct i as [d | d j | | p d | p d |].
  - rewrite Hval, Hp. apply core_obs_write; assumption.
  - rewrite <- (Hval d). destruct (E.val k d) as [| n].
    + rewrite Hp. apply obs_goto, Hk.
    + apply core_obs_write; assumption.
  - exact Hk.
  - assert (Ck : E.check_ok k p d = E.check_ok k' p d).
    { unfold E.check_ok. rewrite Ek, <- He, Hval, Hlen. reflexivity. }
    rewrite Ck. destruct (E.check_ok k' p d); [apply obs_record, Hk | apply obs_trap, Hk].
  - assert (Cm : E.commit_ok k p d = E.commit_ok k' p d).
    { unfold E.commit_ok. rewrite Ek, <- He, !exists_claim, Hf. reflexivity. }
    rewrite Cm. destruct (E.commit_ok k' p d); [apply obs_commit, Hk | apply obs_trap, Hk].
  - assert (Co : E.certify_ok k = E.certify_ok k') by (unfold E.certify_ok; rewrite Ek, <- He, Hcs; reflexivity).
    rewrite Co. destruct (E.certify_ok k'); [rewrite Hp; apply obs_goto, Hk | apply obs_trap, Hk].
Qed.

Theorem obs_run : forall tr s t, vbounded (E.core_of s) -> vbounded (E.core_of t) ->
  gobs s = gobs t -> gobs (E.run tr s) = gobs (E.run tr t).
Proof.
  induction tr as [| i tr IH]; intros s t Vs Vt H; [exact H |]. simpl.
  apply IH; [apply vb_step, Vs | apply vb_step, Vt | apply obs_step; assumption].
Qed.

(* Same gobs: the same next instruction of any program, so the same run. *)
Theorem obs_run_prog : forall n P s t, vbounded (E.core_of s) -> vbounded (E.core_of t) ->
  gobs s = gobs t -> gobs (E.run_prog n P s) = gobs (E.run_prog n P t).
Proof.
  induction n as [| n IH]; intros P s t Vs Vt H; [exact H |]. simpl.
  assert (N : E.next_instr P (E.core_of s) = E.next_instr P (E.core_of t)).
  { unfold gobs in H. injection H as _ _ Hp He _ _ _ _. unfold E.next_instr. rewrite He, Hp. reflexivity. }
  unfold E.step. rewrite N. destruct (E.next_instr P (E.core_of t)).
  - apply IH; [apply vb_step, Vs | apply vb_step, Vt | apply obs_step; assumption].
  - apply IH; assumption.
Qed.

(* gobs forgets version numbers: two start-like states differing only in
   the version of counter A have the same gobs. *)
Example obs_forgets_versions :
  gobs (E.mkst (E.mkcore 0 0 0 0 1 [] None false) 0 false) =
  gobs (E.mkst (E.mkcore 0 0 5 0 1 [] None false) 0 false).
Proof. reflexivity. Qed.

(* ================================================================= *)
(* B. U's state determines gobs of the guest at matching points.      *)
(* ================================================================= *)

Definition bank (r : nat) : E.ctr := if Nat.ltb r 64 then E.CA else E.CB.

Definition hfobs (h : @M.state hprop) (f : @M.fact hprop) : E.prop * E.ctr * bool :=
  (match unpair (hv h (M.f_reg f)) with Some (m, _) => pdec m | None => E.PZero end,
   bank (M.f_reg f), Nat.eqb (M.f_ver f) (hver h (M.f_reg f))).

Definition hobs (h : @M.state hprop) : GObs :=
  (hv h RA, hv h RB, hv h GPC, herr h, map (hfobs h) (M.facts (M.core_of h)),
   option_map (hfobs h) (M.chan (M.core_of h)), M.mu h, M.cert h).

Lemma bank_slot : forall c k, k < 16 -> bank (SLOT c k) = c.
Proof.
  intros [] k Hk; unfold bank, SLOT, ccode;
    [destruct (Nat.ltb_spec (48 + 16 * 0 + k) 64) | destruct (Nat.ltb_spec (48 + 16 * 1 + k) 64)];
    first [reflexivity | lia].
Qed.

Lemma rec_obs : forall g h r, rec_ok g h r ->
  hfobs h (hfact r) = fobs (E.core_of g) (gfact r).
Proof.
  intros g h r (Hk & Hv & _ & _ & Hiff & _ & _). unfold hfobs, fobs, hfact, gfact. simpl.
  rewrite Hv, unpair_pair, pdec_pcode, bank_slot by exact Hk. f_equal.
  destruct (Nat.eqb_spec (r_hv r) (hver h (SLOT (r_c r) (r_k r)))) as [E1 | E1];
  destruct (Nat.eqb_spec (r_gv r) (E.ver (E.core_of g) (r_c r))) as [E2 | E2]; try reflexivity.
  - exfalso. apply E2, Hiff, E1.
  - exfalso. apply E1, Hiff, E2.
Qed.

Theorem U_obs_at_rel : forall P sg rho g h, rel_with P sg rho g h -> hobs h = gobs g.
Proof.
  intros P sg rho g h R. unfold hobs, gobs.
  assert (HA : hv h RA = E.ca (E.core_of g)) by (rewrite <- greg_CA; exact (rw_greg _ _ _ _ _ R E.CA)).
  assert (HB : hv h RB = E.cb (E.core_of g)) by (rewrite <- greg_CB; exact (rw_greg _ _ _ _ _ R E.CB)).
  destruct (rw_head _ _ _ _ _ R) as (_ & He & _).
  rewrite HA, HB, (rw_gpc _ _ _ _ _ R), He, (rw_err _ _ _ _ _ R), (rw_mu _ _ _ _ _ R),
    (rw_cert _ _ _ _ _ R), (rw_hfacts _ _ _ _ _ R), (rw_gfacts _ _ _ _ _ R),
    (rw_hchan _ _ _ _ _ R), (rw_gchan _ _ _ _ _ R).
  assert (Mf : map (hfobs h) (map hfact sg) = map (fobs (E.core_of g)) (map gfact sg)).
  { rewrite !map_map. apply map_ext_in. intros r Hr. apply (rec_obs g h r), (rw_recs _ _ _ _ _ R), Hr. }
  assert (Mc : option_map (hfobs h) (option_map hfact rho) =
               option_map (fobs (E.core_of g)) (option_map gfact rho)).
  { destruct rho as [r |]; [| reflexivity]. simpl. f_equal.
    apply (rec_obs g h r), (rw_recs _ _ _ _ _ R), (rw_rho _ _ _ _ _ R), eq_refl. }
  rewrite Mf, Mc. reflexivity.
Qed.

(* ================================================================= *)
(* C. In order, with the full observation.                            *)
(* ================================================================= *)

Definition trapobs (ca cb : nat) (mu : nat) (cert : bool) : GObs :=
  (ca, cb, 0, true, [], None, mu, cert).

Definition gobsT (i : sinst) (s : E.state) : GObs :=
  if E.err (E.core_of s) then trapobs (E.ca (E.core_of s)) (E.cb (E.core_of s)) (E.mu s) (E.cert s)
  else gobs s.

Definition hobsT (h : @M.state hprop) : GObs :=
  if herr h then trapobs (hv h RA) (hv h RB) (M.mu h) (M.cert h) else hobs h.

Lemma GObs_dec : forall a b : GObs, {a = b} + {a <> b}.
Proof.
  assert (Pd : forall p q : E.prop, {p = q} + {p <> q}) by (decide equality; apply Nat.eq_dec).
  assert (Cd : forall p q : E.ctr, {p = q} + {p <> q}) by decide equality.
  assert (Od : forall a b : E.prop * E.ctr * bool, {a = b} + {a <> b})
    by (decide equality; [apply Bool.bool_dec | decide equality]).
  intros a b. repeat decide equality; try apply Nat.eq_dec; try apply Bool.bool_dec; auto.
Defined.

Theorem U_meets_strong_obs :
  universal_thiele small_class U_host (fun _ => GObs) gobsT 0.
Proof.
  exists U, (fun i => hload (fst (fst i)) (snd (fst i)) (snd i)), (fun _ => hobsT).
  intros [[P x] y]. simpl fst; simpl snd. split; [apply U_clause1 |]. split; [| intros n; apply clause3_free].
  set (Do := fun m t => hobsT (UniversalRun.hrun P x y t) = gobsT (P, x, y) (UniversalRun.grun P x y m)).
  assert (Ddec : forall m t, {Do m t} + {~ Do m t}) by (intros m t; apply GObs_dec).
  assert (RD : forall m t, Lu P x y m -> Ru P x y m t -> Do m t).
  { intros m t _ [[sg [rho R]] | [He RH]]; unfold Do, hobsT, gobsT.
    - destruct (rw_head _ _ _ _ _ R) as (_ & Hhe & _). rewrite Hhe, (rw_err _ _ _ _ _ R).
      apply (U_obs_at_rel P sg rho), R.
    - destruct RH as (_ & _ & HA & HB & Hhe & Hmu & Hc & _). rewrite Hhe, He.
      unfold trapobs. rewrite HA, HB, Hmu, Hc. reflexivity. }
  destruct (in_order (Lu P x y) (fun m => live_dec small_class (P, x, y) m)
              (fun m => live_prev small_class (P, x, y) m) Do Ddec (Ru P x y) RD
              (Ru_0 P x y) (Ru_S P x y)) as (f & Hinc & HD).
  exists f. split; [intros m _; apply Hinc |].
  intros m Hl. pose proof (HD m Hl) as Hd. unfold Do in Hd.
  (* ledger and flag come out of the observation *)
  assert (Hmc : M.mu (UniversalRun.hrun P x y (f m)) = E.mu (UniversalRun.grun P x y m) /\
                M.cert (UniversalRun.hrun P x y (f m)) = E.cert (UniversalRun.grun P x y m)).
  { unfold hobsT, gobsT, hobs, gobs, trapobs in Hd.
    destruct (herr _), (E.err _); injection Hd; intros; split; assumption. }
  destruct Hmc as [Hmu Hc].
  unfold match_at. simpl hP in *. rewrite !U_hr. fold (UniversalRun.hrun P x y (f m)).
  split; [| split].
  - rewrite (small_gr (P, x, y)). exact Hd.
  - simpl. rewrite Hc. pose proof (glat_cert (P, x, y) m) as Hlat.
    rewrite (small_gr (P, x, y)) in Hlat. simpl in Hlat. rewrite Hlat. reflexivity.
  - exists 0. split; [lia |]. rewrite U_ledger_at, <- small_gl. simpl. lia.
Qed.

Print Assumptions obs_run.
Print Assumptions obs_run_prog.
Print Assumptions U_obs_at_rel.
Print Assumptions U_meets_strong_obs.
