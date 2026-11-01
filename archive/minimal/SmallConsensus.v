(** SmallConsensus: the small machine's state, shared, solves wait-free
    consensus among any number of processes.

    Picture the state of EarnedCore.v shared by processes that each run
    instructions on it as indivisible steps and can read it. Each process
    proposes a bit. Process p runs CHECK on counter A with the property
    PZero to propose 0 or PEven to propose 1; both hold of a counter at 0,
    and nobody writes a counter. Then it reads the state and decides the bit
    named by the oldest fact in the table.

    The fact table is added to at the front and never loses an entry, and a
    CHECK that finds it full sets the trap latch, after which nothing
    changes. So the first CHECK of the run fixes the oldest fact for good.

    - Under every schedule, every decision is the oldest fact's bit, and
      that bit is some process's proposal ([sc_agreement], [sc_validity]).
    - Every process decides after two of its own steps, whatever the others
      do ([sc_wait_free]).

    In Herlihy's ranking of shared objects by the number of processes they
    bring to agreement with nobody waiting, the object sits at the top, with
    the sticky bit. The order of the fact table does the work here; the
    version rule and the commitment channel are not used. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(** A proposal is written as a property; the decision reads it back. *)
Definition sc_code (b : bool) : E.prop := if b then E.PEven else E.PZero.
Definition sc_decode (p : E.prop) : bool := match p with E.PEven => true | _ => false end.

Lemma sc_decode_code : forall b, sc_decode (sc_code b) = b.
Proof. intros []; reflexivity. Qed.

Definition sc_default : E.fact := E.mkfact E.PZero E.CA 0.
Definition sc_oldest (l : list E.fact) : E.fact := last l sc_default.

(** Each process is about to CHECK, is about to read, or has decided. *)
Inductive sc_local : Type := SStart | SChecked | SDecided (b : bool).

Record sc_config : Type := mkcfg { sc_state : E.state; sc_loc : nat -> sc_local }.

Section Protocol.

Variable inp : nat -> bool.

Definition sc_upd (loc : nat -> sc_local) (p : nat) (x : sc_local) (q : nat) : sc_local :=
  if Nat.eqb q p then x else loc q.

(** One step of process p. *)
Definition sc_step (c : sc_config) (p : nat) : sc_config :=
  match sc_loc c p with
  | SStart => mkcfg (E.exec (sc_state c) (E.CHECK (sc_code (inp p)) E.CA)) (sc_upd (sc_loc c) p SChecked)
  | SChecked => mkcfg (sc_state c)
      (sc_upd (sc_loc c) p (SDecided (sc_decode (E.f_prop (sc_oldest (E.facts (E.core_of (sc_state c))))))))
  | SDecided _ => c
  end.

(** A schedule is any list of process names, in the order they step. *)
Definition sc_run (c : sc_config) (sched : list nat) : sc_config := fold_left sc_step sched c.

Definition sc_init : sc_config := mkcfg (E.start 0 0) (fun _ => SStart).

Definition sc_facts (c : sc_config) : list E.fact := E.facts (E.core_of (sc_state c)).

Definition sc_inv (c : sc_config) : Prop :=
  E.ca (E.core_of (sc_state c)) = 0 /\
  (E.err (E.core_of (sc_state c)) = true -> sc_facts c <> []) /\
  (forall p, sc_loc c p <> SStart -> sc_facts c <> []) /\
  (sc_facts c <> [] -> exists r, E.f_prop (sc_oldest (sc_facts c)) = sc_code (inp r)) /\
  (forall p b, sc_loc c p = SDecided b -> b = sc_decode (E.f_prop (sc_oldest (sc_facts c)))).

Lemma sc_init_inv : sc_inv sc_init.
Proof.
  unfold sc_inv, sc_init, sc_facts. cbn.
  split; [reflexivity |]. split; [discriminate |].
  split; [intros p H; exfalso; apply H; reflexivity |].
  split; [intros H; exfalso; apply H; reflexivity |].
  intros p b H. discriminate.
Qed.

Lemma sc_oldest_cons : forall f l, l <> [] -> sc_oldest (f :: l) = sc_oldest l.
Proof. intros f [| g l] H; [contradiction | reflexivity]. Qed.

(** What a CHECK of a proposal does to a core whose counter A is 0. *)
Lemma sc_check_effect : forall k b, E.ca k = 0 ->
  let k' := E.cexec k (E.CHECK (sc_code b) E.CA) in
  E.ca k' = 0 /\
  ((E.facts k' = E.facts k /\ (E.err k = true \/ (E.err k' = true /\ E.facts k <> []))) \/
   (E.facts k' = E.claim k (sc_code b) E.CA :: E.facts k /\ E.err k' = E.err k)).
Proof.
  intros k b Hca k'. unfold k', E.cexec.
  destruct (E.err k) eqn:He.
  - split; [exact Hca |]. left. split; [reflexivity | left; reflexivity].
  - unfold E.check_ok. rewrite He. cbn [negb andb].
    assert (Hev : E.eval (sc_code b) (E.val k E.CA) = true).
    { unfold E.val. rewrite Hca. destruct b; reflexivity. }
    rewrite Hev. cbn [andb].
    destruct (Nat.ltb (length (E.facts k)) E.fact_cap) eqn:Hl.
    + cbn. split; [exact Hca |]. right. split; [reflexivity | exact He].
    + cbn. split; [exact Hca |]. left. split; [reflexivity | right; split; [reflexivity |]].
      apply Nat.ltb_ge in Hl. unfold E.fact_cap in Hl. intro Z. rewrite Z in Hl. simpl in Hl. lia.
Qed.

Lemma sc_step_inv : forall c p, sc_inv c -> sc_inv (sc_step c p).
Proof.
  intros c p [Hca [Herr [Hloc [Hold Hdec]]]]. unfold sc_step.
  destruct (sc_loc c p) as [| | b0] eqn:Hp.
  - (* the CHECK *)
    destruct (sc_check_effect (E.core_of (sc_state c)) (inp p) Hca) as [Hca' Hcase].
    unfold sc_inv, sc_facts in *. cbn [sc_state sc_loc E.core_of E.exec].
    destruct Hcase as [[Hf Herr'] | [Hf Herr']]; rewrite Hf.
    + (* the table did not change: the CHECK found the latch up or the table full *)
      assert (Hne : E.facts (E.core_of (sc_state c)) <> []).
      { destruct Herr' as [H | [_ H]]; [apply Herr; exact H | exact H]. }
      repeat split.
      * exact Hca'.
      * intros _. exact Hne.
      * intros q _. exact Hne.
      * exact Hold.
      * intros q b Hq. unfold sc_upd in Hq. destruct (Nat.eqb q p); [discriminate | exact (Hdec q b Hq)].
    + (* the fact went in at the front *)
      repeat split.
      * exact Hca'.
      * intros _. discriminate.
      * intros q _. discriminate.
      * intros _. destruct (E.facts (E.core_of (sc_state c))) as [| g l] eqn:Hl.
        -- exists p. reflexivity.
        -- rewrite sc_oldest_cons by discriminate. apply Hold. discriminate.
      * intros q b Hq. unfold sc_upd in Hq. destruct (Nat.eqb q p) eqn:Hqp; [discriminate |].
        rewrite (Hdec q b Hq). assert (Hne : E.facts (E.core_of (sc_state c)) <> []).
        { apply (Hloc q). rewrite Hq. discriminate. }
        rewrite sc_oldest_cons by exact Hne. reflexivity.
  - (* the read *)
    assert (Hne : sc_facts c <> []) by (apply (Hloc p); rewrite Hp; discriminate).
    unfold sc_inv. cbn [sc_state sc_loc]. unfold sc_facts in *. repeat split.
    + exact Hca.
    + exact Herr.
    + intros q _. exact Hne.
    + exact Hold.
    + intros q b Hq. unfold sc_upd in Hq. destruct (Nat.eqb q p).
      * injection Hq as <-. reflexivity.
      * exact (Hdec q b Hq).
  - repeat split; assumption.
Qed.

Lemma sc_run_inv : forall sched c, sc_inv c -> sc_inv (sc_run c sched).
Proof.
  induction sched as [| p sched IH]; intros c Hc; [exact Hc |].
  simpl. apply IH. apply sc_step_inv. exact Hc.
Qed.

(** Agreement: under every schedule, any two decisions are equal. *)
Theorem sc_agreement : forall sched p q bp bq,
  sc_loc (sc_run sc_init sched) p = SDecided bp ->
  sc_loc (sc_run sc_init sched) q = SDecided bq -> bp = bq.
Proof.
  intros sched p q bp bq Hp Hq.
  destruct (sc_run_inv sched sc_init sc_init_inv) as [_ [_ [_ [_ Hdec]]]].
  rewrite (Hdec p bp Hp), (Hdec q bq Hq). reflexivity.
Qed.

(** Validity: every decision is some process's proposal. *)
Theorem sc_validity : forall sched p b,
  sc_loc (sc_run sc_init sched) p = SDecided b -> exists r, b = inp r.
Proof.
  intros sched p b Hp.
  destruct (sc_run_inv sched sc_init sc_init_inv) as [_ [_ [Hloc [Hold Hdec]]]].
  assert (Hne : sc_facts (sc_run sc_init sched) <> []) by (apply (Hloc p); rewrite Hp; discriminate).
  destruct (Hold Hne) as [r Hr]. exists r. rewrite (Hdec p b Hp), Hr. apply sc_decode_code.
Qed.

(** A step of another process leaves p's local state alone. *)
Lemma sc_step_other : forall c p q, q <> p -> sc_loc (sc_step c q) p = sc_loc c p.
Proof.
  intros c p q Hqp. unfold sc_step. destruct (sc_loc c q); cbn [sc_loc]; try reflexivity;
    unfold sc_upd; replace (Nat.eqb p q) with false by (symmetry; apply Nat.eqb_neq; lia); reflexivity.
Qed.

Definition sc_progress (x : sc_local) : nat := match x with SStart => 0 | SChecked => 1 | SDecided _ => 2 end.

Lemma sc_step_progress : forall c p q,
  sc_progress (sc_loc (sc_step c q) p) >= sc_progress (sc_loc c p) /\
  (q = p -> sc_progress (sc_loc (sc_step c q) p) >= min 2 (S (sc_progress (sc_loc c p)))).
Proof.
  intros c p q. destruct (Nat.eq_dec q p) as [-> | Hne].
  - unfold sc_step. destruct (sc_loc c p) eqn:Hp; cbn [sc_loc]; unfold sc_upd; rewrite ?Nat.eqb_refl;
      rewrite ?Hp; simpl; lia.
  - rewrite (sc_step_other c p q Hne). split; [lia | intro; contradiction].
Qed.

Fixpoint sc_count (p : nat) (sched : list nat) : nat :=
  match sched with [] => 0 | q :: rest => (if Nat.eqb q p then 1 else 0) + sc_count p rest end.

Lemma sc_run_progress : forall sched c p,
  sc_progress (sc_loc (sc_run c sched) p) >= min 2 (sc_progress (sc_loc c p) + sc_count p sched).
Proof.
  induction sched as [| q sched IH]; intros c p; cbn [sc_run fold_left sc_count].
  - set (x := sc_progress (sc_loc c p)). lia.
  - pose proof (IH (sc_step c q) p) as H. unfold sc_run in H. destruct (sc_step_progress c p q) as [H1 H2].
    destruct (Nat.eqb_spec q p) as [-> | Hne].
    + specialize (H2 eq_refl). cbv iota.
      set (x := sc_progress (sc_loc c p)) in *. set (y := sc_progress (sc_loc (sc_step c p) p)) in *.
      set (z := sc_progress (sc_loc (fold_left sc_step sched (sc_step c p)) p)) in *. lia.
    + cbv iota.
      set (x := sc_progress (sc_loc c p)) in *. set (y := sc_progress (sc_loc (sc_step c q) p)) in *.
      set (z := sc_progress (sc_loc (fold_left sc_step sched (sc_step c q)) p)) in *. lia.
Qed.

(** Wait-freedom: a process that has taken two steps has decided, whatever
    the other processes did before, between or after. *)
Theorem sc_wait_free : forall sched p, sc_count p sched >= 2 ->
  exists b, sc_loc (sc_run sc_init sched) p = SDecided b.
Proof.
  intros sched p Hc. pose proof (sc_run_progress sched sc_init p) as H. cbn [sc_init sc_loc sc_progress] in H.
  set (k := sc_count p sched) in *.
  destruct (sc_loc (sc_run sc_init sched) p) as [| | b]; cbn [sc_progress] in H;
    [lia | lia | exists b; reflexivity].
Qed.

End Protocol.

Print Assumptions sc_agreement.
Print Assumptions sc_validity.
Print Assumptions sc_wait_free.
