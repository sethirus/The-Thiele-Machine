(** Presented.v: a Thiele machine with a driver and number codes, and
    what its runs, ledger, latch and surcharge are.

    A presented machine is a certification system (the record of
    ThieleComplete.v, field for field the record of the book: states,
    moves, a step, a cost per move, a yes/no reading, and the toll
    cs_cert_costs) together with

      pm_next     a driver: in each state, the move to take, or None to halt;
      pm_scode    a number for each state, with a decoder pm_sdec that
                  gives the state back from its number;
      pm_icode    a number for each move, with a decoder pm_idec that gives
                  the move back from its number.

    Each code is injective because it has a left inverse
    [presented_scode_inj, presented_icode_inj].

    For a start state s0 and a number of steps n:

      presented_run M s0 n   the state after n driven steps (a halted
                             machine stays where it is);
      mledger M s0 n         the total cost of the moves taken in those
                             steps;
      mhalted M s0 n         the driver has halted by step n;
      mlatch M s0 n          the reading has been yes at some state among
                             the first n + 1;
      first_raise M s0 n     the first move that turns the reading from no
                             to yes within n steps, if the reading starts at
                             no and some move does;
      surcharge M s0 n       when the latch is up, 3 minus the cost of the
                             first raising move (that cost counted as 0
                             when the reading is yes at the start); 0 when
                             the latch is down.

    The surcharge is what a host that must pay at least 3 to raise its own
    flag adds to the guest's ledger. What is proved (every result closed
    under the global context):

      1. Runs compose and a halted run stays put, ledger included
         [presented_run_add, mledger_add, presented_halted_stable].
      2. The latch is up exactly when the reading has been yes at some
         state so far, so it is monotone in n [presented_mlatch_iff,
         presented_mlatch_mono].
      3. The first raise is a real raise: a move taken from a state where
         the reading is no, every earlier reading is no, and the move turns
         the reading to yes; it does not change as n grows
         [presented_first_raise_spec, presented_first_raise_stable].
      4. When the reading starts at no, the surcharge is at most 2,
         because the raising move pays the toll cs_cert_costs
         [presented_surcharge_le_two]; while the latch is down it is 0
         [presented_surcharge_zero_before_raise]; when the reading starts
         at yes it is 3 [presented_surcharge_raised_at_start]; once the
         latch is up it does not change [presented_surcharge_stable]; and
         ledger plus surcharge is always at least 3 when the latch is up
         [presented_surcharge_sufficient].
      5. The floor of EarnedPriced.v forbids an exact ledger below 3. If a
         guest's latch is up after n steps with ledger below 3, no run of
         the EarnedPriced machine from a clean start ends with its flag
         equal to that latch and its ledger grown by exactly the guest's
         ledger [presented_no_exact_below_three,
         presented_no_exact_below_three_program]; any extra amount x that
         makes such a match possible has ledger + x >= 3
         [presented_extra_at_least]. A two-state guest that raises its
         reading with one move of cost 1 shows the case is not empty
         [presented_flip_facts, presented_flip_no_exact].

    Dependencies: Coq standard library, EarnedCore.v, EarnedGeneric.v,
    EarnedPriced.v and ThieleComplete.v. No axioms, no Admitted.            *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   ThieleComplete.v: this file imports nothing outside the standard library
   and the minimal files, so it re-checks from a clean checkout. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedGeneric.
Require Minimal.EarnedPriced.
Require Minimal.ThieleComplete.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Module T := Minimal.ThieleComplete.

(* ================================================================= *)
(* Presented machines.                                                *)
(* ================================================================= *)

Record presented_machine : Type := mk_presented {
  pm_sys : T.CertificationSystem;
  pm_next : T.cs_state pm_sys -> option (T.cs_instr pm_sys);
  pm_scode : T.cs_state pm_sys -> nat;
  pm_sdec : nat -> option (T.cs_state pm_sys);
  pm_icode : T.cs_instr pm_sys -> nat;
  pm_idec : nat -> option (T.cs_instr pm_sys);
  pm_sdec_scode : forall s, pm_sdec (pm_scode s) = Some s;
  pm_idec_icode : forall i, pm_idec (pm_icode i) = Some i
}.

Section Presented.

Variable M : presented_machine.

Local Notation st := (T.cs_state (pm_sys M)).
Local Notation mv := (T.cs_instr (pm_sys M)).
Local Notation cstep := (T.cs_step (pm_sys M)).
Local Notation ccost := (T.cs_cost (pm_sys M)).
Local Notation rd := (T.cs_cert (pm_sys M)).
Local Notation next := (pm_next M).

Theorem presented_scode_inj : forall s t : st, pm_scode M s = pm_scode M t -> s = t.
Proof.
  intros s t H. pose proof (pm_sdec_scode M s) as Hs. pose proof (pm_sdec_scode M t) as Ht.
  rewrite H in Hs. rewrite Hs in Ht. injection Ht as ->. reflexivity.
Qed.

Theorem presented_icode_inj : forall i j : mv, pm_icode M i = pm_icode M j -> i = j.
Proof.
  intros i j H. pose proof (pm_idec_icode M i) as Hi. pose proof (pm_idec_icode M j) as Hj.
  rewrite H in Hi. rewrite Hi in Hj. injection Hj as ->. reflexivity.
Qed.

(* ================================================================= *)
(* Runs, ledger, halting, latch, first raise, surcharge.              *)
(* ================================================================= *)

Fixpoint presented_run (s : st) (n : nat) : st :=
  match n with
  | 0 => s
  | S n' => match next s with None => s | Some i => presented_run (cstep s i) n' end
  end.

Fixpoint mledger (s : st) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match next s with None => 0 | Some i => ccost i + mledger (cstep s i) n' end
  end.

Definition mhalted (s : st) (n : nat) : Prop := next (presented_run s n) = None.

Fixpoint mlatch (s : st) (n : nat) : bool :=
  rd s ||
  match n with
  | 0 => false
  | S n' => match next s with None => false | Some i => mlatch (cstep s i) n' end
  end.

Fixpoint first_raise (s : st) (n : nat) : option mv :=
  if rd s then None else
  match n with
  | 0 => None
  | S n' =>
      match next s with
      | None => None
      | Some i => if rd (cstep s i) then Some i else first_raise (cstep s i) n'
      end
  end.

(* The cost of the first raising move, 0 when there is none. *)
Definition raise_cost (s : st) (n : nat) : nat :=
  match first_raise s n with Some i => ccost i | None => 0 end.

Definition surcharge (s : st) (n : nat) : nat :=
  if mlatch s n then 3 - raise_cost s n else 0.

(* ================================================================= *)
(* Runs and ledger.                                                   *)
(* ================================================================= *)

Lemma presented_run_halted : forall s n, next s = None -> presented_run s n = s.
Proof. intros s [| n] H; simpl; [reflexivity | rewrite H; reflexivity]. Qed.

Lemma mledger_halted : forall s n, next s = None -> mledger s n = 0.
Proof. intros s [| n] H; simpl; [reflexivity | rewrite H; reflexivity]. Qed.

Theorem presented_run_add : forall m n s,
  presented_run s (m + n) = presented_run (presented_run s m) n.
Proof.
  induction m as [| m IH]; intros n s; simpl; [reflexivity |].
  destruct (next s) as [i |] eqn:E; [apply IH |].
  symmetry. apply presented_run_halted. exact E.
Qed.

Theorem mledger_add : forall m n s,
  mledger s (m + n) = mledger s m + mledger (presented_run s m) n.
Proof.
  induction m as [| m IH]; intros n s; simpl; [reflexivity |].
  destruct (next s) as [i |] eqn:E; [rewrite IH; lia |].
  rewrite mledger_halted by exact E. reflexivity.
Qed.

(* One more step, at the end. *)
Theorem presented_run_succ : forall n s,
  presented_run s (S n) =
  match next (presented_run s n) with
  | None => presented_run s n
  | Some i => cstep (presented_run s n) i
  end.
Proof.
  intros n s. replace (S n) with (n + 1) by lia. rewrite presented_run_add.
  simpl. destruct (next (presented_run s n)); reflexivity.
Qed.

Theorem mledger_succ : forall n s,
  mledger s (S n) =
  mledger s n + match next (presented_run s n) with None => 0 | Some i => ccost i end.
Proof.
  intros n s. replace (S n) with (n + 1) by lia. rewrite mledger_add.
  simpl. destruct (next (presented_run s n)); simpl; lia.
Qed.

(* Once halted, the state and the ledger stay put. *)
Theorem presented_halted_stable : forall s n m,
  mhalted s n -> n <= m ->
  presented_run s m = presented_run s n /\ mledger s m = mledger s n.
Proof.
  intros s n m H Hle. unfold mhalted in H.
  replace m with (n + (m - n)) by lia.
  rewrite presented_run_add, mledger_add.
  rewrite (presented_run_halted _ (m - n) H), (mledger_halted _ (m - n) H).
  split; [reflexivity | lia].
Qed.

(* ================================================================= *)
(* The latch.                                                         *)
(* ================================================================= *)

Theorem presented_mlatch_iff : forall n s,
  mlatch s n = true <-> exists m, m <= n /\ rd (presented_run s m) = true.
Proof.
  induction n as [| n IH]; intro s.
  - simpl. rewrite orb_false_r. split.
    + intro H. exists 0. split; [lia | exact H].
    + intros [m [Hm H]]. assert (m = 0) as -> by lia. exact H.
  - simpl. rewrite orb_true_iff. split.
    + intros [H | H].
      * exists 0. split; [lia | exact H].
      * destruct (next s) as [i |] eqn:E; [| discriminate].
        apply IH in H. destruct H as [m [Hm H]].
        exists (S m). split; [lia |]. simpl. rewrite E. exact H.
    + intros [[| m] [Hm H]].
      * left. exact H.
      * simpl in H. destruct (next s) as [i |] eqn:E.
        -- right. apply IH. exists m. split; [lia | exact H].
        -- left. exact H.
Qed.

Theorem presented_mlatch_mono : forall s n m,
  n <= m -> mlatch s n = true -> mlatch s m = true.
Proof.
  intros s n m Hle H. apply presented_mlatch_iff in H. apply presented_mlatch_iff.
  destruct H as [k [Hk H]]. exists k. split; [lia | exact H].
Qed.

Corollary presented_mlatch_succ : forall s n, mlatch s n = true -> mlatch s (S n) = true.
Proof. intros s n. apply presented_mlatch_mono. lia. Qed.

(* ================================================================= *)
(* The first raise.                                                   *)
(* ================================================================= *)

(* If the reading starts at no and the latch is up after n steps, the
   first raise is the move taken at some step m < n, from a state where
   the reading is no, with every reading up to that state no, and the move
   turns the reading to yes. *)
Theorem presented_first_raise_spec : forall n s,
  rd s = false -> mlatch s n = true ->
  exists m i, m < n /\ next (presented_run s m) = Some i /\
    (forall m', m' <= m -> rd (presented_run s m') = false) /\
    rd (cstep (presented_run s m) i) = true /\ first_raise s n = Some i.
Proof.
  induction n as [| n IH]; intros s H0 H1.
  - simpl in H1. rewrite H0 in H1. discriminate.
  - simpl in H1. rewrite H0 in H1. simpl in H1.
    destruct (next s) as [i |] eqn:E; [| discriminate].
    destruct (rd (cstep s i)) eqn:Hr.
    + exists 0, i. split; [lia |]. split; [exact E |].
      split; [intros m' Hm'; assert (m' = 0) as -> by lia; exact H0 |].
      split; [exact Hr |]. simpl. rewrite H0, E. simpl. rewrite Hr. reflexivity.
    + destruct (IH (cstep s i) Hr H1) as [m [j [Hm [Hn [Hall [Hup Hf]]]]]].
      exists (S m), j. split; [lia |].
      split; [simpl; rewrite E; exact Hn |].
      split.
      { intros [| m'] Hm'; [exact H0 |]. simpl. rewrite E. apply Hall. lia. }
      split; [simpl; rewrite E; exact Hup |].
      simpl. rewrite H0, E. simpl. rewrite Hr. exact Hf.
Qed.

(* Once the latch is up, more steps do not change the first raise. *)
Theorem presented_first_raise_stable : forall n m s,
  mlatch s n = true -> n <= m -> first_raise s m = first_raise s n.
Proof.
  induction n as [| n IH]; intros m s H1 Hm.
  - simpl in H1. rewrite orb_false_r in H1.
    destruct m; simpl; rewrite H1; reflexivity.
  - destruct m as [| m]; [lia |].
    simpl. destruct (rd s) eqn:Hs; [reflexivity |].
    simpl in H1. rewrite Hs in H1. simpl in H1.
    destruct (next s) as [i |] eqn:E; [| discriminate].
    destruct (rd (cstep s i)) eqn:Hr; [reflexivity |].
    apply IH; [exact H1 | lia].
Qed.

(* The ledger after n steps includes the cost of the first raise. *)
Theorem presented_raise_cost_le_ledger : forall n s i,
  first_raise s n = Some i -> ccost i <= mledger s n.
Proof.
  induction n as [| n IH]; intros s i H.
  - simpl in H. destruct (rd s); discriminate.
  - simpl in H. destruct (rd s); [discriminate |].
    simpl. destruct (next s) as [j |]; [| discriminate].
    destruct (rd (cstep s j)).
    + injection H as ->. lia.
    + pose proof (IH _ _ H). lia.
Qed.

(* ================================================================= *)
(* The surcharge.                                                     *)
(* ================================================================= *)

(* From a start where the reading is no, the surcharge is at most 2: the
   first raising move pays the toll of at least 1. *)
Theorem presented_surcharge_le_two : forall s0 n,
  rd s0 = false -> surcharge s0 n <= 2.
Proof.
  intros s0 n H0. unfold surcharge. destruct (mlatch s0 n) eqn:Hl; [| lia].
  destruct (presented_first_raise_spec n s0 H0 Hl) as [m [i [_ [_ [Hall [Hup Hf]]]]]].
  unfold raise_cost. rewrite Hf.
  pose proof (T.cs_cert_costs (pm_sys M) (presented_run s0 m) i (Hall m (le_n m)) Hup).
  lia.
Qed.

(* While the reading has been no at every state so far, there is no
   surcharge. *)
Theorem presented_surcharge_zero_before_raise : forall s0 n,
  (forall m, m <= n -> rd (presented_run s0 m) = false) -> surcharge s0 n = 0.
Proof.
  intros s0 n H. unfold surcharge. destruct (mlatch s0 n) eqn:Hl; [| reflexivity].
  apply presented_mlatch_iff in Hl. destruct Hl as [m [Hm Hr]].
  rewrite (H m Hm) in Hr. discriminate.
Qed.

(* A reading that is yes at the start leaves the whole floor of 3 to the
   surcharge. *)
Theorem presented_surcharge_raised_at_start : forall s0 n,
  rd s0 = true -> surcharge s0 n = 3.
Proof.
  intros s0 n H. unfold surcharge, raise_cost.
  assert (Hl : mlatch s0 n = true) by (destruct n; simpl; rewrite H; reflexivity).
  assert (Hf : first_raise s0 n = None) by (destruct n; simpl; rewrite H; reflexivity).
  rewrite Hl, Hf. reflexivity.
Qed.

(* Once the latch is up, the surcharge does not change. *)
Theorem presented_surcharge_stable : forall s0 n m,
  n <= m -> mlatch s0 n = true -> surcharge s0 m = surcharge s0 n.
Proof.
  intros s0 n m Hle Hl. unfold surcharge, raise_cost.
  rewrite Hl, (presented_mlatch_mono s0 n m Hle Hl).
  rewrite (presented_first_raise_stable n m s0 Hl Hle). reflexivity.
Qed.

(* Ledger plus surcharge reaches the floor of 3 whenever the latch is up. *)
Theorem presented_surcharge_sufficient : forall s0 n,
  mlatch s0 n = true -> mledger s0 n + surcharge s0 n >= 3.
Proof.
  intros s0 n Hl. unfold surcharge, raise_cost. rewrite Hl.
  destruct (first_raise s0 n) as [i |] eqn:Hf; [| lia].
  pose proof (presented_raise_cost_le_ledger n s0 i Hf). lia.
Qed.

End Presented.

(* ================================================================= *)
(* The floor of 3 forbids an exact ledger below 3.                    *)
(* ================================================================= *)

(* pr_certified_run_min_cost: a run of the EarnedPriced machine from a
   clean start that ends with the flag up has grown the ledger by at least
   3. So if a guest's latch is up after n steps with ledger below 3, no
   such run ends with its flag equal to the latch and its ledger grown by
   exactly the guest's ledger. *)
Theorem presented_no_exact_below_three :
  forall (prop : Type) (prop_eqb : prop -> prop -> bool) (eval : prop -> nat -> bool),
  (forall p q, prop_eqb p q = true <-> p = q) ->
  forall (M : presented_machine) (g0 : T.cs_state (pm_sys M)) (n : nat),
  mlatch M g0 n = true -> mledger M g0 n < 3 ->
  forall (h0 : @G.state prop) (tr : list (@P.pr_instr prop)),
  G.clean_start h0 ->
  ~ (G.cert (P.pr_run prop_eqb eval tr h0) = mlatch M g0 n /\
     G.mu (P.pr_run prop_eqb eval tr h0) = G.mu h0 + mledger M g0 n).
Proof.
  intros prop prop_eqb eval Heq M g0 n Hl Hlt h0 tr H0 [Hc Hm].
  rewrite Hl in Hc.
  destruct (P.pr_certified_run_min_cost prop_eqb Heq eval h0 tr H0 Hc) as [_ Hge].
  lia.
Qed.

(* The same for a stored program run from a start state, by
   pr_program_certified_min_cost. *)
Theorem presented_no_exact_below_three_program :
  forall (prop : Type) (prop_eqb : prop -> prop -> bool) (eval : prop -> nat -> bool),
  (forall p q, prop_eqb p q = true <-> p = q) ->
  forall (M : presented_machine) (g0 : T.cs_state (pm_sys M)) (n : nat),
  mlatch M g0 n = true -> mledger M g0 n < 3 ->
  forall (Q : list (@P.pr_instr prop)) (k a b : nat),
  ~ (G.cert (P.pr_run_prog prop_eqb eval k Q (G.start a b)) = mlatch M g0 n /\
     G.mu (P.pr_run_prog prop_eqb eval k Q (G.start a b)) = mledger M g0 n).
Proof.
  intros prop prop_eqb eval Heq M g0 n Hl Hlt Q k a b [Hc Hm].
  rewrite Hl in Hc.
  pose proof (P.pr_program_certified_min_cost prop_eqb Heq eval k Q a b Hc). lia.
Qed.

(* Any extra amount x that lets such a run match the latch with ledger
   grown by the guest's ledger plus x has ledger + x >= 3. *)
Theorem presented_extra_at_least :
  forall (prop : Type) (prop_eqb : prop -> prop -> bool) (eval : prop -> nat -> bool),
  (forall p q, prop_eqb p q = true <-> p = q) ->
  forall (M : presented_machine) (g0 : T.cs_state (pm_sys M)) (n x : nat)
         (h0 : @G.state prop) (tr : list (@P.pr_instr prop)),
  G.clean_start h0 -> mlatch M g0 n = true ->
  G.cert (P.pr_run prop_eqb eval tr h0) = mlatch M g0 n ->
  G.mu (P.pr_run prop_eqb eval tr h0) = G.mu h0 + mledger M g0 n + x ->
  mledger M g0 n + x >= 3.
Proof.
  intros prop prop_eqb eval Heq M g0 n x h0 tr H0 Hl Hc Hm.
  rewrite Hl in Hc.
  destruct (P.pr_certified_run_min_cost prop_eqb Heq eval h0 tr H0 Hc) as [_ Hge].
  lia.
Qed.

(* ================================================================= *)
(* A guest that raises its reading for 1.                             *)
(* ================================================================= *)

(* Two states, no and yes; one move, which goes to yes and costs 1. *)
Definition presented_flip_system : T.CertificationSystem :=
  T.mk_cert_system bool unit (fun _ _ => true) (fun _ => 1) (fun b => b)
    (fun _ _ _ _ => le_n 1).

Definition presented_flip_scode (b : bool) : nat := if b then 1 else 0.
Definition presented_flip_sdecode (n : nat) : option bool :=
  match n with 0 => Some false | 1 => Some true | _ => None end.

Lemma presented_flip_sdec : forall b : bool,
  presented_flip_sdecode (presented_flip_scode b) = Some b.
Proof. intros []; reflexivity. Qed.

Lemma presented_flip_idec : forall u : unit, Some tt = Some u.
Proof. intros []; reflexivity. Qed.

(* The driver takes the move while the reading is no, then halts. *)
Definition presented_flip : presented_machine :=
  mk_presented presented_flip_system
    (fun b : bool => if b then None else Some tt)
    presented_flip_scode presented_flip_sdecode
    (fun _ : unit => 0) (fun _ : nat => Some tt)
    presented_flip_sdec presented_flip_idec.

(* From no, one step raises the latch with ledger 1, so the surcharge is
   2, and the run has halted. *)
Theorem presented_flip_facts :
  mlatch presented_flip false 1 = true /\ mledger presented_flip false 1 = 1 /\
  surcharge presented_flip false 1 = 2 /\ mhalted presented_flip false 1.
Proof. repeat split. Qed.

(* So no EarnedPriced run from a clean start matches this guest exactly. *)
Theorem presented_flip_no_exact :
  forall (prop : Type) (prop_eqb : prop -> prop -> bool) (eval : prop -> nat -> bool),
  (forall p q, prop_eqb p q = true <-> p = q) ->
  forall (h0 : @G.state prop) (tr : list (@P.pr_instr prop)),
  G.clean_start h0 ->
  ~ (G.cert (P.pr_run prop_eqb eval tr h0) = mlatch presented_flip false 1 /\
     G.mu (P.pr_run prop_eqb eval tr h0) = G.mu h0 + mledger presented_flip false 1).
Proof.
  intros prop prop_eqb eval Heq h0 tr H0.
  apply (presented_no_exact_below_three prop prop_eqb eval Heq presented_flip false 1);
    [reflexivity | simpl; lia | exact H0].
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions presented_scode_inj.
Print Assumptions presented_icode_inj.
Print Assumptions presented_run_add.
Print Assumptions mledger_add.
Print Assumptions presented_run_succ.
Print Assumptions mledger_succ.
Print Assumptions presented_halted_stable.
Print Assumptions presented_mlatch_iff.
Print Assumptions presented_mlatch_mono.
Print Assumptions presented_mlatch_succ.
Print Assumptions presented_first_raise_spec.
Print Assumptions presented_first_raise_stable.
Print Assumptions presented_raise_cost_le_ledger.
Print Assumptions presented_surcharge_le_two.
Print Assumptions presented_surcharge_zero_before_raise.
Print Assumptions presented_surcharge_raised_at_start.
Print Assumptions presented_surcharge_stable.
Print Assumptions presented_surcharge_sufficient.
Print Assumptions presented_no_exact_below_three.
Print Assumptions presented_no_exact_below_three_program.
Print Assumptions presented_extra_at_least.
Print Assumptions presented_flip_facts.
Print Assumptions presented_flip_no_exact.
