(** UniversalThiele.v: one fixed machine that runs any small-machine program
    as a guest, with the guest's record and toll enforced by its own step.

    Definitions, in the words the book uses.

      A Thiele machine is a certification system: states, moves, a step, a
      cost per move, a yes/no reading (the record), and the toll: a step
      that turns the reading from no to yes costs at least 1.

      Thiele-complete: a Thiele machine whose base computes anything a Turing
      machine can while keeping its own record and paying its own toll.
      EarnedCore.v proves this for the small machine: its INC/DEC fragment is
      the two-counter machine step for step, CERTIFY is the only way up for
      its flag, and the raise costs at least 1.

      A universal Thiele machine: one fixed machine that runs any other
      Thiele machine of a stated class as a guest, with the guest's record
      and toll enforced by the host's own step.

    The guest class. A guest is a small-machine program P (EarnedCore.instr)
    together with a small-machine state g: two unbounded counters with
    versions, a program counter, the fact table, the commitment channel, the
    trap latch, the guest's own ledger and its own certified flag. Its step
    is EarnedCore.step P, its cost is EarnedCore.cost, its reading is its own
    flag. This is the computably presented class in the same sense as
    Turing's: the guest is a finite program over a fixed instruction set,
    held by the host as data.

    Why the class is not trivial. The small machine is Thiele-complete
    (EarnedCore.v, simulation_run and halting_correspondence: every
    two-counter program runs on it unchanged, and by Minsky every Turing
    machine runs as a two-counter program). So every computation runs as a
    guest, and every guest keeps a record that only a paid
    CHECK, COMMIT, CERTIFY chain can raise. What the class does not give is
    a cost-exact image of an arbitrary Thiele machine: a guest pays 1 for
    each CHECK, COMMIT and CERTIFY and 0 for counting, so a foreign machine
    compiled in through Minsky's encoding keeps its computation and its toll
    (a raise still costs at least 1) but not its own price list, and its
    reading has to be computed into a counter and then checked with the
    fixed property language (PZero, PEven, PGe n).

    The host. Its state holds its own small-machine core (counters, program
    counter, facts, channel, trap latch), its own ledger hmu and its own
    flag hcert, and the guest: the guest program as data, the guest state,
    and the mirrored record mrec. Its moves are

      OWN i     run the small-machine instruction i on the host's own core.
                Costs what the small machine charges. Only OWN CERTIFY can
                raise hcert, by the small machine's own rule.
      GSTEP b   one guest step with budget b. The host fetches the guest's
                next instruction; if the guest is running and that
                instruction costs at most b, the host executes it on the
                guest state. The host reads the guest's flag before and
                after, and if it went from no to yes, mrec goes up in that
                same host step. Costs b, always.

    Charging the budget instead of the fetched cost keeps the cost a
    function of the move alone, as the CertificationSystem record asks. A
    guest instruction costs at most 1, so GSTEP 1 runs every guest. The
    host's reading is hcert || mrec; the two halves are stated apart.

    What is proved (every result closed under the global context):

      1. The host is a Thiele machine: a raise of hcert, of mrec, or of the
         combined reading costs at least 1  [host_own_toll,
         host_mirror_toll, host_toll]. It is Thiele-complete: its OWN
         fragment runs every two-counter program, with the halting
         correspondence  [host_thiele_complete].
      2. Universal simulation: n GSTEP 1 moves leave exactly the guest state
         that n guest steps produce; the stored program U, three host
         instructions in a loop, does the same every three host steps
         [universal_simulation, universal_program_simulation].
      3. Record agreement: if mrec starts equal to the guest's flag, it
         stays equal after every host move of every kind
         [record_agreement_step, record_agreement, record_agreement_program,
         simulated_record].
      4. Toll by the host's step: a guest crossing raises mrec in that host
         step, and that step costs the host at least 1; every crossing of a
         simulated guest run is a host crossing at the matching step; the
         host's ledger grows by at least what the guest's ledger grows
         [toll_enforced_by_host_step, every_guest_crossing_is_a_host_crossing,
         host_pays_for_guest, host_cost_covers_guest].
      5. No forging: mrec rises only in a GSTEP whose guest instruction is
         the guest's own CERTIFY, a real guest crossing in the same step,
         for every host instruction sequence and every stored host program;
         a sequence with no GSTEP leaves the guest and mrec untouched
         [no_free_host_certification_step, no_free_host_certification,
         no_free_host_certification_program, guestless_runs_leave_mirror].
      6. Non-vacuity: a concrete guest that certifies, run on the host,
         raises mrec at the third host move and pays 3; a guest that tries
         CERTIFY with nothing committed traps and mrec stays down
         [demo_certifies, demo_program_certifies, demo_forgery_fails].

    Dependencies: Coq standard library and EarnedCore.v. No axioms, no
    Admitted.                                                              *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose, as in
   EarnedCore.v: this file imports nothing outside the standard library and
   EarnedCore.v, so it re-checks from a clean checkout.
   Its link to the abstract record (the host and the guest as
   CertificationSystem instances, and the trace cost floor for the host)
   lives in UniversalThieleLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

(* ================================================================= *)
(* The host.                                                          *)
(* ================================================================= *)

Inductive hinstr : Type :=
| OWN (i : E.instr)    (* a small-machine instruction on the host's core *)
| GSTEP (b : nat).     (* one guest step with budget b                    *)

Definition hcost (i : hinstr) : nat :=
  match i with OWN j => E.cost j | GSTEP b => b end.

Record hstate : Type := mkh {
  hcore : E.core;          (* the host's own base                     *)
  hmu : nat;               (* the host's ledger                       *)
  hcert : bool;            (* the host's own record                   *)
  gprog : list E.instr;    (* the guest program, held as data         *)
  gst : E.state;           (* the guest state                         *)
  mrec : bool              (* the host's mirror of the guest's record *)
}.

(* The guest instruction a budget of b lets the host run, if any. *)
Definition gmove (P : list E.instr) (g : E.state) (b : nat) : option E.instr :=
  match E.next_instr P (E.core_of g) with
  | Some i => if Nat.leb (E.cost i) b then Some i else None
  | None => None
  end.

Definition gnext (P : list E.instr) (g : E.state) (b : nat) : E.state :=
  match gmove P g b with Some i => E.exec g i | None => g end.

(* The guest's reading went from no to yes. *)
Definition crossing (g g' : E.state) : bool := negb (E.cert g) && E.cert g'.

(* The host's step. A trapped host changes nothing but its ledger. *)
Definition hexec (h : hstate) (i : hinstr) : hstate :=
  match i with
  | OWN j =>
      mkh (E.cexec (hcore h) j) (hmu h + E.cost j)
          (hcert h || E.fires (hcore h) j) (gprog h) (gst h) (mrec h)
  | GSTEP b =>
      if E.err (hcore h)
      then mkh (hcore h) (hmu h + b) (hcert h) (gprog h) (gst h) (mrec h)
      else let g' := gnext (gprog h) (gst h) b in
           mkh (E.goto (hcore h) (S (E.pc (hcore h)))) (hmu h + b)
               (hcert h) (gprog h) g' (mrec h || crossing (gst h) g')
  end.

Definition hread (h : hstate) : bool := hcert h || mrec h.

Fixpoint hrun (tr : list hinstr) (h : hstate) : hstate :=
  match tr with [] => h | i :: rest => hrun rest (hexec h i) end.

Fixpoint htotal_cost (tr : list hinstr) : nat :=
  match tr with [] => 0 | i :: rest => hcost i + htotal_cost rest end.

(* Stored host programs, in the small machine's style. *)
Definition hnext (Q : list hinstr) (k : E.core) : option hinstr :=
  if E.err k then None else
  match E.fetch Q (E.pc k) with Some (OWN E.HALT) => None | o => o end.

Definition hhalted (Q : list hinstr) (k : E.core) : Prop := hnext Q k = None.

Definition hstep (Q : list hinstr) (h : hstate) : hstate :=
  match hnext Q (hcore h) with None => h | Some i => hexec h i end.

Fixpoint hrun_prog (n : nat) (Q : list hinstr) (h : hstate) : hstate :=
  match n with 0 => h | S m => hrun_prog m Q (hstep Q h) end.

Fixpoint htrace_of (n : nat) (Q : list hinstr) (h : hstate) : list hinstr :=
  match n with
  | 0 => []
  | S m => match hnext Q (hcore h) with
           | None => []
           | Some i => i :: htrace_of m Q (hexec h i)
           end
  end.

(* Loading a guest: host core at (a, b), guest at (x, y), both clean. *)
Definition hload (a b : nat) (P : list E.instr) (x y : nat) : hstate :=
  mkh (E.start_core a b) 0 false P (E.start x y) false.

(* ================================================================= *)
(* Basic facts.                                                       *)
(* ================================================================= *)

Lemma hrun_app : forall l1 l2 h, hrun (l1 ++ l2) h = hrun l2 (hrun l1 h).
Proof. induction l1; intros; simpl; auto. Qed.

Lemma hrun_prog_halted : forall n Q h, hhalted Q (hcore h) -> hrun_prog n Q h = h.
Proof.
  induction n; intros Q h H; simpl; [reflexivity |].
  unfold hstep. unfold hhalted in H. rewrite H. apply IHn. exact H.
Qed.

(* Every stored-program run is a run of the instructions it executes. *)
Lemma hrun_prog_trace : forall n Q h, hrun_prog n Q h = hrun (htrace_of n Q h) h.
Proof.
  induction n; intros Q h; simpl; [reflexivity |].
  unfold hstep. destruct (hnext Q (hcore h)) eqn:H.
  - apply IHn.
  - apply hrun_prog_halted. exact H.
Qed.

Lemma hrun_prog_add : forall a b Q h,
  hrun_prog (a + b) Q h = hrun_prog b Q (hrun_prog a Q h).
Proof. induction a; intros; simpl; auto. Qed.

Lemma hexec_gprog : forall h i, gprog (hexec h i) = gprog h.
Proof. intros h [j | b]; simpl; [| destruct (E.err (hcore h))]; reflexivity. Qed.

Lemma hmu_conservation : forall h i, hmu (hexec h i) = hmu h + hcost i.
Proof. intros h [j | b]; simpl; [| destruct (E.err (hcore h))]; reflexivity. Qed.

Lemma hmu_conservation_trace : forall tr h, hmu (hrun tr h) = hmu h + htotal_cost tr.
Proof.
  induction tr; intros; simpl; [lia |]. rewrite IHtr, hmu_conservation. lia.
Qed.

Lemma gmove_spec : forall P g b i,
  gmove P g b = Some i -> E.next_instr P (E.core_of g) = Some i /\ E.cost i <= b.
Proof.
  unfold gmove. intros P g b i H.
  destruct (E.next_instr P (E.core_of g)) as [j |]; [| discriminate].
  destruct (Nat.leb (E.cost j) b) eqn:Hl; [| discriminate].
  inversion H; subst. split; [reflexivity | apply Nat.leb_le; exact Hl].
Qed.

(* A guest crossing is a guest CERTIFY executed under the budget. *)
Lemma crossing_is_certify : forall P g b,
  crossing g (gnext P g b) = true ->
  gmove P g b = Some E.CERTIFY /\ E.cert g = false /\ b >= 1.
Proof.
  intros P g b H. unfold crossing, gnext in H.
  destruct (gmove P g b) as [i |] eqn:Hm.
  - apply andb_true_iff in H as [H0 H1]. apply negb_true_iff in H0.
    destruct (E.only_certify_certifies g i H0 H1) as [-> _].
    apply gmove_spec in Hm as [_ Hc]. simpl in Hc. auto.
  - destruct (E.cert g); discriminate.
Qed.

(* ================================================================= *)
(* 5. No forging (stated first; the toll rests on it).                *)
(* ================================================================= *)

Theorem no_free_host_certification_step : forall h i,
  mrec h = false -> mrec (hexec h i) = true ->
  exists b, i = GSTEP b /\ b >= 1 /\ E.err (hcore h) = false /\
    E.next_instr (gprog h) (E.core_of (gst h)) = Some E.CERTIFY /\
    crossing (gst h) (gst (hexec h i)) = true.
Proof.
  intros h [j | b] H0 H1; simpl in H1.
  - congruence.
  - destruct (E.err (hcore h)) eqn:He; simpl in H1; [congruence |].
    rewrite H0 in H1. simpl in H1.
    destruct (crossing_is_certify _ _ _ H1) as [Hm [_ Hb]].
    apply gmove_spec in Hm as [Hn _].
    exists b. simpl. rewrite He. auto.
Qed.

Theorem no_free_host_certification : forall tr h,
  mrec h = false -> mrec (hrun tr h) = true ->
  exists pre b post, tr = pre ++ GSTEP b :: post /\ b >= 1 /\
    crossing (gst (hrun pre h)) (gst (hexec (hrun pre h) (GSTEP b))) = true.
Proof.
  induction tr as [| i rest IH]; intros h H0 H1; simpl in H1; [congruence |].
  destruct (mrec (hexec h i)) eqn:Hm.
  - destruct (no_free_host_certification_step h i H0 Hm)
      as [b [-> [Hb [_ [_ Hc]]]]].
    exists [], b, rest. auto.
  - destruct (IH _ Hm H1) as [pre [b [post [-> [Hb Hc]]]]].
    exists (i :: pre), b, post. auto.
Qed.

Corollary no_free_host_certification_program : forall n Q h,
  mrec h = false -> mrec (hrun_prog n Q h) = true ->
  exists pre b post, htrace_of n Q h = pre ++ GSTEP b :: post /\ b >= 1 /\
    crossing (gst (hrun pre h)) (gst (hexec (hrun pre h) (GSTEP b))) = true.
Proof.
  intros n Q h H0 H1. rewrite hrun_prog_trace in H1.
  apply no_free_host_certification; assumption.
Qed.

Theorem guestless_runs_leave_mirror : forall tr h,
  (forall i, In i tr -> exists j, i = OWN j) ->
  mrec (hrun tr h) = mrec h /\ gst (hrun tr h) = gst h.
Proof.
  induction tr as [| i rest IH]; intros h H; simpl; [auto |].
  destruct (H i (or_introl eq_refl)) as [j ->].
  destruct (IH (hexec h (OWN j))) as [Hm Hg]; [intros; apply H; right; auto |].
  rewrite Hm, Hg. auto.
Qed.

(* The host's own record rises only by the small machine's own CERTIFY. *)
Theorem own_record_only_by_certify : forall h i,
  hcert h = false -> hcert (hexec h i) = true ->
  i = OWN E.CERTIFY /\ E.certify_ok (hcore h) = true.
Proof.
  intros h [j | b] H0 H1; simpl in H1.
  - rewrite H0 in H1. destruct j; simpl in H1; try discriminate. auto.
  - destruct (E.err (hcore h)); simpl in H1; congruence.
Qed.

(* ================================================================= *)
(* 1. The host is a Thiele machine, and Thiele-complete.              *)
(* ================================================================= *)

Theorem host_own_toll : forall h i,
  hcert h = false -> hcert (hexec h i) = true -> hcost i >= 1.
Proof.
  intros h i H0 H1. destruct (own_record_only_by_certify h i H0 H1) as [-> _].
  simpl. lia.
Qed.

Theorem host_mirror_toll : forall h i,
  mrec h = false -> mrec (hexec h i) = true -> hcost i >= 1.
Proof.
  intros h i H0 H1.
  destruct (no_free_host_certification_step h i H0 H1) as [b [-> [Hb _]]].
  exact Hb.
Qed.

Theorem host_toll : forall h i,
  hread h = false -> hread (hexec h i) = true -> hcost i >= 1.
Proof.
  unfold hread. intros h i H0 H1.
  apply orb_false_iff in H0 as [Hc Hm].
  apply orb_true_iff in H1 as [H | H].
  - exact (host_own_toll h i Hc H).
  - exact (host_mirror_toll h i Hm H).
Qed.

Lemma hnext_own : forall P k, hnext (map OWN P) k = option_map OWN (E.next_instr P k).
Proof.
  intros P k. unfold hnext, E.next_instr. destruct (E.err k); [reflexivity |].
  rewrite E.fetch_map. destruct (E.fetch P (E.pc k)) as [[] |]; reflexivity.
Qed.

(* A host program made only of OWN moves runs the small machine itself. *)
Lemma hcore_own_run : forall n P h,
  hcore (hrun_prog n (map OWN P) h) = E.core_run n P (hcore h).
Proof.
  induction n; intros P h; simpl; [reflexivity |].
  rewrite IHn. f_equal. unfold hstep, E.core_step. rewrite hnext_own.
  destruct (E.next_instr P (hcore h)); reflexivity.
Qed.

(* Whatever guest the host holds, its own base runs any two-counter
   program and halts exactly when that program halts. *)
Theorem host_thiele_complete : forall M a b P x y,
  (exists n, E.mstep M (E.mrun n M (1, (a, b))) = None) <->
  (exists n, hhalted (map OWN (E.compile M))
               (hcore (hrun_prog n (map OWN (E.compile M)) (hload a b P x y)))).
Proof.
  intros M a b P x y. rewrite E.halting_correspondence.
  split; intros [n Hn]; exists n.
  - unfold hhalted. rewrite hcore_own_run, hnext_own.
    rewrite E.core_run_prog in Hn. unfold E.halted in Hn.
    change (E.core_of (E.start a b)) with (E.start_core a b) in Hn.
    unfold hload. simpl hcore. rewrite Hn. reflexivity.
  - unfold hhalted in Hn. rewrite hcore_own_run, hnext_own in Hn.
    rewrite E.core_run_prog. unfold E.halted.
    change (E.core_of (E.start a b)) with (E.start_core a b).
    unfold hload in Hn. simpl hcore in Hn.
    destruct (E.next_instr (E.compile M) _); [discriminate | reflexivity].
Qed.

(* ================================================================= *)
(* 2. Universal simulation.                                           *)
(* ================================================================= *)

Lemma gnext_one : forall P g, gnext P g 1 = E.step P g.
Proof.
  intros P g. unfold gnext, gmove, E.step.
  destruct (E.next_instr P (E.core_of g)) as [i |]; [| reflexivity].
  destruct i; reflexivity.
Qed.

Lemma gstep_err : forall h b, E.err (hcore (hexec h (GSTEP b))) = E.err (hcore h).
Proof. intros h b. simpl. destruct (E.err (hcore h)) eqn:He; simpl; auto. Qed.

Lemma gstep_gst : forall h b,
  E.err (hcore h) = false -> gst (hexec h (GSTEP b)) = gnext (gprog h) (gst h) b.
Proof. intros h b He. simpl. rewrite He. reflexivity. Qed.

Theorem universal_simulation : forall n h,
  E.err (hcore h) = false ->
  gst (hrun (repeat (GSTEP 1) n) h) = E.run_prog n (gprog h) (gst h) /\
  gprog (hrun (repeat (GSTEP 1) n) h) = gprog h /\
  E.err (hcore (hrun (repeat (GSTEP 1) n) h)) = false.
Proof.
  induction n; intros h He; [simpl; auto |].
  cbn [repeat hrun E.run_prog].
  destruct (IHn (hexec h (GSTEP 1))) as [Hg [Hp Hr]];
    [rewrite gstep_err; exact He |].
  rewrite Hg, Hp, hexec_gprog, gstep_gst, gnext_one by exact He. auto.
Qed.

(* The universal host program: run one guest step, then jump back. *)
Definition U : list hinstr := [GSTEP 1; OWN (E.INC E.CA); OWN (E.DEC E.CA 1)].

Lemma U_round : forall h,
  E.pc (hcore h) = 1 -> E.err (hcore h) = false ->
  E.pc (hcore (hrun_prog 3 U h)) = 1 /\ E.err (hcore (hrun_prog 3 U h)) = false /\
  gst (hrun_prog 3 U h) = E.step (gprog h) (gst h) /\
  gprog (hrun_prog 3 U h) = gprog h.
Proof.
  intros [[ca cb va vb pc fs ch er] m c P g r] Hp He. simpl in Hp, He. subst.
  cbn. rewrite gnext_one. auto.
Qed.

Theorem universal_program_simulation : forall n h,
  E.pc (hcore h) = 1 -> E.err (hcore h) = false ->
  gst (hrun_prog (3 * n) U h) = E.run_prog n (gprog h) (gst h).
Proof.
  induction n; intros h Hp He; [reflexivity |].
  replace (3 * S n) with (3 + 3 * n) by lia. rewrite hrun_prog_add.
  destruct (U_round h Hp He) as [Hp' [He' [Hg Hq]]].
  rewrite (IHn _ Hp' He'), Hg, Hq. reflexivity.
Qed.

(* ================================================================= *)
(* 3. Record agreement.                                               *)
(* ================================================================= *)

Definition agrees (h : hstate) : Prop := mrec h = E.cert (gst h).

Theorem record_agreement_step : forall h i, agrees h -> agrees (hexec h i).
Proof.
  unfold agrees. intros h [j | b] H; simpl; [exact H |].
  destruct (E.err (hcore h)); simpl; [exact H |].
  unfold gnext, crossing. rewrite H.
  destruct (gmove (gprog h) (gst h) b) as [i |];
    [rewrite E.cert_latch |]; destruct (E.cert (gst h)); reflexivity.
Qed.

Theorem record_agreement : forall tr h, agrees h -> agrees (hrun tr h).
Proof.
  induction tr; intros h H; simpl; [exact H |].
  apply IHtr, record_agreement_step, H.
Qed.

Corollary record_agreement_program : forall n Q h, agrees h -> agrees (hrun_prog n Q h).
Proof. intros. rewrite hrun_prog_trace. apply record_agreement. assumption. Qed.

Lemma hload_agrees : forall a b P x y, agrees (hload a b P x y).
Proof. reflexivity. Qed.

(* After n simulated guest steps the mirror is the guest's own reading. *)
Corollary simulated_record : forall n h,
  E.err (hcore h) = false -> agrees h ->
  mrec (hrun (repeat (GSTEP 1) n) h) = E.cert (E.run_prog n (gprog h) (gst h)).
Proof.
  intros n h He Ha. pose proof (record_agreement (repeat (GSTEP 1) n) h Ha) as H.
  unfold agrees in H. rewrite H. f_equal. apply universal_simulation, He.
Qed.

(* ================================================================= *)
(* 4. The toll is enforced by the host's step.                        *)
(* ================================================================= *)

Theorem toll_enforced_by_host_step : forall h b,
  E.err (hcore h) = false -> agrees h ->
  crossing (gst h) (gnext (gprog h) (gst h) b) = true ->
  mrec h = false /\ mrec (hexec h (GSTEP b)) = true /\
  hmu (hexec h (GSTEP b)) = hmu h + b /\ b >= 1.
Proof.
  intros h b He Ha Hx.
  destruct (crossing_is_certify _ _ _ Hx) as [_ [Hc Hb]].
  unfold agrees in Ha. rewrite Hc in Ha.
  simpl. rewrite He. simpl. rewrite Ha, Hx. auto.
Qed.

Lemma repeat_snoc : forall (A : Type) (x : A) n, repeat x (S n) = repeat x n ++ [x].
Proof. induction n; simpl; [reflexivity | rewrite <- IHn; reflexivity]. Qed.

Lemma run_prog_snoc : forall n P g, E.run_prog (S n) P g = E.step P (E.run_prog n P g).
Proof. induction n; intros; simpl; [reflexivity | apply IHn]. Qed.

(* Every crossing of the simulated guest run is a host crossing at the
   same step, paid by that host step. *)
Corollary every_guest_crossing_is_a_host_crossing : forall n h,
  E.err (hcore h) = false -> agrees h ->
  crossing (E.run_prog n (gprog h) (gst h))
           (E.run_prog (S n) (gprog h) (gst h)) = true ->
  mrec (hrun (repeat (GSTEP 1) n) h) = false /\
  mrec (hrun (repeat (GSTEP 1) (S n)) h) = true /\
  hmu (hrun (repeat (GSTEP 1) (S n)) h) = hmu (hrun (repeat (GSTEP 1) n) h) + 1.
Proof.
  intros n h He Ha Hx.
  destruct (universal_simulation n h He) as [Hg [Hp Hr]].
  set (hn := hrun (repeat (GSTEP 1) n) h) in *.
  rewrite repeat_snoc, hrun_app. fold hn. simpl hrun.
  rewrite run_prog_snoc, <- Hg, <- Hp, <- gnext_one in Hx.
  destruct (toll_enforced_by_host_step hn 1 Hr
              (record_agreement _ _ Ha) Hx) as [H0 [H1 [H2 _]]].
  auto.
Qed.

(* The host's ledger grows by at least what the guest's ledger grows,
   for every host move and every host instruction sequence. *)
Theorem host_pays_for_guest : forall h i,
  E.mu (gst (hexec h i)) + hmu h <= hmu (hexec h i) + E.mu (gst h).
Proof.
  intros h [j | b]; simpl; [lia |].
  destruct (E.err (hcore h)); simpl; [lia |].
  unfold gnext. destruct (gmove (gprog h) (gst h) b) as [i |] eqn:Hm; [| lia].
  apply gmove_spec in Hm as [_ Hc]. rewrite E.mu_conservation. lia.
Qed.

Theorem host_cost_covers_guest : forall tr h,
  E.mu (gst (hrun tr h)) + hmu h <= hmu (hrun tr h) + E.mu (gst h).
Proof.
  induction tr as [| i rest IH]; intros h; simpl; [lia |].
  specialize (IH (hexec h i)). pose proof (host_pays_for_guest h i). lia.
Qed.

(* In the simulation: the guest's total cost over n steps is at most the
   host's total cost over the matching n moves. *)
Corollary simulated_cost : forall n h,
  E.err (hcore h) = false ->
  E.total_cost (E.trace_of n (gprog h) (gst h))
    <= htotal_cost (repeat (GSTEP 1) n).
Proof.
  intros n h He.
  pose proof (host_cost_covers_guest (repeat (GSTEP 1) n) h) as H.
  rewrite hmu_conservation_trace in H.
  destruct (universal_simulation n h He) as [Hg _]. rewrite Hg in H.
  rewrite E.mu_conservation_program in H. lia.
Qed.

(* ================================================================= *)
(* 6. Non-vacuity.                                                    *)
(* ================================================================= *)

(* A guest that earns its flag: check A is 0, commit to it, certify. *)
Definition demo_guest : list E.instr :=
  [E.CHECK E.PZero E.CA; E.COMMIT E.PZero E.CA; E.CERTIFY; E.HALT].

Definition demo_host : hstate := hload 0 0 demo_guest 0 0.

Theorem demo_certifies :
  mrec (hrun (repeat (GSTEP 1) 2) demo_host) = false /\
  mrec (hrun (repeat (GSTEP 1) 3) demo_host) = true /\
  E.cert (gst (hrun (repeat (GSTEP 1) 3) demo_host)) = true /\
  hcert (hrun (repeat (GSTEP 1) 3) demo_host) = false /\
  hmu (hrun (repeat (GSTEP 1) 3) demo_host) = 3.
Proof. vm_compute. auto. Qed.

(* The same guest under the stored universal program: the crossing lands
   on host step 7, the third GSTEP. *)
Theorem demo_program_certifies :
  mrec (hrun_prog 6 U demo_host) = false /\
  mrec (hrun_prog 7 U demo_host) = true /\
  hmu (hrun_prog 7 U demo_host) = 3.
Proof. vm_compute. auto. Qed.

(* A guest that tries to certify with nothing committed traps; the host
   pays its budget and the mirror stays down. *)
Definition forger_guest : list E.instr := [E.CERTIFY; E.CERTIFY].

Theorem demo_forgery_fails :
  mrec (hrun (repeat (GSTEP 1) 5) (hload 0 0 forger_guest 0 0)) = false /\
  E.err (E.core_of (gst (hrun (repeat (GSTEP 1) 5) (hload 0 0 forger_guest 0 0)))) = true /\
  hmu (hrun (repeat (GSTEP 1) 5) (hload 0 0 forger_guest 0 0)) = 5.
Proof. vm_compute. auto. Qed.

Print Assumptions host_toll.
Print Assumptions host_own_toll.
Print Assumptions host_mirror_toll.
Print Assumptions host_thiele_complete.
Print Assumptions universal_simulation.
Print Assumptions universal_program_simulation.
Print Assumptions record_agreement.
Print Assumptions simulated_record.
Print Assumptions toll_enforced_by_host_step.
Print Assumptions every_guest_crossing_is_a_host_crossing.
Print Assumptions host_cost_covers_guest.
Print Assumptions simulated_cost.
Print Assumptions no_free_host_certification.
Print Assumptions no_free_host_certification_program.
Print Assumptions guestless_runs_leave_mirror.
Print Assumptions own_record_only_by_certify.
Print Assumptions demo_certifies.
Print Assumptions demo_program_certifies.
Print Assumptions demo_forgery_fails.
