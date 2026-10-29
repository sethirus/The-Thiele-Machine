(** NecEHost.v: Rice, Kleene and the diagonal on the host machine, at their
    limits.

    1. "Some program has Pi and some lacks it" is needed. A constant
       property respects behaving the same and is decided outright by a
       one-instruction host program [nec_e_wall_needs_nontrivial]; in the
       library's sense it is decidable, so Rice's theorem without the
       premise would make the complement of halting enumerable
       [nec_e_rice_needs_nontrivial].
    2. Extensionality is needed. "The program is the empty program" holds
       of one program and fails of another, is decided outright by a
       three-instruction host program, and does not respect behaving the
       same: the empty program and [HALT] compute the same thing
       [nec_e_wall_needs_extensional, nec_e_rice_needs_extensional].
    3. The recursion theorem up to the record cannot add the fact table or
       the channel: a map computed by a host program, F e = INC r; CHECK r;
       COMMIT r with r one above the number of e, has no fixed point that
       even matches F e's fact table, or its channel, on input 0
       [nec_e_no_fixed_point_facts]. Nor the versions of the registers
       [nec_e_no_fixed_point_versions]. (Every register is
       sm2_no_exact.)

    Dependencies: the host files SmHostBlocks.v, SmCodes.v, SmInterp.v,
    SmHostRice.v, SmKleene.v, SmDecider.v, SmNoExact.v, SmFixedPoint.v and the
    vendored Saarland library. No axioms beyond what those files use.     *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Synthetic Require Import Undecidability.
From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
Require Minimal.EarnedMulti.
Require Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmInterp Kernel.SmEvalL Kernel.SmFuel
  Kernel.SmMMAHost Kernel.SmHostRice Kernel.SmKleene Kernel.SmDecider Kernel.SmNoExact.
Require Minimal.EarnedCore.
Require Kernel.SmGuestRice.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Module EC := Minimal.EarnedCore.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hcore := (@M.core UC.hprop).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hrun := (M.run UC.hprop_eqb UC.heval).
Local Notation hfun := (sm_hfun UC.hprop_eqb UC.heval).
Local Notation hends := (sm_hends UC.hprop_eqb UC.heval).
Local Notation hequiv := (sm_hequiv UC.hprop_eqb UC.heval).
Local Notation hstart := (@sm_hstart UC.hprop).

(* ================================================================= *)
(* 1. Small programs and their runs.                                   *)
(* ================================================================= *)

Lemma nec_e_hfun_det : forall P x a b, hfun P x a -> hfun P x b -> a = b.
Proof.
  intros P x a b [s [Hs Ha]] [t [Ht Hb]].
  rewrite (sm_hends_unique UC.hprop_eqb UC.heval P x s t Hs Ht) in Ha. congruence.
Qed.

(* [INC 0] outputs 1 on every input. *)
Lemma nec_e_inc0_out : forall x, hfun [M.INC 0] x 1.
Proof.
  intro x. exists (hrun_prog 1 [M.INC 0] (hstart x)). split.
  - exists 1. split; [reflexivity |]. reflexivity.
  - reflexivity.
Qed.

(* [DEC 1 3; INC 0; HALT] outputs 1 on input 0 and 0 on every other input. *)
Definition nec_e_is0 : list hinstr := [M.DEC 1 3; M.INC 0; M.HALT].

Lemma nec_e_is0_out : forall x, hfun nec_e_is0 x (if Nat.eqb x 0 then 1 else 0).
Proof.
  intro x. destruct x as [| x].
  - exists (hrun_prog 2 nec_e_is0 (hstart 0)). split.
    + exists 2. split; [reflexivity |]. reflexivity.
    + reflexivity.
  - exists (hrun_prog 1 nec_e_is0 (hstart (S x))). split.
    + exists 1. split; [reflexivity |]. reflexivity.
    + reflexivity.
Qed.

Lemma nec_e_hcode_nil : forall p, sm_hcode p = 0 <-> p = [].
Proof.
  intro p. split.
  - intro H. apply sm_hcode_inj. rewrite H. reflexivity.
  - intros ->. reflexivity.
Qed.

(* [] and [HALT] compute the same partial function: both stop at once. *)
Lemma nec_e_nil_halt_same : forall x y, hfun [] x y <-> hfun [M.HALT] x y.
Proof.
  intros x y. split; intros [s [[n [-> Hh]] Hv]].
  - exists (hstart x). split; [exists 0; split; reflexivity |].
    rewrite (M.multi_run_prog_halted UC.hprop_eqb UC.heval n [] (hstart x)) in Hv by reflexivity.
    exact Hv.
  - exists (hstart x). split; [exists 0; split; reflexivity |].
    rewrite (M.multi_run_prog_halted UC.hprop_eqb UC.heval n [M.HALT] (hstart x)) in Hv by reflexivity.
    exact Hv.
Qed.

Lemma nec_e_nil_halt_hequiv : hequiv [] [M.HALT].
Proof.
  intro x. split.
  - intros s [n [-> Hh]].
    rewrite (M.multi_run_prog_halted UC.hprop_eqb UC.heval n [] (hstart x)) by reflexivity.
    exists (hstart x). split; [exists 0; split; reflexivity |].
    repeat split; reflexivity.
  - intros t [n [-> Hh]].
    rewrite (M.multi_run_prog_halted UC.hprop_eqb UC.heval n [M.HALT] (hstart x)) by reflexivity.
    exists (hstart x). split; [exists 0; split; reflexivity |].
    repeat split; reflexivity.
Qed.

(* ================================================================= *)
(* 2. The diagonal on the host: both premises are needed.              *)
(* ================================================================= *)

(* A property true of every program respects behaving the same, and
   [INC 0] decides it outright. *)
Theorem nec_e_wall_needs_nontrivial : forall Pi : list hinstr -> Prop,
  (forall p, Pi p) ->
  sm_fun_ext Pi /\
  sm_decides [M.INC 0] Pi.
Proof.
  intros Pi HPi. split; [intros p q _ _; apply HPi |].
  intro p. split; [exists 1; apply nec_e_inc0_out |].
  split; [intros _; apply HPi | intros _; apply nec_e_inc0_out].
Qed.

(* "Is the empty program" holds of [] and not of [HALT], does not respect
   computing the same function (nor behaving the same), and the three
   instructions DEC 1 3; INC 0; HALT decide it outright. *)
Theorem nec_e_wall_needs_extensional :
  let Pi := fun p : list hinstr => p = [] in
  Pi [] /\ ~ Pi [M.HALT] /\
  (forall x y, hfun [] x y <-> hfun [M.HALT] x y) /\ hequiv [] [M.HALT] /\
  ~ sm_fun_ext Pi /\ ~ sm_hext UC.hprop_eqb UC.heval Pi /\
  sm_decides nec_e_is0 Pi.
Proof.
  intro Pi.
  split; [reflexivity |]. split; [discriminate |].
  split; [exact nec_e_nil_halt_same |]. split; [exact nec_e_nil_halt_hequiv |].
  split; [intro H; specialize (H [] [M.HALT] nec_e_nil_halt_same eq_refl); discriminate |].
  split; [intro H; specialize (H [] [M.HALT] nec_e_nil_halt_hequiv eq_refl); discriminate |].
  intro p. split; [eexists; apply nec_e_is0_out |].
  split.
  - intro H. pose proof (nec_e_hfun_det _ _ _ _ H (nec_e_is0_out (sm_hcode p))) as E.
    destruct (Nat.eqb (sm_hcode p) 0) eqn:Hc; [| discriminate].
    apply Nat.eqb_eq in Hc. apply nec_e_hcode_nil, Hc.
  - intro H. unfold Pi in H. subst p.
    exact (nec_e_is0_out (sm_hcode [])).
Qed.

(* ================================================================= *)
(* 3. Rice in the library's sense: both premises are needed.           *)
(* ================================================================= *)

Lemma nec_e_dec_const : decidable (fun _ : list hinstr => True).
(* SAFE: the property holds of every program on purpose; the constant decider is the intended witness. *)
Proof. exists (fun _ => true). intro p. unfold reflects. split; auto. Qed.

Lemma nec_e_dec_nil : decidable (fun p : list hinstr => p = []).
Proof.
  exists (fun p => match p with [] => true | _ => false end). intro p. unfold reflects.
  destruct p; split; intro H; congruence.
Qed.

(* Rice's theorem without "some has, some lacks" would make the
   complement of Turing-machine halting enumerable. *)
Theorem nec_e_rice_needs_nontrivial :
  (forall Pi : list hinstr -> Prop, sm_hext UC.hprop_eqb UC.heval Pi -> undecidable Pi) ->
  enumerable (Undecidability.Synthetic.Definitions.complement Undecidability.TM.SBTM.SBTM_HALT).
Proof.
  intro H. apply (H (fun _ => True)); [intros p q _ _; exact Logic.I | exact nec_e_dec_const].
Qed.

(* Rice's theorem without extensionality would make it enumerable too. *)
Theorem nec_e_rice_needs_extensional :
  (forall (Pi : list hinstr -> Prop) y n, Pi y -> ~ Pi n -> undecidable Pi) ->
  enumerable (Undecidability.Synthetic.Definitions.complement Undecidability.TM.SBTM.SBTM_HALT).
Proof.
  intro H. apply (H (fun p => p = []) [] [M.HALT] eq_refl ltac:(discriminate)).
  exact nec_e_dec_nil.
Qed.

(* The same two facts for Rice's theorem on the small machine from the
   clean start. *)
Theorem nec_e_guest_rice_needs_nontrivial :
  (forall Pi : list EC.instr -> Prop, Kernel.SmGuestRice.sm_gext Pi -> undecidable Pi) ->
  enumerable (Undecidability.Synthetic.Definitions.complement Undecidability.TM.SBTM.SBTM_HALT).
Proof.
  intro H. apply (H (fun _ => True)); [intros p q _ _; exact Logic.I |].
  (* SAFE: the property holds of every program on purpose; the constant decider is the intended witness. *)
  exists (fun _ => true). intro p. unfold reflects. split; auto.
Qed.

Theorem nec_e_guest_rice_needs_extensional :
  (forall (Pi : list EC.instr -> Prop) y n, Pi y -> ~ Pi n -> undecidable Pi) ->
  enumerable (Undecidability.Synthetic.Definitions.complement Undecidability.TM.SBTM.SBTM_HALT).
Proof.
  intro H. apply (H (fun p => p = []) [] [EC.HALT] eq_refl ltac:(discriminate)).
  exists (fun p => match p with [] => true | _ => false end). intro p. unfold reflects.
  destruct p; split; intro Hp; congruence.
Qed.

(* Why "run z first, then a free phase that depends on H" cannot give Rice
   for the relation that also compares the fact table: a witness may stop
   by a trap after recording a fact, and then nothing appended after it
   ever runs. Here z checks "A is 0" (recorded, version 0) and then
   "A >= 1" (fails, trap); for every continuation q, z ++ q stops in z's
   own final state after two moves. *)
Definition nec_e_trapz : list EC.instr := [EC.CHECK EC.PZero EC.CA; EC.CHECK (EC.PGe 1) EC.CA].

Theorem nec_e_trap_absorbs : forall q : list EC.instr,
  EC.run_prog 2 (nec_e_trapz ++ q) (EC.start 0 0) = EC.run_prog 2 nec_e_trapz (EC.start 0 0) /\
  EC.halted (nec_e_trapz ++ q) (EC.core_of (EC.run_prog 2 nec_e_trapz (EC.start 0 0))) /\
  EC.halted nec_e_trapz (EC.core_of (EC.run_prog 2 nec_e_trapz (EC.start 0 0))) /\
  EC.err (EC.core_of (EC.run_prog 2 nec_e_trapz (EC.start 0 0))) = true /\
  EC.facts (EC.core_of (EC.run_prog 2 nec_e_trapz (EC.start 0 0))) = [EC.mkfact EC.PZero EC.CA 0].
Proof. intro q. repeat split; reflexivity. Qed.

(* ================================================================= *)
(* 4. The recursion theorem up to the record cannot add the facts.     *)
(* ================================================================= *)

(* The map: F e = INC r; CHECK r; COMMIT r, with r one above the number
   of e. Its number, as a function of the number c of e. *)
Definition nec_e_ff (p : list hinstr) : list hinstr :=
  let r := S (sm_hcode p) in [M.INC r; M.CHECK UC.PSlot r; M.COMMIT UC.PSlot r].

Definition nec_e_fff (w fuel x c : nat) : option nat :=
  Some (UC.pair (UC.pair 0 (S x)) (UC.pair (UC.pair 3 (S x)) (UC.pair (UC.pair 4 (S x)) 0))).

Instance term_nec_e_fff : computable nec_e_fff. Proof. extract. Qed.

Definition nec_e_Rff (v : Vector.t nat 2) (m : nat) : Prop :=
  exists n, nec_e_fff 0 n (Vector.hd v) (Vector.hd (Vector.tl v)) = Some m.

Lemma nec_e_ff_MMA : MMA_computable nec_e_Rff.
Proof.
  apply L_computable_to_MMA_computable.
  exact (@sm_L_computable_fuel2 nat _ nec_e_fff _ 0 (fun n n' x c m H Hle => H)).
Qed.

Lemma nec_e_ff_program : exists T : list hinstr,
  forall x m, hfun T x m <->
    m = UC.pair (UC.pair 0 (S x)) (UC.pair (UC.pair 3 (S x)) (UC.pair (UC.pair 4 (S x)) 0)).
Proof.
  destruct nec_e_ff_MMA as [nn [Pm HPm]].
  exists (sm_mma_host (S (S (S nn))) Pm). intros x m.
  transitivity (nec_e_Rff (Vector.cons nat x 1 (Vector.cons nat 0 0 (Vector.nil nat))) m).
  2: { unfold nec_e_Rff. simpl. split.
       - intros [n H]. injection H as <-. reflexivity.
       - intros ->. exists 0. reflexivity. }
  symmetry.
  rewrite (sm_mma_two nn Pm nec_e_Rff HPm (M.core_of (sm_hstart x)) x 0 m eq_refl eq_refl).
  - unfold sm_hfun, sm_hends. split.
    + intros [n [Hh Hv]]. exists (hrun_prog n (sm_mma_host (S (S (S nn))) Pm) (sm_hstart x)).
      split.
      * exists n. split; [reflexivity |]. rewrite sm_core_run. exact Hh.
      * rewrite sm_core_run. exact Hv.
    + intros [s [[n [-> Hh]] Hv]]. exists n. rewrite sm_core_run in Hh, Hv. split; assumption.
  - intro r. cbn [M.vals M.core_of sm_hstart M.start M.start_core]. unfold sm_hin, sm_in2.
    destruct (Nat.eqb r 1); [reflexivity |]. destruct (Nat.eqb r 2); reflexivity.
Qed.

Lemma nec_e_ff_computed : exists T, sm_computes_map T nec_e_ff.
Proof.
  destruct nec_e_ff_program as [T HT]. exists T. intro p. apply HT. reflexivity.
Qed.

(* A frame for the fact table and the channel: a run that never names
   register r adds no fact about r and commits to none. *)
Definition nec_e_noreg (r : nat) (k : hcore) : Prop :=
  (forall f, In f (M.facts k) -> M.f_reg f <> r) /\
  (forall f, M.chan k = Some f -> M.f_reg f <> r).

Lemma nec_e_noreg_cexec : forall k i r,
  M.mentions i r = false -> nec_e_noreg r k ->
  nec_e_noreg r (M.cexec UC.hprop_eqb UC.heval k i).
Proof.
  intros k i r Hm [Hf Hc]. unfold M.cexec.
  destruct (M.err k); [split; assumption |].
  destruct i as [d | d j | | p d | p d |]; simpl in Hm.
  - split; assumption.
  - destruct (M.vals k d); split; assumption.
  - split; assumption.
  - destruct (M.check_ok UC.heval k p d); [| split; assumption].
    split; [| exact Hc]. intros f [<- | Hin]; [| apply Hf, Hin].
    simpl. apply Nat.eqb_neq. exact Hm.
  - destruct (M.commit_ok UC.hprop_eqb k p d); [| split; assumption].
    split; [exact Hf |]. intros f Hcf. simpl in Hcf. injection Hcf as <-.
    simpl. apply Nat.eqb_neq. exact Hm.
  - destruct (M.certify_ok k); split; assumption.
Qed.

Lemma nec_e_noreg_run : forall tr (s : hstate) r,
  (forall i, In i tr -> M.mentions i r = false) ->
  nec_e_noreg r (M.core_of s) -> nec_e_noreg r (M.core_of (hrun tr s)).
Proof.
  induction tr as [| i tr IH]; intros s r Hm Hs; simpl; [exact Hs |].
  apply IH; [intros j Hj; apply Hm; right; exact Hj |].
  simpl. apply nec_e_noreg_cexec; [apply Hm; left; reflexivity | exact Hs].
Qed.

(* A program never names a register above its own number. *)
Lemma nec_e_ends_noreg : forall e x s, hends e x s ->
  nec_e_noreg (S (sm_hcode e)) (M.core_of s).
Proof.
  intros e x s [n [-> _]]. rewrite (M.multi_run_prog_trace UC.hprop_eqb UC.heval).
  apply nec_e_noreg_run.
  - intros i Hi. destruct (M.mentions i (S (sm_hcode e))) eqn:Hm; [| reflexivity].
    exfalso. pose proof (sm2_reg_bound e i (S (sm_hcode e)) (sm2_trace_in _ _ _ _ Hi) Hm). lia.
  - split; [intros f [] | intros f H; discriminate H].
Qed.

(* The run of INC r; CHECK r; COMMIT r on input 0. *)
Lemma nec_e_ff_run_r : forall r,
  exists t, hends [M.INC r; M.CHECK UC.PSlot r; M.COMMIT UC.PSlot r] 0 t /\
    M.facts (M.core_of t) = [M.mkfact UC.PSlot r 1] /\
    M.chan (M.core_of t) = Some (M.mkfact UC.PSlot r 1).
Proof.
  intro r. set (P := [M.INC r; M.CHECK UC.PSlot r; M.COMMIT UC.PSlot r]).
  assert (H0 : sm_hin 0 r = 0) by (unfold sm_hin; destruct (Nat.eqb r 1); reflexivity).
  set (k := fun p fs ch => @M.mkcore UC.hprop (M.upd (sm_hin 0) r 1) (M.upd (fun _ => 0) r 1) p fs ch false).
  assert (E1 : M.exec UC.hprop_eqb UC.heval (hstart 0) (M.INC r) = M.mkst (k 2 [] None) 0 false).
  { unfold M.exec, M.cexec, M.write, k. cbn. rewrite H0. reflexivity. }
  assert (E2 : M.exec UC.hprop_eqb UC.heval (M.mkst (k 2 [] None) 0 false) (M.CHECK UC.PSlot r) =
               M.mkst (k 3 [M.mkfact UC.PSlot r 1] None) 1 false).
  { unfold M.exec, M.cexec, M.check_ok, M.record_fact, M.claim, k. cbn.
    unfold M.upd. rewrite Nat.eqb_refl. reflexivity. }
  assert (E3 : M.exec UC.hprop_eqb UC.heval (M.mkst (k 3 [M.mkfact UC.PSlot r 1] None) 1 false)
                 (M.COMMIT UC.PSlot r) =
               M.mkst (k 4 [M.mkfact UC.PSlot r 1] (Some (M.mkfact UC.PSlot r 1))) 2 false).
  { unfold M.exec, M.cexec, M.commit_ok, M.commit_to, M.claim, M.fact_eqb, k. cbn.
    unfold M.upd. rewrite !Nat.eqb_refl. reflexivity. }
  exists (M.mkst (k 4 [M.mkfact UC.PSlot r 1] (Some (M.mkfact UC.PSlot r 1))) 2 false).
  split; [| split; reflexivity].
  exists 3. split; [| reflexivity].
  cbn. rewrite E1. cbn. rewrite E2. cbn. rewrite E3. reflexivity.
Qed.

Lemma nec_e_ff_run : forall e,
  exists t, hends (nec_e_ff e) 0 t /\
    M.facts (M.core_of t) = [M.mkfact UC.PSlot (S (sm_hcode e)) 1] /\
    M.chan (M.core_of t) = Some (M.mkfact UC.PSlot (S (sm_hcode e)) 1).
Proof. intro e. exact (nec_e_ff_run_r (S (sm_hcode e))). Qed.

Theorem nec_e_no_fixed_point_facts :
  exists (F : list hinstr -> list hinstr) (T : list hinstr),
    sm_computes_map T F /\
    forall e,
      ~ (forall t, hends (F e) 0 t ->
           exists s, hends e 0 s /\ M.facts (M.core_of s) = M.facts (M.core_of t)) /\
      ~ (forall t, hends (F e) 0 t ->
           exists s, hends e 0 s /\ M.chan (M.core_of s) = M.chan (M.core_of t)).
Proof.
  destruct nec_e_ff_computed as [T HT]. exists nec_e_ff, T. split; [exact HT |].
  intro e. destruct (nec_e_ff_run e) as [t [Ht [Hf Hc]]]. split.
  - intro H. destruct (H t Ht) as [s [Hs Hfs]].
    destruct (nec_e_ends_noreg e 0 s Hs) as [Hno _].
    apply (Hno (M.mkfact UC.PSlot (S (sm_hcode e)) 1)); [rewrite Hfs, Hf; left; reflexivity |].
    reflexivity.
  - intro H. destruct (H t Ht) as [s [Hs Hcs]].
    destruct (nec_e_ends_noreg e 0 s Hs) as [_ Hno].
    apply (Hno (M.mkfact UC.PSlot (S (sm_hcode e)) 1)); [rewrite Hcs, Hc; reflexivity |].
    reflexivity.
Qed.

(* The versions: the repo's map F e = [INC r] (sm2_imp_map) has no fixed
   point that matches the versions of F e's final state on input 0. *)
Theorem nec_e_no_fixed_point_versions :
  exists (F : list hinstr -> list hinstr) (T : list hinstr),
    sm_computes_map T F /\
    forall e,
      ~ (forall t, hends (F e) 0 t ->
           exists s, hends e 0 s /\ forall r, M.vers (M.core_of s) r = M.vers (M.core_of t) r).
Proof.
  destruct sm2_imp_program as [T HT].
  exists sm2_imp_map, T. split; [intro p; apply HT; symmetry; apply sm2_imp_code |].
  intros e H.
  set (r := S (sm_hcode e)).
  assert (Ht : hends (sm2_imp_map e) 0 (hrun_prog 1 (sm2_imp_map e) (hstart 0)))
    by (exists 1; split; reflexivity).
  destruct (H _ Ht) as [s [[n [-> _]] Hv]].
  specialize (Hv r).
  rewrite (M.multi_run_prog_trace UC.hprop_eqb UC.heval) in Hv.
  destruct (M.multi_frame_run UC.hprop_eqb UC.heval
              (M.trace_of UC.hprop_eqb UC.heval n e (hstart 0)) (hstart 0) r) as [_ Hw].
  - intros i Hi. destruct (M.mentions i r) eqn:Hm; [| reflexivity].
    exfalso. pose proof (sm2_reg_bound e i r (sm2_trace_in _ _ _ _ Hi) Hm). unfold r in *. lia.
  - rewrite Hw in Hv. unfold sm2_imp_map in Hv. fold r in Hv.
    cbn - [M.upd] in Hv. unfold M.upd in Hv. rewrite Nat.eqb_refl in Hv. discriminate Hv.
Qed.

(* ================================================================= *)
(* 5. Kleene needs the map to be computed by a host program.           *)
(* ================================================================= *)

(* Given any test h that says exactly which programs halt on input 0 (no
   such test can be built, which is the point), the map "if p halts on 0,
   loop; otherwise output 1" has no fixed point. So the premise that a host
   program computes the map cannot be dropped, and no host program
   computes this map. *)
Theorem nec_e_kleene_needs_computable : forall h : list hinstr -> bool,
  (forall p, h p = true <-> exists y, hfun p 0 y) ->
  let F := fun p => if h p then sm_hloop else [M.INC 0] in
  ~ (exists e, forall x y, hfun e x y <-> hfun (F e) x y) /\
  ~ (exists T, sm_computes_map T F).
Proof.
  intros h Hh F.
  assert (Hloop : forall y, ~ hfun sm_hloop 0 y).
  { intros y [s [[n [-> Hn]] _]]. exact (sm_hloop_diverges UC.hprop_eqb UC.heval 0 n Hn). }
  assert (Hnofix : ~ (exists e, forall x y, hfun e x y <-> hfun (F e) x y)).
  { intros [e He]. unfold F in He. destruct (h e) eqn:Hd.
    - destruct (proj1 (Hh e) Hd) as [y Hy]. apply (Hloop y). apply He, Hy.
    - assert (H1 : hfun e 0 1) by (apply He, nec_e_inc0_out).
      assert (Ht : h e = true) by (apply Hh; exists 1; exact H1). congruence. }
  split; [exact Hnofix |].
  intros [T HT]. apply Hnofix. exact (sm_kleene F T HT).
Qed.

Print Assumptions nec_e_wall_needs_nontrivial.
Print Assumptions nec_e_wall_needs_extensional.
Print Assumptions nec_e_rice_needs_nontrivial.
Print Assumptions nec_e_rice_needs_extensional.
Print Assumptions nec_e_no_fixed_point_facts.
Print Assumptions nec_e_no_fixed_point_versions.
Print Assumptions nec_e_kleene_needs_computable.
Print Assumptions nec_e_guest_rice_needs_nontrivial.
Print Assumptions nec_e_guest_rice_needs_extensional.
Print Assumptions nec_e_trap_absorbs.
