(** UniversalPSim.v: the fixed host program U_P simulates every guest
    program of the priced machine over cg_uprop, one guest step at a time.

    This file is the priced counterpart of UniversalSim.v: the host is the
    machine of EarnedMultiPriced.v (with PAY), the guest is the priced
    machine of EarnedPriced.v over the universal property language
    cg_uprop (UniversalPCodes.v), every name carries the prefix pu_, and
    the host program is U_P.

    The simulation relation rel P g h says that the host state h sits at
    HEAD and mirrors the guest state g of program P. Its witness is a list
    of slot records sg and a channel record rho. A slot record names one
    passing guest CHECK p c: the guest fact (p, c, gv) and the host fact on
    slot register pu_SLOT c k at host version hv, with the value v that was
    checked. The relation states:

      the host is at HEAD (pc 1, trap latch down, pu_PROG holds pu_prog_code P,
      every scratch register 0) and the guest trap latch is down;
      pu_RA and pu_RB hold the guest counters and pu_GPC the guest pc;
      the guest fact table is the list of guest facts of sg, and the host
      fact table is the list of host facts of sg, in the same order;
      the two channels name the guest and the host fact of rho, and rho
      is one of the records;
      the ledgers and the flags are equal;
      pu_NC c is the number of records on counter c, the records on c use
      distinct slots below that number, and every slot is below 16;
      each record's slot holds pair (pcode p) v; the guest fact is current
      exactly when the host fact is; a current record checked the guest's
      present value and its mirror pu_MP c k holds pcode p + 1; a stale
      record's mirror holds 0;
      every slot and mirror that no record uses holds 0, and pu_DEAD holds 0.

    pu_rel_halt P g h says that both machines have stopped (halted or
    trapped), with equal counters, trap latch, ledger and flag, and fact
    tables and channels that still correspond.

      pu_hload_rel     the loaded host is related to the guest start
      pu_U_step_with   one guest step: either the guest is stopped and the host
                    reaches a related stop, or the host takes at least one
                    step to a state related to the guest's next state, or,
                    when the guest traps, to a related host trap; new
                    records are current in the guest's next state; a
                    guest PAY is matched by the host's own PAY
      pu_U_step        the same with the witness hidden

    Dependencies: the Coq standard library, the vendored
    coq-undecidability library, EarnedGeneric.v, EarnedPriced.v,
    EarnedMultiPriced.v, CompilerChecker.v, UniversalPCodes.v, UniversalPBridge.v, UniversalPBlocks.v,
    UniversalPLayout.v and UniversalPPhases.v. No axioms, no Admitted.      *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the universal interpreter U_P of UniversalPRun.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and files under minimal/. Its link to the abstract record (the
   host machine meeting thiele_complete of ThieleComplete.v, and every
   computably presented machine run on U_P) lives in UniversalPRun.v and
   PresentedUniversal.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.UniversalPCodes Minimal.UniversalPBridge Minimal.UniversalPBlocks
  Minimal.UniversalPLayout Minimal.UniversalPPhases.

Local Notation hstate := (@M.pu_state pu_hprop).
Local Notation hrun_prog := (M.pu_run_prog pu_hprop_eqb pu_heval).

(* ================================================================= *)
(* The loaded host.                                                   *)
(* ================================================================= *)

(* pu_RA and pu_RB hold the guest's inputs, pu_PROG the program code, pu_GPC the
   guest pc 1; every other register 0, every version 0, host pc 1. *)
Definition pu_hregs (P : list E.instr) (x y : nat) (r : nat) : nat :=
  if Nat.eqb r pu_RA then x else
  if Nat.eqb r pu_RB then y else
  if Nat.eqb r pu_PROG then pu_prog_code P else
  if Nat.eqb r pu_GPC then 1 else 0.

Definition pu_hload (P : list E.instr) (x y : nat) : hstate := M.pu_start (pu_hregs P x y).

Lemma pu_hload_high : forall P x y r, 4 <= r -> hv (pu_hload P x y) r = 0.
Proof.
  intros P x y r Hr. simpl. unfold pu_hregs, pu_RA, pu_RB, pu_PROG, pu_GPC.
  destruct (Nat.eqb_spec r 0); [lia |]. destruct (Nat.eqb_spec r 1); [lia |].
  destruct (Nat.eqb_spec r 2); [lia |]. destruct (Nat.eqb_spec r 3); [lia |].
  reflexivity.
Qed.

(* ================================================================= *)
(* Slot records.                                                      *)
(* ================================================================= *)

Record pu_srec : Type := mkrec {
  pu_r_p : E.prop; pu_r_c : E.ctr; pu_r_k : nat; pu_r_gv : nat; pu_r_hv : nat; pu_r_v : nat }.

Definition pu_gfact (r : pu_srec) : E.fact := E.mkfact (pu_r_p r) (pu_r_c r) (pu_r_gv r).
Definition pu_hfact (r : pu_srec) : @M.pu_fact pu_hprop := M.mkfact PSlot (pu_SLOT (pu_r_c r) (pu_r_k r)) (pu_r_hv r).
Definition pu_rkey (r : pu_srec) : E.ctr * nat := (pu_r_c r, pu_r_k r).

Definition pu_count (c : E.ctr) (sg : list pu_srec) : nat :=
  length (filter (fun r => E.ctr_eqb (pu_r_c r) c) sg).

Definition pu_occupied (sg : list pu_srec) (c : E.ctr) (k : nat) : Prop :=
  exists r, In r sg /\ pu_r_c r = c /\ pu_r_k r = k.

(* The guest fact of r is about the present version of its counter. *)
Definition pu_current (g : E.state) (r : pu_srec) : Prop :=
  pu_r_gv r = E.ver (E.core_of g) (pu_r_c r).

Definition pu_rec_ok (g : E.state) (h : hstate) (r : pu_srec) : Prop :=
  pu_r_k r < 16 /\
  hv h (pu_SLOT (pu_r_c r) (pu_r_k r)) = pu_pair (pu_pcode (pu_r_p r)) (pu_r_v r) /\
  pu_r_gv r <= E.ver (E.core_of g) (pu_r_c r) /\
  pu_r_hv r <= hver h (pu_SLOT (pu_r_c r) (pu_r_k r)) /\
  (pu_r_gv r = E.ver (E.core_of g) (pu_r_c r) <-> pu_r_hv r = hver h (pu_SLOT (pu_r_c r) (pu_r_k r))) /\
  (pu_r_gv r = E.ver (E.core_of g) (pu_r_c r) ->
     pu_r_v r = E.val (E.core_of g) (pu_r_c r) /\ hv h (pu_MP (pu_r_c r) (pu_r_k r)) = S (pu_pcode (pu_r_p r))) /\
  (pu_r_gv r <> E.ver (E.core_of g) (pu_r_c r) -> hv h (pu_MP (pu_r_c r) (pu_r_k r)) = 0).

Record pu_rel_with (P : list E.instr) (sg : list pu_srec) (rho : option pu_srec)
  (g : E.state) (h : hstate) : Prop := {
  pu_rw_head : pu_at_head P h;
  pu_rw_err : E.err (E.core_of g) = false;
  pu_rw_greg : forall c, hv h (pu_greg c) = E.val (E.core_of g) c;
  pu_rw_gpc : hv h pu_GPC = E.pc (E.core_of g);
  pu_rw_gfacts : E.facts (E.core_of g) = map pu_gfact sg;
  pu_rw_hfacts : M.facts (M.core_of h) = map pu_hfact sg;
  pu_rw_gchan : E.chan (E.core_of g) = option_map pu_gfact rho;
  pu_rw_hchan : M.chan (M.core_of h) = option_map pu_hfact rho;
  pu_rw_rho : forall r, rho = Some r -> In r sg;
  pu_rw_mu : M.mu h = E.mu g;
  pu_rw_cert : M.cert h = E.cert g;
  pu_rw_nc : forall c, hv h (pu_NC c) = pu_count c sg;
  pu_rw_nodup : NoDup (map pu_rkey sg);
  pu_rw_klt : forall r, In r sg -> pu_r_k r < pu_count (pu_r_c r) sg;
  pu_rw_recs : forall r, In r sg -> pu_rec_ok g h r;
  pu_rw_free : forall c k, k < 16 -> ~ pu_occupied sg c k ->
              hv h (pu_SLOT c k) = 0 /\ hv h (pu_MP c k) = 0;
  pu_rw_dead : hv h pu_DEAD = 0 }.

Definition pu_rel (P : list E.instr) (g : E.state) (h : hstate) : Prop :=
  exists sg rho, pu_rel_with P sg rho g h.

Definition pu_rel_halt (P : list E.instr) (g : E.state) (h : hstate) : Prop :=
  E.halted P (E.core_of g) /\ M.pu_halted U_P (M.core_of h) /\
  hv h pu_RA = E.ca (E.core_of g) /\ hv h pu_RB = E.cb (E.core_of g) /\
  herr h = E.err (E.core_of g) /\ M.mu h = E.mu g /\ M.cert h = E.cert g /\
  exists sg rho,
    E.facts (E.core_of g) = map pu_gfact sg /\ M.facts (M.core_of h) = map pu_hfact sg /\
    E.chan (E.core_of g) = option_map pu_gfact rho /\
    M.chan (M.core_of h) = option_map pu_hfact rho.

(* ================================================================= *)
(* Register arithmetic.                                               *)
(* ================================================================= *)

Ltac pu_regs := intros; unfold pu_greg, pu_NC, pu_MP, pu_SLOT, pu_DEAD, pu_GPC, pu_RA, pu_RB, pu_T2,
  pu_in_mp, pu_in_slots in *; repeat match goal with c : E.ctr |- _ => destruct c end;
  simpl in *; lia.

Lemma pu_greg_ne_gpc : forall c, pu_greg c <> pu_GPC. Proof. pu_regs. Qed.
Lemma pu_greg_ne_t2 : forall c, pu_greg c <> pu_T2. Proof. pu_regs. Qed.
Lemma pu_greg_inj : forall c d, pu_greg c = pu_greg d -> c = d.
Proof. intros [] [] H; try reflexivity; discriminate H. Qed.
Lemma pu_greg_not_mp : forall c d, ~ pu_in_mp c (pu_greg d). Proof. pu_regs. Qed.
Lemma pu_gpc_not_mp : forall c, ~ pu_in_mp c pu_GPC. Proof. pu_regs. Qed.
Lemma pu_nc_ne_greg : forall c d, pu_NC d <> pu_greg c. Proof. pu_regs. Qed.
Lemma pu_nc_ne_gpc : forall d, pu_NC d <> pu_GPC. Proof. pu_regs. Qed.
Lemma pu_nc_not_mp : forall c d, ~ pu_in_mp c (pu_NC d). Proof. pu_regs. Qed.
Lemma pu_nc_inj : forall c d, pu_NC c = pu_NC d -> c = d.
Proof. intros [] [] H; try reflexivity; discriminate H. Qed.
Lemma pu_slot_ne_greg : forall c d k, pu_SLOT d k <> pu_greg c. Proof. pu_regs. Qed.
Lemma pu_slot_ne_gpc : forall d k, pu_SLOT d k <> pu_GPC. Proof. pu_regs. Qed.
Lemma pu_slot_ne_nc : forall c d k, pu_SLOT d k <> pu_NC c. Proof. pu_regs. Qed.
Lemma pu_slot_not_mp : forall c d k, ~ pu_in_mp c (pu_SLOT d k). Proof. pu_regs. Qed.
Lemma pu_slot_ge : forall d k, 48 <= pu_SLOT d k. Proof. pu_regs. Qed.
Lemma pu_slot_not_in : forall c d k, k < 16 -> c <> d -> ~ pu_in_slots c (pu_SLOT d k).
Proof. intros [] [] k Hk Hn; try (exfalso; apply Hn; reflexivity); pu_regs. Qed.
Lemma pu_slot_inj : forall c d k q, k < 16 -> q < 16 -> pu_SLOT c k = pu_SLOT d q -> c = d /\ k = q.
Proof.
  intros [] [] k q Hk Hq H; unfold pu_SLOT in H; simpl in H;
    (split; [reflexivity || (exfalso; lia) | lia]).
Qed.
Lemma pu_slot_ne_mp : forall c d k q, q < 16 -> pu_SLOT d k <> pu_MP c q. Proof. pu_regs. Qed.
Lemma pu_slot_ne_dead : forall d k, k < 16 -> pu_SLOT d k <> pu_DEAD. Proof. pu_regs. Qed.
Lemma pu_mp_ne_greg : forall c d k, pu_MP d k <> pu_greg c. Proof. pu_regs. Qed.
Lemma pu_mp_ne_gpc : forall d k, pu_MP d k <> pu_GPC. Proof. pu_regs. Qed.
Lemma pu_mp_ne_nc : forall c d k, pu_MP d k <> pu_NC c. Proof. pu_regs. Qed.
Lemma pu_mp_not_in : forall c d k, k < 16 -> c <> d -> ~ pu_in_mp c (pu_MP d k).
Proof. intros [] [] k Hk Hn; try (exfalso; apply Hn; reflexivity); pu_regs. Qed.
Lemma pu_mp_inj : forall c d k q, k < 16 -> q < 16 -> pu_MP c k = pu_MP d q -> c = d /\ k = q.
Proof.
  intros [] [] k q Hk Hq H; unfold pu_MP in H; simpl in H;
    (split; [reflexivity || (exfalso; lia) | lia]).
Qed.
Lemma pu_mp_ne_dead : forall d k, k < 16 -> pu_MP d k <> pu_DEAD. Proof. pu_regs. Qed.
Lemma pu_dead_ne_greg : forall c, pu_DEAD <> pu_greg c. Proof. pu_regs. Qed.
Lemma pu_dead_ne_gpc : pu_DEAD <> pu_GPC. Proof. pu_regs. Qed.
Lemma pu_dead_ne_nc : forall c, pu_DEAD <> pu_NC c. Proof. pu_regs. Qed.
Lemma pu_dead_ne_t2 : pu_DEAD <> pu_T2. Proof. pu_regs. Qed.
Lemma pu_dead_not_mp : forall c, ~ pu_in_mp c pu_DEAD. Proof. pu_regs. Qed.
Lemma pu_dead_ge : 48 <= pu_DEAD. Proof. pu_regs. Qed.
Lemma pu_dead_not_slots : forall c, ~ pu_in_slots c pu_DEAD. Proof. pu_regs. Qed.
Lemma pu_ra_ne_t2 : pu_RA <> pu_T2. Proof. pu_regs. Qed.
Lemma pu_rb_ne_t2 : pu_RB <> pu_T2. Proof. pu_regs. Qed.
Lemma pu_ra_ne_slot : forall c k, pu_RA <> pu_SLOT c k. Proof. pu_regs. Qed.
Lemma pu_rb_ne_slot : forall c k, pu_RB <> pu_SLOT c k. Proof. pu_regs. Qed.
Lemma pu_ra_ne_t7 : pu_RA <> pu_T7. Proof. unfold pu_RA, pu_T7. lia. Qed.
Lemma pu_rb_ne_t7 : pu_RB <> pu_T7. Proof. unfold pu_RB, pu_T7. lia. Qed.

Lemma pu_ctr_dec : forall c d : E.ctr, {c = d} + {c <> d}.
Proof. decide equality. Qed.

Lemma pu_ctr_eqb_eq : forall c d, E.ctr_eqb c d = true <-> c = d.
Proof. intros [] []; simpl; split; intro H; congruence. Qed.

Lemma pu_ctr_eqb_neq : forall c d, c <> d -> E.ctr_eqb c d = false.
Proof. intros [] [] H; try reflexivity; exfalso; apply H; reflexivity. Qed.

Lemma pu_ctr_eqb_refl : forall c, E.ctr_eqb c c = true.
Proof. intros []; reflexivity. Qed.

(* ================================================================= *)
(* The guest's moves.                                                 *)
(* ================================================================= *)

Lemma pu_gval_write : forall k c n j d,
  E.val (E.write k c n j) d = if E.ctr_eqb c d then n else E.val k d.
Proof. exact E.val_write. Qed.

Lemma pu_gpc_write : forall k c n j, E.pc (E.write k c n j) = j.
Proof. intros k [] n j; reflexivity. Qed.

Lemma pu_gkeep_record : forall k f c,
  E.val (E.record_fact k f) c = E.val k c /\ E.ver (E.record_fact k f) c = E.ver k c.
Proof. intros k f []; split; reflexivity. Qed.

Lemma pu_gkeep_commit : forall k f c,
  E.val (E.commit_to k f) c = E.val k c /\ E.ver (E.commit_to k f) c = E.ver k c.
Proof. intros k f []; split; reflexivity. Qed.

Lemma pu_gkeep_goto : forall k j c,
  E.val (E.goto k j) c = E.val k c /\ E.ver (E.goto k j) c = E.ver k c.
Proof. intros k j []; split; reflexivity. Qed.

Lemma pu_gkeep_trap : forall k c,
  E.val (E.trap k) c = E.val k c /\ E.ver (E.trap k) c = E.ver k c.
Proof. intros k []; split; reflexivity. Qed.

Lemma pu_gstep_exec : forall P g i,
  E.err (E.core_of g) = false -> E.fetch P (E.pc (E.core_of g)) = Some i -> i <> E.HALT ->
  E.step P g = E.exec g i.
Proof.
  intros P g i He Hf Hi. unfold E.step, E.next_instr. rewrite He, Hf.
  destruct i; try reflexivity. contradiction.
Qed.

Lemma pu_ghalted_iff : forall P g,
  E.err (E.core_of g) = false ->
  (E.halted P (E.core_of g) <->
   E.fetch P (E.pc (E.core_of g)) = None \/ E.fetch P (E.pc (E.core_of g)) = Some E.HALT).
Proof.
  intros P g He. unfold E.halted, E.next_instr. rewrite He.
  destruct (E.fetch P (E.pc (E.core_of g))) as [[] |]; split; intro H;
    try discriminate; auto; destruct H; discriminate.
Qed.

Lemma pu_ghalted_trap : forall P k, E.err k = true -> E.halted P k.
Proof. intros P k H. unfold E.halted, E.next_instr. rewrite H. reflexivity. Qed.

Lemma pu_gexec_noerr : forall g i, E.err (E.core_of g) = false ->
  E.exec g i = E.mkst (E.cexec (E.core_of g) i) (E.mu g + E.cost i)
                      (E.cert g || E.fires (E.core_of g) i).
Proof. reflexivity. Qed.

(* ================================================================= *)
(* Counting records.                                                  *)
(* ================================================================= *)

Lemma pu_count_cons : forall c r sg,
  pu_count c (r :: sg) = (if E.ctr_eqb (pu_r_c r) c then 1 else 0) + pu_count c sg.
Proof. intros. unfold pu_count. simpl. destruct (E.ctr_eqb (pu_r_c r) c); reflexivity. Qed.

Lemma pu_count_le_length : forall c sg, pu_count c sg <= length sg.
Proof. intros. unfold pu_count. apply filter_length_le. Qed.

Lemma pu_fresh_slot : forall sg c,
  (forall r, In r sg -> pu_r_k r < pu_count (pu_r_c r) sg) -> ~ pu_occupied sg c (pu_count c sg).
Proof.
  intros sg c H [r [Hin [Hc Hk]]]. specialize (H r Hin). rewrite Hc, Hk in H. lia.
Qed.

Lemma pu_occ_dec : forall sg c j, pu_occupied sg c j \/ ~ pu_occupied sg c j.
Proof.
  intros sg c j. induction sg as [| r sg IH].
  - right. intros [r [[] _]].
  - destruct (pu_ctr_dec (pu_r_c r) c) as [Hc | Hc]; [destruct (Nat.eq_dec (pu_r_k r) j) as [Hk | Hk] |].
    + left. exists r. split; [left; reflexivity | auto].
    + destruct IH as [[r' [Hin Hr']] | Hno].
      * left. exists r'. split; [right; exact Hin | exact Hr'].
      * right. intros [r' [[<- | Hin] [Hc' Hk']]]; [contradiction | apply Hno; exists r'; auto].
    + destruct IH as [[r' [Hin Hr']] | Hno].
      * left. exists r'. split; [right; exact Hin | exact Hr'].
      * right. intros [r' [[<- | Hin] [Hc' Hk']]]; [contradiction | apply Hno; exists r'; auto].
Qed.

Lemma pu_in_map_gfact : forall sg r, In r sg -> In (pu_gfact r) (map pu_gfact sg).
Proof. intros. apply in_map. assumption. Qed.

(* A fact equation between a record's guest fact and a guest claim. *)
Lemma pu_gfact_eq : forall r p c v,
  pu_gfact r = E.mkfact p c v -> pu_r_p r = p /\ pu_r_c r = c /\ pu_r_gv r = v.
Proof. intros r p c v H. unfold pu_gfact in H. injection H. auto. Qed.

(* ================================================================= *)
(* Keeping a record.                                                  *)
(* ================================================================= *)

(* A record whose slot, mirror and counter did not move stays sound. *)
Lemma pu_rec_ok_frame : forall g h g' h' r,
  hv h' (pu_SLOT (pu_r_c r) (pu_r_k r)) = hv h (pu_SLOT (pu_r_c r) (pu_r_k r)) ->
  hver h' (pu_SLOT (pu_r_c r) (pu_r_k r)) = hver h (pu_SLOT (pu_r_c r) (pu_r_k r)) ->
  hv h' (pu_MP (pu_r_c r) (pu_r_k r)) = hv h (pu_MP (pu_r_c r) (pu_r_k r)) ->
  E.ver (E.core_of g') (pu_r_c r) = E.ver (E.core_of g) (pu_r_c r) ->
  E.val (E.core_of g') (pu_r_c r) = E.val (E.core_of g) (pu_r_c r) ->
  pu_rec_ok g h r -> pu_rec_ok g' h' r.
Proof.
  intros g h g' h' r E1 E2 E3 E4 E5 H. unfold pu_rec_ok in *.
  rewrite E1, E2, E3, E4, E5. exact H.
Qed.

(* A record on a counter the guest wrote: the slot kept its value, its
   version rose by 2, the mirror is 0, and the guest version rose by 1, so
   both facts are stale. *)
Lemma pu_rec_ok_bump : forall g h g' h' r,
  hv h' (pu_SLOT (pu_r_c r) (pu_r_k r)) = hv h (pu_SLOT (pu_r_c r) (pu_r_k r)) ->
  hver h' (pu_SLOT (pu_r_c r) (pu_r_k r)) = 2 + hver h (pu_SLOT (pu_r_c r) (pu_r_k r)) ->
  hv h' (pu_MP (pu_r_c r) (pu_r_k r)) = 0 ->
  E.ver (E.core_of g') (pu_r_c r) = S (E.ver (E.core_of g) (pu_r_c r)) ->
  pu_rec_ok g h r -> pu_rec_ok g' h' r.
Proof.
  intros g h g' h' r E1 E2 E3 E4 [Hk [Hs [Hg [Hh _]]]]. unfold pu_rec_ok.
  rewrite E1, E2, E3, E4.
  set (a := E.ver (E.core_of g) (pu_r_c r)) in *.
  set (b := hver h (pu_SLOT (pu_r_c r) (pu_r_k r))) in *.
  split; [exact Hk |]. split; [exact Hs |]. split; [lia |]. split; [lia |].
  split; [split; intro; lia |]. split; [intro; lia | intros _; reflexivity].
Qed.

(* ================================================================= *)
(* The loaded host is related to the guest start.                     *)
(* ================================================================= *)

Theorem pu_hload_rel : forall P x y, pu_rel_with P [] None (E.start x y) (pu_hload P x y).
Proof.
  intros P x y. constructor.
  - split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    intros r Hr. apply pu_hload_high. unfold pu_scratch in Hr. lia.
  - reflexivity.
  - intros []; reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros r H; discriminate H.
  - reflexivity.
  - reflexivity.
  - intros c. apply pu_hload_high. unfold pu_NC. lia.
  - constructor.
  - intros r [].
  - intros r [].
  - intros c k _ _. split; apply pu_hload_high; unfold pu_SLOT, pu_MP; lia.
  - apply pu_hload_high. unfold pu_DEAD. lia.
Qed.

(* ================================================================= *)
(* From hreach to at least one host step.                             *)
(* ================================================================= *)

Lemma pu_hreach_step : forall h h', pu_hreach h h' -> h' <> h ->
  exists n, hrun_prog (S n) U_P h = h'.
Proof.
  intros h h' [n Hn] Hne. destruct n as [| n]; [simpl in Hn; congruence |].
  exists n. exact Hn.
Qed.

Lemma pu_host_at_head_not_halted : forall P h, pu_at_head P h -> ~ M.pu_halted U_P (M.core_of h).
Proof.
  intros P h (Hp & He & _). unfold M.pu_halted, M.pu_next_instr. rewrite He, Hp.
  vm_compute. discriminate.
Qed.

Lemma pu_rel_halt_trap : forall P g h,
  E.err (E.core_of g) = true -> herr h = true ->
  hv h pu_RA = E.ca (E.core_of g) -> hv h pu_RB = E.cb (E.core_of g) ->
  M.mu h = E.mu g -> M.cert h = E.cert g ->
  (exists sg rho,
    E.facts (E.core_of g) = map pu_gfact sg /\ M.facts (M.core_of h) = map pu_hfact sg /\
    E.chan (E.core_of g) = option_map pu_gfact rho /\
    M.chan (M.core_of h) = option_map pu_hfact rho) ->
  pu_rel_halt P g h.
Proof.
  intros P g h Hg Hh Ha Hb Hm Hc Hx. split; [apply pu_ghalted_trap, Hg |].
  split; [apply M.pu_multi_trapped_halted, Hh |].
  split; [exact Ha |]. split; [exact Hb |]. split; [congruence |].
  split; [exact Hm |]. split; [exact Hc | exact Hx].
Qed.

(* ================================================================= *)
(* One guest step.                                                    *)
(* ================================================================= *)

Definition pu_step_result (P : list E.instr) (sg : list pu_srec) (g : E.state) (h : hstate) : Prop :=
  exists n h', hrun_prog (S n) U_P h = h' /\
    ((exists sg' rho', pu_rel_with P sg' rho' (E.step P g) h' /\
        forall r, In r sg' -> In r sg \/ pu_current (E.step P g) r) \/
     (E.err (E.core_of (E.step P g)) = true /\ pu_rel_halt P (E.step P g) h')).

Section Step.

Variables (P : list E.instr) (sg : list pu_srec) (rho : option pu_srec) (g : E.state) (h : hstate).
Hypothesis R : pu_rel_with P sg rho g h.

Local Notation k := (E.core_of g).

Lemma pu_R_fetch : E.fetch P (hv h pu_GPC) = E.fetch P (E.pc k).
Proof. rewrite (pu_rw_gpc _ _ _ _ _ R). reflexivity. Qed.

Lemma pu_R_ra : hv h pu_RA = E.ca k.
Proof. rewrite <- pu_greg_CA. exact (pu_rw_greg _ _ _ _ _ R E.CA). Qed.

Lemma pu_R_rb : hv h pu_RB = E.cb k.
Proof. rewrite <- pu_greg_CB. exact (pu_rw_greg _ _ _ _ _ R E.CB). Qed.

Lemma pu_R_corr : exists sg0 rho0,
  E.facts k = map pu_gfact sg0 /\ M.facts (M.core_of h) = map pu_hfact sg0 /\
  E.chan k = option_map pu_gfact rho0 /\ M.chan (M.core_of h) = option_map pu_hfact rho0.
Proof.
  exists sg, rho. split; [exact (pu_rw_gfacts _ _ _ _ _ R) |].
  split; [exact (pu_rw_hfacts _ _ _ _ _ R) |].
  split; [exact (pu_rw_gchan _ _ _ _ _ R) | exact (pu_rw_hchan _ _ _ _ _ R)].
Qed.

(* Guest stopped: pc 0, past the end, or HALT. *)
Lemma pu_ustep_stop :
  E.fetch P (E.pc k) = None \/ E.fetch P (E.pc k) = Some E.HALT ->
  exists h', pu_hreach h h' /\ pu_rel_halt P g h'.
Proof.
  intro Hf. rewrite <- pu_R_fetch in Hf.
  destruct (pu_phase_stop P h (pu_rw_head _ _ _ _ _ R) Hf)
    as [h' [Hr [_ [He [Hh [Hv [_ [SF [SC [SE [SM SR]]]]]]]]]]].
  exists h'. split; [exact Hr |].
  split; [apply pu_ghalted_iff; [exact (pu_rw_err _ _ _ _ _ R) | rewrite <- pu_R_fetch; exact Hf] |].
  split; [exact Hh |].
  split; [rewrite Hv; exact pu_R_ra |]. split; [rewrite Hv; exact pu_R_rb |].
  split; [rewrite He; symmetry; exact (pu_rw_err _ _ _ _ _ R) |].
  split; [rewrite SM; exact (pu_rw_mu _ _ _ _ _ R) |].
  split; [rewrite SR; exact (pu_rw_cert _ _ _ _ _ R) |].
  destruct pu_R_corr as [sg0 [rho0 [H1 [H2 [H3 H4]]]]].
  exists sg0, rho0. rewrite SF, SC. auto.
Qed.

(* INC c. *)
Lemma pu_ustep_inc : forall c, E.fetch P (E.pc k) = Some (E.INC c) -> pu_step_result P sg g h.
Proof.
  intros c Hf. pose proof (pu_rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g =
    E.mkst (E.write k c (S (E.val k c)) (S (E.pc k))) (E.mu g) (E.cert g)).
  { rewrite (pu_gstep_exec P g (E.INC c) He Hf) by discriminate.
    rewrite pu_gexec_noerr by exact He. unfold E.cexec. rewrite He. simpl.
    rewrite Nat.add_0_r, orb_false_r. reflexivity. }
  rewrite <- pu_R_fetch in Hf.
  destruct (pu_phase_inc P h c (pu_rw_head _ _ _ _ _ R) Hf)
    as [h' [Hr [AH [Hg [Hgpc [Hq [Hoth [Hver [SF [SC [SE [SM SR]]]]]]]]]]]].
  apply pu_hreach_step in Hr.
  2:{ intro E. rewrite E in Hgpc. lia. }
  destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
  exists sg, rho. split; [| intros r Hin; left; exact Hin].
  rewrite Hs. constructor; simpl.
  - exact AH.
  - rewrite E.err_write. exact He.
  - intro d. rewrite pu_gval_write. destruct (pu_ctr_dec c d) as [<- | Hn'].
    + rewrite pu_ctr_eqb_refl, Hg, (pu_rw_greg _ _ _ _ _ R). reflexivity.
    + rewrite (pu_ctr_eqb_neq _ _ Hn'). rewrite Hoth.
      * exact (pu_rw_greg _ _ _ _ _ R d).
      * intro E. apply Hn'. apply pu_greg_inj. congruence.
      * apply pu_greg_ne_gpc.
      * apply pu_greg_not_mp.
  - rewrite pu_gpc_write, Hgpc, (pu_rw_gpc _ _ _ _ _ R). reflexivity.
  - rewrite E.facts_write. exact (pu_rw_gfacts _ _ _ _ _ R).
  - rewrite SF. exact (pu_rw_hfacts _ _ _ _ _ R).
  - rewrite E.chan_write. exact (pu_rw_gchan _ _ _ _ _ R).
  - rewrite SC. exact (pu_rw_hchan _ _ _ _ _ R).
  - exact (pu_rw_rho _ _ _ _ _ R).
  - rewrite SM. exact (pu_rw_mu _ _ _ _ _ R).
  - rewrite SR. exact (pu_rw_cert _ _ _ _ _ R).
  - intro d. rewrite Hoth; [exact (pu_rw_nc _ _ _ _ _ R d) | apply pu_nc_ne_greg | apply pu_nc_ne_gpc
                           | apply pu_nc_not_mp].
  - exact (pu_rw_nodup _ _ _ _ _ R).
  - exact (pu_rw_klt _ _ _ _ _ R).
  - intros r Hin. pose proof (pu_rw_recs _ _ _ _ _ R r Hin) as Hok.
    pose proof (proj1 Hok) as Hk.
    destruct (pu_ctr_dec (pu_r_c r) c) as [Hc | Hc].
    + destruct (Hq (pu_r_k r) Hk) as [Q1 [Q2 Q3]]. rewrite <- Hc in Q1, Q2, Q3.
      apply (pu_rec_ok_bump g h); [exact Q2 | exact Q3 | exact Q1 | | exact Hok].
      simpl. rewrite E.ver_write, Hc, pu_ctr_eqb_refl. reflexivity.
    + apply (pu_rec_ok_frame g h); [| | | | | exact Hok].
      * apply Hoth; [apply pu_slot_ne_greg | apply pu_slot_ne_gpc | apply pu_slot_not_mp].
      * apply Hver; [apply pu_slot_ge | apply pu_slot_not_in; [exact Hk | congruence]].
      * apply Hoth; [apply pu_mp_ne_greg | apply pu_mp_ne_gpc | apply pu_mp_not_in; [exact Hk | congruence]].
      * simpl. rewrite E.ver_write, pu_ctr_eqb_neq by congruence. reflexivity.
      * simpl. rewrite pu_gval_write, pu_ctr_eqb_neq by congruence. reflexivity.
  - intros d q Hq16 Hno. destruct (pu_rw_free _ _ _ _ _ R d q Hq16 Hno) as [F1 F2].
    destruct (pu_ctr_dec d c) as [-> | Hc].
    + destruct (Hq q Hq16) as [Q1 [Q2 _]]. rewrite Q2. auto.
    + rewrite !Hoth; auto using pu_slot_ne_greg, pu_slot_ne_gpc, pu_slot_not_mp, pu_mp_ne_greg, pu_mp_ne_gpc.
      apply pu_mp_not_in; [exact Hq16 | congruence].
  - rewrite Hoth; [exact (pu_rw_dead _ _ _ _ _ R) | apply pu_dead_ne_greg | apply pu_dead_ne_gpc
                  | apply pu_dead_not_mp].
Qed.

(* DEC c j on a positive counter. *)
Lemma pu_ustep_dec_taken : forall c j u,
  E.fetch P (E.pc k) = Some (E.DEC c j) -> E.val k c = S u -> pu_step_result P sg g h.
Proof.
  intros c j u Hf Hu. pose proof (pu_rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g = E.mkst (E.write k c u j) (E.mu g) (E.cert g)).
  { rewrite (pu_gstep_exec P g (E.DEC c j) He Hf) by discriminate.
    rewrite pu_gexec_noerr by exact He. unfold E.cexec. rewrite He, Hu. simpl.
    rewrite Nat.add_0_r, orb_false_r. reflexivity. }
  rewrite <- pu_R_fetch in Hf.
  assert (Hu' : hv h (pu_greg c) = S u) by (rewrite (pu_rw_greg _ _ _ _ _ R); exact Hu).
  destruct (pu_phase_dec_taken P h c j u (pu_rw_head _ _ _ _ _ R) Hf Hu')
    as [h' [Hr [AH [Hg [Hgpc [Hq [Hoth [Hver [SF [SC [SE [SM SR]]]]]]]]]]]].
  apply pu_hreach_step in Hr.
  2:{ intro E. rewrite E in Hg. lia. }
  destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
  exists sg, rho. split; [| intros r Hin; left; exact Hin].
  rewrite Hs. constructor; simpl.
  - exact AH.
  - rewrite E.err_write. exact He.
  - intro d. rewrite pu_gval_write. destruct (pu_ctr_dec c d) as [<- | Hn'].
    + rewrite pu_ctr_eqb_refl, Hg. reflexivity.
    + rewrite (pu_ctr_eqb_neq _ _ Hn'). rewrite Hoth.
      * exact (pu_rw_greg _ _ _ _ _ R d).
      * intro E. apply Hn'. apply pu_greg_inj. congruence.
      * apply pu_greg_ne_gpc.
      * apply pu_greg_not_mp.
  - rewrite pu_gpc_write, Hgpc. reflexivity.
  - rewrite E.facts_write. exact (pu_rw_gfacts _ _ _ _ _ R).
  - rewrite SF. exact (pu_rw_hfacts _ _ _ _ _ R).
  - rewrite E.chan_write. exact (pu_rw_gchan _ _ _ _ _ R).
  - rewrite SC. exact (pu_rw_hchan _ _ _ _ _ R).
  - exact (pu_rw_rho _ _ _ _ _ R).
  - rewrite SM. exact (pu_rw_mu _ _ _ _ _ R).
  - rewrite SR. exact (pu_rw_cert _ _ _ _ _ R).
  - intro d. rewrite Hoth; [exact (pu_rw_nc _ _ _ _ _ R d) | apply pu_nc_ne_greg | apply pu_nc_ne_gpc
                           | apply pu_nc_not_mp].
  - exact (pu_rw_nodup _ _ _ _ _ R).
  - exact (pu_rw_klt _ _ _ _ _ R).
  - intros r Hin. pose proof (pu_rw_recs _ _ _ _ _ R r Hin) as Hok.
    pose proof (proj1 Hok) as Hk.
    destruct (pu_ctr_dec (pu_r_c r) c) as [Hc | Hc].
    + destruct (Hq (pu_r_k r) Hk) as [Q1 [Q2 Q3]]. rewrite <- Hc in Q1, Q2, Q3.
      apply (pu_rec_ok_bump g h); [exact Q2 | exact Q3 | exact Q1 | | exact Hok].
      simpl. rewrite E.ver_write, Hc, pu_ctr_eqb_refl. reflexivity.
    + apply (pu_rec_ok_frame g h); [| | | | | exact Hok].
      * apply Hoth; [apply pu_slot_ne_greg | apply pu_slot_ne_gpc | apply pu_slot_not_mp].
      * apply Hver; [apply pu_slot_ge | apply pu_slot_not_in; [exact Hk | congruence]].
      * apply Hoth; [apply pu_mp_ne_greg | apply pu_mp_ne_gpc | apply pu_mp_not_in; [exact Hk | congruence]].
      * simpl. rewrite E.ver_write, pu_ctr_eqb_neq by congruence. reflexivity.
      * simpl. rewrite pu_gval_write, pu_ctr_eqb_neq by congruence. reflexivity.
  - intros d q Hq16 Hno. destruct (pu_rw_free _ _ _ _ _ R d q Hq16 Hno) as [F1 F2].
    destruct (pu_ctr_dec d c) as [-> | Hc].
    + destruct (Hq q Hq16) as [Q1 [Q2 _]]. rewrite Q2. auto.
    + rewrite !Hoth; auto using pu_slot_ne_greg, pu_slot_ne_gpc, pu_slot_not_mp, pu_mp_ne_greg, pu_mp_ne_gpc.
      apply pu_mp_not_in; [exact Hq16 | congruence].
  - rewrite Hoth; [exact (pu_rw_dead _ _ _ _ _ R) | apply pu_dead_ne_greg | apply pu_dead_ne_gpc
                  | apply pu_dead_not_mp].
Qed.

(* A move that changes only pu_GPC on the host side, every version from 48
   on kept, and a guest core with the same counters and versions. *)
Lemma pu_rel_keep : forall g' h',
  pu_at_head P h' ->
  E.err (E.core_of g') = false ->
  (forall r, r <> pu_GPC -> hv h' r = hv h r) ->
  (forall r, 48 <= r -> hver h' r = hver h r) ->
  (forall c, E.val (E.core_of g') c = E.val k c /\ E.ver (E.core_of g') c = E.ver k c) ->
  hv h' pu_GPC = E.pc (E.core_of g') ->
  E.facts (E.core_of g') = E.facts k -> M.facts (M.core_of h') = M.facts (M.core_of h) ->
  forall rho', E.chan (E.core_of g') = option_map pu_gfact rho' ->
  M.chan (M.core_of h') = option_map pu_hfact rho' -> (forall r, rho' = Some r -> In r sg) ->
  M.mu h' = E.mu g' -> M.cert h' = E.cert g' ->
  pu_rel_with P sg rho' g' h'.
Proof.
  intros g' h' AH He Hv Hw Hk Hgpc HF1 HF2 rho' HC1 HC2 Hrho HM HR. constructor.
  - exact AH.
  - exact He.
  - intro d. rewrite Hv by apply pu_greg_ne_gpc. rewrite (proj1 (Hk d)).
    exact (pu_rw_greg _ _ _ _ _ R d).
  - exact Hgpc.
  - rewrite HF1. exact (pu_rw_gfacts _ _ _ _ _ R).
  - rewrite HF2. exact (pu_rw_hfacts _ _ _ _ _ R).
  - exact HC1.
  - exact HC2.
  - exact Hrho.
  - exact HM.
  - exact HR.
  - intro d. rewrite Hv by apply pu_nc_ne_gpc. exact (pu_rw_nc _ _ _ _ _ R d).
  - exact (pu_rw_nodup _ _ _ _ _ R).
  - exact (pu_rw_klt _ _ _ _ _ R).
  - intros r Hin. apply (pu_rec_ok_frame g h).
    + apply Hv, pu_slot_ne_gpc.
    + apply Hw, pu_slot_ge.
    + apply Hv, pu_mp_ne_gpc.
    + exact (proj2 (Hk (pu_r_c r))).
    + exact (proj1 (Hk (pu_r_c r))).
    + exact (pu_rw_recs _ _ _ _ _ R r Hin).
  - intros d q Hq Hno. rewrite !Hv by (apply pu_slot_ne_gpc || apply pu_mp_ne_gpc).
    exact (pu_rw_free _ _ _ _ _ R d q Hq Hno).
  - rewrite Hv by exact pu_dead_ne_gpc. exact (pu_rw_dead _ _ _ _ _ R).
Qed.

(* DEC c j on a zero counter. *)
Lemma pu_ustep_dec_zero : forall c j,
  E.fetch P (E.pc k) = Some (E.DEC c j) -> E.val k c = 0 -> pu_step_result P sg g h.
Proof.
  intros c j Hf Hz. pose proof (pu_rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g = E.mkst (E.goto k (S (E.pc k))) (E.mu g) (E.cert g)).
  { rewrite (pu_gstep_exec P g (E.DEC c j) He Hf) by discriminate.
    rewrite pu_gexec_noerr by exact He. unfold E.cexec. rewrite He, Hz. simpl.
    rewrite Nat.add_0_r, orb_false_r. reflexivity. }
  rewrite <- pu_R_fetch in Hf.
  assert (Hz' : hv h (pu_greg c) = 0) by (rewrite (pu_rw_greg _ _ _ _ _ R); exact Hz).
  destruct (pu_phase_dec_zero P h c j (pu_rw_head _ _ _ _ _ R) Hf Hz')
    as [h' [Hr [AH [Hgpc [Hoth [Hver [SF [SC [SE [SM SR]]]]]]]]]].
  apply pu_hreach_step in Hr.
  2:{ intro E. rewrite E in Hgpc. lia. }
  destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
  exists sg, rho. split; [| intros r Hin; left; exact Hin].
  rewrite Hs. apply pu_rel_keep; simpl.
  - exact AH.
  - exact He.
  - exact Hoth.
  - exact Hver.
  - intro d. apply pu_gkeep_goto.
  - rewrite Hgpc, (pu_rw_gpc _ _ _ _ _ R). reflexivity.
  - reflexivity.
  - exact SF.
  - exact (pu_rw_gchan _ _ _ _ _ R).
  - rewrite SC. exact (pu_rw_hchan _ _ _ _ _ R).
  - exact (pu_rw_rho _ _ _ _ _ R).
  - rewrite SM. exact (pu_rw_mu _ _ _ _ _ R).
  - rewrite SR. exact (pu_rw_cert _ _ _ _ _ R).
Qed.

(* CHECK p c. *)
Lemma pu_ustep_check : forall p c,
  E.fetch P (E.pc k) = Some (E.CHECK p c) -> pu_step_result P sg g h.
Proof.
  intros p c Hf. pose proof (pu_rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g =
    E.mkst (if E.check_ok k p c then E.record_fact k (E.claim k p c) else E.trap k)
           (E.mu g + 1) (E.cert g)).
  { rewrite (pu_gstep_exec P g (E.CHECK p c) He Hf) by discriminate.
    rewrite pu_gexec_noerr by exact He. unfold E.cexec. rewrite He. simpl.
    rewrite orb_false_r. reflexivity. }
  rewrite <- pu_R_fetch in Hf.
  pose proof (pu_rw_head _ _ _ _ _ R) as AH0.
  set (j := pu_count c sg).
  assert (Hnc : hv h (pu_NC c) = j) by exact (pu_rw_nc _ _ _ _ _ R c).
  assert (Hlen : length (M.facts (M.core_of h)) = length (E.facts k)).
  { rewrite (pu_rw_hfacts _ _ _ _ _ R), (pu_rw_gfacts _ _ _ _ _ R), !map_length. reflexivity. }
  destruct (lt_dec j 16) as [Hj | Hj].
  - (* a fresh slot *)
    assert (Hfree : ~ pu_occupied sg c j) by (apply pu_fresh_slot, (pu_rw_klt _ _ _ _ _ R)).
    destruct (pu_rw_free _ _ _ _ _ R c j Hj Hfree) as [Hsl Hmp].
    destruct (E.check_ok k p c) eqn:Hck.
    + (* the check passes *)
      unfold E.check_ok in Hck. rewrite He in Hck. simpl in Hck.
      apply andb_true_iff in Hck as [Hev Hcap].
      apply E.eval_iff in Hev. apply Nat.ltb_lt in Hcap.
      assert (Hev' : E.holds p (hv h (pu_greg c))) by (rewrite (pu_rw_greg _ _ _ _ _ R); exact Hev).
      assert (Hcap' : length (M.facts (M.core_of h)) < M.pu_fact_cap)
        by (rewrite Hlen; exact Hcap).
      destruct (pu_phase_check_pass P h p c j AH0 Hf Hnc Hj Hsl Hev' Hcap')
        as [h' [Hr [AH [Hgpc [Hnc' [Hmp' [Hsl' [Hvl [HF [HC [HM [HR [Hoth Hver]]]]]]]]]]]]].
      apply pu_hreach_step in Hr.
      2:{ intro E. rewrite E in HM. lia. }
      destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
      set (r0 := mkrec p c j (E.ver k c) (hver h' (pu_SLOT c j)) (E.val k c)).
      exists (r0 :: sg), rho.
      assert (Hkey : forall r, In r sg -> pu_rkey r <> (c, j)).
      { intros r Hin E. apply Hfree. exists r. unfold pu_rkey in E. injection E. auto. }
      split.
      2:{ intros r [<- | Hin]; [right | left; exact Hin].
          unfold pu_current. rewrite Hs. pose proof (pu_gkeep_record k (E.claim k p c) c) as [G1 G2].
          simpl in G1, G2 |- *. rewrite G2. reflexivity. }
      rewrite Hs. constructor; simpl.
      * exact AH.
      * exact He.
      * intro d. rewrite (proj1 (pu_gkeep_record k _ d)).
        rewrite Hoth; [exact (pu_rw_greg _ _ _ _ _ R d) | apply pu_greg_ne_gpc
          | intro E; symmetry in E; exact (pu_nc_ne_greg _ _ E)
          | intro E; symmetry in E; exact (pu_mp_ne_greg _ _ _ E)
          | intro E; symmetry in E; exact (pu_slot_ne_greg _ _ _ E)].
      * rewrite Hgpc, (pu_rw_gpc _ _ _ _ _ R). reflexivity.
      * rewrite (pu_rw_gfacts _ _ _ _ _ R). reflexivity.
      * rewrite HF, (pu_rw_hfacts _ _ _ _ _ R). reflexivity.
      * exact (pu_rw_gchan _ _ _ _ _ R).
      * rewrite HC. exact (pu_rw_hchan _ _ _ _ _ R).
      * intros r Hr. right. exact (pu_rw_rho _ _ _ _ _ R r Hr).
      * rewrite HM, (pu_rw_mu _ _ _ _ _ R). reflexivity.
      * rewrite HR. exact (pu_rw_cert _ _ _ _ _ R).
      * intro d. rewrite pu_count_cons. simpl. destruct (pu_ctr_dec c d) as [<- | Hd].
        -- rewrite pu_ctr_eqb_refl, Hnc'. reflexivity.
        -- rewrite (pu_ctr_eqb_neq _ _ Hd). simpl. rewrite Hoth.
           ++ exact (pu_rw_nc _ _ _ _ _ R d).
           ++ apply pu_nc_ne_gpc.
           ++ intro E. apply Hd. symmetry. apply pu_nc_inj, E.
           ++ apply not_eq_sym, pu_mp_ne_nc.
           ++ apply not_eq_sym, pu_slot_ne_nc.
      * constructor; [| exact (pu_rw_nodup _ _ _ _ _ R)].
        intro Hin. apply in_map_iff in Hin as [r [Hr Hin]]. exact (Hkey r Hin Hr).
      * intros r [<- | Hin].
        -- simpl. rewrite pu_count_cons. simpl. rewrite pu_ctr_eqb_refl. unfold j. lia.
        -- rewrite pu_count_cons. pose proof (pu_rw_klt _ _ _ _ _ R r Hin). lia.
      * intros r [<- | Hin].
        -- unfold pu_rec_ok. pose proof (pu_gkeep_record k (E.claim k p c) c) as [G1 G2].
           simpl in G1, G2 |- *. rewrite G1, G2.
           split; [exact Hj |]. split; [rewrite Hsl', (pu_rw_greg _ _ _ _ _ R); reflexivity |].
           split; [lia |]. split; [lia |]. split; [tauto |].
           split; [intros _; split; [reflexivity | exact Hmp'] | intro E; contradiction].
        -- pose proof (pu_rw_recs _ _ _ _ _ R r Hin) as Hok. pose proof (proj1 Hok) as Hk.
           assert (Hne : pu_rkey r <> (c, j)) by exact (Hkey r Hin).
           assert (Hs1 : pu_SLOT (pu_r_c r) (pu_r_k r) <> pu_SLOT c j).
           { intro E. apply pu_slot_inj in E as [E1 E2]; [| exact Hk | exact Hj].
             apply Hne. unfold pu_rkey. rewrite E1, E2. reflexivity. }
           assert (Hm1 : pu_MP (pu_r_c r) (pu_r_k r) <> pu_MP c j).
           { intro E. apply pu_mp_inj in E as [E1 E2]; [| exact Hk | exact Hj].
             apply Hne. unfold pu_rkey. rewrite E1, E2. reflexivity. }
           apply (pu_rec_ok_frame g h); [| | | | | exact Hok].
           ++ apply Hoth; [apply pu_slot_ne_gpc | apply pu_slot_ne_nc | apply pu_slot_ne_mp; exact Hj
                          | exact Hs1].
           ++ apply Hver; [apply pu_slot_ge | exact Hs1].
           ++ apply Hoth; [apply pu_mp_ne_gpc | apply pu_mp_ne_nc | exact Hm1
                          | apply not_eq_sym, pu_slot_ne_mp; exact Hk].
           ++ simpl. apply pu_gkeep_record.
           ++ simpl. apply pu_gkeep_record.
      * intros d q Hq Hno.
        assert (Hno' : ~ pu_occupied sg d q)
          by (intros [r [Hin Hr]]; apply Hno; exists r; split; [right; exact Hin | exact Hr]).
        assert (Hne : (d, q) <> (c, j))
          by (intro E; injection E as -> ->; apply Hno; exists r0; split; [left |]; auto).
        destruct (pu_rw_free _ _ _ _ _ R d q Hq Hno') as [F1 F2].
        assert (Hs1 : pu_SLOT d q <> pu_SLOT c j).
        { intro E. apply pu_slot_inj in E as [E1 E2]; [| exact Hq | exact Hj].
          apply Hne. rewrite E1, E2. reflexivity. }
        assert (Hm1 : pu_MP d q <> pu_MP c j).
        { intro E. apply pu_mp_inj in E as [E1 E2]; [| exact Hq | exact Hj].
          apply Hne. rewrite E1, E2. reflexivity. }
        rewrite Hoth by first [apply pu_slot_ne_gpc | apply pu_slot_ne_nc | apply pu_slot_ne_mp; exact Hj
                               | exact Hs1].
        rewrite (Hoth (pu_MP d q)) by first [apply pu_mp_ne_gpc | apply pu_mp_ne_nc | exact Hm1
                                          | apply not_eq_sym, pu_slot_ne_mp; exact Hq].
        auto.
      * rewrite Hoth; [exact (pu_rw_dead _ _ _ _ _ R) | exact pu_dead_ne_gpc | apply pu_dead_ne_nc
          | apply not_eq_sym, pu_mp_ne_dead; exact Hj | apply not_eq_sym, pu_slot_ne_dead; exact Hj].
    + (* the check fails: the property is false or the table is full *)
      assert (Hbad : ~ E.holds p (hv h (pu_greg c)) \/ M.pu_fact_cap <= length (M.facts (M.core_of h))).
      { unfold E.check_ok in Hck. rewrite He in Hck. simpl in Hck.
        rewrite (pu_rw_greg _ _ _ _ _ R), Hlen.
        destruct (E.eval p (E.val k c)) eqn:Hev.
        - right. simpl in Hck. apply Nat.ltb_ge in Hck. exact Hck.
        - left. intro H. apply E.eval_iff in H. congruence. }
      destruct (pu_phase_check_fail P h p c j AH0 Hf Hnc Hj Hsl Hbad)
        as [h' [Hr [Herr [_ [HF [HC [HM [HR [_ [_ [Hoth _]]]]]]]]]]].
      apply pu_hreach_step in Hr.
      2:{ intro E. rewrite E in Herr. rewrite (proj1 (proj2 AH0)) in Herr. discriminate. }
      destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. right. rewrite Hs.
      split; [reflexivity |].
      apply pu_rel_halt_trap; simpl.
      * reflexivity.
      * exact Herr.
      * rewrite Hoth; [exact pu_R_ra | exact pu_ra_ne_t2 | apply pu_ra_ne_slot].
      * rewrite Hoth; [exact pu_R_rb | exact pu_rb_ne_t2 | apply pu_rb_ne_slot].
      * rewrite HM, (pu_rw_mu _ _ _ _ _ R). reflexivity.
      * rewrite HR. exact (pu_rw_cert _ _ _ _ _ R).
      * destruct pu_R_corr as [sg0 [rho0 [H1 [H2 [H3 H4]]]]].
        exists sg0, rho0. rewrite HF, HC. auto.
  - (* bank full: CHECK PSlot pu_DEAD *)
    assert (Hck : E.check_ok k p c = false).
    { unfold E.check_ok. apply andb_false_iff. right. apply Nat.ltb_ge.
      rewrite (pu_rw_gfacts _ _ _ _ _ R), map_length.
      pose proof (pu_count_le_length c sg). fold j in H. unfold E.fact_cap. lia. }
    rewrite Hck in Hs.
    assert (H16 : 16 <= hv h (pu_NC c)) by (rewrite Hnc; lia).
    destruct (pu_phase_check_dead P h p c AH0 Hf H16 (pu_rw_dead _ _ _ _ _ R))
      as [h' [Hr [Herr [_ [HF [HC [HM [HR [_ [_ [Hoth _]]]]]]]]]]].
    apply pu_hreach_step in Hr.
    2:{ intro E. rewrite E in Herr. rewrite (proj1 (proj2 AH0)) in Herr. discriminate. }
    destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. right. rewrite Hs.
    split; [reflexivity |].
    apply pu_rel_halt_trap; simpl.
    + reflexivity.
    + exact Herr.
    + rewrite Hoth; [exact pu_R_ra | exact pu_ra_ne_t2 | exact pu_ra_ne_t7].
    + rewrite Hoth; [exact pu_R_rb | exact pu_rb_ne_t2 | exact pu_rb_ne_t7].
    + rewrite HM, (pu_rw_mu _ _ _ _ _ R). reflexivity.
    + rewrite HR. exact (pu_rw_cert _ _ _ _ _ R).
    + destruct pu_R_corr as [sg0 [rho0 [H1 [H2 [H3 H4]]]]].
      exists sg0, rho0. rewrite HF, HC. auto.
Qed.

(* The first index below n where f takes the value x, or none. *)
Lemma pu_first_match : forall (f : nat -> nat) x n,
  (exists j, j < n /\ f j = x /\ forall j', j' < j -> f j' <> x) \/
  (forall j, j < n -> f j <> x).
Proof.
  intros f x n. induction n as [| n IH].
  - right. intros j Hj. lia.
  - destruct IH as [[j [Hj [Hf Hm]]] | Hno].
    + left. exists j. split; [lia |]. auto.
    + destruct (Nat.eq_dec (f n) x) as [E | E].
      * left. exists n. split; [lia |]. split; [exact E | exact Hno].
      * right. intros j Hj. destruct (Nat.eq_dec j n) as [-> | Hn]; [exact E |].
        apply Hno. lia.
Qed.

(* COMMIT p c. *)
Lemma pu_ustep_commit : forall p c,
  E.fetch P (E.pc k) = Some (E.COMMIT p c) -> pu_step_result P sg g h.
Proof.
  intros p c Hf. pose proof (pu_rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g =
    E.mkst (if E.commit_ok k p c then E.commit_to k (E.claim k p c) else E.trap k)
           (E.mu g + 1) (E.cert g)).
  { rewrite (pu_gstep_exec P g (E.COMMIT p c) He Hf) by discriminate.
    rewrite pu_gexec_noerr by exact He. unfold E.cexec. rewrite He. simpl.
    rewrite orb_false_r. reflexivity. }
  rewrite <- pu_R_fetch in Hf.
  pose proof (pu_rw_head _ _ _ _ _ R) as AH0.
  destruct (pu_first_match (fun j => hv h (pu_MP c j)) (S (pu_pcode p)) 16)
    as [[j [Hj [Hm Hfirst]]] | Hno].
  - (* the first matching mirror: its record is current and on p *)
    simpl in Hm, Hfirst.
    assert (Hocc : pu_occupied sg c j).
    { destruct (pu_occ_dec sg c j) as [Ho | Ho]; [exact Ho |].
      destruct (pu_rw_free _ _ _ _ _ R c j Hj Ho) as [_ F]. rewrite F in Hm. discriminate. }
    destruct Hocc as [r [Hin [Hc Hk]]].
    destruct (pu_rw_recs _ _ _ _ _ R r Hin) as [_ [_ [_ [_ [Hiff [Hcur Hstale]]]]]].
    rewrite Hc, Hk in Hiff, Hcur, Hstale.
    destruct (Nat.eq_dec (pu_r_gv r) (E.ver k c)) as [Hg | Hg].
    2:{ rewrite (Hstale Hg) in Hm. discriminate. }
    destruct (Hcur Hg) as [_ Hmp]. rewrite Hm in Hmp. injection Hmp as Hp.
    apply pu_pcode_inj in Hp.
    assert (Hhv : pu_r_hv r = hver h (pu_SLOT c j)) by (apply Hiff, Hg).
    assert (Hhf : pu_hfact r = M.mkfact PSlot (pu_SLOT c j) (hver h (pu_SLOT c j)))
      by (unfold pu_hfact; rewrite Hc, Hk, Hhv; reflexivity).
    assert (Hgf : pu_gfact r = E.claim k p c)
      by (unfold pu_gfact, E.claim; rewrite Hc, Hg, Hp; reflexivity).
    assert (Hhin : In (M.mkfact PSlot (pu_SLOT c j) (hver h (pu_SLOT c j))) (M.facts (M.core_of h))).
    { rewrite (pu_rw_hfacts _ _ _ _ _ R), <- Hhf. apply in_map, Hin. }
    destruct (pu_phase_commit_pass P h p c j AH0 Hf Hj Hm Hfirst Hhin)
      as [h' [Hr [AH [Hgpc [HF [HC [HM [HR [Hoth Hver]]]]]]]]].
    assert (Hck : E.commit_ok k p c = true).
    { apply E.commit_ok_iff. split; [exact He |].
      rewrite (pu_rw_gfacts _ _ _ _ _ R), <- Hgf. apply in_map, Hin. }
    rewrite Hck in Hs.
    apply pu_hreach_step in Hr.
    2:{ intro E. rewrite E in HM. lia. }
    destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
    exists sg, (Some r). split; [| intros r' Hin'; left; exact Hin'].
    rewrite Hs. apply pu_rel_keep; simpl.
    + exact AH.
    + exact He.
    + exact Hoth.
    + exact Hver.
    + intro d. apply pu_gkeep_commit.
    + rewrite Hgpc, (pu_rw_gpc _ _ _ _ _ R). reflexivity.
    + reflexivity.
    + exact HF.
    + rewrite Hgf. reflexivity.
    + rewrite HC, Hhf. reflexivity.
    + intros r' E. injection E as <-. exact Hin.
    + rewrite HM, (pu_rw_mu _ _ _ _ _ R). reflexivity.
    + rewrite HR. exact (pu_rw_cert _ _ _ _ _ R).
  - (* no mirror matches: the guest has no live fact on p and c *)
    assert (Hck : E.commit_ok k p c = false).
    { destruct (E.commit_ok k p c) eqn:Hck; [| reflexivity].
      apply E.commit_ok_iff in Hck as [_ Hin].
      rewrite (pu_rw_gfacts _ _ _ _ _ R) in Hin. apply in_map_iff in Hin as [r [Hr Hin]].
      unfold E.claim in Hr. apply pu_gfact_eq in Hr as [Hp [Hc Hg]].
      destruct (pu_rw_recs _ _ _ _ _ R r Hin) as [Hk [_ [_ [_ [_ [Hcur _]]]]]].
      destruct (Hcur (eq_trans Hg (f_equal (E.ver k) (eq_sym Hc)))) as [_ Hmp].
      rewrite Hc, Hp in Hmp. exfalso. exact (Hno (pu_r_k r) Hk Hmp). }
    rewrite Hck in Hs.
    assert (Hnd : ~ In (M.mkfact PSlot pu_DEAD (hver h pu_DEAD)) (M.facts (M.core_of h))).
    { rewrite (pu_rw_hfacts _ _ _ _ _ R). intro Hin. apply in_map_iff in Hin as [r [Hr Hin]].
      unfold pu_hfact in Hr. apply (f_equal M.f_reg) in Hr. cbn [M.f_reg] in Hr.
      destruct (pu_rw_recs _ _ _ _ _ R r Hin) as [Hk _].
      exact (pu_slot_ne_dead _ _ Hk Hr). }
    destruct (pu_phase_commit_none P h p c AH0 Hf Hno Hnd)
      as [h' [Hr [Herr [_ [HF [HC [HM [HR [_ [Hoth _]]]]]]]]]].
    apply pu_hreach_step in Hr.
    2:{ intro E. rewrite E in Herr. rewrite (proj1 (proj2 AH0)) in Herr. discriminate. }
    destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. right. rewrite Hs.
    split; [reflexivity |].
    apply pu_rel_halt_trap; simpl.
    + reflexivity.
    + exact Herr.
    + rewrite Hoth; [exact pu_R_ra | exact pu_ra_ne_t2].
    + rewrite Hoth; [exact pu_R_rb | exact pu_rb_ne_t2].
    + rewrite HM, (pu_rw_mu _ _ _ _ _ R). reflexivity.
    + rewrite HR. exact (pu_rw_cert _ _ _ _ _ R).
    + destruct pu_R_corr as [sg0 [rho0 [H1 [H2 [H3 H4]]]]].
      exists sg0, rho0. rewrite HF, HC. auto.
Qed.

(* CERTIFY. *)
Lemma pu_ustep_certify : E.fetch P (E.pc k) = Some E.CERTIFY -> pu_step_result P sg g h.
Proof.
  intros Hf. pose proof (pu_rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g =
    E.mkst (if E.certify_ok k then E.goto k (S (E.pc k)) else E.trap k)
           (E.mu g + 1) (E.cert g || E.certify_ok k)).
  { rewrite (pu_gstep_exec P g E.CERTIFY He Hf) by discriminate.
    rewrite pu_gexec_noerr by exact He. unfold E.cexec. rewrite He. reflexivity. }
  rewrite <- pu_R_fetch in Hf.
  pose proof (pu_rw_head _ _ _ _ _ R) as AH0.
  case_eq rho; [intros r Hrho | intros Hrho].
  - (* the channel is full: the flag rises *)
    assert (Hok : E.certify_ok k = true).
    { unfold E.certify_ok. rewrite He, (pu_rw_gchan _ _ _ _ _ R), Hrho. reflexivity. }
    rewrite Hok, orb_true_r in Hs.
    destruct (pu_phase_certify_pass P h (pu_hfact r) AH0 Hf
               (eq_trans (pu_rw_hchan _ _ _ _ _ R) (f_equal (option_map pu_hfact) Hrho)))
      as [h' [Hr [AH [Hgpc [HF [HC [HM [HR [Hoth Hver]]]]]]]]].
    apply pu_hreach_step in Hr.
    2:{ intro E. rewrite E in HM. lia. }
    destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
    exists sg, rho. split; [| intros r' Hin'; left; exact Hin'].
    rewrite Hs. apply pu_rel_keep; simpl.
    + exact AH.
    + exact He.
    + exact Hoth.
    + exact Hver.
    + intro d. apply pu_gkeep_goto.
    + rewrite Hgpc, (pu_rw_gpc _ _ _ _ _ R). reflexivity.
    + reflexivity.
    + exact HF.
    + exact (pu_rw_gchan _ _ _ _ _ R).
    + rewrite HC. exact (pu_rw_hchan _ _ _ _ _ R).
    + exact (pu_rw_rho _ _ _ _ _ R).
    + rewrite HM, (pu_rw_mu _ _ _ _ _ R). reflexivity.
    + exact HR.
  - (* the channel is empty: both trap *)
    assert (Hok : E.certify_ok k = false).
    { unfold E.certify_ok. rewrite He, (pu_rw_gchan _ _ _ _ _ R), Hrho. reflexivity. }
    rewrite Hok, orb_false_r in Hs.
    destruct (pu_phase_certify_fail P h AH0 Hf
               (eq_trans (pu_rw_hchan _ _ _ _ _ R) (f_equal (option_map pu_hfact) Hrho)))
      as [h' [Hr [Herr [_ [HF [HC [HM [HR [Hoth _]]]]]]]]].
    apply pu_hreach_step in Hr.
    2:{ intro E. rewrite E in Herr. rewrite (proj1 (proj2 AH0)) in Herr. discriminate. }
    destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. right. rewrite Hs.
    split; [reflexivity |].
    apply pu_rel_halt_trap; simpl.
    + reflexivity.
    + exact Herr.
    + rewrite Hoth. exact pu_R_ra.
    + rewrite Hoth. exact pu_R_rb.
    + rewrite HM, (pu_rw_mu _ _ _ _ _ R). reflexivity.
    + rewrite HR. exact (pu_rw_cert _ _ _ _ _ R).
    + destruct pu_R_corr as [sg0 [rho0 [H1 [H2 [H3 H4]]]]].
      exists sg0, rho0. rewrite HF, HC. auto.
Qed.

(* PAY: the guest and the host each pay 1 and move on; nothing else moves. *)
Lemma pu_ustep_pay : E.fetch P (E.pc k) = Some E.PAY -> pu_step_result P sg g h.
Proof.
  intros Hf. pose proof (pu_rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g = E.mkst (E.goto k (S (E.pc k))) (E.mu g + 1) (E.cert g)).
  { rewrite (pu_gstep_exec P g E.PAY He Hf) by discriminate.
    rewrite pu_gexec_noerr by exact He. unfold E.cexec. rewrite He. simpl.
    rewrite orb_false_r. reflexivity. }
  rewrite <- pu_R_fetch in Hf.
  pose proof (pu_rw_head _ _ _ _ _ R) as AH0.
  destruct (pu_phase_pay P h AH0 Hf)
    as [h' [Hr [AH [Hgpc [HF [HC [HM [HR [Hoth Hver]]]]]]]]].
  apply pu_hreach_step in Hr.
  2:{ intro E. rewrite E in HM. lia. }
  destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
  exists sg, rho. split; [| intros r' Hin'; left; exact Hin'].
  rewrite Hs. apply pu_rel_keep; simpl.
  + exact AH.
  + exact He.
  + exact Hoth.
  + exact Hver.
  + intro d. apply pu_gkeep_goto.
  + rewrite Hgpc, (pu_rw_gpc _ _ _ _ _ R). reflexivity.
  + reflexivity.
  + exact HF.
  + exact (pu_rw_gchan _ _ _ _ _ R).
  + rewrite HC. exact (pu_rw_hchan _ _ _ _ _ R).
  + exact (pu_rw_rho _ _ _ _ _ R).
  + rewrite HM, (pu_rw_mu _ _ _ _ _ R). reflexivity.
  + rewrite HR. exact (pu_rw_cert _ _ _ _ _ R).
Qed.

End Step.

(* ================================================================= *)
(* The simulation step.                                               *)
(* ================================================================= *)

Lemma pu_gnot_halted : forall P g i,
  E.err (E.core_of g) = false -> E.fetch P (E.pc (E.core_of g)) = Some i -> i <> E.HALT ->
  ~ E.halted P (E.core_of g).
Proof.
  intros P g i He Hf Hi. unfold E.halted, E.next_instr. rewrite He, Hf.
  destruct i; try discriminate. contradiction.
Qed.

Theorem pu_U_step_with : forall P sg rho g h, pu_rel_with P sg rho g h ->
  (E.halted P (E.core_of g) /\ exists h', pu_hreach h h' /\ pu_rel_halt P g h') \/
  (~ E.halted P (E.core_of g) /\ pu_step_result P sg g h).
Proof.
  intros P sg rho g h R. pose proof (pu_rw_err _ _ _ _ _ R) as He.
  destruct (E.fetch P (E.pc (E.core_of g))) as [i |] eqn:Hf.
  - destruct i as [c | c j | | p c | p c | |].
    + right. split; [apply (pu_gnot_halted P g (E.INC c)); auto; discriminate |].
      exact (pu_ustep_inc P sg rho g h R c Hf).
    + right. split; [apply (pu_gnot_halted P g (E.DEC c j)); auto; discriminate |].
      destruct (E.val (E.core_of g) c) as [| u] eqn:Hv.
      * exact (pu_ustep_dec_zero P sg rho g h R c j Hf Hv).
      * exact (pu_ustep_dec_taken P sg rho g h R c j u Hf Hv).
    + left. split; [apply pu_ghalted_iff; auto |].
      apply (pu_ustep_stop P sg rho g h R). right. exact Hf.
    + right. split; [apply (pu_gnot_halted P g (E.CHECK p c)); auto; discriminate |].
      exact (pu_ustep_check P sg rho g h R p c Hf).
    + right. split; [apply (pu_gnot_halted P g (E.COMMIT p c)); auto; discriminate |].
      exact (pu_ustep_commit P sg rho g h R p c Hf).
    + right. split; [apply (pu_gnot_halted P g E.CERTIFY); auto; discriminate |].
      exact (pu_ustep_certify P sg rho g h R Hf).
    + right. split; [apply (pu_gnot_halted P g E.PAY); auto; discriminate |].
      exact (pu_ustep_pay P sg rho g h R Hf).
  - left. split; [apply pu_ghalted_iff; auto |].
    apply (pu_ustep_stop P sg rho g h R). left. exact Hf.
Qed.

Theorem pu_U_step : forall P g h, pu_rel P g h ->
  (E.halted P (E.core_of g) /\ exists h', pu_hreach h h' /\ pu_rel_halt P g h') \/
  (~ E.halted P (E.core_of g) /\
   exists n h', hrun_prog (S n) U_P h = h' /\
     (pu_rel P (E.step P g) h' \/
      (E.err (E.core_of (E.step P g)) = true /\ pu_rel_halt P (E.step P g) h'))).
Proof.
  intros P g h [sg [rho R]].
  destruct (pu_U_step_with P sg rho g h R) as [H | [Hn [n [h' [Hr [[sg' [rho' [R' _]]] | Ht]]]]]].
  - left. exact H.
  - right. split; [exact Hn |]. exists n, h'. split; [exact Hr |]. left. exists sg', rho'.
    exact R'.
  - right. split; [exact Hn |]. exists n, h'. split; [exact Hr |]. right. exact Ht.
Qed.

(* A related host is running, not halted. *)
Lemma pu_rel_host_running : forall P sg rho g h, pu_rel_with P sg rho g h ->
  ~ M.pu_halted U_P (M.core_of h).
Proof. intros P sg rho g h R. exact (pu_host_at_head_not_halted P h (pu_rw_head _ _ _ _ _ R)). Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions pu_hload_rel.
Print Assumptions pu_ustep_stop.
Print Assumptions pu_ustep_inc.
Print Assumptions pu_ustep_dec_taken.
Print Assumptions pu_ustep_dec_zero.
Print Assumptions pu_ustep_check.
Print Assumptions pu_ustep_commit.
Print Assumptions pu_ustep_certify.
Print Assumptions pu_ustep_pay.
Print Assumptions pu_U_step_with.
Print Assumptions pu_U_step.
Print Assumptions pu_rel_host_running.
