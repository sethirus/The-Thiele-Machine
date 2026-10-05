(** UniversalSim.v: the fixed host program U simulates every guest
    program of the small machine, one guest step at a time.

    The simulation relation rel P g h says that the host state h sits at
    HEAD and mirrors the guest state g of program P. Its witness is a list
    of slot records sg and a channel record rho. A slot record names one
    passing guest CHECK p c: the guest fact (p, c, gv) and the host fact on
    slot register SLOT c k at host version hv, with the value v that was
    checked. The relation states:

      the host is at HEAD (pc 1, trap latch down, PROG holds prog_code P,
      every scratch register 0) and the guest trap latch is down;
      RA and RB hold the guest counters and GPC the guest pc;
      the guest fact table is the list of guest facts of sg, and the host
      fact table is the list of host facts of sg, in the same order;
      the two channels name the guest and the host fact of rho, and rho
      is one of the records;
      the ledgers and the flags are equal;
      NC c is the number of records on counter c, the records on c use
      distinct slots below that number, and every slot is below 16;
      each record's slot holds pair (pcode p) v; the guest fact is current
      exactly when the host fact is; a current record checked the guest's
      present value and its mirror MP c k holds pcode p + 1; a stale
      record's mirror holds 0;
      every slot and mirror that no record uses holds 0, and DEAD holds 0.

    rel_halt P g h says that both machines have stopped (halted or
    trapped), with equal counters, trap latch, ledger and flag, and fact
    tables and channels that still correspond.

      hload_rel     the loaded host is related to the guest start
      U_step_with   one guest step: either the guest is stopped and the host
                    reaches a related stop, or the host takes at least one
                    step to a state related to the guest's next state, or,
                    when the guest traps, to a related host trap; new
                    records are current in the guest's next state
      U_step        the same with the witness hidden

    Dependencies: the Coq standard library, the vendored
    coq-undecidability library, EarnedCore.v, EarnedGeneric.v,
    EarnedMulti.v, UniversalCodes.v, UniversalBridge.v, UniversalBlocks.v,
    UniversalLayout.v and UniversalPhases.v. No axioms, no Admitted.      *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.UniversalCodes Minimal.UniversalBridge Minimal.UniversalBlocks
  Minimal.UniversalLayout Minimal.UniversalPhases.

Local Notation hstate := (@M.state hprop).
Local Notation hrun_prog := (M.run_prog hprop_eqb heval).

(* ================================================================= *)
(* The loaded host.                                                   *)
(* ================================================================= *)

(* RA and RB hold the guest's inputs, PROG the program code, GPC the
   guest pc 1; every other register 0, every version 0, host pc 1. *)
Definition hregs (P : list E.instr) (x y : nat) (r : nat) : nat :=
  if Nat.eqb r RA then x else
  if Nat.eqb r RB then y else
  if Nat.eqb r PROG then prog_code P else
  if Nat.eqb r GPC then 1 else 0.

Definition hload (P : list E.instr) (x y : nat) : hstate := M.start (hregs P x y).

Lemma hload_high : forall P x y r, 4 <= r -> hv (hload P x y) r = 0.
Proof.
  intros P x y r Hr. simpl. unfold hregs, RA, RB, PROG, GPC.
  destruct (Nat.eqb_spec r 0); [lia |]. destruct (Nat.eqb_spec r 1); [lia |].
  destruct (Nat.eqb_spec r 2); [lia |]. destruct (Nat.eqb_spec r 3); [lia |].
  reflexivity.
Qed.

(* ================================================================= *)
(* Slot records.                                                      *)
(* ================================================================= *)

Record srec : Type := mkrec {
  r_p : E.prop; r_c : E.ctr; r_k : nat; r_gv : nat; r_hv : nat; r_v : nat }.

Definition gfact (r : srec) : E.fact := E.mkfact (r_p r) (r_c r) (r_gv r).
Definition hfact (r : srec) : @M.fact hprop := M.mkfact PSlot (SLOT (r_c r) (r_k r)) (r_hv r).
Definition rkey (r : srec) : E.ctr * nat := (r_c r, r_k r).

Definition count (c : E.ctr) (sg : list srec) : nat :=
  length (filter (fun r => E.ctr_eqb (r_c r) c) sg).

Definition occupied (sg : list srec) (c : E.ctr) (k : nat) : Prop :=
  exists r, In r sg /\ r_c r = c /\ r_k r = k.

(* The guest fact of r is about the present version of its counter. *)
Definition current (g : E.state) (r : srec) : Prop :=
  r_gv r = E.ver (E.core_of g) (r_c r).

Definition rec_ok (g : E.state) (h : hstate) (r : srec) : Prop :=
  r_k r < 16 /\
  hv h (SLOT (r_c r) (r_k r)) = pair (pcode (r_p r)) (r_v r) /\
  r_gv r <= E.ver (E.core_of g) (r_c r) /\
  r_hv r <= hver h (SLOT (r_c r) (r_k r)) /\
  (r_gv r = E.ver (E.core_of g) (r_c r) <-> r_hv r = hver h (SLOT (r_c r) (r_k r))) /\
  (r_gv r = E.ver (E.core_of g) (r_c r) ->
     r_v r = E.val (E.core_of g) (r_c r) /\ hv h (MP (r_c r) (r_k r)) = S (pcode (r_p r))) /\
  (r_gv r <> E.ver (E.core_of g) (r_c r) -> hv h (MP (r_c r) (r_k r)) = 0).

Record rel_with (P : list E.instr) (sg : list srec) (rho : option srec)
  (g : E.state) (h : hstate) : Prop := {
  rw_head : at_head P h;
  rw_err : E.err (E.core_of g) = false;
  rw_greg : forall c, hv h (greg c) = E.val (E.core_of g) c;
  rw_gpc : hv h GPC = E.pc (E.core_of g);
  rw_gfacts : E.facts (E.core_of g) = map gfact sg;
  rw_hfacts : M.facts (M.core_of h) = map hfact sg;
  rw_gchan : E.chan (E.core_of g) = option_map gfact rho;
  rw_hchan : M.chan (M.core_of h) = option_map hfact rho;
  rw_rho : forall r, rho = Some r -> In r sg;
  rw_mu : M.mu h = E.mu g;
  rw_cert : M.cert h = E.cert g;
  rw_nc : forall c, hv h (NC c) = count c sg;
  rw_nodup : NoDup (map rkey sg);
  rw_klt : forall r, In r sg -> r_k r < count (r_c r) sg;
  rw_recs : forall r, In r sg -> rec_ok g h r;
  rw_free : forall c k, k < 16 -> ~ occupied sg c k ->
              hv h (SLOT c k) = 0 /\ hv h (MP c k) = 0;
  rw_dead : hv h DEAD = 0 }.

Definition rel (P : list E.instr) (g : E.state) (h : hstate) : Prop :=
  exists sg rho, rel_with P sg rho g h.

Definition rel_halt (P : list E.instr) (g : E.state) (h : hstate) : Prop :=
  E.halted P (E.core_of g) /\ M.halted U (M.core_of h) /\
  hv h RA = E.ca (E.core_of g) /\ hv h RB = E.cb (E.core_of g) /\
  herr h = E.err (E.core_of g) /\ M.mu h = E.mu g /\ M.cert h = E.cert g /\
  exists sg rho,
    E.facts (E.core_of g) = map gfact sg /\ M.facts (M.core_of h) = map hfact sg /\
    E.chan (E.core_of g) = option_map gfact rho /\
    M.chan (M.core_of h) = option_map hfact rho.

(* ================================================================= *)
(* Register arithmetic.                                               *)
(* ================================================================= *)

Ltac regs := intros; unfold greg, NC, MP, SLOT, DEAD, GPC, RA, RB, T2,
  in_mp, in_slots in *; repeat match goal with c : E.ctr |- _ => destruct c end;
  simpl in *; lia.

Lemma greg_ne_gpc : forall c, greg c <> GPC. Proof. regs. Qed.
Lemma greg_ne_t2 : forall c, greg c <> T2. Proof. regs. Qed.
Lemma greg_inj : forall c d, greg c = greg d -> c = d.
Proof. intros [] [] H; try reflexivity; discriminate H. Qed.
Lemma greg_not_mp : forall c d, ~ in_mp c (greg d). Proof. regs. Qed.
Lemma gpc_not_mp : forall c, ~ in_mp c GPC. Proof. regs. Qed.
Lemma nc_ne_greg : forall c d, NC d <> greg c. Proof. regs. Qed.
Lemma nc_ne_gpc : forall d, NC d <> GPC. Proof. regs. Qed.
Lemma nc_not_mp : forall c d, ~ in_mp c (NC d). Proof. regs. Qed.
Lemma nc_inj : forall c d, NC c = NC d -> c = d.
Proof. intros [] [] H; try reflexivity; discriminate H. Qed.
Lemma slot_ne_greg : forall c d k, SLOT d k <> greg c. Proof. regs. Qed.
Lemma slot_ne_gpc : forall d k, SLOT d k <> GPC. Proof. regs. Qed.
Lemma slot_ne_nc : forall c d k, SLOT d k <> NC c. Proof. regs. Qed.
Lemma slot_not_mp : forall c d k, ~ in_mp c (SLOT d k). Proof. regs. Qed.
Lemma slot_ge : forall d k, 48 <= SLOT d k. Proof. regs. Qed.
Lemma slot_not_in : forall c d k, k < 16 -> c <> d -> ~ in_slots c (SLOT d k).
Proof. intros [] [] k Hk Hn; try (exfalso; apply Hn; reflexivity); regs. Qed.
Lemma slot_inj : forall c d k q, k < 16 -> q < 16 -> SLOT c k = SLOT d q -> c = d /\ k = q.
Proof.
  intros [] [] k q Hk Hq H; unfold SLOT in H; simpl in H;
    (split; [reflexivity || (exfalso; lia) | lia]).
Qed.
Lemma slot_ne_mp : forall c d k q, q < 16 -> SLOT d k <> MP c q. Proof. regs. Qed.
Lemma slot_ne_dead : forall d k, k < 16 -> SLOT d k <> DEAD. Proof. regs. Qed.
Lemma mp_ne_greg : forall c d k, MP d k <> greg c. Proof. regs. Qed.
Lemma mp_ne_gpc : forall d k, MP d k <> GPC. Proof. regs. Qed.
Lemma mp_ne_nc : forall c d k, MP d k <> NC c. Proof. regs. Qed.
Lemma mp_not_in : forall c d k, k < 16 -> c <> d -> ~ in_mp c (MP d k).
Proof. intros [] [] k Hk Hn; try (exfalso; apply Hn; reflexivity); regs. Qed.
Lemma mp_inj : forall c d k q, k < 16 -> q < 16 -> MP c k = MP d q -> c = d /\ k = q.
Proof.
  intros [] [] k q Hk Hq H; unfold MP in H; simpl in H;
    (split; [reflexivity || (exfalso; lia) | lia]).
Qed.
Lemma mp_ne_dead : forall d k, k < 16 -> MP d k <> DEAD. Proof. regs. Qed.
Lemma dead_ne_greg : forall c, DEAD <> greg c. Proof. regs. Qed.
Lemma dead_ne_gpc : DEAD <> GPC. Proof. regs. Qed.
Lemma dead_ne_nc : forall c, DEAD <> NC c. Proof. regs. Qed.
Lemma dead_ne_t2 : DEAD <> T2. Proof. regs. Qed.
Lemma dead_not_mp : forall c, ~ in_mp c DEAD. Proof. regs. Qed.
Lemma dead_ge : 48 <= DEAD. Proof. regs. Qed.
Lemma dead_not_slots : forall c, ~ in_slots c DEAD. Proof. regs. Qed.
Lemma ra_ne_t2 : RA <> T2. Proof. regs. Qed.
Lemma rb_ne_t2 : RB <> T2. Proof. regs. Qed.
Lemma ra_ne_slot : forall c k, RA <> SLOT c k. Proof. regs. Qed.
Lemma rb_ne_slot : forall c k, RB <> SLOT c k. Proof. regs. Qed.
Lemma ra_ne_t7 : RA <> T7. Proof. unfold RA, T7. lia. Qed.
Lemma rb_ne_t7 : RB <> T7. Proof. unfold RB, T7. lia. Qed.

Lemma ctr_dec : forall c d : E.ctr, {c = d} + {c <> d}.
Proof. decide equality. Qed.

Lemma ctr_eqb_eq : forall c d, E.ctr_eqb c d = true <-> c = d.
Proof. intros [] []; simpl; split; intro H; congruence. Qed.

Lemma ctr_eqb_neq : forall c d, c <> d -> E.ctr_eqb c d = false.
Proof. intros [] [] H; try reflexivity; exfalso; apply H; reflexivity. Qed.

Lemma ctr_eqb_refl : forall c, E.ctr_eqb c c = true.
Proof. intros []; reflexivity. Qed.

(* ================================================================= *)
(* The guest's moves.                                                 *)
(* ================================================================= *)

Lemma gval_write : forall k c n j d,
  E.val (E.write k c n j) d = if E.ctr_eqb c d then n else E.val k d.
Proof. exact E.val_write. Qed.

Lemma gpc_write : forall k c n j, E.pc (E.write k c n j) = j.
Proof. intros k [] n j; reflexivity. Qed.

Lemma gkeep_record : forall k f c,
  E.val (E.record_fact k f) c = E.val k c /\ E.ver (E.record_fact k f) c = E.ver k c.
Proof. intros k f []; split; reflexivity. Qed.

Lemma gkeep_commit : forall k f c,
  E.val (E.commit_to k f) c = E.val k c /\ E.ver (E.commit_to k f) c = E.ver k c.
Proof. intros k f []; split; reflexivity. Qed.

Lemma gkeep_goto : forall k j c,
  E.val (E.goto k j) c = E.val k c /\ E.ver (E.goto k j) c = E.ver k c.
Proof. intros k j []; split; reflexivity. Qed.

Lemma gkeep_trap : forall k c,
  E.val (E.trap k) c = E.val k c /\ E.ver (E.trap k) c = E.ver k c.
Proof. intros k []; split; reflexivity. Qed.

Lemma gstep_exec : forall P g i,
  E.err (E.core_of g) = false -> E.fetch P (E.pc (E.core_of g)) = Some i -> i <> E.HALT ->
  E.step P g = E.exec g i.
Proof.
  intros P g i He Hf Hi. unfold E.step, E.next_instr. rewrite He, Hf.
  destruct i; try reflexivity. contradiction.
Qed.

Lemma ghalted_iff : forall P g,
  E.err (E.core_of g) = false ->
  (E.halted P (E.core_of g) <->
   E.fetch P (E.pc (E.core_of g)) = None \/ E.fetch P (E.pc (E.core_of g)) = Some E.HALT).
Proof.
  intros P g He. unfold E.halted, E.next_instr. rewrite He.
  destruct (E.fetch P (E.pc (E.core_of g))) as [[] |]; split; intro H;
    try discriminate; auto; destruct H; discriminate.
Qed.

Lemma ghalted_trap : forall P k, E.err k = true -> E.halted P k.
Proof. intros P k H. unfold E.halted, E.next_instr. rewrite H. reflexivity. Qed.

Lemma gexec_noerr : forall g i, E.err (E.core_of g) = false ->
  E.exec g i = E.mkst (E.cexec (E.core_of g) i) (E.mu g + E.cost i)
                      (E.cert g || E.fires (E.core_of g) i).
Proof. reflexivity. Qed.

(* ================================================================= *)
(* Counting records.                                                  *)
(* ================================================================= *)

Lemma count_cons : forall c r sg,
  count c (r :: sg) = (if E.ctr_eqb (r_c r) c then 1 else 0) + count c sg.
Proof. intros. unfold count. simpl. destruct (E.ctr_eqb (r_c r) c); reflexivity. Qed.

Lemma count_le_length : forall c sg, count c sg <= length sg.
Proof. intros. unfold count. apply filter_length_le. Qed.

Lemma fresh_slot : forall sg c,
  (forall r, In r sg -> r_k r < count (r_c r) sg) -> ~ occupied sg c (count c sg).
Proof.
  intros sg c H [r [Hin [Hc Hk]]]. specialize (H r Hin). rewrite Hc, Hk in H. lia.
Qed.

Lemma occ_dec : forall sg c j, occupied sg c j \/ ~ occupied sg c j.
Proof.
  intros sg c j. induction sg as [| r sg IH].
  - right. intros [r [[] _]].
  - destruct (ctr_dec (r_c r) c) as [Hc | Hc]; [destruct (Nat.eq_dec (r_k r) j) as [Hk | Hk] |].
    + left. exists r. split; [left; reflexivity | auto].
    + destruct IH as [[r' [Hin Hr']] | Hno].
      * left. exists r'. split; [right; exact Hin | exact Hr'].
      * right. intros [r' [[<- | Hin] [Hc' Hk']]]; [contradiction | apply Hno; exists r'; auto].
    + destruct IH as [[r' [Hin Hr']] | Hno].
      * left. exists r'. split; [right; exact Hin | exact Hr'].
      * right. intros [r' [[<- | Hin] [Hc' Hk']]]; [contradiction | apply Hno; exists r'; auto].
Qed.

Lemma in_map_gfact : forall sg r, In r sg -> In (gfact r) (map gfact sg).
Proof. intros. apply in_map. assumption. Qed.

(* A fact equation between a record's guest fact and a guest claim. *)
Lemma gfact_eq : forall r p c v,
  gfact r = E.mkfact p c v -> r_p r = p /\ r_c r = c /\ r_gv r = v.
Proof. intros r p c v H. unfold gfact in H. injection H. auto. Qed.

(* ================================================================= *)
(* Keeping a record.                                                  *)
(* ================================================================= *)

(* A record whose slot, mirror and counter did not move stays sound. *)
Lemma rec_ok_frame : forall g h g' h' r,
  hv h' (SLOT (r_c r) (r_k r)) = hv h (SLOT (r_c r) (r_k r)) ->
  hver h' (SLOT (r_c r) (r_k r)) = hver h (SLOT (r_c r) (r_k r)) ->
  hv h' (MP (r_c r) (r_k r)) = hv h (MP (r_c r) (r_k r)) ->
  E.ver (E.core_of g') (r_c r) = E.ver (E.core_of g) (r_c r) ->
  E.val (E.core_of g') (r_c r) = E.val (E.core_of g) (r_c r) ->
  rec_ok g h r -> rec_ok g' h' r.
Proof.
  intros g h g' h' r E1 E2 E3 E4 E5 H. unfold rec_ok in *.
  rewrite E1, E2, E3, E4, E5. exact H.
Qed.

(* A record on a counter the guest wrote: the slot kept its value, its
   version rose by 2, the mirror is 0, and the guest version rose by 1, so
   both facts are stale. *)
Lemma rec_ok_bump : forall g h g' h' r,
  hv h' (SLOT (r_c r) (r_k r)) = hv h (SLOT (r_c r) (r_k r)) ->
  hver h' (SLOT (r_c r) (r_k r)) = 2 + hver h (SLOT (r_c r) (r_k r)) ->
  hv h' (MP (r_c r) (r_k r)) = 0 ->
  E.ver (E.core_of g') (r_c r) = S (E.ver (E.core_of g) (r_c r)) ->
  rec_ok g h r -> rec_ok g' h' r.
Proof.
  intros g h g' h' r E1 E2 E3 E4 [Hk [Hs [Hg [Hh _]]]]. unfold rec_ok.
  rewrite E1, E2, E3, E4.
  set (a := E.ver (E.core_of g) (r_c r)) in *.
  set (b := hver h (SLOT (r_c r) (r_k r))) in *.
  split; [exact Hk |]. split; [exact Hs |]. split; [lia |]. split; [lia |].
  split; [split; intro; lia |]. split; [intro; lia | intros _; reflexivity].
Qed.

(* ================================================================= *)
(* The loaded host is related to the guest start.                     *)
(* ================================================================= *)

Theorem hload_rel : forall P x y, rel_with P [] None (E.start x y) (hload P x y).
Proof.
  intros P x y. constructor.
  - split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    intros r Hr. apply hload_high. unfold scratch in Hr. lia.
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
  - intros c. apply hload_high. unfold NC. lia.
  - constructor.
  - intros r [].
  - intros r [].
  - intros c k _ _. split; apply hload_high; unfold SLOT, MP; lia.
  - apply hload_high. unfold DEAD. lia.
Qed.

(* ================================================================= *)
(* From hreach to at least one host step.                             *)
(* ================================================================= *)

Lemma hreach_step : forall h h', hreach h h' -> h' <> h ->
  exists n, hrun_prog (S n) U h = h'.
Proof.
  intros h h' [n Hn] Hne. destruct n as [| n]; [simpl in Hn; congruence |].
  exists n. exact Hn.
Qed.

Lemma host_at_head_not_halted : forall P h, at_head P h -> ~ M.halted U (M.core_of h).
Proof.
  intros P h (Hp & He & _). unfold M.halted, M.next_instr. rewrite He, Hp.
  vm_compute. discriminate.
Qed.

Lemma rel_halt_trap : forall P g h,
  E.err (E.core_of g) = true -> herr h = true ->
  hv h RA = E.ca (E.core_of g) -> hv h RB = E.cb (E.core_of g) ->
  M.mu h = E.mu g -> M.cert h = E.cert g ->
  (exists sg rho,
    E.facts (E.core_of g) = map gfact sg /\ M.facts (M.core_of h) = map hfact sg /\
    E.chan (E.core_of g) = option_map gfact rho /\
    M.chan (M.core_of h) = option_map hfact rho) ->
  rel_halt P g h.
Proof.
  intros P g h Hg Hh Ha Hb Hm Hc Hx. split; [apply ghalted_trap, Hg |].
  split; [apply M.multi_trapped_halted, Hh |].
  split; [exact Ha |]. split; [exact Hb |]. split; [congruence |].
  split; [exact Hm |]. split; [exact Hc | exact Hx].
Qed.

(* ================================================================= *)
(* One guest step.                                                    *)
(* ================================================================= *)

Definition step_result (P : list E.instr) (sg : list srec) (g : E.state) (h : hstate) : Prop :=
  exists n h', hrun_prog (S n) U h = h' /\
    ((exists sg' rho', rel_with P sg' rho' (E.step P g) h' /\
        forall r, In r sg' -> In r sg \/ current (E.step P g) r) \/
     (E.err (E.core_of (E.step P g)) = true /\ rel_halt P (E.step P g) h')).

Section Step.

Variables (P : list E.instr) (sg : list srec) (rho : option srec) (g : E.state) (h : hstate).
Hypothesis R : rel_with P sg rho g h.

Local Notation k := (E.core_of g).

Lemma R_fetch : E.fetch P (hv h GPC) = E.fetch P (E.pc k).
Proof. rewrite (rw_gpc _ _ _ _ _ R). reflexivity. Qed.

Lemma R_ra : hv h RA = E.ca k.
Proof. rewrite <- greg_CA. exact (rw_greg _ _ _ _ _ R E.CA). Qed.

Lemma R_rb : hv h RB = E.cb k.
Proof. rewrite <- greg_CB. exact (rw_greg _ _ _ _ _ R E.CB). Qed.

Lemma R_corr : exists sg0 rho0,
  E.facts k = map gfact sg0 /\ M.facts (M.core_of h) = map hfact sg0 /\
  E.chan k = option_map gfact rho0 /\ M.chan (M.core_of h) = option_map hfact rho0.
Proof.
  exists sg, rho. split; [exact (rw_gfacts _ _ _ _ _ R) |].
  split; [exact (rw_hfacts _ _ _ _ _ R) |].
  split; [exact (rw_gchan _ _ _ _ _ R) | exact (rw_hchan _ _ _ _ _ R)].
Qed.

(* Guest stopped: pc 0, past the end, or HALT. *)
Lemma step_stop :
  E.fetch P (E.pc k) = None \/ E.fetch P (E.pc k) = Some E.HALT ->
  exists h', hreach h h' /\ rel_halt P g h'.
Proof.
  intro Hf. rewrite <- R_fetch in Hf.
  destruct (phase_stop P h (rw_head _ _ _ _ _ R) Hf)
    as [h' [Hr [_ [He [Hh [Hv [_ [SF [SC [SE [SM SR]]]]]]]]]]].
  exists h'. split; [exact Hr |].
  split; [apply ghalted_iff; [exact (rw_err _ _ _ _ _ R) | rewrite <- R_fetch; exact Hf] |].
  split; [exact Hh |].
  split; [rewrite Hv; exact R_ra |]. split; [rewrite Hv; exact R_rb |].
  split; [rewrite He; symmetry; exact (rw_err _ _ _ _ _ R) |].
  split; [rewrite SM; exact (rw_mu _ _ _ _ _ R) |].
  split; [rewrite SR; exact (rw_cert _ _ _ _ _ R) |].
  destruct R_corr as [sg0 [rho0 [H1 [H2 [H3 H4]]]]].
  exists sg0, rho0. rewrite SF, SC. auto.
Qed.

(* INC c. *)
Lemma step_inc : forall c, E.fetch P (E.pc k) = Some (E.INC c) -> step_result P sg g h.
Proof.
  intros c Hf. pose proof (rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g =
    E.mkst (E.write k c (S (E.val k c)) (S (E.pc k))) (E.mu g) (E.cert g)).
  { rewrite (gstep_exec P g (E.INC c) He Hf) by discriminate.
    rewrite gexec_noerr by exact He. unfold E.cexec. rewrite He. simpl.
    rewrite Nat.add_0_r, orb_false_r. reflexivity. }
  rewrite <- R_fetch in Hf.
  destruct (phase_inc P h c (rw_head _ _ _ _ _ R) Hf)
    as [h' [Hr [AH [Hg [Hgpc [Hq [Hoth [Hver [SF [SC [SE [SM SR]]]]]]]]]]]].
  apply hreach_step in Hr.
  2:{ intro E. rewrite E in Hgpc. lia. }
  destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
  exists sg, rho. split; [| intros r Hin; left; exact Hin].
  rewrite Hs. constructor; simpl.
  - exact AH.
  - rewrite E.err_write. exact He.
  - intro d. rewrite gval_write. destruct (ctr_dec c d) as [<- | Hn'].
    + rewrite ctr_eqb_refl, Hg, (rw_greg _ _ _ _ _ R). reflexivity.
    + rewrite (ctr_eqb_neq _ _ Hn'). rewrite Hoth.
      * exact (rw_greg _ _ _ _ _ R d).
      * intro E. apply Hn'. apply greg_inj. congruence.
      * apply greg_ne_gpc.
      * apply greg_not_mp.
  - rewrite gpc_write, Hgpc, (rw_gpc _ _ _ _ _ R). reflexivity.
  - rewrite E.facts_write. exact (rw_gfacts _ _ _ _ _ R).
  - rewrite SF. exact (rw_hfacts _ _ _ _ _ R).
  - rewrite E.chan_write. exact (rw_gchan _ _ _ _ _ R).
  - rewrite SC. exact (rw_hchan _ _ _ _ _ R).
  - exact (rw_rho _ _ _ _ _ R).
  - rewrite SM. exact (rw_mu _ _ _ _ _ R).
  - rewrite SR. exact (rw_cert _ _ _ _ _ R).
  - intro d. rewrite Hoth; [exact (rw_nc _ _ _ _ _ R d) | apply nc_ne_greg | apply nc_ne_gpc
                           | apply nc_not_mp].
  - exact (rw_nodup _ _ _ _ _ R).
  - exact (rw_klt _ _ _ _ _ R).
  - intros r Hin. pose proof (rw_recs _ _ _ _ _ R r Hin) as Hok.
    pose proof (proj1 Hok) as Hk.
    destruct (ctr_dec (r_c r) c) as [Hc | Hc].
    + destruct (Hq (r_k r) Hk) as [Q1 [Q2 Q3]]. rewrite <- Hc in Q1, Q2, Q3.
      apply (rec_ok_bump g h); [exact Q2 | exact Q3 | exact Q1 | | exact Hok].
      simpl. rewrite E.ver_write, Hc, ctr_eqb_refl. reflexivity.
    + apply (rec_ok_frame g h); [| | | | | exact Hok].
      * apply Hoth; [apply slot_ne_greg | apply slot_ne_gpc | apply slot_not_mp].
      * apply Hver; [apply slot_ge | apply slot_not_in; [exact Hk | congruence]].
      * apply Hoth; [apply mp_ne_greg | apply mp_ne_gpc | apply mp_not_in; [exact Hk | congruence]].
      * simpl. rewrite E.ver_write, ctr_eqb_neq by congruence. reflexivity.
      * simpl. rewrite gval_write, ctr_eqb_neq by congruence. reflexivity.
  - intros d q Hq16 Hno. destruct (rw_free _ _ _ _ _ R d q Hq16 Hno) as [F1 F2].
    destruct (ctr_dec d c) as [-> | Hc].
    + destruct (Hq q Hq16) as [Q1 [Q2 _]]. rewrite Q2. auto.
    + rewrite !Hoth; auto using slot_ne_greg, slot_ne_gpc, slot_not_mp, mp_ne_greg, mp_ne_gpc.
      apply mp_not_in; [exact Hq16 | congruence].
  - rewrite Hoth; [exact (rw_dead _ _ _ _ _ R) | apply dead_ne_greg | apply dead_ne_gpc
                  | apply dead_not_mp].
Qed.

(* DEC c j on a positive counter. *)
Lemma step_dec_taken : forall c j u,
  E.fetch P (E.pc k) = Some (E.DEC c j) -> E.val k c = S u -> step_result P sg g h.
Proof.
  intros c j u Hf Hu. pose proof (rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g = E.mkst (E.write k c u j) (E.mu g) (E.cert g)).
  { rewrite (gstep_exec P g (E.DEC c j) He Hf) by discriminate.
    rewrite gexec_noerr by exact He. unfold E.cexec. rewrite He, Hu. simpl.
    rewrite Nat.add_0_r, orb_false_r. reflexivity. }
  rewrite <- R_fetch in Hf.
  assert (Hu' : hv h (greg c) = S u) by (rewrite (rw_greg _ _ _ _ _ R); exact Hu).
  destruct (phase_dec_taken P h c j u (rw_head _ _ _ _ _ R) Hf Hu')
    as [h' [Hr [AH [Hg [Hgpc [Hq [Hoth [Hver [SF [SC [SE [SM SR]]]]]]]]]]]].
  apply hreach_step in Hr.
  2:{ intro E. rewrite E in Hg. lia. }
  destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
  exists sg, rho. split; [| intros r Hin; left; exact Hin].
  rewrite Hs. constructor; simpl.
  - exact AH.
  - rewrite E.err_write. exact He.
  - intro d. rewrite gval_write. destruct (ctr_dec c d) as [<- | Hn'].
    + rewrite ctr_eqb_refl, Hg. reflexivity.
    + rewrite (ctr_eqb_neq _ _ Hn'). rewrite Hoth.
      * exact (rw_greg _ _ _ _ _ R d).
      * intro E. apply Hn'. apply greg_inj. congruence.
      * apply greg_ne_gpc.
      * apply greg_not_mp.
  - rewrite gpc_write, Hgpc. reflexivity.
  - rewrite E.facts_write. exact (rw_gfacts _ _ _ _ _ R).
  - rewrite SF. exact (rw_hfacts _ _ _ _ _ R).
  - rewrite E.chan_write. exact (rw_gchan _ _ _ _ _ R).
  - rewrite SC. exact (rw_hchan _ _ _ _ _ R).
  - exact (rw_rho _ _ _ _ _ R).
  - rewrite SM. exact (rw_mu _ _ _ _ _ R).
  - rewrite SR. exact (rw_cert _ _ _ _ _ R).
  - intro d. rewrite Hoth; [exact (rw_nc _ _ _ _ _ R d) | apply nc_ne_greg | apply nc_ne_gpc
                           | apply nc_not_mp].
  - exact (rw_nodup _ _ _ _ _ R).
  - exact (rw_klt _ _ _ _ _ R).
  - intros r Hin. pose proof (rw_recs _ _ _ _ _ R r Hin) as Hok.
    pose proof (proj1 Hok) as Hk.
    destruct (ctr_dec (r_c r) c) as [Hc | Hc].
    + destruct (Hq (r_k r) Hk) as [Q1 [Q2 Q3]]. rewrite <- Hc in Q1, Q2, Q3.
      apply (rec_ok_bump g h); [exact Q2 | exact Q3 | exact Q1 | | exact Hok].
      simpl. rewrite E.ver_write, Hc, ctr_eqb_refl. reflexivity.
    + apply (rec_ok_frame g h); [| | | | | exact Hok].
      * apply Hoth; [apply slot_ne_greg | apply slot_ne_gpc | apply slot_not_mp].
      * apply Hver; [apply slot_ge | apply slot_not_in; [exact Hk | congruence]].
      * apply Hoth; [apply mp_ne_greg | apply mp_ne_gpc | apply mp_not_in; [exact Hk | congruence]].
      * simpl. rewrite E.ver_write, ctr_eqb_neq by congruence. reflexivity.
      * simpl. rewrite gval_write, ctr_eqb_neq by congruence. reflexivity.
  - intros d q Hq16 Hno. destruct (rw_free _ _ _ _ _ R d q Hq16 Hno) as [F1 F2].
    destruct (ctr_dec d c) as [-> | Hc].
    + destruct (Hq q Hq16) as [Q1 [Q2 _]]. rewrite Q2. auto.
    + rewrite !Hoth; auto using slot_ne_greg, slot_ne_gpc, slot_not_mp, mp_ne_greg, mp_ne_gpc.
      apply mp_not_in; [exact Hq16 | congruence].
  - rewrite Hoth; [exact (rw_dead _ _ _ _ _ R) | apply dead_ne_greg | apply dead_ne_gpc
                  | apply dead_not_mp].
Qed.

(* A move that changes only GPC on the host side, every version from 48
   on kept, and a guest core with the same counters and versions. *)
Lemma rel_keep : forall g' h',
  at_head P h' ->
  E.err (E.core_of g') = false ->
  (forall r, r <> GPC -> hv h' r = hv h r) ->
  (forall r, 48 <= r -> hver h' r = hver h r) ->
  (forall c, E.val (E.core_of g') c = E.val k c /\ E.ver (E.core_of g') c = E.ver k c) ->
  hv h' GPC = E.pc (E.core_of g') ->
  E.facts (E.core_of g') = E.facts k -> M.facts (M.core_of h') = M.facts (M.core_of h) ->
  forall rho', E.chan (E.core_of g') = option_map gfact rho' ->
  M.chan (M.core_of h') = option_map hfact rho' -> (forall r, rho' = Some r -> In r sg) ->
  M.mu h' = E.mu g' -> M.cert h' = E.cert g' ->
  rel_with P sg rho' g' h'.
Proof.
  intros g' h' AH He Hv Hw Hk Hgpc HF1 HF2 rho' HC1 HC2 Hrho HM HR. constructor.
  - exact AH.
  - exact He.
  - intro d. rewrite Hv by apply greg_ne_gpc. rewrite (proj1 (Hk d)).
    exact (rw_greg _ _ _ _ _ R d).
  - exact Hgpc.
  - rewrite HF1. exact (rw_gfacts _ _ _ _ _ R).
  - rewrite HF2. exact (rw_hfacts _ _ _ _ _ R).
  - exact HC1.
  - exact HC2.
  - exact Hrho.
  - exact HM.
  - exact HR.
  - intro d. rewrite Hv by apply nc_ne_gpc. exact (rw_nc _ _ _ _ _ R d).
  - exact (rw_nodup _ _ _ _ _ R).
  - exact (rw_klt _ _ _ _ _ R).
  - intros r Hin. apply (rec_ok_frame g h).
    + apply Hv, slot_ne_gpc.
    + apply Hw, slot_ge.
    + apply Hv, mp_ne_gpc.
    + exact (proj2 (Hk (r_c r))).
    + exact (proj1 (Hk (r_c r))).
    + exact (rw_recs _ _ _ _ _ R r Hin).
  - intros d q Hq Hno. rewrite !Hv by (apply slot_ne_gpc || apply mp_ne_gpc).
    exact (rw_free _ _ _ _ _ R d q Hq Hno).
  - rewrite Hv by exact dead_ne_gpc. exact (rw_dead _ _ _ _ _ R).
Qed.

(* DEC c j on a zero counter. *)
Lemma step_dec_zero : forall c j,
  E.fetch P (E.pc k) = Some (E.DEC c j) -> E.val k c = 0 -> step_result P sg g h.
Proof.
  intros c j Hf Hz. pose proof (rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g = E.mkst (E.goto k (S (E.pc k))) (E.mu g) (E.cert g)).
  { rewrite (gstep_exec P g (E.DEC c j) He Hf) by discriminate.
    rewrite gexec_noerr by exact He. unfold E.cexec. rewrite He, Hz. simpl.
    rewrite Nat.add_0_r, orb_false_r. reflexivity. }
  rewrite <- R_fetch in Hf.
  assert (Hz' : hv h (greg c) = 0) by (rewrite (rw_greg _ _ _ _ _ R); exact Hz).
  destruct (phase_dec_zero P h c j (rw_head _ _ _ _ _ R) Hf Hz')
    as [h' [Hr [AH [Hgpc [Hoth [Hver [SF [SC [SE [SM SR]]]]]]]]]].
  apply hreach_step in Hr.
  2:{ intro E. rewrite E in Hgpc. lia. }
  destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
  exists sg, rho. split; [| intros r Hin; left; exact Hin].
  rewrite Hs. apply rel_keep; simpl.
  - exact AH.
  - exact He.
  - exact Hoth.
  - exact Hver.
  - intro d. apply gkeep_goto.
  - rewrite Hgpc, (rw_gpc _ _ _ _ _ R). reflexivity.
  - reflexivity.
  - exact SF.
  - exact (rw_gchan _ _ _ _ _ R).
  - rewrite SC. exact (rw_hchan _ _ _ _ _ R).
  - exact (rw_rho _ _ _ _ _ R).
  - rewrite SM. exact (rw_mu _ _ _ _ _ R).
  - rewrite SR. exact (rw_cert _ _ _ _ _ R).
Qed.

(* CHECK p c. *)
Lemma step_check : forall p c,
  E.fetch P (E.pc k) = Some (E.CHECK p c) -> step_result P sg g h.
Proof.
  intros p c Hf. pose proof (rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g =
    E.mkst (if E.check_ok k p c then E.record_fact k (E.claim k p c) else E.trap k)
           (E.mu g + 1) (E.cert g)).
  { rewrite (gstep_exec P g (E.CHECK p c) He Hf) by discriminate.
    rewrite gexec_noerr by exact He. unfold E.cexec. rewrite He. simpl.
    rewrite orb_false_r. reflexivity. }
  rewrite <- R_fetch in Hf.
  pose proof (rw_head _ _ _ _ _ R) as AH0.
  set (j := count c sg).
  assert (Hnc : hv h (NC c) = j) by exact (rw_nc _ _ _ _ _ R c).
  assert (Hlen : length (M.facts (M.core_of h)) = length (E.facts k)).
  { rewrite (rw_hfacts _ _ _ _ _ R), (rw_gfacts _ _ _ _ _ R), !map_length. reflexivity. }
  destruct (lt_dec j 16) as [Hj | Hj].
  - (* a fresh slot *)
    assert (Hfree : ~ occupied sg c j) by (apply fresh_slot, (rw_klt _ _ _ _ _ R)).
    destruct (rw_free _ _ _ _ _ R c j Hj Hfree) as [Hsl Hmp].
    destruct (E.check_ok k p c) eqn:Hck.
    + (* the check passes *)
      unfold E.check_ok in Hck. rewrite He in Hck. simpl in Hck.
      apply andb_true_iff in Hck as [Hev Hcap].
      apply E.eval_iff in Hev. apply Nat.ltb_lt in Hcap.
      assert (Hev' : E.holds p (hv h (greg c))) by (rewrite (rw_greg _ _ _ _ _ R); exact Hev).
      assert (Hcap' : length (M.facts (M.core_of h)) < M.fact_cap)
        by (rewrite Hlen; exact Hcap).
      destruct (phase_check_pass P h p c j AH0 Hf Hnc Hj Hsl Hev' Hcap')
        as [h' [Hr [AH [Hgpc [Hnc' [Hmp' [Hsl' [Hvl [HF [HC [HM [HR [Hoth Hver]]]]]]]]]]]]].
      apply hreach_step in Hr.
      2:{ intro E. rewrite E in HM. lia. }
      destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
      set (r0 := mkrec p c j (E.ver k c) (hver h' (SLOT c j)) (E.val k c)).
      exists (r0 :: sg), rho.
      assert (Hkey : forall r, In r sg -> rkey r <> (c, j)).
      { intros r Hin E. apply Hfree. exists r. unfold rkey in E. injection E. auto. }
      split.
      2:{ intros r [<- | Hin]; [right | left; exact Hin].
          unfold current. rewrite Hs. pose proof (gkeep_record k (E.claim k p c) c) as [G1 G2].
          simpl in G1, G2 |- *. rewrite G2. reflexivity. }
      rewrite Hs. constructor; simpl.
      * exact AH.
      * exact He.
      * intro d. rewrite (proj1 (gkeep_record k _ d)).
        rewrite Hoth; [exact (rw_greg _ _ _ _ _ R d) | apply greg_ne_gpc
          | intro E; symmetry in E; exact (nc_ne_greg _ _ E)
          | intro E; symmetry in E; exact (mp_ne_greg _ _ _ E)
          | intro E; symmetry in E; exact (slot_ne_greg _ _ _ E)].
      * rewrite Hgpc, (rw_gpc _ _ _ _ _ R). reflexivity.
      * rewrite (rw_gfacts _ _ _ _ _ R). reflexivity.
      * rewrite HF, (rw_hfacts _ _ _ _ _ R). reflexivity.
      * exact (rw_gchan _ _ _ _ _ R).
      * rewrite HC. exact (rw_hchan _ _ _ _ _ R).
      * intros r Hr. right. exact (rw_rho _ _ _ _ _ R r Hr).
      * rewrite HM, (rw_mu _ _ _ _ _ R). reflexivity.
      * rewrite HR. exact (rw_cert _ _ _ _ _ R).
      * intro d. rewrite count_cons. simpl. destruct (ctr_dec c d) as [<- | Hd].
        -- rewrite ctr_eqb_refl, Hnc'. reflexivity.
        -- rewrite (ctr_eqb_neq _ _ Hd). simpl. rewrite Hoth.
           ++ exact (rw_nc _ _ _ _ _ R d).
           ++ apply nc_ne_gpc.
           ++ intro E. apply Hd. symmetry. apply nc_inj, E.
           ++ apply not_eq_sym, mp_ne_nc.
           ++ apply not_eq_sym, slot_ne_nc.
      * constructor; [| exact (rw_nodup _ _ _ _ _ R)].
        intro Hin. apply in_map_iff in Hin as [r [Hr Hin]]. exact (Hkey r Hin Hr).
      * intros r [<- | Hin].
        -- simpl. rewrite count_cons. simpl. rewrite ctr_eqb_refl. unfold j. lia.
        -- rewrite count_cons. pose proof (rw_klt _ _ _ _ _ R r Hin). lia.
      * intros r [<- | Hin].
        -- unfold rec_ok. pose proof (gkeep_record k (E.claim k p c) c) as [G1 G2].
           simpl in G1, G2 |- *. rewrite G1, G2.
           split; [exact Hj |]. split; [rewrite Hsl', (rw_greg _ _ _ _ _ R); reflexivity |].
           split; [lia |]. split; [lia |]. split; [tauto |].
           split; [intros _; split; [reflexivity | exact Hmp'] | intro E; contradiction].
        -- pose proof (rw_recs _ _ _ _ _ R r Hin) as Hok. pose proof (proj1 Hok) as Hk.
           assert (Hne : rkey r <> (c, j)) by exact (Hkey r Hin).
           assert (Hs1 : SLOT (r_c r) (r_k r) <> SLOT c j).
           { intro E. apply slot_inj in E as [E1 E2]; [| exact Hk | exact Hj].
             apply Hne. unfold rkey. rewrite E1, E2. reflexivity. }
           assert (Hm1 : MP (r_c r) (r_k r) <> MP c j).
           { intro E. apply mp_inj in E as [E1 E2]; [| exact Hk | exact Hj].
             apply Hne. unfold rkey. rewrite E1, E2. reflexivity. }
           apply (rec_ok_frame g h); [| | | | | exact Hok].
           ++ apply Hoth; [apply slot_ne_gpc | apply slot_ne_nc | apply slot_ne_mp; exact Hj
                          | exact Hs1].
           ++ apply Hver; [apply slot_ge | exact Hs1].
           ++ apply Hoth; [apply mp_ne_gpc | apply mp_ne_nc | exact Hm1
                          | apply not_eq_sym, slot_ne_mp; exact Hk].
           ++ simpl. apply gkeep_record.
           ++ simpl. apply gkeep_record.
      * intros d q Hq Hno.
        assert (Hno' : ~ occupied sg d q)
          by (intros [r [Hin Hr]]; apply Hno; exists r; split; [right; exact Hin | exact Hr]).
        assert (Hne : (d, q) <> (c, j))
          by (intro E; injection E as -> ->; apply Hno; exists r0; split; [left |]; auto).
        destruct (rw_free _ _ _ _ _ R d q Hq Hno') as [F1 F2].
        assert (Hs1 : SLOT d q <> SLOT c j).
        { intro E. apply slot_inj in E as [E1 E2]; [| exact Hq | exact Hj].
          apply Hne. rewrite E1, E2. reflexivity. }
        assert (Hm1 : MP d q <> MP c j).
        { intro E. apply mp_inj in E as [E1 E2]; [| exact Hq | exact Hj].
          apply Hne. rewrite E1, E2. reflexivity. }
        rewrite Hoth by first [apply slot_ne_gpc | apply slot_ne_nc | apply slot_ne_mp; exact Hj
                               | exact Hs1].
        rewrite (Hoth (MP d q)) by first [apply mp_ne_gpc | apply mp_ne_nc | exact Hm1
                                          | apply not_eq_sym, slot_ne_mp; exact Hq].
        auto.
      * rewrite Hoth; [exact (rw_dead _ _ _ _ _ R) | exact dead_ne_gpc | apply dead_ne_nc
          | apply not_eq_sym, mp_ne_dead; exact Hj | apply not_eq_sym, slot_ne_dead; exact Hj].
    + (* the check fails: the property is false or the table is full *)
      assert (Hbad : ~ E.holds p (hv h (greg c)) \/ M.fact_cap <= length (M.facts (M.core_of h))).
      { unfold E.check_ok in Hck. rewrite He in Hck. simpl in Hck.
        rewrite (rw_greg _ _ _ _ _ R), Hlen.
        destruct (E.eval p (E.val k c)) eqn:Hev.
        - right. simpl in Hck. apply Nat.ltb_ge in Hck. exact Hck.
        - left. intro H. apply E.eval_iff in H. congruence. }
      destruct (phase_check_fail P h p c j AH0 Hf Hnc Hj Hsl Hbad)
        as [h' [Hr [Herr [_ [HF [HC [HM [HR [_ [_ [Hoth _]]]]]]]]]]].
      apply hreach_step in Hr.
      2:{ intro E. rewrite E in Herr. rewrite (proj1 (proj2 AH0)) in Herr. discriminate. }
      destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. right. rewrite Hs.
      split; [reflexivity |].
      apply rel_halt_trap; simpl.
      * reflexivity.
      * exact Herr.
      * rewrite Hoth; [exact R_ra | exact ra_ne_t2 | apply ra_ne_slot].
      * rewrite Hoth; [exact R_rb | exact rb_ne_t2 | apply rb_ne_slot].
      * rewrite HM, (rw_mu _ _ _ _ _ R). reflexivity.
      * rewrite HR. exact (rw_cert _ _ _ _ _ R).
      * destruct R_corr as [sg0 [rho0 [H1 [H2 [H3 H4]]]]].
        exists sg0, rho0. rewrite HF, HC. auto.
  - (* bank full: CHECK PSlot DEAD *)
    assert (Hck : E.check_ok k p c = false).
    { unfold E.check_ok. apply andb_false_iff. right. apply Nat.ltb_ge.
      rewrite (rw_gfacts _ _ _ _ _ R), map_length.
      pose proof (count_le_length c sg). fold j in H. unfold E.fact_cap. lia. }
    rewrite Hck in Hs.
    assert (H16 : 16 <= hv h (NC c)) by (rewrite Hnc; lia).
    destruct (phase_check_dead P h p c AH0 Hf H16 (rw_dead _ _ _ _ _ R))
      as [h' [Hr [Herr [_ [HF [HC [HM [HR [_ [_ [Hoth _]]]]]]]]]]].
    apply hreach_step in Hr.
    2:{ intro E. rewrite E in Herr. rewrite (proj1 (proj2 AH0)) in Herr. discriminate. }
    destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. right. rewrite Hs.
    split; [reflexivity |].
    apply rel_halt_trap; simpl.
    + reflexivity.
    + exact Herr.
    + rewrite Hoth; [exact R_ra | exact ra_ne_t2 | exact ra_ne_t7].
    + rewrite Hoth; [exact R_rb | exact rb_ne_t2 | exact rb_ne_t7].
    + rewrite HM, (rw_mu _ _ _ _ _ R). reflexivity.
    + rewrite HR. exact (rw_cert _ _ _ _ _ R).
    + destruct R_corr as [sg0 [rho0 [H1 [H2 [H3 H4]]]]].
      exists sg0, rho0. rewrite HF, HC. auto.
Qed.

(* The first index below n where f takes the value x, or none. *)
Lemma first_match : forall (f : nat -> nat) x n,
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
Lemma step_commit : forall p c,
  E.fetch P (E.pc k) = Some (E.COMMIT p c) -> step_result P sg g h.
Proof.
  intros p c Hf. pose proof (rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g =
    E.mkst (if E.commit_ok k p c then E.commit_to k (E.claim k p c) else E.trap k)
           (E.mu g + 1) (E.cert g)).
  { rewrite (gstep_exec P g (E.COMMIT p c) He Hf) by discriminate.
    rewrite gexec_noerr by exact He. unfold E.cexec. rewrite He. simpl.
    rewrite orb_false_r. reflexivity. }
  rewrite <- R_fetch in Hf.
  pose proof (rw_head _ _ _ _ _ R) as AH0.
  destruct (first_match (fun j => hv h (MP c j)) (S (pcode p)) 16)
    as [[j [Hj [Hm Hfirst]]] | Hno].
  - (* the first matching mirror: its record is current and on p *)
    simpl in Hm, Hfirst.
    assert (Hocc : occupied sg c j).
    { destruct (occ_dec sg c j) as [Ho | Ho]; [exact Ho |].
      destruct (rw_free _ _ _ _ _ R c j Hj Ho) as [_ F]. rewrite F in Hm. discriminate. }
    destruct Hocc as [r [Hin [Hc Hk]]].
    destruct (rw_recs _ _ _ _ _ R r Hin) as [_ [_ [_ [_ [Hiff [Hcur Hstale]]]]]].
    rewrite Hc, Hk in Hiff, Hcur, Hstale.
    destruct (Nat.eq_dec (r_gv r) (E.ver k c)) as [Hg | Hg].
    2:{ rewrite (Hstale Hg) in Hm. discriminate. }
    destruct (Hcur Hg) as [_ Hmp]. rewrite Hm in Hmp. injection Hmp as Hp.
    apply pcode_inj in Hp.
    assert (Hhv : r_hv r = hver h (SLOT c j)) by (apply Hiff, Hg).
    assert (Hhf : hfact r = M.mkfact PSlot (SLOT c j) (hver h (SLOT c j)))
      by (unfold hfact; rewrite Hc, Hk, Hhv; reflexivity).
    assert (Hgf : gfact r = E.claim k p c)
      by (unfold gfact, E.claim; rewrite Hc, Hg, Hp; reflexivity).
    assert (Hhin : In (M.mkfact PSlot (SLOT c j) (hver h (SLOT c j))) (M.facts (M.core_of h))).
    { rewrite (rw_hfacts _ _ _ _ _ R), <- Hhf. apply in_map, Hin. }
    destruct (phase_commit_pass P h p c j AH0 Hf Hj Hm Hfirst Hhin)
      as [h' [Hr [AH [Hgpc [HF [HC [HM [HR [Hoth Hver]]]]]]]]].
    assert (Hck : E.commit_ok k p c = true).
    { apply E.commit_ok_iff. split; [exact He |].
      rewrite (rw_gfacts _ _ _ _ _ R), <- Hgf. apply in_map, Hin. }
    rewrite Hck in Hs.
    apply hreach_step in Hr.
    2:{ intro E. rewrite E in HM. lia. }
    destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
    exists sg, (Some r). split; [| intros r' Hin'; left; exact Hin'].
    rewrite Hs. apply rel_keep; simpl.
    + exact AH.
    + exact He.
    + exact Hoth.
    + exact Hver.
    + intro d. apply gkeep_commit.
    + rewrite Hgpc, (rw_gpc _ _ _ _ _ R). reflexivity.
    + reflexivity.
    + exact HF.
    + rewrite Hgf. reflexivity.
    + rewrite HC, Hhf. reflexivity.
    + intros r' E. injection E as <-. exact Hin.
    + rewrite HM, (rw_mu _ _ _ _ _ R). reflexivity.
    + rewrite HR. exact (rw_cert _ _ _ _ _ R).
  - (* no mirror matches: the guest has no live fact on p and c *)
    assert (Hck : E.commit_ok k p c = false).
    { destruct (E.commit_ok k p c) eqn:Hck; [| reflexivity].
      apply E.commit_ok_iff in Hck as [_ Hin].
      rewrite (rw_gfacts _ _ _ _ _ R) in Hin. apply in_map_iff in Hin as [r [Hr Hin]].
      unfold E.claim in Hr. apply gfact_eq in Hr as [Hp [Hc Hg]].
      destruct (rw_recs _ _ _ _ _ R r Hin) as [Hk [_ [_ [_ [_ [Hcur _]]]]]].
      destruct (Hcur (eq_trans Hg (f_equal (E.ver k) (eq_sym Hc)))) as [_ Hmp].
      rewrite Hc, Hp in Hmp. exfalso. exact (Hno (r_k r) Hk Hmp). }
    rewrite Hck in Hs.
    assert (Hnd : ~ In (M.mkfact PSlot DEAD (hver h DEAD)) (M.facts (M.core_of h))).
    { rewrite (rw_hfacts _ _ _ _ _ R). intro Hin. apply in_map_iff in Hin as [r [Hr Hin]].
      unfold hfact in Hr. apply (f_equal M.f_reg) in Hr. cbn [M.f_reg] in Hr.
      destruct (rw_recs _ _ _ _ _ R r Hin) as [Hk _].
      exact (slot_ne_dead _ _ Hk Hr). }
    destruct (phase_commit_none P h p c AH0 Hf Hno Hnd)
      as [h' [Hr [Herr [_ [HF [HC [HM [HR [_ [Hoth _]]]]]]]]]].
    apply hreach_step in Hr.
    2:{ intro E. rewrite E in Herr. rewrite (proj1 (proj2 AH0)) in Herr. discriminate. }
    destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. right. rewrite Hs.
    split; [reflexivity |].
    apply rel_halt_trap; simpl.
    + reflexivity.
    + exact Herr.
    + rewrite Hoth; [exact R_ra | exact ra_ne_t2].
    + rewrite Hoth; [exact R_rb | exact rb_ne_t2].
    + rewrite HM, (rw_mu _ _ _ _ _ R). reflexivity.
    + rewrite HR. exact (rw_cert _ _ _ _ _ R).
    + destruct R_corr as [sg0 [rho0 [H1 [H2 [H3 H4]]]]].
      exists sg0, rho0. rewrite HF, HC. auto.
Qed.

(* CERTIFY. *)
Lemma step_certify : E.fetch P (E.pc k) = Some E.CERTIFY -> step_result P sg g h.
Proof.
  intros Hf. pose proof (rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g =
    E.mkst (if E.certify_ok k then E.goto k (S (E.pc k)) else E.trap k)
           (E.mu g + 1) (E.cert g || E.certify_ok k)).
  { rewrite (gstep_exec P g E.CERTIFY He Hf) by discriminate.
    rewrite gexec_noerr by exact He. unfold E.cexec. rewrite He. reflexivity. }
  rewrite <- R_fetch in Hf.
  pose proof (rw_head _ _ _ _ _ R) as AH0.
  case_eq rho; [intros r Hrho | intros Hrho].
  - (* the channel is full: the flag rises *)
    assert (Hok : E.certify_ok k = true).
    { unfold E.certify_ok. rewrite He, (rw_gchan _ _ _ _ _ R), Hrho. reflexivity. }
    rewrite Hok, orb_true_r in Hs.
    destruct (phase_certify_pass P h (hfact r) AH0 Hf
               (eq_trans (rw_hchan _ _ _ _ _ R) (f_equal (option_map hfact) Hrho)))
      as [h' [Hr [AH [Hgpc [HF [HC [HM [HR [Hoth Hver]]]]]]]]].
    apply hreach_step in Hr.
    2:{ intro E. rewrite E in HM. lia. }
    destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
    exists sg, rho. split; [| intros r' Hin'; left; exact Hin'].
    rewrite Hs. apply rel_keep; simpl.
    + exact AH.
    + exact He.
    + exact Hoth.
    + exact Hver.
    + intro d. apply gkeep_goto.
    + rewrite Hgpc, (rw_gpc _ _ _ _ _ R). reflexivity.
    + reflexivity.
    + exact HF.
    + exact (rw_gchan _ _ _ _ _ R).
    + rewrite HC. exact (rw_hchan _ _ _ _ _ R).
    + exact (rw_rho _ _ _ _ _ R).
    + rewrite HM, (rw_mu _ _ _ _ _ R). reflexivity.
    + exact HR.
  - (* the channel is empty: both trap *)
    assert (Hok : E.certify_ok k = false).
    { unfold E.certify_ok. rewrite He, (rw_gchan _ _ _ _ _ R), Hrho. reflexivity. }
    rewrite Hok, orb_false_r in Hs.
    destruct (phase_certify_fail P h AH0 Hf
               (eq_trans (rw_hchan _ _ _ _ _ R) (f_equal (option_map hfact) Hrho)))
      as [h' [Hr [Herr [_ [HF [HC [HM [HR [Hoth _]]]]]]]]].
    apply hreach_step in Hr.
    2:{ intro E. rewrite E in Herr. rewrite (proj1 (proj2 AH0)) in Herr. discriminate. }
    destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. right. rewrite Hs.
    split; [reflexivity |].
    apply rel_halt_trap; simpl.
    + reflexivity.
    + exact Herr.
    + rewrite Hoth. exact R_ra.
    + rewrite Hoth. exact R_rb.
    + rewrite HM, (rw_mu _ _ _ _ _ R). reflexivity.
    + rewrite HR. exact (rw_cert _ _ _ _ _ R).
    + destruct R_corr as [sg0 [rho0 [H1 [H2 [H3 H4]]]]].
      exists sg0, rho0. rewrite HF, HC. auto.
Qed.

End Step.

(* ================================================================= *)
(* The simulation step.                                               *)
(* ================================================================= *)

Lemma gnot_halted : forall P g i,
  E.err (E.core_of g) = false -> E.fetch P (E.pc (E.core_of g)) = Some i -> i <> E.HALT ->
  ~ E.halted P (E.core_of g).
Proof.
  intros P g i He Hf Hi. unfold E.halted, E.next_instr. rewrite He, Hf.
  destruct i; try discriminate. contradiction.
Qed.

Theorem U_step_with : forall P sg rho g h, rel_with P sg rho g h ->
  (E.halted P (E.core_of g) /\ exists h', hreach h h' /\ rel_halt P g h') \/
  (~ E.halted P (E.core_of g) /\ step_result P sg g h).
Proof.
  intros P sg rho g h R. pose proof (rw_err _ _ _ _ _ R) as He.
  destruct (E.fetch P (E.pc (E.core_of g))) as [i |] eqn:Hf.
  - destruct i as [c | c j | | p c | p c |].
    + right. split; [apply (gnot_halted P g (E.INC c)); auto; discriminate |].
      exact (step_inc P sg rho g h R c Hf).
    + right. split; [apply (gnot_halted P g (E.DEC c j)); auto; discriminate |].
      destruct (E.val (E.core_of g) c) as [| u] eqn:Hv.
      * exact (step_dec_zero P sg rho g h R c j Hf Hv).
      * exact (step_dec_taken P sg rho g h R c j u Hf Hv).
    + left. split; [apply ghalted_iff; auto |].
      apply (step_stop P sg rho g h R). right. exact Hf.
    + right. split; [apply (gnot_halted P g (E.CHECK p c)); auto; discriminate |].
      exact (step_check P sg rho g h R p c Hf).
    + right. split; [apply (gnot_halted P g (E.COMMIT p c)); auto; discriminate |].
      exact (step_commit P sg rho g h R p c Hf).
    + right. split; [apply (gnot_halted P g E.CERTIFY); auto; discriminate |].
      exact (step_certify P sg rho g h R Hf).
  - left. split; [apply ghalted_iff; auto |].
    apply (step_stop P sg rho g h R). left. exact Hf.
Qed.

Theorem U_step : forall P g h, rel P g h ->
  (E.halted P (E.core_of g) /\ exists h', hreach h h' /\ rel_halt P g h') \/
  (~ E.halted P (E.core_of g) /\
   exists n h', hrun_prog (S n) U h = h' /\
     (rel P (E.step P g) h' \/
      (E.err (E.core_of (E.step P g)) = true /\ rel_halt P (E.step P g) h'))).
Proof.
  intros P g h [sg [rho R]].
  destruct (U_step_with P sg rho g h R) as [H | [Hn [n [h' [Hr [[sg' [rho' [R' _]]] | Ht]]]]]].
  - left. exact H.
  - right. split; [exact Hn |]. exists n, h'. split; [exact Hr |]. left. exists sg', rho'.
    exact R'.
  - right. split; [exact Hn |]. exists n, h'. split; [exact Hr |]. right. exact Ht.
Qed.

(* A related host is running, not halted. *)
Lemma rel_host_running : forall P sg rho g h, rel_with P sg rho g h ->
  ~ M.halted U (M.core_of h).
Proof. intros P sg rho g h R. exact (host_at_head_not_halted P h (rw_head _ _ _ _ _ R)). Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions hload_rel.
Print Assumptions step_stop.
Print Assumptions step_inc.
Print Assumptions step_dec_taken.
Print Assumptions step_dec_zero.
Print Assumptions step_check.
Print Assumptions step_commit.
Print Assumptions step_certify.
Print Assumptions U_step_with.
Print Assumptions U_step.
Print Assumptions rel_host_running.
