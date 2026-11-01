(** AxHost: the universal host carries the guest's record, and where a single
    run stops.

    The fixed program U_P (UniversalPRun.v) runs every guest program of the
    priced small machine over the universal property language.  A guest
    program writes out its own chains, CHECK, COMMIT, CERTIFY, for as many
    claims as it likes, up to the cap of 16 facts.  Its record is the fact
    table, the channel, the flag and the trap latch, and its ledger.  The host
    machine keeps the same four things.  Read both through the level 2 record
    of AxRice.v (flag, number of facts, channel committed, trap latch).

    Results (all closed):

      ax_universal_record   at every matching point of every guest run the
                            host's record equals the guest's, and the host's
                            ledger equals the guest's ledger: the surcharge
                            is 0.  At a stopped guest the same holds for the
                            stopped host.
      ax_universal_content  the claim is not lost in the encoding: the host's
                            i-th fact is about a slot register that holds
                            the pair of the code of the guest's i-th
                            property and the value it was checked on, and the
                            two tables list the same slot records in the same
                            order.
      ax_universal_earned   when the host's flag is up, the host's own trace
                            holds the chain CHECK, COMMIT, CERTIFY on one
                            slot, the guest's trace holds its chain on the
                            same property and counter, and the property holds
                            of the value checked.  Chains are preserved.
      ax_surcharge_two_tight  for a presented guest (a computable reading
                            of a record, one flag per compile) the surcharge
                            bound 2 of AxUniversal.v is attained at every
                            threshold of the chain of natural numbers.
      ax_surcharge_three_floor  and at a start already at the threshold it
                            is 3.

    The boundary, in one place.  A guest whose record is written out in
    chains is carried exactly, ledger included, up to 16 claims per run
    (AxHostClaims.v: ax_single_run_boundary, ax_chain_realized).  A guest
    given as a computable reading is compiled with one chain, at the first
    time its reading is yes, so one run of the host carries one threshold of
    its record; the full record is the family of runs, one per threshold, and
    a record that is a chain of three values cannot ride one flag
    (chain_needs_bits).  A fixed program can name only finitely many claims
    (ax_fixed_program_few), so what a fixed universal program carries beyond
    its finite table it carries in the registers the facts point to: that is
    the content statement above. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import AxCore AxUniversal.
Require Import Kernel.UniversalPCodes Kernel.UniversalPBridge Kernel.UniversalPBlocks
  Kernel.UniversalPLayout Kernel.UniversalPPhases Kernel.UniversalPSim Kernel.UniversalPRun.
Require Import Minimal.Presented.

Local Notation hstate := (@M.pu_state pu_hprop).

(** * 1. The two level 2 records *)

Definition ax_chan_flag {A : Type} (o : option A) : bool :=
  match o with Some _ => true | None => false end.

Definition ax_grec (g : E.state) : bool * (nat * (bool * bool)) :=
  (E.cert g, (length (E.facts (E.core_of g)),
              (ax_chan_flag (E.chan (E.core_of g)), E.err (E.core_of g)))).

Definition ax_hrec (h : hstate) : bool * (nat * (bool * bool)) :=
  (M.cert h, (length (M.facts (M.core_of h)),
              (ax_chan_flag (M.chan (M.core_of h)), M.err (M.core_of h)))).

(** When the facts and channels correspond through slot records, the records
    agree. *)
Lemma ax_rec_of_tables : forall (g : E.state) (h : hstate) sg rho,
  E.facts (E.core_of g) = map pu_gfact sg ->
  M.facts (M.core_of h) = map pu_hfact sg ->
  E.chan (E.core_of g) = option_map pu_gfact rho ->
  M.chan (M.core_of h) = option_map pu_hfact rho ->
  M.cert h = E.cert g -> M.err (M.core_of h) = E.err (E.core_of g) ->
  ax_hrec h = ax_grec g.
Proof.
  intros g h sg rho Hgf Hhf Hgc Hhc Hc He.
  unfold ax_hrec, ax_grec. rewrite Hgf, Hhf, Hgc, Hhc, Hc, He.
  rewrite !map_length. destruct rho; reflexivity.
Qed.

(** * 2. The universal host carries the record exactly *)

Theorem ax_universal_record : forall P x y m, exists n,
  (pu_rel P (pu_grun P x y m) (pu_hrun P x y n) /\ m <= n \/
   pu_rel_halt P (pu_grun P x y m) (pu_hrun P x y n)) /\
  ax_hrec (pu_hrun P x y n) = ax_grec (pu_grun P x y m) /\
  M.mu (pu_hrun P x y n) = E.mu (pu_grun P x y m).
Proof.
  intros P x y m. destruct (pu_U_simulation P x y m) as [n [[R Hle] | RH]].
  - exists n. split; [left; split; assumption |].
    destruct R as [sg [rho R]].
    split.
    + apply (ax_rec_of_tables _ _ sg rho);
        [exact (pu_rw_gfacts _ _ _ _ _ R) | exact (pu_rw_hfacts _ _ _ _ _ R)
        | exact (pu_rw_gchan _ _ _ _ _ R) | exact (pu_rw_hchan _ _ _ _ _ R)
        | exact (pu_rw_cert _ _ _ _ _ R) |].
      rewrite (pu_rw_err _ _ _ _ _ R).
      destruct (pu_rw_head _ _ _ _ _ R) as (_ & Herr & _). exact Herr.
    + exact (pu_rw_mu _ _ _ _ _ R).
  - exists n. split; [right; exact RH |].
    destruct RH as (_ & _ & _ & _ & Herr & Hmu & Hc & sg & rho & Hgf & Hhf & Hgc & Hhc).
    split; [| exact Hmu].
    apply (ax_rec_of_tables _ _ sg rho); assumption.
Qed.

(** The content of each claim is carried: the i-th host fact names a slot
    register holding the pair of the code of the i-th guest property and the
    value it was checked on. *)
Theorem ax_universal_content : forall P x y m n sg rho,
  pu_rel_with P sg rho (pu_grun P x y m) (pu_hrun P x y n) ->
  E.facts (E.core_of (pu_grun P x y m)) = map pu_gfact sg /\
  M.facts (M.core_of (pu_hrun P x y n)) = map pu_hfact sg /\
  forall r, In r sg ->
    hv (pu_hrun P x y n) (pu_SLOT (pu_r_c r) (pu_r_k r))
      = pu_pair (pu_pcode (pu_r_p r)) (pu_r_v r).
Proof.
  intros P x y m n sg rho R. split; [exact (pu_rw_gfacts _ _ _ _ _ R) |].
  split; [exact (pu_rw_hfacts _ _ _ _ _ R) |].
  intros r Hr. destruct (pu_rw_recs _ _ _ _ _ R r Hr) as (_ & Hv & _). exact Hv.
Qed.

(** Chains are preserved: the statement of UniversalPRun.v, under the axis
    name.  When the host's flag is up, its own trace holds a passing CHECK, a
    passing COMMIT and the CERTIFY on one slot with the slot unchanged between,
    the slot holds the pair of the code of a property p and a value v with p
    true of v, and the guest's own trace holds its chain CHECK p c, COMMIT p c,
    CERTIFY on the same property and counter. *)
Definition ax_universal_earned := pu_universal_earned.

(** * 3. A presented guest: one threshold per run, the surcharge bound is tight *)

(** The chain of natural numbers as an axis machine: the state is the record,
    one move, cost 1, each move raises the record by 1. *)
Definition ax_chain_sys : AxSys nat nat_pre :=
  mk_axsys nat nat_pre nat unit (fun s _ => S s) (fun _ => 1) (fun s => s).

Lemma ax_chain_a2 : ax_a2 (X := ax_chain_sys).
Proof. intros s i _. simpl. lia. Qed.

Lemma ax_chain_grows : ax_grows (X := ax_chain_sys).
Proof. intros s i. simpl. apply nat_pre_le. lia. Qed.

Definition ax_chain_presented : ax_presented ax_chain_sys :=
  mk_axp ax_chain_sys (fun _ => Some tt) (fun s => s) (fun n => Some n)
    (fun _ => 0) (fun _ => Some tt) (fun s => eq_refl) (fun i => match i with tt => eq_refl end).

Local Notation chainview a := (ax_view_presented ax_chain_sys ax_chain_a2 ax_chain_presented a).

Lemma ax_prun_chain : forall n s, ax_prun ax_chain_sys ax_chain_presented s n = s + n.
Proof.
  induction n as [| n IH]; intro s; [simpl; lia |].
  simpl. rewrite IH. lia.
Qed.

Lemma ax_chain_first_raise : forall a d s n,
  s + S d = a -> S d <= n ->
  first_raise (chainview a) s n = Some tt.
Proof.
  intros a d. induction d as [| d IH]; intros s n Hs Hn.
  - destruct n as [| n]; [lia |].
    unfold first_raise. simpl. fold (first_raise (chainview a)).
    replace (Nat.leb a s) with false by (symmetry; apply Nat.leb_gt; lia).
    replace (Nat.leb a (S s)) with true by (symmetry; apply Nat.leb_le; lia).
    reflexivity.
  - destruct n as [| n]; [lia |].
    unfold first_raise. simpl. fold (first_raise (chainview a)).
    replace (Nat.leb a s) with false by (symmetry; apply Nat.leb_gt; lia).
    replace (Nat.leb a (S s)) with false by (symmetry; apply Nat.leb_gt; lia).
    apply IH; lia.
Qed.

(** The bound of ax_view_surcharge_le_two is attained at every threshold
    1, 2, 3, ... of the chain: the surcharge is exactly 2. *)
Theorem ax_surcharge_two_tight : forall a n,
  1 <= a -> a <= n -> surcharge (chainview a) 0 n = 2.
Proof.
  intros a n Ha Han.
  assert (Hl : mlatch (chainview a) 0 n = true).
  { apply (ax_view_latch_iff ax_chain_sys ax_chain_a2 ax_chain_presented ax_chain_grows).
    simpl. rewrite ax_prun_chain. apply nat_pre_le. lia. }
  unfold surcharge. rewrite Hl. unfold raise_cost.
  destruct a as [| a']; [lia |].
  rewrite (ax_chain_first_raise (S a') a' 0 n); [reflexivity | lia | lia].
Qed.

(** At a start that already meets the threshold the surcharge is 3: the
    bound 2 needs the start below the threshold. *)
Theorem ax_surcharge_three_floor : forall n, surcharge (chainview 0) 0 n = 3.
Proof. intro n. destruct n; reflexivity. Qed.

Print Assumptions ax_universal_record.
Print Assumptions ax_universal_content.
Print Assumptions ax_universal_earned.
Print Assumptions ax_surcharge_two_tight.
Print Assumptions ax_surcharge_three_floor.
