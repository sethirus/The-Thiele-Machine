(** UniversalBlocks.v: the building blocks of the universal interpreter, as
    host programs of EarnedMulti.v with host-level specifications.

    The host is EarnedMulti.v with the property language PSlot of
    UniversalCodes.v. Every block is a function of the address o where it
    is placed (and of its registers and jump targets). A block is placed
    inside a host program Ph by the library's subcode relation,
    subcode (o, block) (1, Ph): the host program starts at address 1 and
    the block occupies addresses o, o + 1, and so on.

    Every specification has the same shape. From a host state s with pc at
    the block's first address and the trap latch down, there is a state s'
    reached by running Ph (hrun: some number of steps, each executed
    instruction an INC or a DEC, so the fact table, channel, trap latch,
    ledger and flag do not change), with a stated pc, stated values of the
    block's registers, and every other register keeping its value and its
    version (hframe).

      Library blocks (MMA_pairing.v), transferred by mma_block_host:
        hJMP a p       go to p
        hJZ x p        go to p when x = 0, else fall through
        hZERO x        x := 0
        hMOVE x y      y := y + x, x := 0
        hMOVE2 x y z   y := y + x, z := z + x, x := 0
        hPACK a x y    x := pair y x, y := 0, a := 0
        hHALF a x p    halve x, go to p when x was even
        hUNPACK a x y  when x = pair m n: x := n, y := m, a := 0
      Single instructions: hINC r, hDEC r j.
      New blocks:
        hCOPY x y t    y := x, t := 0, x keeps its value
        hDISP x t ps   jump to the (x)-th address of ps, or fall through
                       with x reduced by the length of ps
        hEQC x c t u p go to p when x = c, else fall through
        hEQR x y t1 t2 u p   go to p when x = y, else fall through
        hFETCH         copy the program code and guest pc, strip
                       instruction codes, and read the code of the
                       current instruction (UniversalCodes.fetch_code),
                       with separate exits for guest pc 0 and for a pc
                       past the end of the program
        hBUMP sl mp    the slot sl keeps its value and its version goes
                       up by exactly 2; its mirror mp becomes 0
      One-instruction lemmas for CHECK PSlot r, COMMIT PSlot r and CERTIFY:
      what each does to the fact table, the channel, the ledger, the flag
      and the trap latch, given the slot's contents.

    Dependencies: the Coq standard library, the vendored coq-undecidability
    library, EarnedCore.v, EarnedGeneric.v, EarnedMulti.v,
    UniversalCodes.v and UniversalBridge.v. No axioms, no Admitted.         *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the universal interpreter of UniversalRun.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and the standard-library files under minimal/. Its link to the
   abstract record (the host as a CertificationSystem, the undecidability
   of U's halting problem, and the agreement with complete_cs) lives in
   UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import Vec.pos Vec.vec Code.subcode Code.sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.Util Require Import MMA_pairing.
Require Import Minimal.UniversalCodes Kernel.UniversalBridge.

(* The host machine at the PSlot property language. *)
Local Notation hinstr := (@M.instr hprop).
Local Notation hstate := (@M.state hprop).
Local Notation hrun_prog := (M.run_prog hprop_eqb heval).
Local Notation hexec := (M.exec hprop_eqb heval).
Local Notation htrace := (M.trace_of hprop_eqb heval).
Local Notation Hrun := (hrun hprop_eqb heval).

(* ================================================================= *)
(* Placement helpers.                                                 *)
(* ================================================================= *)

Lemma sc_app_l : forall (o : nat) (l1 l2 Ph : list hinstr),
  subcode (o, l1 ++ l2) (1, Ph) -> subcode (o, l1) (1, Ph).
Proof.
  intros o l1 l2 Ph H. eapply subcode_trans; [| exact H]. apply subcode_left. reflexivity.
Qed.

Lemma sc_app_r : forall (o n : nat) (l1 l2 Ph : list hinstr),
  n = length l1 + o -> subcode (o, l1 ++ l2) (1, Ph) -> subcode (n, l2) (1, Ph).
Proof.
  intros o n l1 l2 Ph En H. eapply subcode_trans; [| exact H].
  apply subcode_right. lia.
Qed.

Lemma sc_cons_l : forall (o : nat) (i : hinstr) l Ph,
  subcode (o, i :: l) (1, Ph) -> subcode (o, [i]) (1, Ph).
Proof. intros o i l Ph H. apply (sc_app_l o [i] l Ph H). Qed.

Lemma sc_cons_r : forall (o : nat) (i : hinstr) l Ph,
  subcode (o, i :: l) (1, Ph) -> subcode (S o, l) (1, Ph).
Proof. intros o i l Ph H. apply (sc_app_r o (S o) [i] l Ph); [reflexivity | exact H]. Qed.

Lemma sc_pos : forall (n m : nat) (l Ph : list hinstr),
  n = m -> subcode (n, l) (1, Ph) -> subcode (m, l) (1, Ph).
Proof. intros n m l Ph -> H. exact H. Qed.

(* One plain instruction at the current pc is one hrun step. *)
Lemma hstep1 : forall Ph s o i,
  subcode (o, [i]) (1, Ph) -> hpc s = o -> herr s = false -> M.plain i = true ->
  Hrun Ph s (hexec s i).
Proof.
  intros Ph s o i Hsc Hpc He Hp.
  assert (Hh : i <> M.HALT) by (intro; subst; discriminate).
  exists 1. split.
  - apply (host_step_at hprop_eqb heval Ph s o i Hsc Hpc He Hh).
  - rewrite (host_trace_at hprop_eqb heval Ph s o i Hsc Hpc He Hh). repeat constructor. exact Hp.
Qed.

Lemma hexec_plain_sub : forall s i, M.plain i = true -> same_sub s (hexec s i).
Proof.
  intros s i Hp. destruct (M.multi_plain_step hprop_eqb heval s i Hp) as [A [B [C [D F]]]].
  repeat split; assumption.
Qed.

(* Distinct positions. *)
Lemma p01_2 : (pos0 : pos 2) <> pos1. Proof. discriminate. Qed.
Lemma p01 : (pos0 : pos 3) <> pos1. Proof. discriminate. Qed.
Lemma p02 : (pos0 : pos 3) <> pos2. Proof. discriminate. Qed.
Lemma p12 : (pos1 : pos 3) <> pos2.
Proof. intro H. apply pos_nxt_inj in H. discriminate. Qed.

Lemma nd1 : forall a : nat, NoDup (vec_list (a ## vec_nil)).
Proof. intro a. simpl. repeat constructor. simpl. tauto. Qed.

Lemma nd2 : forall a b : nat, a <> b -> NoDup (vec_list (a ## b ## vec_nil)).
Proof.
  intros a b H. simpl. constructor; [simpl; intuition | ].
  constructor; [simpl; tauto | constructor].
Qed.

Lemma nd3 : forall a b c : nat, a <> b -> a <> c -> b <> c ->
  NoDup (vec_list (a ## b ## c ## vec_nil)).
Proof.
  intros a b c H1 H2 H3. simpl. constructor; [simpl; intuition |].
  constructor; [simpl; intuition |]. constructor; [simpl; tauto | constructor].
Qed.

(* ================================================================= *)
(* Single INC and DEC.                                                *)
(* ================================================================= *)

Definition hINC (r : nat) (o : nat) : list hinstr := [M.INC r].
Definition hDEC (r j : nat) (o : nat) : list hinstr := [M.DEC r j].

Lemma hINC_spec : forall r o Ph s,
  subcode (o, hINC r o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = S o /\
    hv s' r = S (hv s r) /\ hver s' r = S (hver s r) /\ hframe [r] s s'.
Proof.
  intros r o Ph s Hsc Hpc He.
  exists (hexec s (M.INC r)). split; [apply (hstep1 Ph s o); auto |].
  assert (Hk : M.core_of (hexec s (M.INC r))
               = M.write (M.core_of s) r (S (hv s r)) (S (hpc s)))
    by (simpl; unfold M.cexec; rewrite He; reflexivity).
  rewrite Hk, M.multi_pc_write, (M.multi_val_write (M.core_of s)),
    (M.multi_ver_write (M.core_of s)), Nat.eqb_refl, Hpc.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  intros d Hd. rewrite Hk, (M.multi_val_write (M.core_of s)), (M.multi_ver_write (M.core_of s)).
  destruct (Nat.eqb_spec r d) as [-> | _]; [exfalso; apply Hd; left; reflexivity | auto].
Qed.

Lemma hDEC_spec : forall r j o Ph s,
  subcode (o, hDEC r j o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hframe [r] s s' /\
    match hv s r with
    | 0 => hpc s' = S o /\ hv s' r = 0 /\ hver s' r = hver s r
    | S u => hpc s' = j /\ hv s' r = u /\ hver s' r = S (hver s r)
    end.
Proof.
  intros r j o Ph s Hsc Hpc He.
  exists (hexec s (M.DEC r j)). split; [apply (hstep1 Ph s o); auto |].
  destruct (hv s r) as [| u] eqn:Hr.
  - assert (Hk : M.core_of (hexec s (M.DEC r j)) = M.goto (M.core_of s) (S (hpc s)))
      by (simpl; unfold M.cexec; rewrite He, Hr; reflexivity).
    split; [intros d _; rewrite Hk; auto |]. rewrite Hk. simpl. rewrite Hpc, Hr. auto.
  - assert (Hk : M.core_of (hexec s (M.DEC r j)) = M.write (M.core_of s) r u j)
      by (simpl; unfold M.cexec; rewrite He, Hr; reflexivity).
    rewrite Hk, M.multi_pc_write, (M.multi_val_write (M.core_of s)),
      (M.multi_ver_write (M.core_of s)), Nat.eqb_refl.
    split; [| auto].
    intros d Hd. rewrite Hk, (M.multi_val_write (M.core_of s)), (M.multi_ver_write (M.core_of s)).
    destruct (Nat.eqb_spec r d) as [-> | _]; [exfalso; apply Hd; left; reflexivity | auto].
Qed.

(* ================================================================= *)
(* Library blocks, transferred to the host.                           *)
(* ================================================================= *)

Definition hJMP (a p o : nat) : list hinstr :=
  map (lift (vec_pos (a ## vec_nil))) (JMP pos0 p o).
Definition hJZ (x p o : nat) : list hinstr :=
  map (lift (vec_pos (x ## vec_nil))) (JZ pos0 p o).
Definition hZERO (x o : nat) : list hinstr :=
  map (lift (vec_pos (x ## vec_nil))) (MMA_pairing.ZERO pos0 o).
Definition hMOVE (x y o : nat) : list hinstr :=
  map (lift (vec_pos (x ## y ## vec_nil))) (MOVE pos0 pos1 o).
Definition hMOVE2 (x y z o : nat) : list hinstr :=
  map (lift (vec_pos (x ## y ## z ## vec_nil))) (MOVE2 pos0 pos1 pos2 o).
Definition hPACK (a x y o : nat) : list hinstr :=
  map (lift (vec_pos (a ## x ## y ## vec_nil))) (PACK pos0 pos1 pos2 o).
Definition hHALF (a x p o : nat) : list hinstr :=
  map (lift (vec_pos (a ## x ## vec_nil))) (HALF pos0 pos1 p o).
Definition hUNPACK (a x y o : nat) : list hinstr :=
  map (lift (vec_pos (a ## x ## y ## vec_nil))) (UNPACK pos0 pos1 pos2 o).

Lemma hJMP_length : forall a p o, length (hJMP a p o) = JMP_len.
Proof. reflexivity. Qed.
Lemma hJZ_length : forall x p o, length (hJZ x p o) = JZ_len.
Proof. reflexivity. Qed.
Lemma hZERO_length : forall x o, length (hZERO x o) = ZERO_len.
Proof. reflexivity. Qed.
Lemma hMOVE_length : forall x y o, length (hMOVE x y o) = MOVE_len.
Proof. reflexivity. Qed.
Lemma hMOVE2_length : forall x y z o, length (hMOVE2 x y z o) = MOVE2_len.
Proof. reflexivity. Qed.
Lemma hPACK_length : forall a x y o, length (hPACK a x y o) = PACK_len.
Proof. reflexivity. Qed.
Lemma hHALF_length : forall a x p o, length (hHALF a x p o) = HALF_len.
Proof. reflexivity. Qed.
Lemma hUNPACK_length : forall a x y o, length (hUNPACK a x y o) = UNPACK_len.
Proof. reflexivity. Qed.

Lemma hJMP_spec : forall a p o Ph s,
  subcode (o, hJMP a p o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = p /\ hv s' a = hv s a /\ hframe [a] s s'.
Proof.
  intros a p o Ph s Hsc Hpc He.
  destruct (mma_block_host hprop_eqb heval 1 (a ## vec_nil) (nd1 a) o (JMP pos0 p o) Ph s _ _
              Hsc Hpc He (JMP_spec pos0 p _ o)) as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |]. split; [| exact Hf].
  apply (Hv pos0).
Qed.

Lemma hJZ_spec : forall x p o Ph s,
  subcode (o, hJZ x p o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\
    hpc s' = (match hv s x with 0 => p | S _ => JZ_len + o end) /\
    hv s' x = hv s x /\ hframe [x] s s'.
Proof.
  intros x p o Ph s Hsc Hpc He.
  destruct (mma_block_host hprop_eqb heval 1 (x ## vec_nil) (nd1 x) o (JZ pos0 p o) Ph s _ _
              Hsc Hpc He (JZ_spec pos0 p _ o)) as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |]. split; [| exact Hf].
  apply (Hv pos0).
Qed.

Lemma hZERO_spec : forall x o Ph s,
  subcode (o, hZERO x o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = S o /\ hv s' x = 0 /\ hframe [x] s s'.
Proof.
  intros x o Ph s Hsc Hpc He.
  destruct (mma_block_host hprop_eqb heval 1 (x ## vec_nil) (nd1 x) o (MMA_pairing.ZERO pos0 o)
              Ph s _ _ Hsc Hpc He (ZERO_spec pos0 _ o)) as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |]. split; [| exact Hf].
  apply (Hv pos0).
Qed.

Lemma hMOVE_spec : forall x y o Ph s, x <> y ->
  subcode (o, hMOVE x y o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = MOVE_len + o /\
    hv s' y = hv s y + hv s x /\ hv s' x = 0 /\ hframe [x; y] s s'.
Proof.
  intros x y o Ph s Hxy Hsc Hpc He.
  destruct (mma_block_host hprop_eqb heval 2 (x ## y ## vec_nil) (nd2 x y Hxy) o
              (MOVE pos0 pos1 o) Ph s _ _ Hsc Hpc He (MOVE_spec pos0 pos1 _ o p01_2))
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos1) | split; [apply (Hv pos0) | exact Hf]].
Qed.

Lemma hMOVE2_spec : forall x y z o Ph s, x <> y -> x <> z -> y <> z ->
  subcode (o, hMOVE2 x y z o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = MOVE2_len + o /\
    hv s' y = hv s y + hv s x /\ hv s' z = hv s z + hv s x /\ hv s' x = 0 /\
    hframe [x; y; z] s s'.
Proof.
  intros x y z o Ph s H1 H2 H3 Hsc Hpc He.
  destruct (mma_block_host hprop_eqb heval 3 (x ## y ## z ## vec_nil) (nd3 x y z H1 H2 H3) o
              (MOVE2 pos0 pos1 pos2 o) Ph s _ _ Hsc Hpc He
              (MOVE2_spec pos0 pos1 pos2 _ o p01 p02))
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos1) |]. split; [apply (Hv pos2) |].
  split; [apply (Hv pos0) | exact Hf].
Qed.

Lemma hPACK_spec : forall a x y o Ph s, a <> x -> a <> y -> x <> y ->
  subcode (o, hPACK a x y o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = PACK_len + o /\
    hv s' x = pair (hv s y) (hv s x) /\ hv s' y = 0 /\ hv s' a = 0 /\
    hframe [a; x; y] s s'.
Proof.
  intros a x y o Ph s H1 H2 H3 Hsc Hpc He.
  destruct (mma_block_host hprop_eqb heval 3 (a ## x ## y ## vec_nil) (nd3 a x y H1 H2 H3) o
              (PACK pos0 pos1 pos2 o) Ph s _ _ Hsc Hpc He
              (PACK_spec pos0 pos1 pos2 _ o p01 p02 p12))
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos1) |]. split; [apply (Hv pos2) |].
  split; [apply (Hv pos0) | exact Hf].
Qed.

Lemma hHALF_spec : forall a x p o Ph s, a <> x ->
  subcode (o, hHALF a x p o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\
    hpc s' = (if snd (half (hv s x)) then p else HALF_len + o) /\
    hv s' x = fst (half (hv s x)) /\ hv s' a = 0 /\ hframe [a; x] s s'.
Proof.
  intros a x p o Ph s H1 Hsc Hpc He.
  pose proof (HALF_spec pos0 pos1 p (hvec (vec_pos (a ## x ## vec_nil)) (M.core_of s)) o p01_2)
    as Hm.
  simpl in Hm. destruct (half (M.vals (M.core_of s) x)) as [m b] eqn:Eh.
  destruct (mma_block_host hprop_eqb heval 2 (a ## x ## vec_nil) (nd2 a x H1) o
              (HALF pos0 pos1 p o) Ph s _ _ Hsc Hpc He Hm)
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos1) |]. split; [apply (Hv pos0) | exact Hf].
Qed.

Lemma hUNPACK_spec : forall a x y m n o Ph s, a <> x -> a <> y -> x <> y ->
  hv s x = pair m n ->
  subcode (o, hUNPACK a x y o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = UNPACK_len + o /\
    hv s' x = n /\ hv s' y = m /\ hv s' a = 0 /\ hframe [a; x; y] s s'.
Proof.
  intros a x y m n o Ph s H1 H2 H3 Hx Hsc Hpc He.
  assert (Hx' : vec_pos (hvec (vec_pos (a ## x ## y ## vec_nil)) (M.core_of s)) pos1
                = (n + n + 1) * 2 ^ m) by (simpl; rewrite Hx; reflexivity).
  destruct (mma_block_host hprop_eqb heval 3 (a ## x ## y ## vec_nil) (nd3 a x y H1 H2 H3) o
              (UNPACK pos0 pos1 pos2 o) Ph s _ _ Hsc Hpc He
              (@UNPACK_spec 3 pos0 pos1 pos2 m n _ o Hx' p01 p02 p12))
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos1) |]. split; [apply (Hv pos2) |].
  split; [apply (Hv pos0) | exact Hf].
Qed.

(* UNPACK on 0 jumps to address 0, where no host instruction lives; the
   fetch loop guards every UNPACK with a JZ so this case never runs. *)
Lemma hUNPACK0_spec : forall a x y o Ph s, a <> x -> a <> y -> x <> y ->
  hv s x = 0 ->
  subcode (o, hUNPACK a x y o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = 0 /\
    hv s' a = hv s a /\ hv s' x = 0 /\ hv s' y = hv s y /\ hframe [a; x; y] s s'.
Proof.
  intros a x y o Ph s H1 H2 H3 Hx Hsc Hpc He.
  assert (Hx' : vec_pos (hvec (vec_pos (a ## x ## y ## vec_nil)) (M.core_of s)) pos1 = 0)
    by (simpl; exact Hx).
  destruct (mma_block_host hprop_eqb heval 3 (a ## x ## y ## vec_nil) (nd3 a x y H1 H2 H3) o
              (UNPACK pos0 pos1 pos2 o) Ph s _ _ Hsc Hpc He
              (@UNPACK0_spec 3 pos0 pos1 pos2 _ o Hx'))
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos0) |]. split; [etransitivity; [apply (Hv pos1) | exact Hx'] |].
  split; [apply (Hv pos2) | exact Hf].
Qed.

(* ================================================================= *)
(* Tactics for chaining block specifications.                         *)
(* ================================================================= *)

Lemma hrun_err : forall Ph (s s' : hstate), Hrun Ph s s' -> herr s = false -> herr s' = false.
Proof.
  intros Ph s s' H He. destruct (hrun_same_sub _ _ _ _ _ H) as [_ [_ [E _]]]. congruence.
Qed.

(* Split a placement of l1 ++ l2 into placements of l1 and of l2. *)
Ltac sc_split H H1 H2 :=
  match type of H with
  | subcode (?o, ?l1 ++ ?l2) (1, ?Ph) =>
      pose proof (sc_app_l o l1 l2 Ph H) as H1;
      pose proof (sc_app_r o (length l1 + o) l1 l2 Ph eq_refl H) as H2
  end.

(* The trap latch stays down along a chain of hrun hypotheses. *)
Ltac herr_tac :=
  first [ assumption
        | eapply hrun_err; [eassumption | herr_tac] ].

(* An hrun from the first state to the last along hrun hypotheses. *)
Ltac chain :=
  first [ apply hrun_refl
        | eassumption
        | eapply hrun_trans; [eassumption | chain] ].

(* For register r, record the value and version equation of every frame
   hypothesis whose list does not contain r. *)
Ltac frames r :=
  repeat match goal with
  | F : hframe ?rs ?a ?b |- _ =>
      lazymatch goal with
      | _ : hv b r = hv a r |- _ => fail
      | _ =>
          let H1 := fresh "Fv" in
          let H2 := fresh "Fw" in
          assert (H1 : hv b r = hv a r) by (apply (fun N => proj1 (F r N)); simpl; intuition congruence);
          assert (H2 : hver b r = hver a r) by (apply (fun N => proj2 (F r N)); simpl; intuition congruence)
      end
  end.

(* Prove a frame goal from the frame hypotheses of a chain. *)
Ltac solve_frame :=
  let r := fresh "r" in
  let Hr := fresh "Hr" in
  intros r Hr; simpl in Hr; frames r; split; congruence.

Ltac nodup_neqs H :=
  repeat (let Hn := fresh "Hn" in
          let H' := fresh "Hd" in
          destruct (proj1 (NoDup_cons_iff _ _) H) as [Hn H']; clear H; rename H' into H;
          simpl in Hn).

(* ================================================================= *)
(* COPY: y := x and t := 0, x keeps its value.                        *)
(* ================================================================= *)

Definition COPY_len : nat := 2 + MOVE2_len + MOVE_len.

Definition hCOPY (x y t o : nat) : list hinstr :=
  hZERO y o ++ hZERO t (1 + o) ++ hMOVE2 x y t (2 + o) ++ hMOVE t x (2 + MOVE2_len + o).

Lemma hCOPY_length : forall x y t o, length (hCOPY x y t o) = COPY_len.
Proof. reflexivity. Qed.

Theorem hCOPY_spec : forall x y t o Ph s, x <> y -> x <> t -> y <> t ->
  subcode (o, hCOPY x y t o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = COPY_len + o /\
    hv s' x = hv s x /\ hv s' y = hv s x /\ hv s' t = 0 /\ hframe [x; y; t] s s'.
Proof.
  intros x y t o Ph s Hxy Hxt Hyt Hsc Hpc He. unfold hCOPY in Hsc.
  sc_split Hsc S0 Hsc1.
  destruct (hZERO_spec y o Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & F1).
  sc_split Hsc1 S1 Hsc2.
  destruct (hZERO_spec t (1 + o) Ph s1 S1 P1 ltac:(herr_tac)) as (s2 & R2 & P2 & V2 & F2).
  sc_split Hsc2 S2 S3.
  destruct (hMOVE2_spec x y t (2 + o) Ph s2 Hxy Hxt Hyt S2 P2 ltac:(herr_tac))
    as (s3 & R3 & P3 & V3y & V3t & V3x & F3).
  destruct (hMOVE_spec t x (2 + MOVE2_len + o) Ph s3 (not_eq_sym Hxt) S3 P3 ltac:(herr_tac))
    as (s4 & R4 & P4 & V4x & V4t & F4).
  exists s4. split; [chain |]. split; [rewrite P4; reflexivity |].
  frames x. frames y. frames t.
  split; [lia |]. split; [lia |]. split; [lia |].
  solve_frame.
Qed.

(* ================================================================= *)
(* DISP: a k-way jump on a counter, by a chain of DEC instructions.   *)
(* ================================================================= *)

(* Stage i at address o + 3i: DEC x to the next stage; when x is 0, jump
   to the i-th target (with t as the jump's helper, restored). *)
Fixpoint hDISP (x t : nat) (ps : list nat) (o : nat) : list hinstr :=
  match ps with
  | [] => []
  | p :: ps' => M.DEC x (3 + o) :: hJMP t p (1 + o) ++ hDISP x t ps' (3 + o)
  end.

Lemma hDISP_length : forall x t ps o, length (hDISP x t ps o) = 3 * length ps.
Proof.
  intros x t ps. induction ps as [| p ps IH]; intro o; [reflexivity |].
  simpl. rewrite IH. lia.
Qed.

Theorem hDISP_spec : forall x t ps o Ph s, x <> t ->
  subcode (o, hDISP x t ps o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hframe [x; t] s s' /\ hv s' t = hv s t /\
    (hv s x < length ps -> hpc s' = nth (hv s x) ps 0 /\ hv s' x = 0) /\
    (length ps <= hv s x -> hpc s' = 3 * length ps + o /\ hv s' x = hv s x - length ps).
Proof.
  intros x t ps. induction ps as [| p ps IH]; intros o Ph s Hxt Hsc Hpc He.
  - exists s. split; [apply hrun_refl |]. split; [apply hframe_refl |].
    split; [reflexivity |]. simpl. split; [lia | intros _; split; lia].
  - cbn [hDISP] in Hsc. pose proof (sc_cons_l _ _ _ _ Hsc) as S0.
    pose proof (sc_cons_r _ _ _ _ Hsc) as Hsc1.
    destruct (hDEC_spec x (3 + o) o Ph s S0 Hpc He) as (s1 & R1 & F1 & D1).
    destruct (hv s x) as [| u] eqn:Hx.
    + destruct D1 as (P1 & V1 & W1).
      sc_split Hsc1 S1 Hsc2.
      destruct (hJMP_spec t p (1 + o) Ph s1 S1 P1 ltac:(herr_tac)) as (s2 & R2 & P2 & V2 & F2).
      exists s2. split; [chain |]. split; [solve_frame |].
      frames t. frames x. split; [congruence |]. simpl.
      split; [intros _; split; [exact P2 | lia] | lia].
    + destruct D1 as (P1 & V1 & W1).
      sc_split Hsc1 S1 S2.
      destruct (IH (3 + o) Ph s1 Hxt S2 P1 ltac:(herr_tac)) as (s2 & R2 & F2 & T2 & L2 & G2).
      rewrite V1 in L2, G2.
      exists s2. split; [chain |]. split; [solve_frame |].
      frames t. split; [congruence |]. simpl. split.
      * intros Hl. apply L2. lia.
      * intros Hl. destruct (G2 ltac:(lia)) as [G2a G2b]. split; lia.
Qed.

(* ================================================================= *)
(* EQC: go to p when x = c, else fall through; x keeps its value.     *)
(* ================================================================= *)

Definition EQC_fail (c o : nat) : nat := COPY_len + 3 * S c + o.
Definition EQC_len (c : nat) : nat := COPY_len + 3 * S c + 1.

Definition hEQC (x c t u p o : nat) : list hinstr :=
  hCOPY x t u o ++ hDISP t u (repeat (EQC_fail c o) c ++ [p]) (COPY_len + o) ++
  hZERO t (EQC_fail c o).

Lemma hEQC_length : forall x c t u p o, length (hEQC x c t u p o) = EQC_len c.
Proof.
  intros. unfold hEQC, EQC_len. rewrite !app_length, hCOPY_length, hDISP_length, app_length,
    repeat_length, hZERO_length. simpl. unfold ZERO_len, DEC_len. lia.
Qed.

Lemma nth_repeat_last : forall c f p v, v < S c ->
  nth v (repeat f c ++ [p]) 0 = if Nat.eqb v c then p else f.
Proof.
  intros c f p v Hv. destruct (Nat.eqb_spec v c) as [-> | Hne].
  - rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length, Nat.sub_diag. reflexivity.
  - rewrite app_nth1 by (rewrite repeat_length; lia).
    rewrite (nth_indep _ 0 f) by (rewrite repeat_length; lia). apply nth_repeat.
Qed.

Theorem hEQC_spec : forall x c t u p o Ph s, x <> t -> x <> u -> t <> u ->
  subcode (o, hEQC x c t u p o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hframe [x; t; u] s s' /\
    hv s' x = hv s x /\ hv s' t = 0 /\ hv s' u = 0 /\
    hpc s' = (if Nat.eqb (hv s x) c then p else EQC_len c + o).
Proof.
  intros x c t u p o Ph s Hxt Hxu Htu Hsc Hpc He. unfold hEQC in Hsc.
  sc_split Hsc S0 Hsc1.
  destruct (hCOPY_spec x t u o Ph s Hxt Hxu Htu S0 Hpc He)
    as (s1 & R1 & P1 & V1x & V1t & V1u & F1).
  sc_split Hsc1 S1 Hsc2.
  destruct (hDISP_spec t u (repeat (EQC_fail c o) c ++ [p]) (COPY_len + o) Ph s1 Htu S1
              ltac:(rewrite P1; reflexivity) ltac:(herr_tac))
    as (s2 & R2 & F2 & T2 & L2 & G2).
  rewrite app_length, repeat_length in L2, G2. simpl in L2, G2.
  assert (S3 : subcode (EQC_fail c o, hZERO t (EQC_fail c o)) (1, Ph)).
  { refine (sc_pos _ _ _ _ _ Hsc2). rewrite hDISP_length, app_length, repeat_length,
      hCOPY_length. unfold EQC_fail. simpl. lia. }
  rewrite V1t in L2, G2.
  destruct (Nat.eqb_spec (hv s x) c) as [Heq | Hne].
  - destruct (L2 ltac:(lia)) as [P2 V2]. rewrite nth_repeat_last in P2 by lia.
    rewrite Heq, Nat.eqb_refl in P2.
    exists s2. split; [chain |]. split; [solve_frame |].
    frames x. split; [congruence |]. split; [exact V2 |]. split; [congruence | exact P2].
  - assert (P2 : hpc s2 = EQC_fail c o).
    { destruct (Nat.lt_ge_cases (hv s x) (S c)) as [Hl | Hl].
      - destruct (L2 ltac:(lia)) as [P2 _]. rewrite nth_repeat_last in P2 by lia.
        destruct (Nat.eqb_spec (hv s x) c); [contradiction | exact P2].
      - destruct (G2 ltac:(lia)) as [P2 _]. rewrite P2.
        unfold EQC_fail, COPY_len, MOVE2_len, MOVE_len, JMP_len, INC_len, DEC_len. lia. }
    destruct (hZERO_spec t (EQC_fail c o) Ph s2 S3 P2 ltac:(herr_tac)) as (s3 & R3 & P3 & V3 & F3).
    exists s3. split; [chain |]. split; [solve_frame |].
    frames x. frames u. split; [congruence |]. split; [exact V3 |]. split; [congruence |].
    rewrite P3. unfold EQC_fail, EQC_len. lia.
Qed.

(* ================================================================= *)
(* EQR: go to p when x = y, else fall through; x, y keep values.      *)
(* ================================================================= *)

Definition EQR_loop (o : nat) : nat := 2 * COPY_len + o.
Definition EQR_ne (o : nat) : nat := 2 * COPY_len + 10 + o.
Definition EQR_len : nat := 2 * COPY_len + 12.

(* After the two copies, t1 and t2 count down together. t1 reaching 0
   first means x <= y: equal exactly when t2 is 0 too. t2 reaching 0
   first means x > y. *)
Definition hEQR (x y t1 t2 u p o : nat) : list hinstr :=
  hCOPY x t1 u o ++ hCOPY y t2 u (COPY_len + o) ++
  [M.DEC t1 (7 + EQR_loop o)] ++
  hJZ t2 p (1 + EQR_loop o) ++
  hJMP u (EQR_ne o) (5 + EQR_loop o) ++
  [M.DEC t2 (EQR_loop o)] ++
  hJMP u (EQR_ne o) (8 + EQR_loop o) ++
  hZERO t1 (EQR_ne o) ++ hZERO t2 (1 + EQR_ne o).

Lemma hEQR_length : forall x y t1 t2 u p o, length (hEQR x y t1 t2 u p o) = EQR_len.
Proof. reflexivity. Qed.

Lemma hEQR_loop : forall x y t1 t2 u p o Ph, t1 <> t2 -> t1 <> u -> t2 <> u ->
  subcode (o, hEQR x y t1 t2 u p o) (1, Ph) ->
  forall a b s, hpc s = EQR_loop o -> herr s = false -> hv s t1 = a -> hv s t2 = b ->
  exists s', Hrun Ph s s' /\ hframe [t1; t2; u] s s' /\ hv s' u = hv s u /\
    (a = b -> hpc s' = p /\ hv s' t1 = 0 /\ hv s' t2 = 0) /\
    (a <> b -> hpc s' = EQR_ne o).
Proof.
  intros x y t1 t2 u p o Ph H12 H1u H2u Hsc. unfold hEQR in Hsc.
  sc_split Hsc X0 Hsc1. sc_split Hsc1 X1 Hsc2. sc_split Hsc2 SD1 Hsc3.
  sc_split Hsc3 SJZ Hsc4. sc_split Hsc4 SJ1 Hsc5. sc_split Hsc5 SD2 Hsc6.
  sc_split Hsc6 SJ2 X2. clear X0 X1 X2 Hsc Hsc1 Hsc2 Hsc3 Hsc4 Hsc5 Hsc6.
  induction a as [| a IH]; intros b s Hpc He Ha Hb.
  - destruct (hDEC_spec t1 (7 + EQR_loop o) (EQR_loop o) Ph s SD1 Hpc He) as (s1 & R1 & F1 & D1).
    rewrite Ha in D1. destruct D1 as (P1 & V1 & W1).
    destruct (hJZ_spec t2 p (1 + EQR_loop o) Ph s1 SJZ P1 ltac:(herr_tac))
      as (s2 & R2 & P2 & V2 & F2).
    frames t2. rewrite Fv, Hb in P2.
    destruct b as [| b].
    + exists s2. split; [chain |]. split; [solve_frame |]. frames u. frames t1.
      split; [congruence |]. split; [intros _; split; [exact P2 | split; congruence] | lia].
    + destruct (hJMP_spec u (EQR_ne o) (5 + EQR_loop o) Ph s2 SJ1 P2 ltac:(herr_tac))
        as (s3 & R3 & P3 & V3 & F3).
      exists s3. split; [chain |]. split; [solve_frame |]. frames u.
      split; [congruence |]. split; [lia | intros _; exact P3].
  - destruct (hDEC_spec t1 (7 + EQR_loop o) (EQR_loop o) Ph s SD1 Hpc He) as (s1 & R1 & F1 & D1).
    rewrite Ha in D1. destruct D1 as (P1 & V1 & W1).
    destruct (hDEC_spec t2 (EQR_loop o) (7 + EQR_loop o) Ph s1 SD2 P1 ltac:(herr_tac))
      as (s2 & R2 & F2 & D2).
    frames t2. rewrite Fv, Hb in D2.
    destruct b as [| b].
    + destruct D2 as (P2 & V2 & W2).
      destruct (hJMP_spec u (EQR_ne o) (8 + EQR_loop o) Ph s2 SJ2 P2 ltac:(herr_tac))
        as (s3 & R3 & P3 & V3 & F3).
      exists s3. split; [chain |]. split; [solve_frame |]. frames u.
      split; [congruence |]. split; [lia | intros _; exact P3].
    + destruct D2 as (P2 & V2 & W2).
      frames t1.
      destruct (IH b s2 P2 ltac:(herr_tac) ltac:(congruence) V2) as (s3 & R3 & F3 & U3 & E3 & N3).
      exists s3. split; [chain |]. split; [solve_frame |]. frames u.
      split; [congruence |]. split.
      * intros Hab. apply E3. lia.
      * intros Hab. apply N3. lia.
Qed.

Theorem hEQR_spec : forall x y t1 t2 u p o Ph s, NoDup [x; y; t1; t2; u] ->
  subcode (o, hEQR x y t1 t2 u p o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hframe [x; y; t1; t2; u] s s' /\
    hv s' x = hv s x /\ hv s' y = hv s y /\
    hv s' t1 = 0 /\ hv s' t2 = 0 /\ hv s' u = 0 /\
    hpc s' = (if Nat.eqb (hv s x) (hv s y) then p else EQR_len + o).
Proof.
  intros x y t1 t2 u p o Ph s Hnd Hsc Hpc He. pose proof Hsc as Hsc0.
  nodup_neqs Hnd. unfold hEQR in Hsc.
  sc_split Hsc S0 Hsc1. sc_split Hsc1 S1 Hsc2.
  destruct (hCOPY_spec x t1 u o Ph s ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) S0 Hpc He)
    as (s1 & R1 & P1 & V1x & V1t & V1u & F1).
  destruct (hCOPY_spec y t2 u (COPY_len + o) Ph s1 ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) S1 P1
              ltac:(herr_tac)) as (s2 & R2 & P2 & V2y & V2t & V2u & F2).
  frames x. frames y. frames t1.
  destruct (hEQR_loop x y t1 t2 u p o Ph ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) Hsc0
              (hv s x) (hv s y) s2 P2 ltac:(herr_tac) ltac:(congruence) ltac:(congruence))
    as (s3 & R3 & F3 & U3 & E3 & N3).
  destruct (Nat.eqb_spec (hv s x) (hv s y)) as [Heq | Hne].
  - destruct (E3 Heq) as (P3 & T13 & T23).
    exists s3. split; [chain |]. split; [solve_frame |]. frames x. frames y.
    split; [congruence |]. split; [congruence |]. split; [exact T13 |]. split; [exact T23 |].
    split; [congruence | exact P3].
  - pose proof (N3 Hne) as P3.
    sc_split Hsc2 X3 Hsc3. sc_split Hsc3 X4 Hsc4. sc_split Hsc4 X5 Hsc5.
    sc_split Hsc5 X6 Hsc6. sc_split Hsc6 X7 Hsc7. sc_split Hsc7 SZ1 SZ2.
    destruct (hZERO_spec t1 (EQR_ne o) Ph s3 SZ1 P3 ltac:(herr_tac)) as (s4 & R4 & P4 & V4 & F4).
    destruct (hZERO_spec t2 (1 + EQR_ne o) Ph s4 SZ2 P4 ltac:(herr_tac))
      as (s5 & R5 & P5 & V5 & F5).
    exists s5. split; [chain |]. split; [solve_frame |].
    frames x. frames y. frames t1. frames u.
    split; [congruence |]. split; [congruence |]. split; [congruence |]. split; [exact V5 |].
    split; [congruence |]. rewrite P5. reflexivity.
Qed.

(* ================================================================= *)
(* FETCH: read the code of the current guest instruction.             *)
(* ================================================================= *)

(* Registers: prog holds the program code and gpc the guest pc (both keep
   their values); w, kk, h, a, t are scratch. Layout:

     o                 w := prog              (COPY, helper t)
     COPY_len + o      kk := gpc              (COPY, helper t)
     2 COPY_len + o    JZ kk pz               guest pc 0: exit to pz
                       DEC kk (to the loop)   kk := gpc - 1
     loop              JZ w pe                code exhausted: exit to pe
                       UNPACK a w h           h := head, w := tail
                       JZ kk end              kk = 0: h is the instruction
                       DEC kk loop            one more instruction to skip
     end = FETCH_len + o                                                   *)

Definition FETCH_loop (o : nat) : nat := 2 * COPY_len + JZ_len + 1 + o.
Definition FETCH_len : nat := 2 * COPY_len + 3 * JZ_len + UNPACK_len + 2.

Definition hFETCH (prog gpc w kk h a t pz pe o : nat) : list hinstr :=
  hCOPY prog w t o ++
  hCOPY gpc kk t (COPY_len + o) ++
  hJZ kk pz (2 * COPY_len + o) ++
  [M.DEC kk (FETCH_loop o)] ++
  hJZ w pe (FETCH_loop o) ++
  hUNPACK a w h (JZ_len + FETCH_loop o) ++
  hJZ kk (FETCH_len + o) (JZ_len + UNPACK_len + FETCH_loop o) ++
  [M.DEC kk (FETCH_loop o)].

Lemma hFETCH_length : forall prog gpc w kk h a t pz pe o,
  length (hFETCH prog gpc w kk h a t pz pe o) = FETCH_len.
Proof. reflexivity. Qed.

Lemma fetch_code_zero : forall k, fetch_code 0 k = None.
Proof. intros [| k]; reflexivity. Qed.

Lemma fetch_code_0 : forall c, fetch_code c 0 = option_map fst (unpair c).
Proof. reflexivity. Qed.

Lemma hFETCH_loop : forall prog gpc w kk h a t pz pe o Ph,
  w <> kk -> w <> h -> w <> a -> kk <> h -> kk <> a -> h <> a ->
  subcode (o, hFETCH prog gpc w kk h a t pz pe o) (1, Ph) ->
  forall k s, hpc s = FETCH_loop o -> herr s = false -> hv s kk = k ->
  exists s', Hrun Ph s s' /\ hframe [w; kk; h; a] s s' /\
    match fetch_code (hv s w) k with
    | Some c => hpc s' = FETCH_len + o /\ hv s' h = c /\ hv s' kk = 0 /\ hv s' a = 0 /\
                hv s' w = skip_code (hv s w) (S k)
    | None => hpc s' = pe /\ hv s' w = 0
    end.
Proof.
  intros prog gpc w kk h a t pz pe o Ph Hwk Hwh Hwa Hkh Hka Hha Hsc. unfold hFETCH in Hsc.
  sc_split Hsc X0 Hsc1. sc_split Hsc1 X1 Hsc2. sc_split Hsc2 X2 Hsc3. sc_split Hsc3 X3 Hsc4.
  sc_split Hsc4 SJW Hsc5. sc_split Hsc5 SUN Hsc6. sc_split Hsc6 SJK SDK.
  clear X0 X1 X2 X3 Hsc Hsc1 Hsc2 Hsc3 Hsc4 Hsc5 Hsc6.
  induction k as [| k IH]; intros s Hpc He Hk;
    destruct (hJZ_spec w pe (FETCH_loop o) Ph s SJW Hpc He) as (s1 & R1 & P1 & V1 & F1);
    destruct (hv s w) as [| c'] eqn:Hw; try rewrite Hw in P1.
  - rewrite fetch_code_zero. exists s1. split; [chain |]. split; [solve_frame |].
    split; [exact P1 | congruence].
  - destruct (unpair_some (S c') (Nat.lt_0_succ c')) as (m & n & Hun & Hpair).
    destruct (hUNPACK_spec a w h m n (JZ_len + FETCH_loop o) Ph s1
                ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) SUN P1
                ltac:(herr_tac))
      as (s2 & R2 & P2 & V2w & V2h & V2a & F2).
    frames kk.
    destruct (hJZ_spec kk (FETCH_len + o) (JZ_len + UNPACK_len + FETCH_loop o) Ph s2 SJK P2
                ltac:(herr_tac)) as (s3 & R3 & P3 & V3 & F3).
    assert (K2 : hv s2 kk = 0) by congruence. rewrite K2 in P3.
    rewrite fetch_code_0, Hun. cbn [option_map fst].
    exists s3. split; [chain |]. split; [solve_frame |].
    frames h. frames a. frames w.
    split; [exact P3 |]. split; [congruence |]. split; [congruence |]. split; [congruence |].
    rewrite skip_code_S, Hun. cbn [skip_code]. congruence.
  - rewrite fetch_code_zero. exists s1. split; [chain |]. split; [solve_frame |].
    split; [exact P1 | congruence].
  - destruct (unpair_some (S c') (Nat.lt_0_succ c')) as (m & n & Hun & Hpair).
    destruct (hUNPACK_spec a w h m n (JZ_len + FETCH_loop o) Ph s1
                ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) SUN P1
                ltac:(herr_tac))
      as (s2 & R2 & P2 & V2w & V2h & V2a & F2).
    frames kk.
    destruct (hJZ_spec kk (FETCH_len + o) (JZ_len + UNPACK_len + FETCH_loop o) Ph s2 SJK P2
                ltac:(herr_tac)) as (s3 & R3 & P3 & V3 & F3).
    assert (K2 : hv s2 kk = S k) by congruence. rewrite K2 in P3.
    destruct (hDEC_spec kk (FETCH_loop o) (JZ_len + (JZ_len + UNPACK_len + FETCH_loop o)) Ph s3
                SDK P3 ltac:(herr_tac)) as (s4 & R4 & F4 & D4).
    assert (K3 : hv s3 kk = S k) by congruence. rewrite K3 in D4.
    destruct D4 as (P4 & V4 & W4).
    destruct (IH s4 P4 ltac:(herr_tac) V4) as (s5 & R5 & F5 & G5).
    frames w.
    assert (W4' : hv s4 w = n) by congruence. rewrite W4' in G5.
    rewrite fetch_code_S, Hun, skip_code_S, Hun.
    exists s5. split; [chain |]. split; [solve_frame |]. exact G5.
Qed.

Theorem hFETCH_spec : forall prog gpc w kk h a t pz pe o Ph s,
  NoDup [prog; gpc; w; kk; h; a; t] ->
  subcode (o, hFETCH prog gpc w kk h a t pz pe o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hframe [prog; gpc; w; kk; h; a; t] s s' /\
    hv s' prog = hv s prog /\ hv s' gpc = hv s gpc /\ hv s' t = 0 /\
    match hv s gpc with
    | 0 => hpc s' = pz /\ hv s' kk = 0 /\ hv s' w = hv s prog
    | S k =>
        match fetch_code (hv s prog) k with
        | Some c => hpc s' = FETCH_len + o /\ hv s' h = c /\ hv s' kk = 0 /\ hv s' a = 0 /\
                    hv s' w = skip_code (hv s prog) (S k)
        | None => hpc s' = pe /\ hv s' w = 0
        end
    end.
Proof.
  intros prog gpc w kk h a t pz pe o Ph s Hnd Hsc Hpc He. pose proof Hsc as Hsc0.
  nodup_neqs Hnd. unfold hFETCH in Hsc.
  sc_split Hsc S0 Hsc1. sc_split Hsc1 S1 Hsc2. sc_split Hsc2 S2 Hsc3. sc_split Hsc3 S3 Hsc4.
  destruct (hCOPY_spec prog w t o Ph s ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) S0 Hpc He)
    as (s1 & R1 & P1 & V1p & V1w & V1t & F1).
  destruct (hCOPY_spec gpc kk t (COPY_len + o) Ph s1 ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) S1 P1
              ltac:(herr_tac)) as (s2 & R2 & P2 & V2g & V2k & V2t & F2).
  destruct (hJZ_spec kk pz (2 * COPY_len + o) Ph s2 S2 P2 ltac:(herr_tac))
    as (s3 & R3 & P3 & V3 & F3).
  frames prog. frames gpc. frames w. frames t.
  assert (K2 : hv s2 kk = hv s gpc) by congruence. rewrite K2 in P3.
  destruct (hv s gpc) as [| k] eqn:Hg.
  - exists s3. split; [chain |]. split; [solve_frame |].
    split; [congruence |]. split; [congruence |]. split; [congruence |].
    split; [exact P3 |]. split; congruence.
  - destruct (hDEC_spec kk (FETCH_loop o) (JZ_len + (2 * COPY_len + o)) Ph s3 S3 P3
                ltac:(herr_tac)) as (s4 & R4 & F4 & D4).
    assert (K3 : hv s3 kk = S k) by congruence. rewrite K3 in D4.
    destruct D4 as (P4 & V4 & W4).
    destruct (hFETCH_loop prog gpc w kk h a t pz pe o Ph ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence)
                ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) Hsc0 k s4 P4 ltac:(herr_tac) V4)
      as (s5 & R5 & F5 & G5).
    frames prog. frames gpc. frames w. frames t.
    assert (W4' : hv s4 w = hv s prog) by congruence. rewrite W4' in G5.
    exists s5. split; [chain |]. split; [solve_frame |].
    split; [congruence |]. split; [congruence |]. split; [congruence |]. exact G5.
Qed.

(* FETCH on the code of a guest program. *)
Corollary hFETCH_guest : forall (P : list E.instr) prog gpc w kk h a t pz pe o Ph s k,
  NoDup [prog; gpc; w; kk; h; a; t] ->
  subcode (o, hFETCH prog gpc w kk h a t pz pe o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s prog = prog_code P -> hv s gpc = S k ->
  exists s', Hrun Ph s s' /\ hframe [prog; gpc; w; kk; h; a; t] s s' /\
    hv s' prog = prog_code P /\ hv s' gpc = S k /\ hv s' t = 0 /\
    match nth_error P k with
    | Some i => hpc s' = FETCH_len + o /\ hv s' h = icode i /\ hv s' kk = 0 /\
                hv s' a = 0 /\ hv s' w = prog_code (skipn (S k) P)
    | None => hpc s' = pe /\ hv s' w = 0
    end.
Proof.
  intros P prog gpc w kk h a t pz pe o Ph s k Hnd Hsc Hpc He Hp Hg.
  destruct (hFETCH_spec prog gpc w kk h a t pz pe o Ph s Hnd Hsc Hpc He)
    as (s' & R & F & Vp & Vg & Vt & G).
  rewrite Hg, Hp, fetch_code_prog, skip_code_prog in G.
  exists s'. split; [exact R |]. split; [exact F |].
  split; [congruence |]. split; [congruence |]. split; [exact Vt |].
  destruct (nth_error P k); exact G.
Qed.

(* Guest pc 0 on the code of a guest program: the FETCH exits to pz. *)
Corollary hFETCH_guest_pc0 : forall (P : list E.instr) prog gpc w kk h a t pz pe o Ph s,
  NoDup [prog; gpc; w; kk; h; a; t] ->
  subcode (o, hFETCH prog gpc w kk h a t pz pe o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s prog = prog_code P -> hv s gpc = 0 ->
  exists s', Hrun Ph s s' /\ hframe [prog; gpc; w; kk; h; a; t] s s' /\
    hv s' prog = prog_code P /\ hv s' gpc = 0 /\ hv s' t = 0 /\ hpc s' = pz.
Proof.
  intros P prog gpc w kk h a t pz pe o Ph s Hnd Hsc Hpc He Hp Hg.
  destruct (hFETCH_spec prog gpc w kk h a t pz pe o Ph s Hnd Hsc Hpc He)
    as (s' & R & F & Vp & Vg & Vt & G).
  rewrite Hg in G. destruct G as [G _].
  exists s'. split; [exact R |]. split; [exact F |]. split; [congruence |].
  split; [congruence |]. split; [exact Vt | exact G].
Qed.

(* ================================================================= *)
(* BUMP: a slot keeps its value, its version goes up by 2, and its    *)
(* mirror is cleared.                                                  *)
(* ================================================================= *)

Definition BUMP_len : nat := 3.

Definition hBUMP (sl mp o : nat) : list hinstr :=
  [M.INC sl; M.DEC sl (2 + o)] ++ hZERO mp (2 + o).

Lemma hBUMP_length : forall sl mp o, length (hBUMP sl mp o) = BUMP_len.
Proof. reflexivity. Qed.

Theorem hBUMP_spec : forall sl mp o Ph s, sl <> mp ->
  subcode (o, hBUMP sl mp o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = BUMP_len + o /\
    hv s' sl = hv s sl /\ hver s' sl = 2 + hver s sl /\ hv s' mp = 0 /\
    hframe [sl; mp] s s'.
Proof.
  intros sl mp o Ph s Hne Hsc Hpc He. unfold hBUMP in Hsc.
  sc_split Hsc S01 S2.
  pose proof (sc_cons_l _ _ _ _ S01) as S0. pose proof (sc_cons_r _ _ _ _ S01) as S1.
  destruct (hINC_spec sl o Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & W1 & F1).
  destruct (hDEC_spec sl (2 + o) (S o) Ph s1 S1 P1 ltac:(herr_tac)) as (s2 & R2 & F2 & D2).
  rewrite V1 in D2. destruct D2 as (P2 & V2 & W2).
  destruct (hZERO_spec mp (2 + o) Ph s2 S2 P2 ltac:(herr_tac)) as (s3 & R3 & P3 & V3 & F3).
  exists s3. split; [chain |]. split; [exact P3 |].
  frames sl. split; [congruence |]. split; [lia |]. split; [exact V3 |].
  solve_frame.
Qed.

(* ================================================================= *)
(* The three record moves: CHECK PSlot r, COMMIT PSlot r, CERTIFY.    *)
(* ================================================================= *)

Definition hCHECK (r o : nat) : list hinstr := [M.CHECK PSlot r].
Definition hCOMMIT (r o : nat) : list hinstr := [M.COMMIT PSlot r].
Definition hCERTIFY (o : nat) : list hinstr := [M.CERTIFY].

Lemma hCHECK_step : forall r o Ph s,
  subcode (o, hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hrun_prog 1 Ph s = hexec s (M.CHECK PSlot r) /\ htrace 1 Ph s = [M.CHECK PSlot r].
Proof.
  intros r o Ph s Hsc Hpc He. split.
  - apply (host_step_at hprop_eqb heval Ph s o); auto. discriminate.
  - apply (host_trace_at hprop_eqb heval Ph s o); auto. discriminate.
Qed.

Lemma hCOMMIT_step : forall r o Ph s,
  subcode (o, hCOMMIT r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hrun_prog 1 Ph s = hexec s (M.COMMIT PSlot r) /\ htrace 1 Ph s = [M.COMMIT PSlot r].
Proof.
  intros r o Ph s Hsc Hpc He. split.
  - apply (host_step_at hprop_eqb heval Ph s o); auto. discriminate.
  - apply (host_trace_at hprop_eqb heval Ph s o); auto. discriminate.
Qed.

Lemma hCERTIFY_step : forall o Ph s,
  subcode (o, hCERTIFY o) (1, Ph) -> hpc s = o -> herr s = false ->
  hrun_prog 1 Ph s = hexec s M.CERTIFY /\ htrace 1 Ph s = [M.CERTIFY].
Proof.
  intros o Ph s Hsc Hpc He. split.
  - apply (host_step_at hprop_eqb heval Ph s o); auto. discriminate.
  - apply (host_trace_at hprop_eqb heval Ph s o); auto. discriminate.
Qed.

(* CHECK on a slot holding pair (pcode p) v, when p holds of v and the
   fact table has room: the fact (PSlot, r, current version of r) is
   recorded, pc moves on, the ledger goes up by 1; nothing else changes. *)
Theorem hCHECK_pass : forall r o Ph s p v,
  subcode (o, hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s r = pair (pcode p) v -> E.holds p v ->
  length (M.facts (M.core_of s)) < M.fact_cap ->
  hrun_prog 1 Ph s =
  M.mkst (M.record_fact (M.core_of s) (M.mkfact PSlot r (hver s r))) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s p v Hsc Hpc He Hv Hh Hcap.
  destruct (hCHECK_step r o Ph s Hsc Hpc He) as [E _]. rewrite E.
  rewrite (M.multi_exec_check_pass hprop_eqb heval); [reflexivity |].
  unfold M.check_ok. rewrite He, Hv, heval_pair.
  apply E.eval_iff in Hh. rewrite Hh. apply Nat.ltb_lt in Hcap. rewrite Hcap. reflexivity.
Qed.

Corollary hCHECK_pass_fields : forall r o Ph s p v,
  subcode (o, hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s r = pair (pcode p) v -> E.holds p v ->
  length (M.facts (M.core_of s)) < M.fact_cap ->
  let s' := hrun_prog 1 Ph s in
  M.facts (M.core_of s') = M.mkfact PSlot r (hver s r) :: M.facts (M.core_of s) /\
  M.chan (M.core_of s') = M.chan (M.core_of s) /\
  hpc s' = S o /\ herr s' = false /\ M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
  (forall d, hv s' d = hv s d /\ hver s' d = hver s d).
Proof.
  intros r o Ph s p v Hsc Hpc He Hv Hh Hcap s'. unfold s'.
  rewrite (hCHECK_pass r o Ph s p v Hsc Hpc He Hv Hh Hcap). simpl.
  rewrite Hpc, He. repeat split.
Qed.

(* A CHECK that fails traps: the latch rises, the ledger goes up by 1,
   and the fact table, channel, registers and flag stay as they were. *)
Theorem hCHECK_fail : forall r o Ph s,
  subcode (o, hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  M.check_ok heval (M.core_of s) PSlot r = false ->
  hrun_prog 1 Ph s = M.mkst (M.trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s Hsc Hpc He Hc.
  destruct (hCHECK_step r o Ph s Hsc Hpc He) as [E _]. rewrite E.
  apply (M.multi_exec_check_fail hprop_eqb heval); assumption.
Qed.

Corollary hCHECK_fail_holds : forall r o Ph s p v,
  subcode (o, hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s r = pair (pcode p) v -> ~ E.holds p v ->
  hrun_prog 1 Ph s = M.mkst (M.trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s p v Hsc Hpc He Hv Hh. apply (hCHECK_fail r o Ph s Hsc Hpc He).
  unfold M.check_ok. rewrite Hv, heval_pair.
  destruct (E.eval p v) eqn:Ev; [exfalso; apply Hh, E.eval_iff, Ev |].
  rewrite andb_false_r. reflexivity.
Qed.

Corollary hCHECK_fail_cap : forall r o Ph s,
  subcode (o, hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  M.fact_cap <= length (M.facts (M.core_of s)) ->
  hrun_prog 1 Ph s = M.mkst (M.trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s Hsc Hpc He Hcap. apply (hCHECK_fail r o Ph s Hsc Hpc He).
  unfold M.check_ok. apply Nat.ltb_ge in Hcap. rewrite Hcap, andb_false_r. reflexivity.
Qed.

(* A slot holding 0 (an unused slot, or the dead register) never passes. *)
Corollary hCHECK_fail_zero : forall r o Ph s,
  subcode (o, hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s r = 0 ->
  hrun_prog 1 Ph s = M.mkst (M.trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s Hsc Hpc He Hv. apply (hCHECK_fail r o Ph s Hsc Hpc He).
  unfold M.check_ok. rewrite Hv, heval_zero, andb_false_r. reflexivity.
Qed.

(* COMMIT on a slot whose current version carries a recorded PSlot fact:
   the channel holds that fact, pc moves on, the ledger goes up by 1. *)
Theorem hCOMMIT_pass : forall r o Ph s,
  subcode (o, hCOMMIT r o) (1, Ph) -> hpc s = o -> herr s = false ->
  In (M.mkfact PSlot r (hver s r)) (M.facts (M.core_of s)) ->
  hrun_prog 1 Ph s =
  M.mkst (M.commit_to (M.core_of s) (M.mkfact PSlot r (hver s r))) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s Hsc Hpc He Hin.
  destruct (hCOMMIT_step r o Ph s Hsc Hpc He) as [E _]. rewrite E.
  rewrite (M.multi_exec_commit_pass hprop_eqb hprop_eqb_eq heval); [reflexivity |].
  apply (M.multi_commit_ok_iff hprop_eqb hprop_eqb_eq). split; [exact He | exact Hin].
Qed.

Corollary hCOMMIT_pass_fields : forall r o Ph s,
  subcode (o, hCOMMIT r o) (1, Ph) -> hpc s = o -> herr s = false ->
  In (M.mkfact PSlot r (hver s r)) (M.facts (M.core_of s)) ->
  let s' := hrun_prog 1 Ph s in
  M.facts (M.core_of s') = M.facts (M.core_of s) /\
  M.chan (M.core_of s') = Some (M.mkfact PSlot r (hver s r)) /\
  hpc s' = S o /\ herr s' = false /\ M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
  (forall d, hv s' d = hv s d /\ hver s' d = hver s d).
Proof.
  intros r o Ph s Hsc Hpc He Hin s'. unfold s'.
  rewrite (hCOMMIT_pass r o Ph s Hsc Hpc He Hin). simpl.
  rewrite Hpc, He. repeat split.
Qed.

(* COMMIT without that fact traps. *)
Theorem hCOMMIT_fail : forall r o Ph s,
  subcode (o, hCOMMIT r o) (1, Ph) -> hpc s = o -> herr s = false ->
  ~ In (M.mkfact PSlot r (hver s r)) (M.facts (M.core_of s)) ->
  hrun_prog 1 Ph s = M.mkst (M.trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s Hsc Hpc He Hin.
  destruct (hCOMMIT_step r o Ph s Hsc Hpc He) as [E _]. rewrite E.
  apply (M.multi_exec_commit_fail hprop_eqb heval); [exact He |].
  destruct (M.commit_ok hprop_eqb (M.core_of s) PSlot r) eqn:Hc; [| reflexivity].
  exfalso. apply (M.multi_commit_ok_iff hprop_eqb hprop_eqb_eq) in Hc. apply Hin, Hc.
Qed.

(* CERTIFY with a full channel raises the flag; pc moves on, the ledger
   goes up by 1. *)
Theorem hCERTIFY_pass : forall o Ph s f,
  subcode (o, hCERTIFY o) (1, Ph) -> hpc s = o -> herr s = false ->
  M.chan (M.core_of s) = Some f ->
  hrun_prog 1 Ph s = M.mkst (M.goto (M.core_of s) (S o)) (M.mu s + 1) true.
Proof.
  intros o Ph s f Hsc Hpc He Hc.
  destruct (hCERTIFY_step o Ph s Hsc Hpc He) as [E _]. rewrite E.
  rewrite (M.multi_exec_certify_pass hprop_eqb heval), Hpc; [reflexivity |].
  unfold M.certify_ok. rewrite He, Hc. reflexivity.
Qed.

(* CERTIFY with an empty channel traps. *)
Theorem hCERTIFY_fail : forall o Ph s,
  subcode (o, hCERTIFY o) (1, Ph) -> hpc s = o -> herr s = false ->
  M.chan (M.core_of s) = None ->
  hrun_prog 1 Ph s = M.mkst (M.trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros o Ph s Hsc Hpc He Hc.
  destruct (hCERTIFY_step o Ph s Hsc Hpc He) as [E _]. rewrite E.
  apply (M.multi_exec_certify_fail hprop_eqb heval); [exact He |].
  unfold M.certify_ok. rewrite He, Hc. reflexivity.
Qed.

(* A trapped state: same registers, fact table, channel and pc; the latch
   is up, so the host takes no further step. *)
Lemma trap_fields : forall (k : @M.core hprop),
  M.vals (M.trap k) = M.vals k /\ M.vers (M.trap k) = M.vers k /\
  M.facts (M.trap k) = M.facts k /\ M.chan (M.trap k) = M.chan k /\
  M.pc (M.trap k) = M.pc k /\ M.err (M.trap k) = true.
Proof. intro k. repeat split. Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions hINC_spec.
Print Assumptions hDEC_spec.
Print Assumptions hJMP_spec.
Print Assumptions hJZ_spec.
Print Assumptions hZERO_spec.
Print Assumptions hMOVE_spec.
Print Assumptions hMOVE2_spec.
Print Assumptions hPACK_spec.
Print Assumptions hHALF_spec.
Print Assumptions hUNPACK_spec.
Print Assumptions hUNPACK0_spec.
Print Assumptions hCOPY_spec.
Print Assumptions hDISP_spec.
Print Assumptions hEQC_spec.
Print Assumptions hEQR_spec.
Print Assumptions hFETCH_spec.
Print Assumptions hFETCH_guest.
Print Assumptions hFETCH_guest_pc0.
Print Assumptions hBUMP_spec.
Print Assumptions hCHECK_pass.
Print Assumptions hCHECK_pass_fields.
Print Assumptions hCHECK_fail_holds.
Print Assumptions hCHECK_fail_cap.
Print Assumptions hCHECK_fail_zero.
Print Assumptions hCOMMIT_pass.
Print Assumptions hCOMMIT_pass_fields.
Print Assumptions hCOMMIT_fail.
Print Assumptions hCERTIFY_pass.
Print Assumptions hCERTIFY_fail.
