(** UniversalPBlocks.v: the building blocks of the universal interpreter, as
    host programs of EarnedMultiPriced.v with host-level specifications.

    This file is the priced counterpart of UniversalBlocks.v: the host is the
    machine of EarnedMultiPriced.v (with PAY), the guest is the priced
    machine of EarnedPriced.v over the universal property language
    cg_uprop (UniversalPCodes.v), every name carries the prefix pu_, and
    the host program is U_P.

    The host is EarnedMultiPriced.v with the property language PSlot of
    UniversalPCodes.v. Every block is a function of the address o where it
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

      Library blocks (MMA_pairing.v), transferred by pu_mma_block_host:
        pu_hJMP a p       go to p
        pu_hJZ x p        go to p when x = 0, else fall through
        pu_hZERO x        x := 0
        pu_hMOVE x y      y := y + x, x := 0
        pu_hMOVE2 x y z   y := y + x, z := z + x, x := 0
        pu_hPACK a x y    x := pair y x, y := 0, a := 0
        pu_hHALF a x p    halve x, go to p when x was even
        pu_hUNPACK a x y  when x = pair m n: x := n, y := m, a := 0
      Single instructions: pu_hINC r, pu_hDEC r j.
      New blocks:
        pu_hCOPY x y t    y := x, t := 0, x keeps its value
        pu_hDISP x t ps   jump to the (x)-th address of ps, or fall through
                       with x reduced by the length of ps
        pu_hEQC x c t u p go to p when x = c, else fall through
        pu_hEQR x y t1 t2 u p   go to p when x = y, else fall through
        pu_hFETCH         copy the program code and guest pc, strip
                       instruction codes, and read the code of the
                       current instruction (UniversalCodes.fetch_code),
                       with separate exits for guest pc 0 and for a pc
                       past the end of the program
        pu_hBUMP sl mp    the slot sl keeps its value and its version goes
                       up by exactly 2; its mirror mp becomes 0
      One-instruction lemmas for CHECK PSlot r, COMMIT PSlot r, CERTIFY and
      PAY (pu_hPAY, pu_hPAY_pass: pc + 1, ledger + 1, nothing else):
      what each does to the fact table, the channel, the ledger, the flag
      and the trap latch, given the slot's contents.

    Dependencies: the Coq standard library, the vendored coq-undecidability
    library, EarnedGeneric.v, EarnedPriced.v, EarnedMultiPriced.v, CompilerChecker.v,
    UniversalPCodes.v and UniversalPBridge.v. No axioms, no Admitted.         *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the universal interpreter U_P of UniversalPRun.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and files under minimal/. Its link to the abstract record (the
   host machine meeting thiele_complete of ThieleComplete.v, and every
   computably presented machine run on U_P) lives in UniversalPRun.v and
   PresentedUniversal.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import Vec.pos Vec.vec Code.subcode Code.sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.Util Require Import MMA_pairing.
Require Import Minimal.UniversalPCodes Minimal.UniversalPBridge.

(* The host machine at the PSlot property language. *)
Local Notation hinstr := (@M.pu_instr pu_hprop).
Local Notation hstate := (@M.pu_state pu_hprop).
Local Notation hrun_prog := (M.pu_run_prog pu_hprop_eqb pu_heval).
Local Notation hexec := (M.pu_exec pu_hprop_eqb pu_heval).
Local Notation htrace := (M.pu_trace_of pu_hprop_eqb pu_heval).
Local Notation Hrun := (pu_hrun pu_hprop_eqb pu_heval).

(* ================================================================= *)
(* Placement helpers.                                                 *)
(* ================================================================= *)

Lemma pu_sc_app_l : forall (o : nat) (l1 l2 Ph : list hinstr),
  subcode (o, l1 ++ l2) (1, Ph) -> subcode (o, l1) (1, Ph).
Proof.
  intros o l1 l2 Ph H. eapply subcode_trans; [| exact H]. apply subcode_left. reflexivity.
Qed.

Lemma pu_sc_app_r : forall (o n : nat) (l1 l2 Ph : list hinstr),
  n = length l1 + o -> subcode (o, l1 ++ l2) (1, Ph) -> subcode (n, l2) (1, Ph).
Proof.
  intros o n l1 l2 Ph En H. eapply subcode_trans; [| exact H].
  apply subcode_right. lia.
Qed.

Lemma pu_sc_cons_l : forall (o : nat) (i : hinstr) l Ph,
  subcode (o, i :: l) (1, Ph) -> subcode (o, [i]) (1, Ph).
Proof. intros o i l Ph H. apply (pu_sc_app_l o [i] l Ph H). Qed.

Lemma pu_sc_cons_r : forall (o : nat) (i : hinstr) l Ph,
  subcode (o, i :: l) (1, Ph) -> subcode (S o, l) (1, Ph).
Proof. intros o i l Ph H. apply (pu_sc_app_r o (S o) [i] l Ph); [reflexivity | exact H]. Qed.

Lemma pu_sc_pos : forall (n m : nat) (l Ph : list hinstr),
  n = m -> subcode (n, l) (1, Ph) -> subcode (m, l) (1, Ph).
Proof. intros n m l Ph -> H. exact H. Qed.

(* One plain instruction at the current pc is one hrun step. *)
Lemma pu_hstep1 : forall Ph s o i,
  subcode (o, [i]) (1, Ph) -> hpc s = o -> herr s = false -> M.pu_plain i = true ->
  Hrun Ph s (hexec s i).
Proof.
  intros Ph s o i Hsc Hpc He Hp.
  assert (Hh : i <> M.HALT) by (intro; subst; discriminate).
  exists 1. split.
  - apply (pu_host_step_at pu_hprop_eqb pu_heval Ph s o i Hsc Hpc He Hh).
  - rewrite (pu_host_trace_at pu_hprop_eqb pu_heval Ph s o i Hsc Hpc He Hh). repeat constructor. exact Hp.
Qed.

Lemma pu_hexec_plain_sub : forall s i, M.pu_plain i = true -> pu_same_sub s (hexec s i).
Proof.
  intros s i Hp. destruct (M.pu_multi_plain_step pu_hprop_eqb pu_heval s i Hp) as [A [B [C [D F]]]].
  repeat split; assumption.
Qed.

(* Distinct positions. *)
Lemma pu_p01_2 : (pos0 : pos 2) <> pos1. Proof. discriminate. Qed.
Lemma pu_p01 : (pos0 : pos 3) <> pos1. Proof. discriminate. Qed.
Lemma pu_p02 : (pos0 : pos 3) <> pos2. Proof. discriminate. Qed.
Lemma pu_p12 : (pos1 : pos 3) <> pos2.
Proof. intro H. apply pos_nxt_inj in H. discriminate. Qed.

Lemma pu_nd1 : forall a : nat, NoDup (vec_list (a ## vec_nil)).
Proof. intro a. simpl. repeat constructor. simpl. tauto. Qed.

Lemma pu_nd2 : forall a b : nat, a <> b -> NoDup (vec_list (a ## b ## vec_nil)).
Proof.
  intros a b H. simpl. constructor; [simpl; intuition | ].
  constructor; [simpl; tauto | constructor].
Qed.

Lemma pu_nd3 : forall a b c : nat, a <> b -> a <> c -> b <> c ->
  NoDup (vec_list (a ## b ## c ## vec_nil)).
Proof.
  intros a b c H1 H2 H3. simpl. constructor; [simpl; intuition |].
  constructor; [simpl; intuition |]. constructor; [simpl; tauto | constructor].
Qed.

(* ================================================================= *)
(* Single INC and DEC.                                                *)
(* ================================================================= *)

Definition pu_hINC (r : nat) (o : nat) : list hinstr := [M.INC r].
Definition pu_hDEC (r j : nat) (o : nat) : list hinstr := [M.DEC r j].

Lemma pu_hINC_spec : forall r o Ph s,
  subcode (o, pu_hINC r o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = S o /\
    hv s' r = S (hv s r) /\ hver s' r = S (hver s r) /\ pu_hframe [r] s s'.
Proof.
  intros r o Ph s Hsc Hpc He.
  exists (hexec s (M.INC r)). split; [apply (pu_hstep1 Ph s o); auto |].
  assert (Hk : M.core_of (hexec s (M.INC r))
               = M.pu_write (M.core_of s) r (S (hv s r)) (S (hpc s)))
    by (simpl; unfold M.pu_cexec; rewrite He; reflexivity).
  rewrite Hk, M.pu_multi_pc_write, (M.pu_multi_val_write (M.core_of s)),
    (M.pu_multi_ver_write (M.core_of s)), Nat.eqb_refl, Hpc.
  split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
  intros d Hd. rewrite Hk, (M.pu_multi_val_write (M.core_of s)), (M.pu_multi_ver_write (M.core_of s)).
  destruct (Nat.eqb_spec r d) as [-> | _]; [exfalso; apply Hd; left; reflexivity | auto].
Qed.

Lemma pu_hDEC_spec : forall r j o Ph s,
  subcode (o, pu_hDEC r j o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ pu_hframe [r] s s' /\
    match hv s r with
    | 0 => hpc s' = S o /\ hv s' r = 0 /\ hver s' r = hver s r
    | S u => hpc s' = j /\ hv s' r = u /\ hver s' r = S (hver s r)
    end.
Proof.
  intros r j o Ph s Hsc Hpc He.
  exists (hexec s (M.DEC r j)). split; [apply (pu_hstep1 Ph s o); auto |].
  destruct (hv s r) as [| u] eqn:Hr.
  - assert (Hk : M.core_of (hexec s (M.DEC r j)) = M.pu_goto (M.core_of s) (S (hpc s)))
      by (simpl; unfold M.pu_cexec; rewrite He, Hr; reflexivity).
    split; [intros d _; rewrite Hk; auto |]. rewrite Hk. simpl. rewrite Hpc, Hr. auto.
  - assert (Hk : M.core_of (hexec s (M.DEC r j)) = M.pu_write (M.core_of s) r u j)
      by (simpl; unfold M.pu_cexec; rewrite He, Hr; reflexivity).
    rewrite Hk, M.pu_multi_pc_write, (M.pu_multi_val_write (M.core_of s)),
      (M.pu_multi_ver_write (M.core_of s)), Nat.eqb_refl.
    split; [| auto].
    intros d Hd. rewrite Hk, (M.pu_multi_val_write (M.core_of s)), (M.pu_multi_ver_write (M.core_of s)).
    destruct (Nat.eqb_spec r d) as [-> | _]; [exfalso; apply Hd; left; reflexivity | auto].
Qed.

(* ================================================================= *)
(* Library blocks, transferred to the host.                           *)
(* ================================================================= *)

Definition pu_hJMP (a p o : nat) : list hinstr :=
  map (pu_lift (vec_pos (a ## vec_nil))) (JMP pos0 p o).
Definition pu_hJZ (x p o : nat) : list hinstr :=
  map (pu_lift (vec_pos (x ## vec_nil))) (JZ pos0 p o).
Definition pu_hZERO (x o : nat) : list hinstr :=
  map (pu_lift (vec_pos (x ## vec_nil))) (MMA_pairing.ZERO pos0 o).
Definition pu_hMOVE (x y o : nat) : list hinstr :=
  map (pu_lift (vec_pos (x ## y ## vec_nil))) (MOVE pos0 pos1 o).
Definition pu_hMOVE2 (x y z o : nat) : list hinstr :=
  map (pu_lift (vec_pos (x ## y ## z ## vec_nil))) (MOVE2 pos0 pos1 pos2 o).
Definition pu_hPACK (a x y o : nat) : list hinstr :=
  map (pu_lift (vec_pos (a ## x ## y ## vec_nil))) (PACK pos0 pos1 pos2 o).
Definition pu_hHALF (a x p o : nat) : list hinstr :=
  map (pu_lift (vec_pos (a ## x ## vec_nil))) (HALF pos0 pos1 p o).
Definition pu_hUNPACK (a x y o : nat) : list hinstr :=
  map (pu_lift (vec_pos (a ## x ## y ## vec_nil))) (UNPACK pos0 pos1 pos2 o).

Lemma pu_hJMP_length : forall a p o, length (pu_hJMP a p o) = JMP_len.
Proof. reflexivity. Qed.
Lemma pu_hJZ_length : forall x p o, length (pu_hJZ x p o) = JZ_len.
Proof. reflexivity. Qed.
Lemma pu_hZERO_length : forall x o, length (pu_hZERO x o) = ZERO_len.
Proof. reflexivity. Qed.
Lemma pu_hMOVE_length : forall x y o, length (pu_hMOVE x y o) = MOVE_len.
Proof. reflexivity. Qed.
Lemma pu_hMOVE2_length : forall x y z o, length (pu_hMOVE2 x y z o) = MOVE2_len.
Proof. reflexivity. Qed.
Lemma pu_hPACK_length : forall a x y o, length (pu_hPACK a x y o) = PACK_len.
Proof. reflexivity. Qed.
Lemma pu_hHALF_length : forall a x p o, length (pu_hHALF a x p o) = HALF_len.
Proof. reflexivity. Qed.
Lemma pu_hUNPACK_length : forall a x y o, length (pu_hUNPACK a x y o) = UNPACK_len.
Proof. reflexivity. Qed.

Lemma pu_hJMP_spec : forall a p o Ph s,
  subcode (o, pu_hJMP a p o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = p /\ hv s' a = hv s a /\ pu_hframe [a] s s'.
Proof.
  intros a p o Ph s Hsc Hpc He.
  destruct (pu_mma_block_host pu_hprop_eqb pu_heval 1 (a ## vec_nil) (pu_nd1 a) o (JMP pos0 p o) Ph s _ _
              Hsc Hpc He (JMP_spec pos0 p _ o)) as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |]. split; [| exact Hf].
  apply (Hv pos0).
Qed.

Lemma pu_hJZ_spec : forall x p o Ph s,
  subcode (o, pu_hJZ x p o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\
    hpc s' = (match hv s x with 0 => p | S _ => JZ_len + o end) /\
    hv s' x = hv s x /\ pu_hframe [x] s s'.
Proof.
  intros x p o Ph s Hsc Hpc He.
  destruct (pu_mma_block_host pu_hprop_eqb pu_heval 1 (x ## vec_nil) (pu_nd1 x) o (JZ pos0 p o) Ph s _ _
              Hsc Hpc He (JZ_spec pos0 p _ o)) as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |]. split; [| exact Hf].
  apply (Hv pos0).
Qed.

Lemma pu_hZERO_spec : forall x o Ph s,
  subcode (o, pu_hZERO x o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = S o /\ hv s' x = 0 /\ pu_hframe [x] s s'.
Proof.
  intros x o Ph s Hsc Hpc He.
  destruct (pu_mma_block_host pu_hprop_eqb pu_heval 1 (x ## vec_nil) (pu_nd1 x) o (MMA_pairing.ZERO pos0 o)
              Ph s _ _ Hsc Hpc He (ZERO_spec pos0 _ o)) as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |]. split; [| exact Hf].
  apply (Hv pos0).
Qed.

Lemma pu_hMOVE_spec : forall x y o Ph s, x <> y ->
  subcode (o, pu_hMOVE x y o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = MOVE_len + o /\
    hv s' y = hv s y + hv s x /\ hv s' x = 0 /\ pu_hframe [x; y] s s'.
Proof.
  intros x y o Ph s Hxy Hsc Hpc He.
  destruct (pu_mma_block_host pu_hprop_eqb pu_heval 2 (x ## y ## vec_nil) (pu_nd2 x y Hxy) o
              (MOVE pos0 pos1 o) Ph s _ _ Hsc Hpc He (MOVE_spec pos0 pos1 _ o pu_p01_2))
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos1) | split; [apply (Hv pos0) | exact Hf]].
Qed.

Lemma pu_hMOVE2_spec : forall x y z o Ph s, x <> y -> x <> z -> y <> z ->
  subcode (o, pu_hMOVE2 x y z o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = MOVE2_len + o /\
    hv s' y = hv s y + hv s x /\ hv s' z = hv s z + hv s x /\ hv s' x = 0 /\
    pu_hframe [x; y; z] s s'.
Proof.
  intros x y z o Ph s H1 H2 H3 Hsc Hpc He.
  destruct (pu_mma_block_host pu_hprop_eqb pu_heval 3 (x ## y ## z ## vec_nil) (pu_nd3 x y z H1 H2 H3) o
              (MOVE2 pos0 pos1 pos2 o) Ph s _ _ Hsc Hpc He
              (MOVE2_spec pos0 pos1 pos2 _ o pu_p01 pu_p02))
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos1) |]. split; [apply (Hv pos2) |].
  split; [apply (Hv pos0) | exact Hf].
Qed.

Lemma pu_hPACK_spec : forall a x y o Ph s, a <> x -> a <> y -> x <> y ->
  subcode (o, pu_hPACK a x y o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = PACK_len + o /\
    hv s' x = pu_pair (hv s y) (hv s x) /\ hv s' y = 0 /\ hv s' a = 0 /\
    pu_hframe [a; x; y] s s'.
Proof.
  intros a x y o Ph s H1 H2 H3 Hsc Hpc He.
  destruct (pu_mma_block_host pu_hprop_eqb pu_heval 3 (a ## x ## y ## vec_nil) (pu_nd3 a x y H1 H2 H3) o
              (PACK pos0 pos1 pos2 o) Ph s _ _ Hsc Hpc He
              (PACK_spec pos0 pos1 pos2 _ o pu_p01 pu_p02 pu_p12))
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos1) |]. split; [apply (Hv pos2) |].
  split; [apply (Hv pos0) | exact Hf].
Qed.

Lemma pu_hHALF_spec : forall a x p o Ph s, a <> x ->
  subcode (o, pu_hHALF a x p o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\
    hpc s' = (if snd (half (hv s x)) then p else HALF_len + o) /\
    hv s' x = fst (half (hv s x)) /\ hv s' a = 0 /\ pu_hframe [a; x] s s'.
Proof.
  intros a x p o Ph s H1 Hsc Hpc He.
  pose proof (HALF_spec pos0 pos1 p (pu_hvec (vec_pos (a ## x ## vec_nil)) (M.core_of s)) o pu_p01_2)
    as Hm.
  simpl in Hm. destruct (half (M.vals (M.core_of s) x)) as [m b] eqn:Eh.
  destruct (pu_mma_block_host pu_hprop_eqb pu_heval 2 (a ## x ## vec_nil) (pu_nd2 a x H1) o
              (HALF pos0 pos1 p o) Ph s _ _ Hsc Hpc He Hm)
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos1) |]. split; [apply (Hv pos0) | exact Hf].
Qed.

Lemma pu_hUNPACK_spec : forall a x y m n o Ph s, a <> x -> a <> y -> x <> y ->
  hv s x = pu_pair m n ->
  subcode (o, pu_hUNPACK a x y o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = UNPACK_len + o /\
    hv s' x = n /\ hv s' y = m /\ hv s' a = 0 /\ pu_hframe [a; x; y] s s'.
Proof.
  intros a x y m n o Ph s H1 H2 H3 Hx Hsc Hpc He.
  assert (Hx' : vec_pos (pu_hvec (vec_pos (a ## x ## y ## vec_nil)) (M.core_of s)) pos1
                = (n + n + 1) * 2 ^ m) by (simpl; rewrite Hx; reflexivity).
  destruct (pu_mma_block_host pu_hprop_eqb pu_heval 3 (a ## x ## y ## vec_nil) (pu_nd3 a x y H1 H2 H3) o
              (UNPACK pos0 pos1 pos2 o) Ph s _ _ Hsc Hpc He
              (@UNPACK_spec 3 pos0 pos1 pos2 m n _ o Hx' pu_p01 pu_p02 pu_p12))
    as (s' & Hr & Hp & Hv & Hf).
  exists s'. split; [exact Hr |]. split; [exact Hp |].
  split; [apply (Hv pos1) |]. split; [apply (Hv pos2) |].
  split; [apply (Hv pos0) | exact Hf].
Qed.

(* UNPACK on 0 jumps to address 0, where no host instruction lives; the
   fetch loop guards every UNPACK with a JZ so this case never runs. *)
Lemma pu_hUNPACK0_spec : forall a x y o Ph s, a <> x -> a <> y -> x <> y ->
  hv s x = 0 ->
  subcode (o, pu_hUNPACK a x y o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = 0 /\
    hv s' a = hv s a /\ hv s' x = 0 /\ hv s' y = hv s y /\ pu_hframe [a; x; y] s s'.
Proof.
  intros a x y o Ph s H1 H2 H3 Hx Hsc Hpc He.
  assert (Hx' : vec_pos (pu_hvec (vec_pos (a ## x ## y ## vec_nil)) (M.core_of s)) pos1 = 0)
    by (simpl; exact Hx).
  destruct (pu_mma_block_host pu_hprop_eqb pu_heval 3 (a ## x ## y ## vec_nil) (pu_nd3 a x y H1 H2 H3) o
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

Lemma pu_hrun_err : forall Ph (s s' : hstate), Hrun Ph s s' -> herr s = false -> herr s' = false.
Proof.
  intros Ph s s' H He. destruct (pu_hrun_same_sub _ _ _ _ _ H) as [_ [_ [E _]]]. congruence.
Qed.

(* Split a placement of l1 ++ l2 into placements of l1 and of l2. *)
Ltac pu_sc_split H H1 H2 :=
  match type of H with
  | subcode (?o, ?l1 ++ ?l2) (1, ?Ph) =>
      pose proof (pu_sc_app_l o l1 l2 Ph H) as H1;
      pose proof (pu_sc_app_r o (length l1 + o) l1 l2 Ph eq_refl H) as H2
  end.

(* The trap latch stays down along a chain of hrun hypotheses. *)
Ltac pu_herr_tac :=
  first [ assumption
        | eapply pu_hrun_err; [eassumption | pu_herr_tac] ].

(* An hrun from the first state to the last along hrun hypotheses. *)
Ltac pu_chain :=
  first [ apply pu_hrun_refl
        | eassumption
        | eapply pu_hrun_trans; [eassumption | pu_chain] ].

(* For register r, record the value and version equation of every frame
   hypothesis whose list does not contain r. *)
Ltac pu_frames r :=
  repeat match goal with
  | F : pu_hframe ?rs ?a ?b |- _ =>
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
Ltac pu_solve_frame :=
  let r := fresh "r" in
  let Hr := fresh "Hr" in
  intros r Hr; simpl in Hr; pu_frames r; split; congruence.

Ltac pu_nodup_neqs H :=
  repeat (let Hn := fresh "Hn" in
          let H' := fresh "Hd" in
          destruct (proj1 (NoDup_cons_iff _ _) H) as [Hn H']; clear H; rename H' into H;
          simpl in Hn).

(* ================================================================= *)
(* COPY: y := x and t := 0, x keeps its value.                        *)
(* ================================================================= *)

Definition pu_COPY_len : nat := 2 + MOVE2_len + MOVE_len.

Definition pu_hCOPY (x y t o : nat) : list hinstr :=
  pu_hZERO y o ++ pu_hZERO t (1 + o) ++ pu_hMOVE2 x y t (2 + o) ++ pu_hMOVE t x (2 + MOVE2_len + o).

Lemma pu_hCOPY_length : forall x y t o, length (pu_hCOPY x y t o) = pu_COPY_len.
Proof. reflexivity. Qed.

Theorem pu_hCOPY_spec : forall x y t o Ph s, x <> y -> x <> t -> y <> t ->
  subcode (o, pu_hCOPY x y t o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_COPY_len + o /\
    hv s' x = hv s x /\ hv s' y = hv s x /\ hv s' t = 0 /\ pu_hframe [x; y; t] s s'.
Proof.
  intros x y t o Ph s Hxy Hxt Hyt Hsc Hpc He. unfold pu_hCOPY in Hsc.
  pu_sc_split Hsc S0 Hsc1.
  destruct (pu_hZERO_spec y o Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & F1).
  pu_sc_split Hsc1 S1 Hsc2.
  destruct (pu_hZERO_spec t (1 + o) Ph s1 S1 P1 ltac:(pu_herr_tac)) as (s2 & R2 & P2 & V2 & F2).
  pu_sc_split Hsc2 S2 S3.
  destruct (pu_hMOVE2_spec x y t (2 + o) Ph s2 Hxy Hxt Hyt S2 P2 ltac:(pu_herr_tac))
    as (s3 & R3 & P3 & V3y & V3t & V3x & F3).
  destruct (pu_hMOVE_spec t x (2 + MOVE2_len + o) Ph s3 (not_eq_sym Hxt) S3 P3 ltac:(pu_herr_tac))
    as (s4 & R4 & P4 & V4x & V4t & F4).
  exists s4. split; [pu_chain |]. split; [rewrite P4; reflexivity |].
  pu_frames x. pu_frames y. pu_frames t.
  split; [lia |]. split; [lia |]. split; [lia |].
  pu_solve_frame.
Qed.

(* ================================================================= *)
(* DISP: a k-way jump on a counter, by a chain of DEC instructions.   *)
(* ================================================================= *)

(* Stage i at address o + 3i: DEC x to the next stage; when x is 0, jump
   to the i-th target (with t as the jump's helper, restored). *)
Fixpoint pu_hDISP (x t : nat) (ps : list nat) (o : nat) : list hinstr :=
  match ps with
  | [] => []
  | p :: ps' => M.DEC x (3 + o) :: pu_hJMP t p (1 + o) ++ pu_hDISP x t ps' (3 + o)
  end.

Lemma pu_hDISP_length : forall x t ps o, length (pu_hDISP x t ps o) = 3 * length ps.
Proof.
  intros x t ps. induction ps as [| p ps IH]; intro o; [reflexivity |].
  simpl. rewrite IH. lia.
Qed.

Theorem pu_hDISP_spec : forall x t ps o Ph s, x <> t ->
  subcode (o, pu_hDISP x t ps o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ pu_hframe [x; t] s s' /\ hv s' t = hv s t /\
    (hv s x < length ps -> hpc s' = nth (hv s x) ps 0 /\ hv s' x = 0) /\
    (length ps <= hv s x -> hpc s' = 3 * length ps + o /\ hv s' x = hv s x - length ps).
Proof.
  intros x t ps. induction ps as [| p ps IH]; intros o Ph s Hxt Hsc Hpc He.
  - exists s. split; [apply pu_hrun_refl |]. split; [apply pu_hframe_refl |].
    split; [reflexivity |]. simpl. split; [lia | intros _; split; lia].
  - cbn [pu_hDISP] in Hsc. pose proof (pu_sc_cons_l _ _ _ _ Hsc) as S0.
    pose proof (pu_sc_cons_r _ _ _ _ Hsc) as Hsc1.
    destruct (pu_hDEC_spec x (3 + o) o Ph s S0 Hpc He) as (s1 & R1 & F1 & D1).
    destruct (hv s x) as [| u] eqn:Hx.
    + destruct D1 as (P1 & V1 & W1).
      pu_sc_split Hsc1 S1 Hsc2.
      destruct (pu_hJMP_spec t p (1 + o) Ph s1 S1 P1 ltac:(pu_herr_tac)) as (s2 & R2 & P2 & V2 & F2).
      exists s2. split; [pu_chain |]. split; [pu_solve_frame |].
      pu_frames t. pu_frames x. split; [congruence |]. simpl.
      split; [intros _; split; [exact P2 | lia] | lia].
    + destruct D1 as (P1 & V1 & W1).
      pu_sc_split Hsc1 S1 S2.
      destruct (IH (3 + o) Ph s1 Hxt S2 P1 ltac:(pu_herr_tac)) as (s2 & R2 & F2 & T2 & L2 & G2).
      rewrite V1 in L2, G2.
      exists s2. split; [pu_chain |]. split; [pu_solve_frame |].
      pu_frames t. split; [congruence |]. simpl. split.
      * intros Hl. apply L2. lia.
      * intros Hl. destruct (G2 ltac:(lia)) as [G2a G2b]. split; lia.
Qed.

(* ================================================================= *)
(* EQC: go to p when x = c, else fall through; x keeps its value.     *)
(* ================================================================= *)

Definition pu_EQC_fail (c o : nat) : nat := pu_COPY_len + 3 * S c + o.
Definition pu_EQC_len (c : nat) : nat := pu_COPY_len + 3 * S c + 1.

Definition pu_hEQC (x c t u p o : nat) : list hinstr :=
  pu_hCOPY x t u o ++ pu_hDISP t u (repeat (pu_EQC_fail c o) c ++ [p]) (pu_COPY_len + o) ++
  pu_hZERO t (pu_EQC_fail c o).

Lemma pu_hEQC_length : forall x c t u p o, length (pu_hEQC x c t u p o) = pu_EQC_len c.
Proof.
  intros. unfold pu_hEQC, pu_EQC_len. rewrite !app_length, pu_hCOPY_length, pu_hDISP_length, app_length,
    repeat_length, pu_hZERO_length. simpl. unfold ZERO_len, DEC_len. lia.
Qed.

Lemma pu_nth_repeat_last : forall c f p v, v < S c ->
  nth v (repeat f c ++ [p]) 0 = if Nat.eqb v c then p else f.
Proof.
  intros c f p v Hv. destruct (Nat.eqb_spec v c) as [-> | Hne].
  - rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length, Nat.sub_diag. reflexivity.
  - rewrite app_nth1 by (rewrite repeat_length; lia).
    rewrite (nth_indep _ 0 f) by (rewrite repeat_length; lia). apply nth_repeat.
Qed.

Theorem pu_hEQC_spec : forall x c t u p o Ph s, x <> t -> x <> u -> t <> u ->
  subcode (o, pu_hEQC x c t u p o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ pu_hframe [x; t; u] s s' /\
    hv s' x = hv s x /\ hv s' t = 0 /\ hv s' u = 0 /\
    hpc s' = (if Nat.eqb (hv s x) c then p else pu_EQC_len c + o).
Proof.
  intros x c t u p o Ph s Hxt Hxu Htu Hsc Hpc He. unfold pu_hEQC in Hsc.
  pu_sc_split Hsc S0 Hsc1.
  destruct (pu_hCOPY_spec x t u o Ph s Hxt Hxu Htu S0 Hpc He)
    as (s1 & R1 & P1 & V1x & V1t & V1u & F1).
  pu_sc_split Hsc1 S1 Hsc2.
  destruct (pu_hDISP_spec t u (repeat (pu_EQC_fail c o) c ++ [p]) (pu_COPY_len + o) Ph s1 Htu S1
              ltac:(rewrite P1; reflexivity) ltac:(pu_herr_tac))
    as (s2 & R2 & F2 & T2 & L2 & G2).
  rewrite app_length, repeat_length in L2, G2. simpl in L2, G2.
  assert (S3 : subcode (pu_EQC_fail c o, pu_hZERO t (pu_EQC_fail c o)) (1, Ph)).
  { refine (pu_sc_pos _ _ _ _ _ Hsc2). rewrite pu_hDISP_length, app_length, repeat_length,
      pu_hCOPY_length. unfold pu_EQC_fail. simpl. lia. }
  rewrite V1t in L2, G2.
  destruct (Nat.eqb_spec (hv s x) c) as [Heq | Hne].
  - destruct (L2 ltac:(lia)) as [P2 V2]. rewrite pu_nth_repeat_last in P2 by lia.
    rewrite Heq, Nat.eqb_refl in P2.
    exists s2. split; [pu_chain |]. split; [pu_solve_frame |].
    pu_frames x. split; [congruence |]. split; [exact V2 |]. split; [congruence | exact P2].
  - assert (P2 : hpc s2 = pu_EQC_fail c o).
    { destruct (Nat.lt_ge_cases (hv s x) (S c)) as [Hl | Hl].
      - destruct (L2 ltac:(lia)) as [P2 _]. rewrite pu_nth_repeat_last in P2 by lia.
        destruct (Nat.eqb_spec (hv s x) c); [contradiction | exact P2].
      - destruct (G2 ltac:(lia)) as [P2 _]. rewrite P2.
        unfold pu_EQC_fail, pu_COPY_len, MOVE2_len, MOVE_len, JMP_len, INC_len, DEC_len. lia. }
    destruct (pu_hZERO_spec t (pu_EQC_fail c o) Ph s2 S3 P2 ltac:(pu_herr_tac)) as (s3 & R3 & P3 & V3 & F3).
    exists s3. split; [pu_chain |]. split; [pu_solve_frame |].
    pu_frames x. pu_frames u. split; [congruence |]. split; [exact V3 |]. split; [congruence |].
    rewrite P3. unfold pu_EQC_fail, pu_EQC_len. lia.
Qed.

(* ================================================================= *)
(* EQR: go to p when x = y, else fall through; x, y keep values.      *)
(* ================================================================= *)

Definition pu_EQR_loop (o : nat) : nat := 2 * pu_COPY_len + o.
Definition pu_EQR_ne (o : nat) : nat := 2 * pu_COPY_len + 10 + o.
Definition pu_EQR_len : nat := 2 * pu_COPY_len + 12.

(* After the two copies, t1 and t2 count down together. t1 reaching 0
   first means x <= y: equal exactly when t2 is 0 too. t2 reaching 0
   first means x > y. *)
Definition pu_hEQR (x y t1 t2 u p o : nat) : list hinstr :=
  pu_hCOPY x t1 u o ++ pu_hCOPY y t2 u (pu_COPY_len + o) ++
  [M.DEC t1 (7 + pu_EQR_loop o)] ++
  pu_hJZ t2 p (1 + pu_EQR_loop o) ++
  pu_hJMP u (pu_EQR_ne o) (5 + pu_EQR_loop o) ++
  [M.DEC t2 (pu_EQR_loop o)] ++
  pu_hJMP u (pu_EQR_ne o) (8 + pu_EQR_loop o) ++
  pu_hZERO t1 (pu_EQR_ne o) ++ pu_hZERO t2 (1 + pu_EQR_ne o).

Lemma pu_hEQR_length : forall x y t1 t2 u p o, length (pu_hEQR x y t1 t2 u p o) = pu_EQR_len.
Proof. reflexivity. Qed.

Lemma pu_hEQR_loop : forall x y t1 t2 u p o Ph, t1 <> t2 -> t1 <> u -> t2 <> u ->
  subcode (o, pu_hEQR x y t1 t2 u p o) (1, Ph) ->
  forall a b s, hpc s = pu_EQR_loop o -> herr s = false -> hv s t1 = a -> hv s t2 = b ->
  exists s', Hrun Ph s s' /\ pu_hframe [t1; t2; u] s s' /\ hv s' u = hv s u /\
    (a = b -> hpc s' = p /\ hv s' t1 = 0 /\ hv s' t2 = 0) /\
    (a <> b -> hpc s' = pu_EQR_ne o).
Proof.
  intros x y t1 t2 u p o Ph H12 H1u H2u Hsc. unfold pu_hEQR in Hsc.
  pu_sc_split Hsc X0 Hsc1. pu_sc_split Hsc1 X1 Hsc2. pu_sc_split Hsc2 SD1 Hsc3.
  pu_sc_split Hsc3 SJZ Hsc4. pu_sc_split Hsc4 SJ1 Hsc5. pu_sc_split Hsc5 SD2 Hsc6.
  pu_sc_split Hsc6 SJ2 X2. clear X0 X1 X2 Hsc Hsc1 Hsc2 Hsc3 Hsc4 Hsc5 Hsc6.
  induction a as [| a IH]; intros b s Hpc He Ha Hb.
  - destruct (pu_hDEC_spec t1 (7 + pu_EQR_loop o) (pu_EQR_loop o) Ph s SD1 Hpc He) as (s1 & R1 & F1 & D1).
    rewrite Ha in D1. destruct D1 as (P1 & V1 & W1).
    destruct (pu_hJZ_spec t2 p (1 + pu_EQR_loop o) Ph s1 SJZ P1 ltac:(pu_herr_tac))
      as (s2 & R2 & P2 & V2 & F2).
    pu_frames t2. rewrite Fv, Hb in P2.
    destruct b as [| b].
    + exists s2. split; [pu_chain |]. split; [pu_solve_frame |]. pu_frames u. pu_frames t1.
      split; [congruence |]. split; [intros _; split; [exact P2 | split; congruence] | lia].
    + destruct (pu_hJMP_spec u (pu_EQR_ne o) (5 + pu_EQR_loop o) Ph s2 SJ1 P2 ltac:(pu_herr_tac))
        as (s3 & R3 & P3 & V3 & F3).
      exists s3. split; [pu_chain |]. split; [pu_solve_frame |]. pu_frames u.
      split; [congruence |]. split; [lia | intros _; exact P3].
  - destruct (pu_hDEC_spec t1 (7 + pu_EQR_loop o) (pu_EQR_loop o) Ph s SD1 Hpc He) as (s1 & R1 & F1 & D1).
    rewrite Ha in D1. destruct D1 as (P1 & V1 & W1).
    destruct (pu_hDEC_spec t2 (pu_EQR_loop o) (7 + pu_EQR_loop o) Ph s1 SD2 P1 ltac:(pu_herr_tac))
      as (s2 & R2 & F2 & D2).
    pu_frames t2. rewrite Fv, Hb in D2.
    destruct b as [| b].
    + destruct D2 as (P2 & V2 & W2).
      destruct (pu_hJMP_spec u (pu_EQR_ne o) (8 + pu_EQR_loop o) Ph s2 SJ2 P2 ltac:(pu_herr_tac))
        as (s3 & R3 & P3 & V3 & F3).
      exists s3. split; [pu_chain |]. split; [pu_solve_frame |]. pu_frames u.
      split; [congruence |]. split; [lia | intros _; exact P3].
    + destruct D2 as (P2 & V2 & W2).
      pu_frames t1.
      destruct (IH b s2 P2 ltac:(pu_herr_tac) ltac:(congruence) V2) as (s3 & R3 & F3 & U3 & E3 & N3).
      exists s3. split; [pu_chain |]. split; [pu_solve_frame |]. pu_frames u.
      split; [congruence |]. split.
      * intros Hab. apply E3. lia.
      * intros Hab. apply N3. lia.
Qed.

Theorem pu_hEQR_spec : forall x y t1 t2 u p o Ph s, NoDup [x; y; t1; t2; u] ->
  subcode (o, pu_hEQR x y t1 t2 u p o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ pu_hframe [x; y; t1; t2; u] s s' /\
    hv s' x = hv s x /\ hv s' y = hv s y /\
    hv s' t1 = 0 /\ hv s' t2 = 0 /\ hv s' u = 0 /\
    hpc s' = (if Nat.eqb (hv s x) (hv s y) then p else pu_EQR_len + o).
Proof.
  intros x y t1 t2 u p o Ph s Hnd Hsc Hpc He. pose proof Hsc as Hsc0.
  pu_nodup_neqs Hnd. unfold pu_hEQR in Hsc.
  pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 S1 Hsc2.
  destruct (pu_hCOPY_spec x t1 u o Ph s ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) S0 Hpc He)
    as (s1 & R1 & P1 & V1x & V1t & V1u & F1).
  destruct (pu_hCOPY_spec y t2 u (pu_COPY_len + o) Ph s1 ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) S1 P1
              ltac:(pu_herr_tac)) as (s2 & R2 & P2 & V2y & V2t & V2u & F2).
  pu_frames x. pu_frames y. pu_frames t1.
  destruct (pu_hEQR_loop x y t1 t2 u p o Ph ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) Hsc0
              (hv s x) (hv s y) s2 P2 ltac:(pu_herr_tac) ltac:(congruence) ltac:(congruence))
    as (s3 & R3 & F3 & U3 & E3 & N3).
  destruct (Nat.eqb_spec (hv s x) (hv s y)) as [Heq | Hne].
  - destruct (E3 Heq) as (P3 & T13 & T23).
    exists s3. split; [pu_chain |]. split; [pu_solve_frame |]. pu_frames x. pu_frames y.
    split; [congruence |]. split; [congruence |]. split; [exact T13 |]. split; [exact T23 |].
    split; [congruence | exact P3].
  - pose proof (N3 Hne) as P3.
    pu_sc_split Hsc2 X3 Hsc3. pu_sc_split Hsc3 X4 Hsc4. pu_sc_split Hsc4 X5 Hsc5.
    pu_sc_split Hsc5 X6 Hsc6. pu_sc_split Hsc6 X7 Hsc7. pu_sc_split Hsc7 SZ1 SZ2.
    destruct (pu_hZERO_spec t1 (pu_EQR_ne o) Ph s3 SZ1 P3 ltac:(pu_herr_tac)) as (s4 & R4 & P4 & V4 & F4).
    destruct (pu_hZERO_spec t2 (1 + pu_EQR_ne o) Ph s4 SZ2 P4 ltac:(pu_herr_tac))
      as (s5 & R5 & P5 & V5 & F5).
    exists s5. split; [pu_chain |]. split; [pu_solve_frame |].
    pu_frames x. pu_frames y. pu_frames t1. pu_frames u.
    split; [congruence |]. split; [congruence |]. split; [congruence |]. split; [exact V5 |].
    split; [congruence |]. rewrite P5. reflexivity.
Qed.

(* ================================================================= *)
(* FETCH: read the code of the current guest instruction.             *)
(* ================================================================= *)

(* Registers: prog holds the program code and gpc the guest pc (both keep
   their values); w, kk, h, a, t are scratch. Layout:

     o                 w := prog              (COPY, helper t)
     pu_COPY_len + o      kk := gpc              (COPY, helper t)
     2 pu_COPY_len + o    JZ kk pz               guest pc 0: exit to pz
                       DEC kk (to the loop)   kk := gpc - 1
     loop              JZ w pe                code exhausted: exit to pe
                       UNPACK a w h           h := head, w := tail
                       JZ kk end              kk = 0: h is the instruction
                       DEC kk loop            one more instruction to skip
     end = pu_FETCH_len + o                                                   *)

Definition pu_FETCH_loop (o : nat) : nat := 2 * pu_COPY_len + JZ_len + 1 + o.
Definition pu_FETCH_len : nat := 2 * pu_COPY_len + 3 * JZ_len + UNPACK_len + 2.

Definition pu_hFETCH (prog gpc w kk h a t pz pe o : nat) : list hinstr :=
  pu_hCOPY prog w t o ++
  pu_hCOPY gpc kk t (pu_COPY_len + o) ++
  pu_hJZ kk pz (2 * pu_COPY_len + o) ++
  [M.DEC kk (pu_FETCH_loop o)] ++
  pu_hJZ w pe (pu_FETCH_loop o) ++
  pu_hUNPACK a w h (JZ_len + pu_FETCH_loop o) ++
  pu_hJZ kk (pu_FETCH_len + o) (JZ_len + UNPACK_len + pu_FETCH_loop o) ++
  [M.DEC kk (pu_FETCH_loop o)].

Lemma pu_hFETCH_length : forall prog gpc w kk h a t pz pe o,
  length (pu_hFETCH prog gpc w kk h a t pz pe o) = pu_FETCH_len.
Proof. reflexivity. Qed.

Lemma pu_fetch_code_zero : forall k, pu_fetch_code 0 k = None.
Proof. intros [| k]; reflexivity. Qed.

Lemma pu_fetch_code_0 : forall c, pu_fetch_code c 0 = option_map fst (pu_unpair c).
Proof. reflexivity. Qed.

Lemma pu_hFETCH_loop : forall prog gpc w kk h a t pz pe o Ph,
  w <> kk -> w <> h -> w <> a -> kk <> h -> kk <> a -> h <> a ->
  subcode (o, pu_hFETCH prog gpc w kk h a t pz pe o) (1, Ph) ->
  forall k s, hpc s = pu_FETCH_loop o -> herr s = false -> hv s kk = k ->
  exists s', Hrun Ph s s' /\ pu_hframe [w; kk; h; a] s s' /\
    match pu_fetch_code (hv s w) k with
    | Some c => hpc s' = pu_FETCH_len + o /\ hv s' h = c /\ hv s' kk = 0 /\ hv s' a = 0 /\
                hv s' w = pu_skip_code (hv s w) (S k)
    | None => hpc s' = pe /\ hv s' w = 0
    end.
Proof.
  intros prog gpc w kk h a t pz pe o Ph Hwk Hwh Hwa Hkh Hka Hha Hsc. unfold pu_hFETCH in Hsc.
  pu_sc_split Hsc X0 Hsc1. pu_sc_split Hsc1 X1 Hsc2. pu_sc_split Hsc2 X2 Hsc3. pu_sc_split Hsc3 X3 Hsc4.
  pu_sc_split Hsc4 SJW Hsc5. pu_sc_split Hsc5 SUN Hsc6. pu_sc_split Hsc6 SJK SDK.
  clear X0 X1 X2 X3 Hsc Hsc1 Hsc2 Hsc3 Hsc4 Hsc5 Hsc6.
  induction k as [| k IH]; intros s Hpc He Hk;
    destruct (pu_hJZ_spec w pe (pu_FETCH_loop o) Ph s SJW Hpc He) as (s1 & R1 & P1 & V1 & F1);
    destruct (hv s w) as [| c'] eqn:Hw; try rewrite Hw in P1.
  - rewrite pu_fetch_code_zero. exists s1. split; [pu_chain |]. split; [pu_solve_frame |].
    split; [exact P1 | congruence].
  - destruct (pu_unpair_some (S c') (Nat.lt_0_succ c')) as (m & n & Hun & Hpair).
    destruct (pu_hUNPACK_spec a w h m n (JZ_len + pu_FETCH_loop o) Ph s1
                ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) SUN P1
                ltac:(pu_herr_tac))
      as (s2 & R2 & P2 & V2w & V2h & V2a & F2).
    pu_frames kk.
    destruct (pu_hJZ_spec kk (pu_FETCH_len + o) (JZ_len + UNPACK_len + pu_FETCH_loop o) Ph s2 SJK P2
                ltac:(pu_herr_tac)) as (s3 & R3 & P3 & V3 & F3).
    assert (K2 : hv s2 kk = 0) by congruence. rewrite K2 in P3.
    rewrite pu_fetch_code_0, Hun. cbn [option_map fst].
    exists s3. split; [pu_chain |]. split; [pu_solve_frame |].
    pu_frames h. pu_frames a. pu_frames w.
    split; [exact P3 |]. split; [congruence |]. split; [congruence |]. split; [congruence |].
    rewrite pu_skip_code_S, Hun. cbn [pu_skip_code]. congruence.
  - rewrite pu_fetch_code_zero. exists s1. split; [pu_chain |]. split; [pu_solve_frame |].
    split; [exact P1 | congruence].
  - destruct (pu_unpair_some (S c') (Nat.lt_0_succ c')) as (m & n & Hun & Hpair).
    destruct (pu_hUNPACK_spec a w h m n (JZ_len + pu_FETCH_loop o) Ph s1
                ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) SUN P1
                ltac:(pu_herr_tac))
      as (s2 & R2 & P2 & V2w & V2h & V2a & F2).
    pu_frames kk.
    destruct (pu_hJZ_spec kk (pu_FETCH_len + o) (JZ_len + UNPACK_len + pu_FETCH_loop o) Ph s2 SJK P2
                ltac:(pu_herr_tac)) as (s3 & R3 & P3 & V3 & F3).
    assert (K2 : hv s2 kk = S k) by congruence. rewrite K2 in P3.
    destruct (pu_hDEC_spec kk (pu_FETCH_loop o) (JZ_len + (JZ_len + UNPACK_len + pu_FETCH_loop o)) Ph s3
                SDK P3 ltac:(pu_herr_tac)) as (s4 & R4 & F4 & D4).
    assert (K3 : hv s3 kk = S k) by congruence. rewrite K3 in D4.
    destruct D4 as (P4 & V4 & W4).
    destruct (IH s4 P4 ltac:(pu_herr_tac) V4) as (s5 & R5 & F5 & G5).
    pu_frames w.
    assert (W4' : hv s4 w = n) by congruence. rewrite W4' in G5.
    rewrite pu_fetch_code_S, Hun, pu_skip_code_S, Hun.
    exists s5. split; [pu_chain |]. split; [pu_solve_frame |]. exact G5.
Qed.

Theorem pu_hFETCH_spec : forall prog gpc w kk h a t pz pe o Ph s,
  NoDup [prog; gpc; w; kk; h; a; t] ->
  subcode (o, pu_hFETCH prog gpc w kk h a t pz pe o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ pu_hframe [prog; gpc; w; kk; h; a; t] s s' /\
    hv s' prog = hv s prog /\ hv s' gpc = hv s gpc /\ hv s' t = 0 /\
    match hv s gpc with
    | 0 => hpc s' = pz /\ hv s' kk = 0 /\ hv s' w = hv s prog
    | S k =>
        match pu_fetch_code (hv s prog) k with
        | Some c => hpc s' = pu_FETCH_len + o /\ hv s' h = c /\ hv s' kk = 0 /\ hv s' a = 0 /\
                    hv s' w = pu_skip_code (hv s prog) (S k)
        | None => hpc s' = pe /\ hv s' w = 0
        end
    end.
Proof.
  intros prog gpc w kk h a t pz pe o Ph s Hnd Hsc Hpc He. pose proof Hsc as Hsc0.
  pu_nodup_neqs Hnd. unfold pu_hFETCH in Hsc.
  pu_sc_split Hsc S0 Hsc1. pu_sc_split Hsc1 S1 Hsc2. pu_sc_split Hsc2 S2 Hsc3. pu_sc_split Hsc3 S3 Hsc4.
  destruct (pu_hCOPY_spec prog w t o Ph s ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) S0 Hpc He)
    as (s1 & R1 & P1 & V1p & V1w & V1t & F1).
  destruct (pu_hCOPY_spec gpc kk t (pu_COPY_len + o) Ph s1 ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) S1 P1
              ltac:(pu_herr_tac)) as (s2 & R2 & P2 & V2g & V2k & V2t & F2).
  destruct (pu_hJZ_spec kk pz (2 * pu_COPY_len + o) Ph s2 S2 P2 ltac:(pu_herr_tac))
    as (s3 & R3 & P3 & V3 & F3).
  pu_frames prog. pu_frames gpc. pu_frames w. pu_frames t.
  assert (K2 : hv s2 kk = hv s gpc) by congruence. rewrite K2 in P3.
  destruct (hv s gpc) as [| k] eqn:Hg.
  - exists s3. split; [pu_chain |]. split; [pu_solve_frame |].
    split; [congruence |]. split; [congruence |]. split; [congruence |].
    split; [exact P3 |]. split; congruence.
  - destruct (pu_hDEC_spec kk (pu_FETCH_loop o) (JZ_len + (2 * pu_COPY_len + o)) Ph s3 S3 P3
                ltac:(pu_herr_tac)) as (s4 & R4 & F4 & D4).
    assert (K3 : hv s3 kk = S k) by congruence. rewrite K3 in D4.
    destruct D4 as (P4 & V4 & W4).
    destruct (pu_hFETCH_loop prog gpc w kk h a t pz pe o Ph ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence)
                ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) Hsc0 k s4 P4 ltac:(pu_herr_tac) V4)
      as (s5 & R5 & F5 & G5).
    pu_frames prog. pu_frames gpc. pu_frames w. pu_frames t.
    assert (W4' : hv s4 w = hv s prog) by congruence. rewrite W4' in G5.
    exists s5. split; [pu_chain |]. split; [pu_solve_frame |].
    split; [congruence |]. split; [congruence |]. split; [congruence |]. exact G5.
Qed.

(* FETCH on the code of a guest program. *)
Corollary pu_hFETCH_guest : forall (P : list E.instr) prog gpc w kk h a t pz pe o Ph s k,
  NoDup [prog; gpc; w; kk; h; a; t] ->
  subcode (o, pu_hFETCH prog gpc w kk h a t pz pe o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s prog = pu_prog_code P -> hv s gpc = S k ->
  exists s', Hrun Ph s s' /\ pu_hframe [prog; gpc; w; kk; h; a; t] s s' /\
    hv s' prog = pu_prog_code P /\ hv s' gpc = S k /\ hv s' t = 0 /\
    match nth_error P k with
    | Some i => hpc s' = pu_FETCH_len + o /\ hv s' h = pu_icode i /\ hv s' kk = 0 /\
                hv s' a = 0 /\ hv s' w = pu_prog_code (skipn (S k) P)
    | None => hpc s' = pe /\ hv s' w = 0
    end.
Proof.
  intros P prog gpc w kk h a t pz pe o Ph s k Hnd Hsc Hpc He Hp Hg.
  destruct (pu_hFETCH_spec prog gpc w kk h a t pz pe o Ph s Hnd Hsc Hpc He)
    as (s' & R & F & Vp & Vg & Vt & G).
  rewrite Hg, Hp, pu_fetch_code_prog, pu_skip_code_prog in G.
  exists s'. split; [exact R |]. split; [exact F |].
  split; [congruence |]. split; [congruence |]. split; [exact Vt |].
  destruct (nth_error P k); exact G.
Qed.

(* Guest pc 0 on the code of a guest program: the FETCH exits to pz. *)
Corollary pu_hFETCH_guest_pc0 : forall (P : list E.instr) prog gpc w kk h a t pz pe o Ph s,
  NoDup [prog; gpc; w; kk; h; a; t] ->
  subcode (o, pu_hFETCH prog gpc w kk h a t pz pe o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s prog = pu_prog_code P -> hv s gpc = 0 ->
  exists s', Hrun Ph s s' /\ pu_hframe [prog; gpc; w; kk; h; a; t] s s' /\
    hv s' prog = pu_prog_code P /\ hv s' gpc = 0 /\ hv s' t = 0 /\ hpc s' = pz.
Proof.
  intros P prog gpc w kk h a t pz pe o Ph s Hnd Hsc Hpc He Hp Hg.
  destruct (pu_hFETCH_spec prog gpc w kk h a t pz pe o Ph s Hnd Hsc Hpc He)
    as (s' & R & F & Vp & Vg & Vt & G).
  rewrite Hg in G. destruct G as [G _].
  exists s'. split; [exact R |]. split; [exact F |]. split; [congruence |].
  split; [congruence |]. split; [exact Vt | exact G].
Qed.

(* ================================================================= *)
(* BUMP: a slot keeps its value, its version goes up by 2, and its    *)
(* mirror is cleared.                                                  *)
(* ================================================================= *)

Definition pu_BUMP_len : nat := 3.

Definition pu_hBUMP (sl mp o : nat) : list hinstr :=
  [M.INC sl; M.DEC sl (2 + o)] ++ pu_hZERO mp (2 + o).

Lemma pu_hBUMP_length : forall sl mp o, length (pu_hBUMP sl mp o) = pu_BUMP_len.
Proof. reflexivity. Qed.

Theorem pu_hBUMP_spec : forall sl mp o Ph s, sl <> mp ->
  subcode (o, pu_hBUMP sl mp o) (1, Ph) -> hpc s = o -> herr s = false ->
  exists s', Hrun Ph s s' /\ hpc s' = pu_BUMP_len + o /\
    hv s' sl = hv s sl /\ hver s' sl = 2 + hver s sl /\ hv s' mp = 0 /\
    pu_hframe [sl; mp] s s'.
Proof.
  intros sl mp o Ph s Hne Hsc Hpc He. unfold pu_hBUMP in Hsc.
  pu_sc_split Hsc S01 S2.
  pose proof (pu_sc_cons_l _ _ _ _ S01) as S0. pose proof (pu_sc_cons_r _ _ _ _ S01) as S1.
  destruct (pu_hINC_spec sl o Ph s S0 Hpc He) as (s1 & R1 & P1 & V1 & W1 & F1).
  destruct (pu_hDEC_spec sl (2 + o) (S o) Ph s1 S1 P1 ltac:(pu_herr_tac)) as (s2 & R2 & F2 & D2).
  rewrite V1 in D2. destruct D2 as (P2 & V2 & W2).
  destruct (pu_hZERO_spec mp (2 + o) Ph s2 S2 P2 ltac:(pu_herr_tac)) as (s3 & R3 & P3 & V3 & F3).
  exists s3. split; [pu_chain |]. split; [exact P3 |].
  pu_frames sl. split; [congruence |]. split; [lia |]. split; [exact V3 |].
  pu_solve_frame.
Qed.

(* ================================================================= *)
(* The three record moves: CHECK PSlot r, COMMIT PSlot r, CERTIFY.    *)
(* ================================================================= *)

Definition pu_hCHECK (r o : nat) : list hinstr := [M.CHECK PSlot r].
Definition pu_hCOMMIT (r o : nat) : list hinstr := [M.COMMIT PSlot r].
Definition pu_hCERTIFY (o : nat) : list hinstr := [M.CERTIFY].

Lemma pu_hCHECK_step : forall r o Ph s,
  subcode (o, pu_hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hrun_prog 1 Ph s = hexec s (M.CHECK PSlot r) /\ htrace 1 Ph s = [M.CHECK PSlot r].
Proof.
  intros r o Ph s Hsc Hpc He. split.
  - apply (pu_host_step_at pu_hprop_eqb pu_heval Ph s o); auto. discriminate.
  - apply (pu_host_trace_at pu_hprop_eqb pu_heval Ph s o); auto. discriminate.
Qed.

Lemma pu_hCOMMIT_step : forall r o Ph s,
  subcode (o, pu_hCOMMIT r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hrun_prog 1 Ph s = hexec s (M.COMMIT PSlot r) /\ htrace 1 Ph s = [M.COMMIT PSlot r].
Proof.
  intros r o Ph s Hsc Hpc He. split.
  - apply (pu_host_step_at pu_hprop_eqb pu_heval Ph s o); auto. discriminate.
  - apply (pu_host_trace_at pu_hprop_eqb pu_heval Ph s o); auto. discriminate.
Qed.

Lemma pu_hCERTIFY_step : forall o Ph s,
  subcode (o, pu_hCERTIFY o) (1, Ph) -> hpc s = o -> herr s = false ->
  hrun_prog 1 Ph s = hexec s M.CERTIFY /\ htrace 1 Ph s = [M.CERTIFY].
Proof.
  intros o Ph s Hsc Hpc He. split.
  - apply (pu_host_step_at pu_hprop_eqb pu_heval Ph s o); auto. discriminate.
  - apply (pu_host_trace_at pu_hprop_eqb pu_heval Ph s o); auto. discriminate.
Qed.

(* CHECK on a slot holding pair (pcode p) v, when p holds of v and the
   fact table has room: the fact (PSlot, r, current version of r) is
   recorded, pc moves on, the ledger goes up by 1; nothing else changes. *)
Theorem pu_hCHECK_pass : forall r o Ph s p v,
  subcode (o, pu_hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s r = pu_pair (pu_pcode p) v -> E.holds p v ->
  length (M.facts (M.core_of s)) < M.pu_fact_cap ->
  hrun_prog 1 Ph s =
  M.mkst (M.pu_record_fact (M.core_of s) (M.mkfact PSlot r (hver s r))) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s p v Hsc Hpc He Hv Hh Hcap.
  destruct (pu_hCHECK_step r o Ph s Hsc Hpc He) as [E _]. rewrite E.
  rewrite (M.pu_multi_exec_check_pass pu_hprop_eqb pu_heval); [reflexivity |].
  unfold M.pu_check_ok. rewrite He, Hv, pu_heval_pair.
  apply E.eval_iff in Hh. rewrite Hh. apply Nat.ltb_lt in Hcap. rewrite Hcap. reflexivity.
Qed.

Corollary pu_hCHECK_pass_fields : forall r o Ph s p v,
  subcode (o, pu_hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s r = pu_pair (pu_pcode p) v -> E.holds p v ->
  length (M.facts (M.core_of s)) < M.pu_fact_cap ->
  let s' := hrun_prog 1 Ph s in
  M.facts (M.core_of s') = M.mkfact PSlot r (hver s r) :: M.facts (M.core_of s) /\
  M.chan (M.core_of s') = M.chan (M.core_of s) /\
  hpc s' = S o /\ herr s' = false /\ M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
  (forall d, hv s' d = hv s d /\ hver s' d = hver s d).
Proof.
  intros r o Ph s p v Hsc Hpc He Hv Hh Hcap s'. unfold s'.
  rewrite (pu_hCHECK_pass r o Ph s p v Hsc Hpc He Hv Hh Hcap). simpl.
  rewrite Hpc, He. repeat split.
Qed.

(* A CHECK that fails traps: the latch rises, the ledger goes up by 1,
   and the fact table, channel, registers and flag stay as they were. *)
Theorem pu_hCHECK_fail : forall r o Ph s,
  subcode (o, pu_hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  M.pu_check_ok pu_heval (M.core_of s) PSlot r = false ->
  hrun_prog 1 Ph s = M.mkst (M.pu_trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s Hsc Hpc He Hc.
  destruct (pu_hCHECK_step r o Ph s Hsc Hpc He) as [E _]. rewrite E.
  apply (M.pu_multi_exec_check_fail pu_hprop_eqb pu_heval); assumption.
Qed.

Corollary pu_hCHECK_fail_holds : forall r o Ph s p v,
  subcode (o, pu_hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s r = pu_pair (pu_pcode p) v -> ~ E.holds p v ->
  hrun_prog 1 Ph s = M.mkst (M.pu_trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s p v Hsc Hpc He Hv Hh. apply (pu_hCHECK_fail r o Ph s Hsc Hpc He).
  unfold M.pu_check_ok. rewrite Hv, pu_heval_pair.
  destruct (E.eval p v) eqn:Ev; [exfalso; apply Hh, E.eval_iff, Ev |].
  rewrite andb_false_r. reflexivity.
Qed.

Corollary pu_hCHECK_fail_cap : forall r o Ph s,
  subcode (o, pu_hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  M.pu_fact_cap <= length (M.facts (M.core_of s)) ->
  hrun_prog 1 Ph s = M.mkst (M.pu_trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s Hsc Hpc He Hcap. apply (pu_hCHECK_fail r o Ph s Hsc Hpc He).
  unfold M.pu_check_ok. apply Nat.ltb_ge in Hcap. rewrite Hcap, andb_false_r. reflexivity.
Qed.

(* A slot holding 0 (an unused slot, or the dead register) never passes. *)
Corollary pu_hCHECK_fail_zero : forall r o Ph s,
  subcode (o, pu_hCHECK r o) (1, Ph) -> hpc s = o -> herr s = false ->
  hv s r = 0 ->
  hrun_prog 1 Ph s = M.mkst (M.pu_trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s Hsc Hpc He Hv. apply (pu_hCHECK_fail r o Ph s Hsc Hpc He).
  unfold M.pu_check_ok. rewrite Hv, pu_heval_zero, andb_false_r. reflexivity.
Qed.

(* COMMIT on a slot whose current version carries a recorded PSlot fact:
   the channel holds that fact, pc moves on, the ledger goes up by 1. *)
Theorem pu_hCOMMIT_pass : forall r o Ph s,
  subcode (o, pu_hCOMMIT r o) (1, Ph) -> hpc s = o -> herr s = false ->
  In (M.mkfact PSlot r (hver s r)) (M.facts (M.core_of s)) ->
  hrun_prog 1 Ph s =
  M.mkst (M.pu_commit_to (M.core_of s) (M.mkfact PSlot r (hver s r))) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s Hsc Hpc He Hin.
  destruct (pu_hCOMMIT_step r o Ph s Hsc Hpc He) as [E _]. rewrite E.
  rewrite (M.pu_multi_exec_commit_pass pu_hprop_eqb pu_hprop_eqb_eq pu_heval); [reflexivity |].
  apply (M.pu_multi_commit_ok_iff pu_hprop_eqb pu_hprop_eqb_eq). split; [exact He | exact Hin].
Qed.

Corollary pu_hCOMMIT_pass_fields : forall r o Ph s,
  subcode (o, pu_hCOMMIT r o) (1, Ph) -> hpc s = o -> herr s = false ->
  In (M.mkfact PSlot r (hver s r)) (M.facts (M.core_of s)) ->
  let s' := hrun_prog 1 Ph s in
  M.facts (M.core_of s') = M.facts (M.core_of s) /\
  M.chan (M.core_of s') = Some (M.mkfact PSlot r (hver s r)) /\
  hpc s' = S o /\ herr s' = false /\ M.mu s' = M.mu s + 1 /\ M.cert s' = M.cert s /\
  (forall d, hv s' d = hv s d /\ hver s' d = hver s d).
Proof.
  intros r o Ph s Hsc Hpc He Hin s'. unfold s'.
  rewrite (pu_hCOMMIT_pass r o Ph s Hsc Hpc He Hin). simpl.
  rewrite Hpc, He. repeat split.
Qed.

(* COMMIT without that fact traps. *)
Theorem pu_hCOMMIT_fail : forall r o Ph s,
  subcode (o, pu_hCOMMIT r o) (1, Ph) -> hpc s = o -> herr s = false ->
  ~ In (M.mkfact PSlot r (hver s r)) (M.facts (M.core_of s)) ->
  hrun_prog 1 Ph s = M.mkst (M.pu_trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros r o Ph s Hsc Hpc He Hin.
  destruct (pu_hCOMMIT_step r o Ph s Hsc Hpc He) as [E _]. rewrite E.
  apply (M.pu_multi_exec_commit_fail pu_hprop_eqb pu_heval); [exact He |].
  destruct (M.pu_commit_ok pu_hprop_eqb (M.core_of s) PSlot r) eqn:Hc; [| reflexivity].
  exfalso. apply (M.pu_multi_commit_ok_iff pu_hprop_eqb pu_hprop_eqb_eq) in Hc. apply Hin, Hc.
Qed.

(* CERTIFY with a full channel raises the flag; pc moves on, the ledger
   goes up by 1. *)
Theorem pu_hCERTIFY_pass : forall o Ph s f,
  subcode (o, pu_hCERTIFY o) (1, Ph) -> hpc s = o -> herr s = false ->
  M.chan (M.core_of s) = Some f ->
  hrun_prog 1 Ph s = M.mkst (M.pu_goto (M.core_of s) (S o)) (M.mu s + 1) true.
Proof.
  intros o Ph s f Hsc Hpc He Hc.
  destruct (pu_hCERTIFY_step o Ph s Hsc Hpc He) as [E _]. rewrite E.
  rewrite (M.pu_multi_exec_certify_pass pu_hprop_eqb pu_heval), Hpc; [reflexivity |].
  unfold M.pu_certify_ok. rewrite He, Hc. reflexivity.
Qed.

(* CERTIFY with an empty channel traps. *)
Theorem pu_hCERTIFY_fail : forall o Ph s,
  subcode (o, pu_hCERTIFY o) (1, Ph) -> hpc s = o -> herr s = false ->
  M.chan (M.core_of s) = None ->
  hrun_prog 1 Ph s = M.mkst (M.pu_trap (M.core_of s)) (M.mu s + 1) (M.cert s).
Proof.
  intros o Ph s Hsc Hpc He Hc.
  destruct (pu_hCERTIFY_step o Ph s Hsc Hpc He) as [E _]. rewrite E.
  apply (M.pu_multi_exec_certify_fail pu_hprop_eqb pu_heval); [exact He |].
  unfold M.pu_certify_ok. rewrite He, Hc. reflexivity.
Qed.

(* PAY: one paid step that moves to the next address and changes nothing
   else. It never traps on a live machine. *)
Definition pu_hPAY (o : nat) : list hinstr := [M.PAY].

Lemma pu_hPAY_step : forall o Ph s,
  subcode (o, pu_hPAY o) (1, Ph) -> hpc s = o -> herr s = false ->
  hrun_prog 1 Ph s = hexec s M.PAY /\ htrace 1 Ph s = [M.PAY].
Proof.
  intros o Ph s Hsc Hpc He. split.
  - apply (pu_host_step_at pu_hprop_eqb pu_heval Ph s o); auto. discriminate.
  - apply (pu_host_trace_at pu_hprop_eqb pu_heval Ph s o); auto. discriminate.
Qed.

Theorem pu_hPAY_pass : forall o Ph s,
  subcode (o, pu_hPAY o) (1, Ph) -> hpc s = o -> herr s = false ->
  hrun_prog 1 Ph s = M.mkst (M.pu_goto (M.core_of s) (S o)) (M.mu s + 1) (M.cert s).
Proof.
  intros o Ph s Hsc Hpc He.
  destruct (pu_hPAY_step o Ph s Hsc Hpc He) as [E _]. rewrite E.
  rewrite (M.pu_multi_exec_pay pu_hprop_eqb pu_heval s He), Hpc. reflexivity.
Qed.

(* A trapped state: same registers, fact table, channel and pc; the latch
   is up, so the host takes no further step. *)
Lemma pu_trap_fields : forall (k : @M.pu_core pu_hprop),
  M.vals (M.pu_trap k) = M.vals k /\ M.vers (M.pu_trap k) = M.vers k /\
  M.facts (M.pu_trap k) = M.facts k /\ M.chan (M.pu_trap k) = M.chan k /\
  M.pc (M.pu_trap k) = M.pc k /\ M.err (M.pu_trap k) = true.
Proof. intro k. repeat split. Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions pu_hINC_spec.
Print Assumptions pu_hDEC_spec.
Print Assumptions pu_hJMP_spec.
Print Assumptions pu_hJZ_spec.
Print Assumptions pu_hZERO_spec.
Print Assumptions pu_hMOVE_spec.
Print Assumptions pu_hMOVE2_spec.
Print Assumptions pu_hPACK_spec.
Print Assumptions pu_hHALF_spec.
Print Assumptions pu_hUNPACK_spec.
Print Assumptions pu_hUNPACK0_spec.
Print Assumptions pu_hCOPY_spec.
Print Assumptions pu_hDISP_spec.
Print Assumptions pu_hEQC_spec.
Print Assumptions pu_hEQR_spec.
Print Assumptions pu_hFETCH_spec.
Print Assumptions pu_hFETCH_guest.
Print Assumptions pu_hFETCH_guest_pc0.
Print Assumptions pu_hBUMP_spec.
Print Assumptions pu_hCHECK_pass.
Print Assumptions pu_hCHECK_pass_fields.
Print Assumptions pu_hCHECK_fail_holds.
Print Assumptions pu_hCHECK_fail_cap.
Print Assumptions pu_hCHECK_fail_zero.
Print Assumptions pu_hCOMMIT_pass.
Print Assumptions pu_hCOMMIT_pass_fields.
Print Assumptions pu_hCOMMIT_fail.
Print Assumptions pu_hCERTIFY_pass.
Print Assumptions pu_hCERTIFY_fail.
Print Assumptions pu_hPAY_step.
Print Assumptions pu_hPAY_pass.
