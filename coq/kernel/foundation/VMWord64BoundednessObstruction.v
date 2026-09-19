(** VMWord64BoundednessObstruction.v — the abstract VM's register/memory file
    is a genuine finite-state system once every cell has been touched, and no
    finite program can inject arbitrarily many distinct inputs into it.

    Motivation. VMEncodedInputAccess.v shows one specific encoding channel
    (vm_logic_acc) cannot drive a self-interpreter because no opcode reads it
    generically. That does not by itself explain why re-encoding into
    vm_regs/vm_mem would fare any better, since those DO have general
    read/write opcodes (LOAD, STORE, ADD, ...). This file proves the sharper,
    channel-independent reason: write_reg and write_mem apply word64 (mask to
    the low 64 bits) on every write, unconditionally, "so hardware wraparound
    matches the Coq model" (VMState.v's own comment on word64). Every writing
    instruction in vm_apply routes through one of write_reg, write_mem, or
    swap_regs (checked exhaustively below against SimulationProof.v's ~50
    match arms). swap_regs is the one exception: it relocates two existing
    register values without masking, but only ever moves values already
    present in the register file — it cannot synthesize a new one.

    Consequence: starting from a state where every register and memory cell
    already holds a value below 2^64 (state_64bit_bounded), that property is
    an invariant of every reachable state, forever. The register+memory file
    is then no more expressive than a genuine finite-state machine with at
    most (2^64)^144 configurations (16 registers + 128 words). A pigeonhole
    argument over that fixed bound then shows: no function from an infinite
    domain (standing for "which of arbitrarily many guest programs was fed
    in") into such a state can be injective on its final register+memory
    content. This is the rigorous form of "you cannot derive new unboundedly
    large working state via ordinary computation here" — it is what actually
    blocks a self-interpreter, independent of which register or cell the
    guest program's encoding starts in.

    This file does not touch coq/kami_hw or the ISA. It is a fact about the
    abstract VM (VMState.v/VMStep.v/SimulationProof.v) exactly as specified.
    It does not claim vm_encode_concrete-style initial encodings are
    impossible (an untouched cell may start above 2^64 — that is exactly how
    vm_encode_concrete/VMSubstrateEncoded.v work); it claims that once
    execution begins and the machine actually computes with that content,
    every derived value collapses into the 64-bit-bounded regime, and the
    bounded regime alone has finite capacity. *)

From Coq Require Import Arith Lia List Bool.
From Coq Require Import NArith.NArith.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.

(** * 1. word64 is bounded by 2^64, proved via N-arithmetic only.

    two64 is left fully symbolic throughout this file: it is never unfolded
    or computed as a literal unary nat (which would be astronomically
    expensive). Every fact about it is derived algebraically. *)

Definition two64 : nat := 2 ^ 64.

Lemma two64_pos : 0 < two64.
Proof. unfold two64. apply Nat.Private_NZPow.pow_pos_nonneg; lia. Qed.

Lemma two64_N_eq : N.to_nat (2 ^ 64)%N = two64.
Proof. unfold two64. rewrite N2Nat.inj_pow. reflexivity. Qed.

Lemma word64_lt_two64 : forall x, word64 x < two64.
Proof.
  intro x. unfold word64, word64_mask.
  rewrite N.land_ones.
  rewrite <- two64_N_eq.
  apply Nat.compare_lt_iff.
  rewrite <- N2Nat.inj_compare.
  apply N.compare_lt_iff.
  apply N.mod_lt.
  apply N.pow_nonzero. lia.
Qed.

(** * 2. Small list helpers: Forall survives firstn/skipn, and nth with a
    bounded-Forall list is itself bounded (whether or not the index is in
    range — the out-of-range default is 0, safely below two64). *)

Lemma Forall_firstn : forall {A} (P : A -> Prop) n l,
  Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n l H. rewrite <- (firstn_skipn n l) in H.
  apply Forall_app in H. apply H.
Qed.

Lemma Forall_skipn : forall {A} (P : A -> Prop) n l,
  Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n l H. rewrite <- (firstn_skipn n l) in H.
  apply Forall_app in H. apply H.
Qed.

Lemma Forall_nth_default_lt_two64 : forall l idx,
  Forall (fun x => x < two64) l -> nth idx l 0 < two64.
Proof.
  intros l idx H.
  destruct (le_lt_dec (length l) idx) as [Hge | Hlt].
  - rewrite nth_overflow by exact Hge. exact two64_pos.
  - apply (Forall_forall (fun x => x < two64) l); [exact H | apply nth_In; exact Hlt].
Qed.

(** * 3. write_reg / write_mem: length-preserving (given the invariant length
    already holds) and always land the fresh value under two64. *)

Lemma write_reg_length : forall s r v,
  length s.(vm_regs) = REG_COUNT -> length (write_reg s r v) = REG_COUNT.
Proof.
  intros s r v Hlen. unfold write_reg.
  rewrite app_length, app_length, firstn_length, skipn_length, Hlen. cbn [length].
  unfold reg_index.
  pose proof (Nat.mod_upper_bound r REG_COUNT ltac:(unfold REG_COUNT; lia)) as Hb.
  lia.
Qed.

Lemma write_mem_length : forall s a v,
  length s.(vm_mem) = MEM_SIZE -> length (write_mem s a v) = MEM_SIZE.
Proof.
  intros s a v Hlen. unfold write_mem.
  rewrite app_length, app_length, firstn_length, skipn_length, Hlen. cbn [length].
  unfold mem_index.
  pose proof (Nat.mod_upper_bound a MEM_SIZE ltac:(unfold MEM_SIZE; lia)) as Hb.
  lia.
Qed.

Lemma write_reg_bounded : forall s r v,
  length s.(vm_regs) = REG_COUNT ->
  Forall (fun x => x < two64) s.(vm_regs) ->
  Forall (fun x => x < two64) (write_reg s r v).
Proof.
  intros s r v Hlen Hb. unfold write_reg.
  apply Forall_app; split; [apply Forall_firstn; exact Hb |].
  apply Forall_app; split; [constructor; [apply word64_lt_two64 | constructor] |].
  apply Forall_skipn; exact Hb.
Qed.

Lemma write_mem_bounded : forall s a v,
  Forall (fun x => x < two64) s.(vm_mem) ->
  Forall (fun x => x < two64) (write_mem s a v).
Proof.
  intros s a v Hb. unfold write_mem.
  apply Forall_app; split; [apply Forall_firstn; exact Hb |].
  apply Forall_app; split; [constructor; [apply word64_lt_two64 | constructor] |].
  apply Forall_skipn; exact Hb.
Qed.

(** * 4. swap_regs: the one write path that skips word64. It only relocates
    two values already present in the register file, so it cannot introduce
    anything above two64 that was not already there — and given a
    64-bit-bounded input, both relocated values are themselves bounded, so
    the result stays bounded too (this file does not need swap_regs'
    unmasked exactness beyond that; VMWitnessCounterMonotonicity-style
    "cannot synthesize new large values" is exactly the point). *)

Lemma swap_regs_length : forall regs a b,
  length regs = REG_COUNT -> length (swap_regs regs a b) = REG_COUNT.
Proof.
  intros regs a b Hlen. unfold swap_regs.
  set (a_idx := a mod REG_COUNT). set (b_idx := b mod REG_COUNT).
  set (regs' := firstn a_idx regs ++ [nth b_idx regs 0] ++ skipn (S a_idx) regs).
  assert (Hlen' : length regs' = REG_COUNT).
  { unfold regs'. rewrite app_length, app_length, firstn_length, skipn_length, Hlen. cbn [length].
    pose proof (Nat.mod_upper_bound a REG_COUNT ltac:(unfold REG_COUNT; lia)) as Hb.
    unfold a_idx. lia. }
  rewrite app_length, app_length, firstn_length, skipn_length, Hlen'. cbn [length].
  pose proof (Nat.mod_upper_bound b REG_COUNT ltac:(unfold REG_COUNT; lia)) as Hb.
  unfold b_idx. lia.
Qed.

Lemma swap_regs_bounded : forall regs a b,
  Forall (fun x => x < two64) regs ->
  Forall (fun x => x < two64) (swap_regs regs a b).
Proof.
  intros regs a b Hb. unfold swap_regs.
  set (a_idx := a mod REG_COUNT). set (b_idx := b mod REG_COUNT).
  set (va := nth a_idx regs 0). set (vb := nth b_idx regs 0).
  assert (Hva : va < two64) by (apply Forall_nth_default_lt_two64; exact Hb).
  assert (Hvb : vb < two64) by (apply Forall_nth_default_lt_two64; exact Hb).
  set (regs' := firstn a_idx regs ++ [vb] ++ skipn (S a_idx) regs).
  assert (Hb' : Forall (fun x => x < two64) regs').
  { unfold regs'. apply Forall_app; split; [apply Forall_firstn; exact Hb |].
    apply Forall_app; split; [constructor; [exact Hvb | constructor] |].
    apply Forall_skipn; exact Hb. }
  apply Forall_app; split; [apply Forall_firstn; exact Hb' |].
  apply Forall_app; split; [constructor; [exact Hva | constructor] |].
  apply Forall_skipn; exact Hb'.
Qed.

(** * 5. state_64bit_bounded: the invariant, and its preservation across one
    vm_apply step and across any finite run. Proved by exhaustive case
    analysis on vm_apply's match arms in SimulationProof.v: every arm either
    leaves vm_regs/vm_mem untouched (the shared advance_state /
    advance_state_reveal / jump_state builders pass s.(vm_regs)/s.(vm_mem)
    through unchanged, and the direct record-literal arms for
    LASSERT/CHSH_TRIAL/CERTIFY/CHSH_LASSERT-family all write
    vm_regs := s.(vm_regs); vm_mem := s.(vm_mem) verbatim), or writes via
    write_reg/write_mem (covered by write_reg_bounded/write_mem_bounded), or
    (XOR_SWAP only) via swap_regs (covered by swap_regs_bounded). *)

Definition state_64bit_bounded (s : VMState) : Prop :=
  length s.(vm_regs) = REG_COUNT /\ length s.(vm_mem) = MEM_SIZE /\
  Forall (fun x => x < two64) s.(vm_regs) /\ Forall (fun x => x < two64) s.(vm_mem).

Lemma advance_state_regs_mem : forall s instr g c e,
  (advance_state s instr g c e).(vm_regs) = s.(vm_regs) /\
  (advance_state s instr g c e).(vm_mem) = s.(vm_mem).
Proof. intros. split; reflexivity. Qed.

Lemma advance_state_reveal_regs_mem : forall s instr fi d g c e,
  (advance_state_reveal s instr fi d g c e).(vm_regs) = s.(vm_regs) /\
  (advance_state_reveal s instr fi d g c e).(vm_mem) = s.(vm_mem).
Proof. intros. split; reflexivity. Qed.

Lemma jump_state_regs_mem : forall s instr t,
  (jump_state s instr t).(vm_regs) = s.(vm_regs) /\
  (jump_state s instr t).(vm_mem) = s.(vm_mem).
Proof. intros. split; reflexivity. Qed.

Theorem state_64bit_bounded_step : forall s i,
  state_64bit_bounded s -> state_64bit_bounded (vm_apply s i).
Proof.
  intros s i [Hrl [Hml [Hrb Hmb]]].
  unfold state_64bit_bounded.
  destruct i; cbn [vm_apply];
    repeat match goal with
    | |- context [ if ?x then _ else _ ] => destruct x
    | |- context [ match ?x with Some _ => _ | None => _ end ] => destruct x
    | |- context [ let '(_, _) := ?x in _ ] => destruct x
    end;
    cbn [vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err
         vm_logic_acc vm_mstatus vm_witness vm_certified
         advance_state advance_state_reveal advance_state_rm
         jump_state jump_state_rm];
    repeat split;
    (exact Hrl || exact Hml || exact Hrb || exact Hmb
     || (apply write_reg_length; exact Hrl)
     || (apply write_mem_length; exact Hml)
     || (apply swap_regs_length; exact Hrl)
     || (apply write_reg_bounded; [exact Hrl | exact Hrb])
     || (apply write_mem_bounded; exact Hmb)
     || (apply swap_regs_bounded; exact Hrb)
     || idtac).
Qed.

Theorem state_64bit_bounded_run : forall n p s,
  state_64bit_bounded s -> state_64bit_bounded (run_vm n p s).
Proof.
  induction n as [| n IH]; intros p s Hs; cbn [run_vm].
  - exact Hs.
  - destruct (nth_error p s.(vm_pc)) as [i |].
    + apply IH. apply state_64bit_bounded_step. exact Hs.
    + exact Hs.
Qed.

(** * 6. Finite capacity: enumerate every length-n list with entries below a
    bound b, and show its length is exactly b^n (reusing no unproved
    combinatorial fact — this is a direct induction). *)

Fixpoint all_bounded_lists (n b : nat) : list (list nat) :=
  match n with
  | 0 => [ [] ]
  | S n' => flat_map (fun x => map (cons x) (all_bounded_lists n' b)) (seq 0 b)
  end.

Lemma flat_map_cons_length : forall (l : list (list nat)) (xs : list nat),
  length (flat_map (fun x => map (cons x) l) xs) = length xs * length l.
Proof.
  intros l xs. induction xs as [| x xs IH]; cbn [flat_map length].
  - reflexivity.
  - rewrite app_length, map_length, IH. reflexivity.
Qed.

Lemma all_bounded_lists_length : forall n b,
  length (all_bounded_lists n b) = b ^ n.
Proof.
  induction n as [| n IH]; intro b; cbn [all_bounded_lists Nat.pow].
  - reflexivity.
  - rewrite flat_map_cons_length, IH, seq_length. lia.
Qed.

Lemma all_bounded_lists_complete : forall n b l,
  length l = n -> Forall (fun x => x < b) l -> In l (all_bounded_lists n b).
Proof.
  induction n as [| n IH]; intros b l Hlen Hb.
  - apply length_zero_iff_nil in Hlen. subst l. left. reflexivity.
  - destruct l as [| x rest]; cbn [length] in Hlen; [discriminate |].
    apply Forall_cons_iff in Hb. destruct Hb as [Hx Hrest].
    assert (Hlen' : length rest = n) by lia.
    cbn [all_bounded_lists]. apply in_flat_map.
    exists x. split.
    + apply in_seq. lia.
    + apply in_map. apply IH; [exact Hlen' | exact Hrest].
Qed.

(** * 7. The pigeonhole theorem: no function from an unbounded domain (any
    countable family of "which guest program" indices) into 64-bit-bounded
    VM register+memory content can be injective. Combined with
    state_64bit_bounded_run, this is the rigorous content of "an interpreter
    cannot inject arbitrarily many distinct guest programs into its own
    working state once that state is 64-bit-bounded (as it always becomes,
    the moment any instruction computes with it)": there are only
    two64^144 possible (regs++mem) contents to land in, ever, but
    infinitely many candidate inputs to distinguish. *)

Definition combined (s : VMState) : list nat := s.(vm_regs) ++ s.(vm_mem).

Lemma NoDup_map_injective : forall {A B} (f : A -> B) (l : list A),
  NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (map f l).
Proof.
  induction l as [| a l IH]; intros Hnd Hinj; cbn [map].
  - constructor.
  - inversion Hnd as [| ? ? Hnotin Hnd']; subst.
    constructor.
    + intro Hin. apply in_map_iff in Hin. destruct Hin as [y [Heq Hiny]].
      assert (a = y) as Hay
        by (apply Hinj; [left; reflexivity | right; exact Hiny | symmetry; exact Heq]).
      subst y. contradiction.
    + apply IH; [exact Hnd' |].
      intros x y Hx Hy Hfxy. apply Hinj; [right | right |]; assumption.
Qed.

Theorem no_injective_bounded_encoding :
  forall (f : nat -> VMState),
    (forall k, state_64bit_bounded (f k)) ->
    ~ (forall k1 k2, combined (f k1) = combined (f k2) -> k1 = k2).
Proof.
  intros f Hbounded Hinj.
  set (bound := two64 ^ (REG_COUNT + MEM_SIZE)).
  set (dom := seq 0 (S bound)).
  set (images := map (fun k => combined (f k)) dom).
  assert (Hnodup : NoDup images).
  { unfold images. apply NoDup_map_injective; [apply seq_NoDup |].
    intros x y _ _ Heq. apply Hinj. exact Heq. }
  assert (Hincl : incl images (all_bounded_lists (REG_COUNT + MEM_SIZE) two64)).
  { unfold images. intros v Hv. apply in_map_iff in Hv.
    destruct Hv as [k [Hk _]]. subst v.
    destruct (Hbounded k) as [Hrl [Hml [Hrb Hmb]]].
    apply all_bounded_lists_complete.
    - unfold combined. rewrite app_length, Hrl, Hml. reflexivity.
    - unfold combined. apply Forall_app. split; assumption. }
  pose proof (NoDup_incl_length Hnodup Hincl) as Hle.
  rewrite all_bounded_lists_length in Hle.
  unfold images, dom in Hle. rewrite map_length, seq_length in Hle.
  fold bound in Hle. lia.
Qed.
