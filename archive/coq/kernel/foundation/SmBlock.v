(** SmBlock.v: a Minsky-computable relation of two numbers as a block of
    host instructions with a clean interface.

    A relation R of x, c and m that is MMA_computable (two inputs in
    counters 1 and 2, the answer in counter 0) gives a block of host
    instructions that works in a window of registers base .. base + N - 1
    and can sit anywhere in a bigger program Q [sm2_bint]. The interface
    says what the block does and nothing else.

      sm2_bi_ctx   if R x c m holds and the window holds 0, x, c, 0, 0, ... then
               Q runs from the first line of the block to the line after it,
               with no earlier stop, leaving m in register base, every
               register and version outside the window as it was, and the
               fact table, channel, trap latch, ledger and flag as they were.
      sm2_bi_halt  if Q stops while it is in the block, then some m has R x c m.

    [sm2_bint_of_MMA] builds the interface from MMA_computable.

    Dependencies: Coq standard library, the vendored coq-undecidability
    library, SmMMAOff.v and SmKleene.v (for the start vector). No axioms,
    no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here blocks of host instructions that compute a Minsky-computable relation in a window of registers.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmLoops Kernel.SmMMAOff Kernel.SmKleene.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).

Record sm2_bint (R : nat -> nat -> nat -> Prop) : Type := sm2_mkbint {
  sm2_bi_prog : nat -> list hinstr;
  sm2_bi_len : nat;
  sm2_bi_N : nat;
  sm2_bi_N3 : 3 <= sm2_bi_N;
  sm2_bi_len_eq : forall base, length (sm2_bi_prog base) = sm2_bi_len;
  sm2_bi_ctx : forall base off Q (u : hstate) x c m,
    sm_embeds Q (sm2_bi_prog base) off ->
    M.pc (M.core_of u) = S off -> M.err (M.core_of u) = false ->
    (forall j, j < sm2_bi_N -> M.vals (M.core_of u) (base + j) = sm_in2 x c j) ->
    R x c m ->
    exists u', sm2_RR Q u u' /\ M.pc (M.core_of u') = S (off + sm2_bi_len) /\
      M.err (M.core_of u') = false /\ M.vals (M.core_of u') base = m /\
      (forall q, (q < base \/ base + sm2_bi_N <= q) ->
         M.vals (M.core_of u') q = M.vals (M.core_of u) q /\
         M.vers (M.core_of u') q = M.vers (M.core_of u) q) /\
      sm2_pfe u u';
  sm2_bi_halt : forall base off Q (u : hstate) x c,
    sm_embeds Q (sm2_bi_prog base) off ->
    M.pc (M.core_of u) = S off -> M.err (M.core_of u) = false ->
    (forall j, j < sm2_bi_N -> M.vals (M.core_of u) (base + j) = sm_in2 x c j) ->
    forall n, M.next_instr Q (M.core_of (hrun_prog n Q u)) = None ->
    exists m, R x c m
}.

Arguments sm2_bi_prog {R}.
Arguments sm2_bi_len {R}.
Arguments sm2_bi_N {R}.
Arguments sm2_bi_N3 {R}.
Arguments sm2_bi_len_eq {R}.
Arguments sm2_bi_ctx {R}.
Arguments sm2_bi_halt {R}.

Theorem sm2_bint_of_MMA : forall (R : nat -> nat -> nat -> Prop),
  MMA_computable (fun (v : Vector.t nat 2) m => R (Vector.hd v) (Vector.hd (Vector.tl v)) m) ->
  inhabited (sm2_bint R).
Proof.
  intros R [nn [Pm HPm]].
  assert (Hwin : forall base (u : hstate) x c,
    (forall j, j < S (S (S nn)) -> M.vals (M.core_of u) (base + j) = sm_in2 x c j) ->
    forall p : pos (S (S (S nn))),
      M.vals (M.core_of u) (base + pos2nat p) =
      vec_pos (Vector.append (Vector.cons nat 0 2 (Vector.cons nat x 1 (Vector.cons nat c 0 (Vector.nil nat))))
                 (Vector.const 0 nn)) p).
  { intros base u x c H p. pose proof (sm_v0_pos nn x c p) as E. cbn in E |- *. rewrite E. apply H. exact (pos2nat_prop p). }
  constructor.
  refine (sm2_mkbint R (fun base => sm2_mma_host (S (S (S nn))) base Pm) (length Pm) (S (S (S nn))) _ _ _ _).
  - lia.
  - intro base. unfold sm2_mma_host. apply map_length.
  - intros base off Q u x c m Hemb Hp He Hv HR.
    pose proof (HPm (Vector.cons nat x 1 (Vector.cons nat c 0 (Vector.nil nat))) m) as Hiff.
    cbn [Vector.hd Vector.tl] in Hiff. apply Hiff in HR.
    exact (sm2_mma_ctx (S (S nn)) base off Q Pm u _ m Hemb Hp He (Hwin base u x c Hv) HR).
  - intros base off Q u x c Hemb Hp He Hv n Hn.
    destruct (sm2_mma_ctx_halt (S (S nn)) base off Q Pm u _ Hemb Hp He (Hwin base u x c Hv) n Hn)
      as [cc [w Hout]].
    exists (Vector.hd w).
    pose proof (HPm (Vector.cons nat x 1 (Vector.cons nat c 0 (Vector.nil nat))) (Vector.hd w)) as Hiff.
    cbn [Vector.hd Vector.tl] in Hiff. apply Hiff.
    exists cc, (Vector.tl w). rewrite <- (Vector.eta w) at 1. exact Hout.
Qed.

Print Assumptions sm2_bint_of_MMA.
