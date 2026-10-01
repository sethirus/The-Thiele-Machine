(** LoaderReceiver: the serial receiver of [ThieleLoader] as a Coq function,
    and what it does with one frame.

    [rx_step] is the receiver part of the loader's [rxSample] method written
    as an ordinary function: the two synchronizer registers, the frame
    state, the bit-time counter, the bit index and the shift register, with
    each next value given by the same expression the Kami method writes.
    [rx_step] returns the received byte on the cycle the method's
    [byte_done] condition holds, and nothing otherwise.

    [rx_frame] is the waveform of one byte on the line: a low start bit,
    eight data bits least significant first, and a high stop bit, each held
    for [ClksPerBit] cycles, then the line left high. [rx_one_frame] states
    that from the idle receiver this waveform yields exactly that byte,
    exactly once, and leaves the receiver idle again; it is checked for all
    256 byte values. *)
Require Import Kami.Kami.
From KamiHW Require Import ThieleTypes ThieleLoader.
From Coq Require Import List ZArith Lia.
Import ListNotations.

Definition weqb {n} (a b : word n) : bool := if weq a b then true else false.

Record RxState := {
  rx_sync1 : bool;
  rx_sync2 : bool;
  rx_state : word 2;
  rx_clk : word 8;
  rx_bit : word 3;
  rx_shift : word 8
}.

(** The receiver at reset: the line seen high, waiting for a start bit. *)
Definition rx_idle : RxState :=
  {| rx_sync1 := true; rx_sync2 := true; rx_state := natToWord 2 0;
     rx_clk := natToWord 8 0; rx_bit := natToWord 3 0; rx_shift := natToWord 8 0 |}.

Definition rx_step (r : RxState) (pin : bool) : RxState * option (word 8) :=
  let b := rx_sync2 r in
  let st := rx_state r in
  let clk := rx_clk r in
  let bitn := rx_bit r in
  let shift := rx_shift r in
  let half_bit := weqb clk rx_half_last in
  let full_bit := weqb clk bit_last in
  let in_bit : word 1 := if b then WO~1 else WO~0 in
  let shifted : word 8 := Word.combine (split2 1 7 shift) in_bit in
  let byte_done := weqb st (natToWord 2 3) && full_bit && b in
  let st' :=
    if weqb st (natToWord 2 0) then (if b then natToWord 2 0 else natToWord 2 1)
    else if weqb st (natToWord 2 1) then
      (if half_bit then (if b then natToWord 2 0 else natToWord 2 2) else natToWord 2 1)
    else if weqb st (natToWord 2 2) then
      (if full_bit && weqb bitn (natToWord 3 7) then natToWord 2 3 else natToWord 2 2)
    else (if full_bit then natToWord 2 0 else natToWord 2 3) in
  let clk' :=
    if weqb st (natToWord 2 0) then natToWord 8 0
    else if weqb st (natToWord 2 1) && half_bit then natToWord 8 0
    else if full_bit then natToWord 8 0
    else clk ^+ natToWord 8 1 in
  let bit' :=
    if weqb st (natToWord 2 2) then (if full_bit then bitn ^+ natToWord 3 1 else bitn)
    else natToWord 3 0 in
  let shift' := if weqb st (natToWord 2 2) && full_bit then shifted else shift in
  ({| rx_sync1 := pin; rx_sync2 := rx_sync1 r; rx_state := st'; rx_clk := clk';
      rx_bit := bit'; rx_shift := shift' |},
   if byte_done then Some shift else None).

(** Runs the receiver over a list of line samples, collecting the bytes. *)
Fixpoint rx_run (r : RxState) (samples : list bool) : RxState * list (word 8) :=
  match samples with
  | nil => (r, nil)
  | p :: ps =>
      let (r1, out) := rx_step r p in
      let (r2, outs) := rx_run r1 ps in
      (r2, match out with Some v => v :: outs | None => outs end)
  end.

Definition bit_time (level : bool) : list bool := repeat level ClksPerBit.

Definition rx_frame (v : word 8) : list bool :=
  bit_time false
  ++ flat_map (fun i => bit_time (Z.testbit (Z.of_nat (wordToNat v)) (Z.of_nat i))) (seq 0 8)
  ++ bit_time true.

(** The line held high long enough for the receiver to settle at idle. *)
Definition rx_settle : list bool := repeat true 4.

Definition rx_frame_ok (v : word 8) : bool :=
  let '(r, out) := rx_run rx_idle (rx_frame v ++ rx_settle) in
  match out with
  | w :: nil => weqb w v && weqb (rx_state r) (natToWord 2 0)
           && Bool.eqb (rx_sync1 r) true && Bool.eqb (rx_sync2 r) true
  | _ => false
  end.

Definition all_bytes_ok : bool :=
  forallb (fun n => rx_frame_ok (natToWord 8 n)) (seq 0 256).

Lemma all_bytes_ok_true : all_bytes_ok = true.
Proof. vm_compute. reflexivity. Qed.

Theorem rx_one_frame : forall v : word 8,
  let '(r, out) := rx_run rx_idle (rx_frame v ++ rx_settle) in
  out = v :: nil /\ rx_state r = natToWord 2 0 /\ rx_sync1 r = true /\ rx_sync2 r = true.
Proof.
  intro v.
  assert (Hv : rx_frame_ok v = true).
  { pose proof all_bytes_ok_true as H. unfold all_bytes_ok in H.
    rewrite forallb_forall in H.
    rewrite <- (natToWord_wordToNat v).
    apply H. apply in_seq. pose proof (wordToNat_bound v) as Hb.
    cbn in Hb. split; [apply Nat.le_0_l|]. cbn. lia. }
  unfold rx_frame_ok in Hv.
  destruct (rx_run rx_idle (rx_frame v ++ rx_settle)) as [r out].
  destruct out as [|w [|w' rest]]; try discriminate.
  repeat rewrite Bool.andb_true_iff in Hv.
  destruct Hv as [[[Hw Hs] H1] H2].
  unfold weqb in Hw, Hs. destruct (weq w v); try discriminate. destruct (weq (rx_state r) (natToWord 2 0)); try discriminate.
  apply Bool.eqb_prop in H1. apply Bool.eqb_prop in H2.
  subst. repeat split; auto.
Qed.
