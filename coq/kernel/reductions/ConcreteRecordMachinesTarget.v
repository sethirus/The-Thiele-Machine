(** SCOPE NOTE: standalone proof scope. These small RAM/reversible-machine
    targets are comparison machines and do not claim a simulation by a Thiele machine.

    Concrete machine targets. *)

From Coq Require Import List Arith.PeanoNat ZArith Lia.
Import ListNotations.

Inductive RAMInstr := RSet (value : nat) | RInc | RDec.

Definition ram_step (i : RAMInstr) (x : nat) : nat :=
  match i with RSet v => v | RInc => S x | RDec => pred x end.

Record RecordedRAM := {
  rr_value : nat;
  rr_record : list nat
}.

Definition tied_step (i : RAMInstr) (s : RecordedRAM) : RecordedRAM :=
  let next := ram_step i (rr_value s) in
  {| rr_value := next;
     rr_record := match i with
                  | RSet _ => rr_record s ++ [rr_value s]
                  | _ => rr_record s
                  end |}.

Definition untied_step (i : RAMInstr) (s : RecordedRAM) : RecordedRAM :=
  {| rr_value := ram_step i (rr_value s); rr_record := rr_record s |}.

Definition tied_overwrite_records_old_value : Prop :=
  forall s v, rr_record (tied_step (RSet v) s) = rr_record s ++ [rr_value s].

Definition untied_overwrite_has_no_record : Prop :=
  forall s v, rr_record (untied_step (RSet v) s) = rr_record s.

(** Janus-like reversible arithmetic: an update and its syntactic inverse. *)
Inductive JInstr := JAdd (delta : Z) | JSub (delta : Z).

Definition jinverse (i : JInstr) : JInstr :=
  match i with JAdd d => JSub d | JSub d => JAdd d end.

Definition junbounded_step (i : JInstr) (x : Z) : Z :=
  match i with JAdd d => x + d | JSub d => x - d end.

Definition jbounded_step (modulus : Z) (i : JInstr) (x : Z) : Z :=
  Z.modulo (junbounded_step i x) modulus.

Definition janus_unbounded_inverse : Prop :=
  forall i x, junbounded_step (jinverse i) (junbounded_step i x) = x.

Definition janus_bounded_inverse : Prop :=
  forall (modulus : Z) (i : JInstr) (x : Z), (0 < modulus)%Z ->
    (0 <= x < modulus)%Z ->
    jbounded_step modulus (jinverse i) (jbounded_step modulus i x) = x.

Definition untied_record_not_determined_by_base : Prop :=
  exists s1 s2,
    rr_value s1 = rr_value s2 /\ rr_record s1 <> rr_record s2.
