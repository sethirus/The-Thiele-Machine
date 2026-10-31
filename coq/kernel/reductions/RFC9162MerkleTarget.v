(** SCOPE NOTE: standalone proof scope. This file transcribes RFC 9162 verifier
    control flow and deliberately imports no machine semantics; the comparison to
    the record axis is a separately reported modeling classification.

    Executable vocabulary taken from RFC 9162 Sections 2.1.1, 2.1.3.2,
    and 2.1.4.2. Cryptographic properties of the selected hash remain outside
    the executable verifier. *)

From Coq Require Import List Bool Arith.PeanoNat.
Import ListNotations.

Record HashAlgorithm (entry digest : Type) : Type := {
  hash_empty : digest;
  hash_leaf : entry -> digest;       (* HASH(0x00 || entry) *)
  hash_node : digest -> digest -> digest; (* HASH(0x01 || left || right) *)
  digest_eqb : digest -> digest -> bool
}.

Arguments hash_empty {entry digest}.
Arguments hash_leaf {entry digest}.
Arguments hash_node {entry digest}.
Arguments digest_eqb {entry digest}.

(** RFC 9162 Section 2.1.3.2 step 4.2: when [fn] is even in the
    left-combination branch, shift [fn] and [sn] together until [fn] is odd
    or zero. Fuel makes the directly executable transcription total. *)
Fixpoint shift_until_odd_or_zero (fuel fn sn : nat) : nat * nat :=
  match fuel with
  | 0 => (fn, sn)
  | S fuel' =>
      if (Nat.eqb fn 0 || Nat.odd fn)%bool then (fn, sn)
      else shift_until_odd_or_zero fuel' (Nat.div2 fn) (Nat.div2 sn)
  end.

Fixpoint inclusion_fold {entry digest : Type}
    (H : HashAlgorithm entry digest) (path : list digest)
    (fn sn : nat) (r : digest) : option (nat * nat * digest) :=
  match path with
  | [] => Some (fn, sn, r)
  | p :: path' =>
      if Nat.eqb sn 0 then None
      else if (Nat.odd fn || Nat.eqb fn sn)%bool then
        let '(fn0, sn0) :=
          if Nat.odd fn then (fn, sn)
          else shift_until_odd_or_zero (S fn) fn sn in
        inclusion_fold H path' (Nat.div2 fn0) (Nat.div2 sn0)
          (hash_node H p r)
      else
        inclusion_fold H path' (Nat.div2 fn) (Nat.div2 sn)
          (hash_node H r p)
  end.

Definition verify_inclusion {entry digest : Type}
    (H : HashAlgorithm entry digest) (leaf_index tree_size : nat)
    (leaf_hash root_hash : digest) (path : list digest) : bool :=
  if Nat.ltb leaf_index tree_size then
    match inclusion_fold H path leaf_index (tree_size - 1) leaf_hash with
    | Some (_, sn, r) => Nat.eqb sn 0 && digest_eqb H r root_hash
    | None => false
    end
  else false.

(** RFC 9162 Section 2.1.4.2 step 4: shift while [fn] is odd. *)
Fixpoint shift_while_odd (fuel fn sn : nat) : nat * nat :=
  match fuel with
  | 0 => (fn, sn)
  | S fuel' =>
      if Nat.odd fn
      then shift_while_odd fuel' (Nat.div2 fn) (Nat.div2 sn)
      else (fn, sn)
  end.

Definition exact_power_of_two (n : nat) : bool :=
  negb (Nat.eqb n 0) && Nat.eqb (Nat.pow 2 (Nat.log2 n)) n.

Fixpoint consistency_fold {entry digest : Type}
    (H : HashAlgorithm entry digest) (path : list digest)
    (fn sn : nat) (fr sr : digest)
    : option (nat * nat * digest * digest) :=
  match path with
  | [] => Some (fn, sn, fr, sr)
  | c :: path' =>
      if Nat.eqb sn 0 then None
      else if (Nat.odd fn || Nat.eqb fn sn)%bool then
        let fr' := hash_node H c fr in
        let sr' := hash_node H c sr in
        let '(fn0, sn0) :=
          if Nat.odd fn then (fn, sn)
          else shift_until_odd_or_zero (S fn) fn sn in
        consistency_fold H path' (Nat.div2 fn0) (Nat.div2 sn0) fr' sr'
      else
        consistency_fold H path' (Nat.div2 fn) (Nat.div2 sn)
          fr (hash_node H sr c)
  end.

Definition verify_consistency {entry digest : Type}
    (H : HashAlgorithm entry digest) (first second : nat)
    (first_hash second_hash : digest) (proof : list digest) : bool :=
  if (Nat.ltb 0 first && Nat.ltb first second)%bool then
    let path := if exact_power_of_two first then first_hash :: proof else proof in
    match path with
    | [] => false
    | seed :: rest =>
        let '(fn0, sn0) := shift_while_odd first (first - 1) (second - 1) in
        match consistency_fold H rest fn0 sn0 seed seed with
        | Some (_, sn, fr, sr) =>
            Nat.eqb sn 0 && digest_eqb H fr first_hash
              && digest_eqb H sr second_hash
        | None => false
        end
    end
  else false.

(** The exact success properties of the verifier. *)
Definition inclusion_boundary_safe : Prop :=
  forall (entry digest : Type) (H : HashAlgorithm entry digest)
         tree_size leaf_hash root_hash path,
    verify_inclusion H tree_size tree_size leaf_hash root_hash path = false.

Definition consistency_boundary_safe : Prop :=
  forall (entry digest : Type) (H : HashAlgorithm entry digest)
         n root proof,
    verify_consistency H n n root root proof = false.
