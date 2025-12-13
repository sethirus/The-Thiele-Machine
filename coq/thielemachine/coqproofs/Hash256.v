(** Minimal executable 256-bit hash (non-cryptographic).

    This is *not* SHA-256. It is an efficient, deterministic 256-bit mixer
    intended to provide an executable state commitment function inside Coq
    without introducing Parameters/Axioms.

    Security claims (collision resistance, etc.) are intentionally out of scope.
*)

From Coq Require Import List ZArith Bool.
Import ListNotations.
Open Scope Z_scope.

Module Hash256.

  Definition modulus : Z := 2 ^ 256.

  Definition mix (acc x : Z) : Z :=
    (* A simple polynomial-style mixer; kept total and fast. *)
    Z.modulo (acc * 1315423911 + x + 2654435761) modulus.

  Fixpoint fold_mix (xs : list Z) (acc : Z) : Z :=
    match xs with
    | [] => acc
    | x :: xs' => fold_mix xs' (mix acc x)
    end.

  Definition testbit_nat (z : Z) (i : nat) : bool :=
    Z.testbit z (Z.of_nat i).

  Fixpoint bits_be (k : nat) (z : Z) : list bool :=
    match k with
    | 0%nat => []
    | S k' => bits_be k' z ++ [testbit_nat z k']
    end.

  Definition hash256 (xs : list Z) : list bool :=
    let acc := fold_mix xs 0 in
    bits_be 256%nat acc.

End Hash256.
