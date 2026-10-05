(** SCOPE NOTE: standalone proof scope. These are outcomes for the RFC 9162
    verifier model, not a Thiele machine, so no unused kernel import is asserted.

    Checked outcomes for the RFC 9162 executable Merkle verifier model. *)

From Coq Require Import List Bool Arith Lia.
Import ListNotations.

From Kernel Require Import RFC9162MerkleTarget.

Theorem rfc9162_inclusion_boundary_safe : inclusion_boundary_safe.
Proof.
  intros entry digest H tree_size leaf_hash root_hash path.
  unfold verify_inclusion. rewrite Nat.ltb_irrefl. reflexivity.
Qed.

Theorem rfc9162_consistency_boundary_safe : consistency_boundary_safe.
Proof.
  intros entry digest H n root proof.
  unfold verify_consistency. rewrite Nat.ltb_irrefl, andb_false_r.
  reflexivity.
Qed.

(** Symbolic hashes preserve the RFC's domain separation and let the published
    Section 2.1.5 paths execute without assuming cryptographic security. *)
Inductive SymbolicDigest : Type :=
| sd_empty
| sd_leaf (entry : nat)
| sd_node (left right : SymbolicDigest).

Definition symbolic_digest_eq_dec :
  forall a b : SymbolicDigest, {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition symbolic_digest_eqb (a b : SymbolicDigest) : bool :=
  if symbolic_digest_eq_dec a b then true else false.

Lemma symbolic_digest_eqb_refl :
  forall d, symbolic_digest_eqb d d = true.
Proof.
  intro d. unfold symbolic_digest_eqb.
  destruct (symbolic_digest_eq_dec d d); [reflexivity | contradiction].
Qed.

Definition symbolic_hash : HashAlgorithm nat SymbolicDigest :=
  {| hash_empty := sd_empty;
     hash_leaf := sd_leaf;
     hash_node := sd_node;
     digest_eqb := symbolic_digest_eqb |}.

Definition a := sd_leaf 0.
Definition b := sd_leaf 1.
Definition c := sd_leaf 2.
Definition d := sd_leaf 3.
Definition e := sd_leaf 4.
Definition f := sd_leaf 5.
Definition j := sd_leaf 6.
Definition g := sd_node a b.
Definition h := sd_node c d.
Definition i := sd_node e f.
Definition k := sd_node g h.
Definition l := sd_node i j.
Definition rfc9162_example_root := sd_node k l.

Theorem rfc9162_example_inclusion_d0 :
  verify_inclusion symbolic_hash 0 7 a rfc9162_example_root [b; h; l] = true.
Proof. reflexivity. Qed.

Theorem rfc9162_example_inclusion_d3 :
  verify_inclusion symbolic_hash 3 7 d rfc9162_example_root [c; g; l] = true.
Proof. reflexivity. Qed.

Theorem rfc9162_example_inclusion_d4 :
  verify_inclusion symbolic_hash 4 7 e rfc9162_example_root [f; j; k] = true.
Proof. reflexivity. Qed.

Theorem rfc9162_example_inclusion_d6 :
  verify_inclusion symbolic_hash 6 7 j rfc9162_example_root [i; k] = true.
Proof. reflexivity. Qed.

Theorem rfc9162_example_consistency_4_7 :
  verify_consistency symbolic_hash 4 7 k rfc9162_example_root [l] = true.
Proof. reflexivity. Qed.

(** RFC 9162 Section 4 calls the log a single append-only Merkle tree. The
    history-level operation is list append; Merkle proofs authenticate this
    relation but do not create it. *)
Definition ct_extend {A : Type} (old added : list A) : list A := old ++ added.

Theorem ct_extension_preserves_entries :
  forall (A : Type) (old added : list A) x,
    In x old -> In x (ct_extend old added).
Proof.
  intros A old added x Hin. unfold ct_extend. apply in_or_app. left. exact Hin.
Qed.

Theorem ct_extension_size_monotone :
  forall (A : Type) (old added : list A),
    length old <= length (ct_extend old added).
Proof.
  intros A old added. unfold ct_extend. rewrite app_length. lia.
Qed.

Print Assumptions rfc9162_inclusion_boundary_safe.
Print Assumptions rfc9162_consistency_boundary_safe.
Print Assumptions rfc9162_example_inclusion_d0.
Print Assumptions rfc9162_example_consistency_4_7.
Print Assumptions ct_extension_preserves_entries.
Print Assumptions ct_extension_size_monotone.
