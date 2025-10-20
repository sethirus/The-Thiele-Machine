From Coq Require Import List Bool Arith.PeanoNat.
From Coq Require Import Strings.String Strings.Ascii.
Import ListNotations.
Local Open Scope list_scope.

Require Import Kernel.VMState.

(** * Canonical binary encoding of VM state onto the kernel tape. *)

(** ** Primitive encodings *)

Fixpoint encode_nat (n : nat) : list bool :=
  match n with
  | 0 => [false]
  | S n' => true :: encode_nat n'
  end.

Fixpoint decode_nat (bs : list bool) : option (nat * list bool) :=
  match bs with
  | [] => None
  | false :: rest => Some (0, rest)
  | true :: rest =>
      match decode_nat rest with
      | Some (n, rest') => Some (S n, rest')
      | None => None
      end
  end.

Lemma decode_nat_correct :
  forall n rest,
    decode_nat (encode_nat n ++ rest) = Some (n, rest).
Proof.
  induction n as [|n IH]; intros rest; simpl.
  - reflexivity.
  - simpl.
    destruct (decode_nat (encode_nat n ++ rest)) as [[n' rest']|] eqn:Hdecode.
    + specialize (IH rest).
      rewrite IH in Hdecode.
      inversion Hdecode; subst; reflexivity.
    + specialize (IH rest).
      rewrite IH in Hdecode.
      discriminate.
Qed.

Definition encode_bool (b : bool) : list bool := [b].

Definition decode_bool (bs : list bool) : option (bool * list bool) :=
  match bs with
  | [] => None
  | b :: rest => Some (b, rest)
  end.

Lemma decode_bool_correct :
  forall b rest,
    decode_bool (encode_bool b ++ rest) = Some (b, rest).
Proof.
  intros b rest.
  reflexivity.
Qed.

Definition encode_ascii (a : ascii) : list bool :=
  match a with
  | Ascii b0 b1 b2 b3 b4 b5 b6 b7 =>
      [b0; b1; b2; b3; b4; b5; b6; b7]
  end.

Definition decode_ascii (bs : list bool) : option (ascii * list bool) :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      Some (Ascii b0 b1 b2 b3 b4 b5 b6 b7, rest)
  | _ => None
  end.

Lemma decode_ascii_correct :
  forall a rest,
    decode_ascii (encode_ascii a ++ rest) = Some (a, rest).
Proof.
  intros a rest.
  destruct a as [b0 b1 b2 b3 b4 b5 b6 b7]; simpl.
  reflexivity.
Qed.

(** ** List combinators *)

Fixpoint encode_list_payload {A}
  (encode : A -> list bool) (xs : list A) : list bool :=
  match xs with
  | [] => []
  | x :: xs' => encode x ++ encode_list_payload encode xs'
  end.

Definition encode_list {A} (encode : A -> list bool) (xs : list A) : list bool :=
  List.app (encode_nat (List.length xs)) (encode_list_payload encode xs).

Fixpoint decode_list {A}
  (decode : list bool -> option (A * list bool))
  (count : nat) (bs : list bool) : option (list A * list bool) :=
  match count with
  | 0 => Some ([], bs)
  | S count' =>
      match decode bs with
      | Some (x, rest) =>
          match decode_list decode count' rest with
          | Some (xs, rest') => Some (x :: xs, rest')
          | None => None
          end
      | None => None
      end
  end.

Definition decode_sequence {A}
  (decode : list bool -> option (A * list bool))
  (bs : list bool) : option (list A * list bool) :=
  match decode_nat bs with
  | Some (count, rest) => decode_list decode count rest
  | None => None
  end.

Lemma decode_list_payload_correct :
  forall (A : Type) (encode : A -> list bool)
         (decode : list bool -> option (A * list bool))
         (xs : list A) rest,
    (forall x rest', decode (encode x ++ rest') = Some (x, rest')) ->
    decode_list decode (List.length xs)
      (encode_list_payload encode xs ++ rest) = Some (xs, rest).
Proof.
  intros A encode decode xs.
  induction xs as [|x xs IH]; intros rest Hdecode; simpl.
  - reflexivity.
  - pose proof Hdecode as Hdecode_all.
    rewrite <- app_assoc.
    specialize (Hdecode x).
    specialize (Hdecode (encode_list_payload encode xs ++ rest)).
    rewrite Hdecode.
    simpl.
    rewrite (IH rest Hdecode_all).
    reflexivity.
Qed.

Lemma decode_sequence_correct :
  forall (A : Type) (encode : A -> list bool)
         (decode : list bool -> option (A * list bool))
         (xs : list A) rest,
    (forall x rest', decode (encode x ++ rest') = Some (x, rest')) ->
    decode_sequence decode (encode_list encode xs ++ rest) =
      Some (xs, rest).
Proof.
  intros A encode decode xs rest Hdecode.
  unfold decode_sequence, encode_list.
  rewrite <- app_assoc.
  rewrite decode_nat_correct.
  apply decode_list_payload_correct.
  assumption.
Qed.

(** ** Structured encodings for VM data types *)

Definition encode_string (s : string) : list bool :=
  encode_list encode_ascii (list_ascii_of_string s).

Definition decode_string (bs : list bool) : option (string * list bool) :=
  match decode_sequence decode_ascii bs with
  | Some (chars, rest) => Some (string_of_list_ascii chars, rest)
  | None => None
  end.

Lemma decode_string_correct :
  forall s rest,
    decode_string (encode_string s ++ rest) = Some (s, rest).
Proof.
  intros s rest.
  unfold encode_string, decode_string.
  rewrite decode_sequence_correct with (xs := list_ascii_of_string s).
  - simpl.
    rewrite string_of_list_ascii_of_string.
    reflexivity.
  - apply decode_ascii_correct.
Qed.

Definition encode_nat_list (xs : list nat) : list bool :=
  encode_list encode_nat xs.

Definition decode_nat_list (bs : list bool) : option (list nat * list bool) :=
  decode_sequence decode_nat bs.

Definition encode_string_list (xs : list string) : list bool :=
  encode_list encode_string xs.

Definition decode_string_list (bs : list bool)
  : option (list string * list bool) :=
  decode_sequence decode_string bs.

Lemma decode_nat_list_correct :
  forall xs rest,
    decode_nat_list (encode_nat_list xs ++ rest) = Some (xs, rest).
Proof.
  intros xs rest.
  unfold decode_nat_list, encode_nat_list.
  apply decode_sequence_correct.
  apply decode_nat_correct.
Qed.

Lemma decode_string_list_correct :
  forall xs rest,
    decode_string_list (encode_string_list xs ++ rest) = Some (xs, rest).
Proof.
  intros xs rest.
  unfold decode_string_list, encode_string_list.
  apply decode_sequence_correct.
  apply decode_string_correct.
Qed.

Definition encode_module_state (m : ModuleState) : list bool :=
  encode_nat_list m.(module_region) ++
  encode_string_list m.(module_axioms).

Definition decode_module_state (bs : list bool)
  : option (ModuleState * list bool) :=
  match decode_nat_list bs with
  | Some (region, rest) =>
      match decode_string_list rest with
      | Some (axioms, rest') =>
          Some ({| module_region := region;
                  module_axioms := axioms |}, rest')
      | None => None
      end
  | None => None
  end.

Lemma decode_module_state_correct :
  forall m rest,
    decode_module_state (encode_module_state m ++ rest) = Some (m, rest).
Proof.
  intros m rest.
  unfold encode_module_state, decode_module_state.
  change ((encode_nat_list (module_region m) ++ encode_string_list (module_axioms m)) ++ rest)
    with (encode_nat_list (module_region m) ++ (encode_string_list (module_axioms m) ++ rest)).
  rewrite decode_nat_list_correct.
  simpl.
  rewrite decode_string_list_correct.
  reflexivity.
Qed.

Definition encode_module_entry (entry : ModuleID * ModuleState) : list bool :=
  let '(mid, m) := entry in
  encode_nat mid ++ encode_module_state m.

Definition decode_module_entry (bs : list bool)
  : option ((ModuleID * ModuleState) * list bool) :=
  match decode_nat bs with
  | Some (mid, rest) =>
      match decode_module_state rest with
      | Some (m, rest') => Some ((mid, m), rest')
      | None => None
      end
  | None => None
  end.

Lemma decode_module_entry_correct :
  forall entry rest,
    decode_module_entry (encode_module_entry entry ++ rest) = Some (entry, rest).
Proof.
  intros [mid m] rest.
  unfold encode_module_entry, decode_module_entry.
  change ((encode_nat mid ++ encode_module_state m) ++ rest)
    with (encode_nat mid ++ (encode_module_state m ++ rest)).
  rewrite decode_nat_correct.
  simpl.
  rewrite decode_module_state_correct.
  reflexivity.
Qed.

Definition encode_partition_graph (g : PartitionGraph) : list bool :=
  encode_nat g.(pg_next_id) ++
  encode_list encode_module_entry g.(pg_modules).

Definition decode_partition_graph (bs : list bool)
  : option (PartitionGraph * list bool) :=
  match decode_nat bs with
  | Some (next_id, rest) =>
      match decode_sequence decode_module_entry rest with
      | Some (modules, rest') =>
          Some ({| pg_next_id := next_id;
                  pg_modules := modules |}, rest')
      | None => None
      end
  | None => None
  end.

Lemma decode_partition_graph_correct :
  forall g rest,
    decode_partition_graph (encode_partition_graph g ++ rest) = Some (g, rest).
Proof.
  intros g rest.
  unfold encode_partition_graph, decode_partition_graph.
  change ((encode_nat (pg_next_id g) ++ encode_list encode_module_entry (pg_modules g)) ++ rest)
    with (encode_nat (pg_next_id g) ++ (encode_list encode_module_entry (pg_modules g) ++ rest)).
  rewrite decode_nat_correct.
  simpl.
  rewrite decode_sequence_correct with (xs := pg_modules g).
  - reflexivity.
  - apply decode_module_entry_correct.
Qed.


Definition encode_csr (csrs : CSRState) : list bool :=
  encode_nat csrs.(csr_cert_addr) ++
  encode_nat csrs.(csr_status) ++
  encode_nat csrs.(csr_err).

Definition decode_csr (bs : list bool) : option (CSRState * list bool) :=
  match decode_nat bs with
  | Some (cert, rest) =>
      match decode_nat rest with
      | Some (status, rest') =>
          match decode_nat rest' with
          | Some (err, rest'') =>
              Some ({| csr_cert_addr := cert;
                      csr_status := status;
                      csr_err := err |}, rest'')
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Lemma decode_csr_correct :
  forall csrs rest,
    decode_csr (encode_csr csrs ++ rest) = Some (csrs, rest).
Proof.
  intros [cert status err] rest.
  unfold encode_csr, decode_csr.
  change ((encode_nat cert ++ encode_nat status ++ encode_nat err) ++ rest)
    with (encode_nat cert ++ (encode_nat status ++ (encode_nat err ++ rest))).
  rewrite decode_nat_correct.
  simpl.
  rewrite decode_nat_correct.
  simpl.
  rewrite decode_nat_correct.
  reflexivity.
Qed.


Definition encode_vm_state (s : VMState) : list bool :=
  encode_partition_graph s.(vm_graph) ++
  encode_csr s.(vm_csrs) ++
  encode_nat s.(vm_pc) ++
  encode_nat s.(vm_mu) ++
  encode_bool s.(vm_err).

Definition decode_vm_state (bs : list bool)
  : option (VMState * list bool) :=
  match decode_partition_graph bs with
  | Some (graph, rest) =>
      match decode_csr rest with
      | Some (csrs, rest') =>
          match decode_nat rest' with
          | Some (pc, rest'') =>
              match decode_nat rest'' with
              | Some (mu, rest''') =>
                  match decode_bool rest''' with
                  | Some (err, rest'''') =>
                      Some ({| vm_graph := graph;
                              vm_csrs := csrs;
                              vm_pc := pc;
                              vm_mu := mu;
                              vm_err := err |}, rest'''')
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Lemma decode_vm_state_correct :
  forall s rest,
    decode_vm_state (encode_vm_state s ++ rest) = Some (s, rest).
Proof.
  intros [graph csrs pc mu err] rest.
  unfold encode_vm_state, decode_vm_state.
  change ((encode_partition_graph graph ++ encode_csr csrs ++ encode_nat pc ++ encode_nat mu ++ encode_bool err) ++ rest)
    with (encode_partition_graph graph ++ (encode_csr csrs ++ (encode_nat pc ++ (encode_nat mu ++ (encode_bool err ++ rest))))).
  rewrite decode_partition_graph_correct.
  simpl.
  rewrite decode_csr_correct.
  simpl.
  rewrite decode_nat_correct.
  simpl.
  rewrite decode_nat_correct.
  simpl.
  rewrite decode_bool_correct.
  reflexivity.
Qed.

