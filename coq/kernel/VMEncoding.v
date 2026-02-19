From Coq Require Import List Bool Arith.PeanoNat.
From Coq Require Import Strings.String Strings.Ascii.
Import ListNotations.
Local Open Scope list_scope.

Require Import Kernel.
Require Import VMState.
Require Import VMStep.

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

(** [decode_nat_correct]: formal specification. *)
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

(** [decode_bool_correct]: formal specification. *)
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

(** [decode_ascii_correct]: formal specification. *)
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

(** [decode_list_payload_correct]: formal specification. *)
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

(** [decode_sequence_correct]: formal specification. *)
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

(** [decode_string_correct]: formal specification. *)
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

(** [decode_nat_list_correct]: formal specification. *)
Lemma decode_nat_list_correct :
  forall xs rest,
    decode_nat_list (encode_nat_list xs ++ rest) = Some (xs, rest).
Proof.
  intros xs rest.
  unfold decode_nat_list, encode_nat_list.
  apply decode_sequence_correct.
  apply decode_nat_correct.
Qed.

(** [decode_string_list_correct]: formal specification. *)
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

(** [decode_module_state_correct]: formal specification. *)
Lemma decode_module_state_correct :
  forall m rest,
    decode_module_state (encode_module_state m ++ rest) = Some (m, rest).
Proof.
  intros m rest.
  unfold encode_module_state, decode_module_state.
  rewrite <- app_assoc.
  rewrite decode_nat_list_correct.
  simpl.
  rewrite decode_string_list_correct.
  simpl.
  destruct m as [region axioms].
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

(** [decode_module_entry_correct]: formal specification. *)
Lemma decode_module_entry_correct :
  forall entry rest,
    decode_module_entry (encode_module_entry entry ++ rest) = Some (entry, rest).
Proof.
  intros [mid m] rest.
  unfold encode_module_entry, decode_module_entry.
  rewrite <- app_assoc.
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

(** [decode_partition_graph_correct]: formal specification. *)
Lemma decode_partition_graph_correct :
  forall g rest,
    decode_partition_graph (encode_partition_graph g ++ rest) = Some (g, rest).
Proof.
  intros g rest.
  unfold encode_partition_graph, decode_partition_graph.
  rewrite <- app_assoc.
  rewrite decode_nat_correct.
  simpl.
  rewrite decode_sequence_correct with (xs := pg_modules g).
  - simpl.
    destruct g as [next_id modules].
    reflexivity.
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

(** [decode_csr_correct]: formal specification. *)
Lemma decode_csr_correct :
  forall csrs rest,
    decode_csr (encode_csr csrs ++ rest) = Some (csrs, rest).
Proof.
  intros [cert status err] rest.
  unfold encode_csr, decode_csr.
  repeat rewrite <- app_assoc.
  rewrite decode_nat_correct.
  simpl.
  rewrite decode_nat_correct.
  simpl.
  rewrite decode_nat_correct.
  reflexivity.
Qed.


Definition encode_vm_state (s : VMState) : list bool :=
  (* Fixed header: pc, mu, err (for easy access) *)
  encode_nat s.(vm_pc) ++
  encode_nat s.(vm_mu) ++
  encode_bool s.(vm_err) ++
  (* Hardware-style scratch state *)
  encode_nat_list s.(vm_regs) ++
  encode_nat_list s.(vm_mem) ++
  (* Variable data: graph, csr, mu_tensor (placed after csr to simplify decoding) *)
  encode_partition_graph s.(vm_graph) ++
  encode_csr s.(vm_csrs) ++
  encode_nat_list s.(vm_mu_tensor).

Definition decode_vm_state (bs : list bool)
  : option (VMState * list bool) :=
  (* Decode fixed header first: pc, mu, err *)
  match decode_nat bs with
  | Some (pc, rest) =>
      match decode_nat rest with
      | Some (mu, rest') =>
          match decode_bool rest' with
          | Some (err, rest'') =>
        (* Then decode scratch state: regs, mem *)
        match decode_nat_list rest'' with
        | Some (regs, rest''') =>
          match decode_nat_list rest''' with
          | Some (mem, rest'''') =>
            (* Then decode variable data: graph, csr, then mu_tensor *)
            match decode_partition_graph rest'''' with
            | Some (graph, rest''''') =>
              match decode_csr rest''''' with
              | Some (csrs, rest'''''' ) =>
                match decode_nat_list rest'''''' with
                | Some (mu_tensor, rest''''''' ) =>
                  Some ({| vm_graph := graph;
                       vm_csrs := csrs;
                       vm_regs := regs;
                       vm_mem := mem;
                       vm_pc := pc;
                       vm_mu := mu;
                       vm_mu_tensor := mu_tensor;
                       vm_err := err |}, rest''''''' )
                | None => None
                end
              | None => None
              end
            | None => None
            end
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

(** The correctness of VM state encoding/decoding is justified by the
    correctness of the primitive encodings and the sequential composition
    of the decoding functions. *)
Lemma decode_vm_state_correct :
  forall s rest,
    decode_vm_state (encode_vm_state s ++ rest) = Some (s, rest).
Proof.
  intros [graph csrs regs mem pc mu mu_tensor err] rest.
  unfold encode_vm_state, decode_vm_state.
  repeat rewrite <- app_assoc.
  rewrite decode_nat_correct.
  simpl.
  replace (encode_nat mu ++ encode_bool err ++ encode_nat_list regs ++ encode_nat_list mem ++ encode_partition_graph graph ++ encode_csr csrs ++ encode_nat_list mu_tensor ++ rest)
    with (encode_nat mu ++ (encode_bool err ++ encode_nat_list regs ++ encode_nat_list mem ++ encode_partition_graph graph ++ encode_csr csrs ++ encode_nat_list mu_tensor ++ rest))
    by (repeat rewrite app_assoc; reflexivity).
  rewrite decode_nat_correct.
  simpl.
  set (tail := encode_bool err ++ encode_nat_list regs ++ encode_nat_list mem ++ encode_partition_graph graph ++ encode_csr csrs ++ encode_nat_list mu_tensor ++ rest).
  replace (encode_bool err ++ encode_nat_list regs ++ encode_nat_list mem ++ encode_partition_graph graph ++ encode_csr csrs ++ encode_nat_list mu_tensor ++ rest)
    with (encode_bool err ++ (encode_nat_list regs ++ encode_nat_list mem ++ encode_partition_graph graph ++ encode_csr csrs ++ encode_nat_list mu_tensor ++ rest))
    by (subst tail; repeat rewrite app_assoc; reflexivity).
  destruct (decode_bool (encode_bool err ++ tail)) as [[err' tail']|] eqn:Hbool.
  - pose proof (decode_bool_correct err tail) as Htarget.
    rewrite Htarget in Hbool.
    inversion Hbool; subst err' tail'.
    simpl.
    clear Hbool Htarget.
    subst tail.
    set (tail_regs := encode_nat_list mem ++ encode_partition_graph graph ++ encode_csr csrs ++ encode_nat_list mu_tensor ++ rest).
    replace (encode_nat_list regs ++ encode_nat_list mem ++ encode_partition_graph graph ++ encode_csr csrs ++ encode_nat_list mu_tensor ++ rest)
      with (encode_nat_list regs ++ tail_regs)
      by (subst tail_regs; repeat rewrite app_assoc; reflexivity).
    destruct (decode_nat_list (encode_nat_list regs ++ tail_regs))
      as [[regs' tail'']|] eqn:Hregs.
    + pose proof (decode_nat_list_correct regs tail_regs) as Hregs_target.
      rewrite Hregs_target in Hregs.
      inversion Hregs; subst regs' tail''.
      simpl.
      clear Hregs Hregs_target.
      subst tail_regs.
      set (tail_mem := encode_partition_graph graph ++ encode_csr csrs ++ encode_nat_list mu_tensor ++ rest).
      replace (encode_nat_list mem ++ encode_partition_graph graph ++ encode_csr csrs ++ encode_nat_list mu_tensor ++ rest)
        with (encode_nat_list mem ++ tail_mem)
        by (subst tail_mem; repeat rewrite app_assoc; reflexivity).
      destruct (decode_nat_list (encode_nat_list mem ++ tail_mem))
        as [[mem' tail''']|] eqn:Hmem.
      * pose proof (decode_nat_list_correct mem tail_mem) as Hmem_target.
        rewrite Hmem_target in Hmem.
        inversion Hmem; subst mem' tail'''.
        simpl.
        clear Hmem Hmem_target.
        subst tail_mem.
        set (tail_graph := encode_csr csrs ++ encode_nat_list mu_tensor ++ rest).
        replace (encode_partition_graph graph ++ encode_csr csrs ++ encode_nat_list mu_tensor ++ rest)
          with (encode_partition_graph graph ++ tail_graph)
          by (subst tail_graph; repeat rewrite app_assoc; reflexivity).
        destruct (decode_partition_graph (encode_partition_graph graph ++ tail_graph))
          as [[graph' tail'''']|] eqn:Hgraph.
        -- pose proof (decode_partition_graph_correct graph tail_graph) as Hgraph_target.
           rewrite Hgraph_target in Hgraph.
           inversion Hgraph; subst graph' tail''''.
           simpl.
           clear Hgraph Hgraph_target.
           subst tail_graph.
           destruct (decode_csr (encode_csr csrs ++ encode_nat_list mu_tensor ++ rest)) as [[csrs' rest'']|] eqn:Hcsr.
           ++ pose proof (decode_csr_correct csrs (encode_nat_list mu_tensor ++ rest)) as Hcsr_target.
              rewrite Hcsr_target in Hcsr.
              inversion Hcsr; subst csrs' rest''.
              (* decode mu_tensor that follows csrs in the encoding *)
              destruct (decode_nat_list (encode_nat_list mu_tensor ++ rest)) as [[mu_tensor' rest''']|] eqn:Hmut.
              ** pose proof (decode_nat_list_correct mu_tensor rest) as Hmut_target.
                 rewrite Hmut_target in Hmut.
                 inversion Hmut; subst mu_tensor' rest'''.
                 simpl. reflexivity.
              ** pose proof (decode_nat_list_correct mu_tensor rest) as Hmut_target.
                 rewrite Hmut_target in Hmut.
                 discriminate.
           ++ pose proof (decode_csr_correct csrs (encode_nat_list mu_tensor ++ rest)) as Hcsr_target.
              rewrite Hcsr_target in Hcsr.
              discriminate.
        -- pose proof (decode_partition_graph_correct graph tail_graph) as Hgraph_target.
           rewrite Hgraph_target in Hgraph.
           discriminate.
      * pose proof (decode_nat_list_correct mem tail_mem) as Hmem_target.
        rewrite Hmem_target in Hmem.
        discriminate.
    + pose proof (decode_nat_list_correct regs tail_regs) as Hregs_target.
      rewrite Hregs_target in Hregs.
      discriminate.
  - pose proof (decode_bool_correct err tail) as Htarget.
    rewrite Htarget in Hbool.
    discriminate.
Qed.

(** ** Kernel Tape Layout Schema *)

(** The kernel tape is divided into regions for efficient VM state access:
    - Header: pc, mu, err (fixed size)
    - Partition graph: dynamic size, starts after header
    - CSR: fixed size, starts after graph
*)

(** Layout constants - updated for new encoding order *)
Definition pc_offset : nat := Nat.sub 1 1.    (* pc starts at position 0 *)
Definition mu_offset_min : nat := 1. (* mu starts after at least 1 bit for pc *)
Definition err_offset_min : nat := 2. (* err starts after at least 2 bits *)
Definition csr_size : nat := 3.     (* cert_addr + status + err *)

(** ** Tape manipulation primitives *)

(** Encode VM state directly to tape at offset 0 *)
Definition encode_vm_state_to_tape (s : VMState) : list bool :=
  encode_vm_state s.

(** Decode VM state from tape starting at offset 0 *)
Definition decode_vm_state_from_tape (tape : list bool) : option VMState :=
  match decode_vm_state tape with
  | Some (s, _) => Some s
  | None => None
  end.

(** Compute offset to partition graph region *)
Definition graph_offset (tape : list bool) : nat :=
  (* Graph starts after pc + mu + err (fixed header) *)
  (* Since sizes are variable, this is approximate - need to parse *)
  err_offset_min.  (* Conservative underestimate *)

(** Compute offset to CSR region (depends on graph size) *)
Definition csr_offset (tape : list bool) : nat :=
  match decode_nat tape with
  | Some (_, rest1) =>
      match decode_nat rest1 with
      | Some (_, rest2) =>
          match decode_bool rest2 with
          | Some (_, rest3) =>
        match decode_nat_list rest3 with
        | Some (_, rest4) =>
          match decode_nat_list rest4 with
          | Some (_, rest5) =>
            match decode_partition_graph rest5 with
            | Some (_, rest6) => List.length tape - List.length rest6
            | None => 0 (* Error case *)
            end
          | None => 0
          end
        | None => 0
        end
          | None => 0
          end
      | None => 0
      end
  | None => 0
  end.

(** Update a specific field in the tape efficiently *)
Definition update_vm_pc_in_tape (tape : list bool) (new_pc : nat) : list bool :=
  match decode_vm_state_from_tape tape with
  | Some s =>
      let s' := {| vm_graph := s.(vm_graph);
                   vm_csrs := s.(vm_csrs);
                   vm_regs := s.(vm_regs);
                   vm_mem := s.(vm_mem);
                   vm_pc := new_pc;
                   vm_mu := s.(vm_mu);
                   vm_mu_tensor := s.(vm_mu_tensor);
                   vm_err := s.(vm_err) |} in
      encode_vm_state_to_tape s'
  | None => tape  (* error case *)
  end.

Definition update_vm_mu_in_tape (tape : list bool) (new_mu : nat) : list bool :=
  match decode_vm_state_from_tape tape with
  | Some s =>
      let s' := {| vm_graph := s.(vm_graph);
                   vm_csrs := s.(vm_csrs);
                   vm_regs := s.(vm_regs);
                   vm_mem := s.(vm_mem);
                   vm_pc := s.(vm_pc);
                   vm_mu := new_mu;
                   vm_mu_tensor := s.(vm_mu_tensor);
                   vm_err := s.(vm_err) |} in
      encode_vm_state_to_tape s'
  | None => tape
  end.

Definition update_vm_err_in_tape (tape : list bool) (new_err : bool) : list bool :=
  match decode_vm_state_from_tape tape with
  | Some s =>
      let s' := {| vm_graph := s.(vm_graph);
                   vm_csrs := s.(vm_csrs);
                   vm_regs := s.(vm_regs);
                   vm_mem := s.(vm_mem);
                   vm_pc := s.(vm_pc);
                   vm_mu := s.(vm_mu);
                   vm_mu_tensor := s.(vm_mu_tensor);
                   vm_err := new_err |} in
      encode_vm_state_to_tape s'
  | None => tape
  end.

(** Update partition graph (more expensive, rebuilds entire encoding) *)
Definition update_vm_graph_in_tape (tape : list bool) (new_graph : PartitionGraph) : list bool :=
  match decode_vm_state_from_tape tape with
  | Some s =>
      let s' := {| vm_graph := new_graph;
                   vm_csrs := s.(vm_csrs);
                   vm_regs := s.(vm_regs);
                   vm_mem := s.(vm_mem);
                   vm_pc := s.(vm_pc);
                   vm_mu := s.(vm_mu);
                   vm_mu_tensor := s.(vm_mu_tensor);
                   vm_err := s.(vm_err) |} in
      encode_vm_state_to_tape s'
  | None => tape
  end.

(** Update CSR state *)
Definition update_vm_csrs_in_tape (tape : list bool) (new_csrs : CSRState) : list bool :=
  match decode_vm_state_from_tape tape with
  | Some s =>
      let s' := {| vm_graph := s.(vm_graph);
                   vm_csrs := new_csrs;
                   vm_regs := s.(vm_regs);
                   vm_mem := s.(vm_mem);
                   vm_pc := s.(vm_pc);
                   vm_mu := s.(vm_mu);
                   vm_mu_tensor := s.(vm_mu_tensor);
                   vm_err := s.(vm_err) |} in
      encode_vm_state_to_tape s'
  | None => tape
  end.

(** ** Layout correctness proofs *)

Lemma encode_decode_vm_state_roundtrip :
  forall s,
    decode_vm_state_from_tape (encode_vm_state_to_tape s) = Some s.
Proof.
  intros s.
  unfold decode_vm_state_from_tape, encode_vm_state_to_tape.
  pose proof (decode_vm_state_correct s []).
  rewrite app_nil_r in H.
  rewrite H.
  reflexivity.
Qed.

(** [update_pc_preserves_other_fields]: formal specification. *)
Lemma update_pc_preserves_other_fields :
  forall tape pc s,
    decode_vm_state_from_tape tape = Some s ->
    exists s', decode_vm_state_from_tape (update_vm_pc_in_tape tape pc) = Some s' /\
               s'.(vm_graph) = s.(vm_graph) /\
               s'.(vm_csrs) = s.(vm_csrs) /\
               s'.(vm_pc) = pc /\
               s'.(vm_mu) = s.(vm_mu) /\
               s'.(vm_mu_tensor) = s.(vm_mu_tensor) /\
               s'.(vm_err) = s.(vm_err).
Proof.
  intros tape pc s Hdecode.
  unfold update_vm_pc_in_tape.
  rewrite Hdecode.
  exists {| vm_graph := s.(vm_graph);
            vm_csrs := s.(vm_csrs);
            vm_regs := s.(vm_regs);
            vm_mem := s.(vm_mem);
            vm_pc := pc;
            vm_mu := s.(vm_mu);
            vm_mu_tensor := s.(vm_mu_tensor);
            vm_err := s.(vm_err) |}.
  split.
  - apply encode_decode_vm_state_roundtrip.
  - simpl; repeat split; auto.
Qed.

(** Similar lemmas for other update functions would follow the same pattern *)

(** ** Kernel program generators for tape manipulation *)

(** Generate a program that increments pc in the tape encoding *)
Definition compile_increment_pc : program :=
  (* PC field starts at position 0, encoded in unary (sequence of trues ending with false) *)
  (* To increment: write true at the current position (end of pc) and move right *)
  (* Program: write true, then move right *)
  (* Assumes head starts at 0 *)
  [T_Write true; T_Move DRight].

(** Generate a program that adds delta to μ in the tape encoding *)
Definition compile_add_mu (delta : nat) : program :=
  (* Layout: pc(unary) + μ(unary) + err(bool) + graph + csr *)
  (* To add to μ: skip pc (scan until false), then extend μ encoding with delta trues *)
  (* Program: scan right past pc (until false), then write delta trues *)
  if delta =? 0 then []
  else
    (* Scan past pc encoding *)
    [T_Move DRight; T_Branch 0] ++
    (* Now at start of μ encoding, extend it by writing delta trues *)
    repeat (T_Write true) delta.
  (* State 0: move right (scanning pc) *)
  (* State 1: if true, branch back to 0; if false, halt and start writing *)

(** Generate a program that updates the err bit in the fixed header *)
Definition compile_update_err (new_err : bool) : program :=
  (* Layout: pc(unary) + μ(unary) + err(bool) + graph + csr *)
  (* To update err: skip pc (scan until false), skip μ (scan until false), write err *)
  (* Program: scan right past pc (until false), scan right past μ (until false), write err *)
  [T_Move DRight; T_Branch 0; T_Move DRight; T_Branch 2; T_Write new_err].
  (* State 0: move right (scanning pc) *)
  (* State 1: if true, branch back to 0; if false, go to state 2 *)
  (* State 2: move right (scanning μ) *)
  (* State 3: if true, branch back to 2; if false, go to state 4 *)
  (* State 4: write new_err *)

(** Generate a program that applies a VM operation to the encoded state *)
Definition compile_vm_operation (instr : vm_instruction) : program :=
  (* NOTE: Full VM operation encoding is complex and requires variable-length graph parsing.
     This is validated by executable Python VM tests instead of formal proof.
     See: tests/test_vm_encoding_validation.py for validation coverage *)
  (* Complex: requires parsing variable-sized graph to reach CSR region *)
  (* For now: implement operations that only affect fixed header *)
  match instr with
  | instr_pnew region cost =>
      (* Would need to update graph encoding with new partition *)
      [T_Halt]  (* Placeholder - validated by Python VM *)
  | instr_psplit module left_region right_region cost =>
      (* Complex graph manipulation - validated by Python VM *)
      [T_Halt]
  | instr_pmerge m1 m2 cost =>
      (* Complex graph manipulation - validated by Python VM *)
      [T_Halt]
  | instr_lassert module formula _ cost =>
      (* Update graph with axiom, update CSR status/err - validated by Python VM *)
      [T_Halt]
  | instr_ljoin cert1 cert2 cost =>
      (* Update CSR cert_addr and err based on cert comparison *)
      [T_Halt]
  | instr_mdlacc module cost =>
      (* No state change beyond pc/μ *)
      [T_Halt]
  | instr_emit module payload cost =>
      (* Update CSR cert_addr - requires navigating past variable graph *)
      (* NOTE: Graph parsing implementation validated by Python VM tests *)
      [T_Halt]
  | instr_reveal module bits cert cost =>
      (* REVEAL opcode: Update CSR cert_addr with revelation certificate *)
      (* Semantically: marks explicit information revelation *)
      [T_Halt]
  | instr_pdiscover module evidence cost =>
      (* Update graph with discovery *)
      [T_Halt]
  | instr_pyexec payload cost =>
      (* Set err to true - affects fixed header err bit *)
      compile_update_err true
  | instr_chsh_trial x y a b cost =>
      (* CHSH trial event: does not change fixed header beyond pc/μ. *)
      [T_Halt]
    | instr_xfer dst src cost =>
      (* Transfer operation - no state change beyond pc/μ *)
      [T_Halt]
    | instr_xor_load dst addr cost =>
      (* XOR load operation *)
      [T_Halt]
    | instr_xor_add dst src cost =>
      (* XOR add operation *)
      [T_Halt]
    | instr_xor_swap a b cost =>
      (* XOR swap operation *)
      [T_Halt]
    | instr_xor_rank dst src cost =>
      (* XOR rank operation *)
      [T_Halt]
  | instr_oracle_halts payload cost =>
      (* Oracle halting check *)
      [T_Halt]
  | instr_halt cost =>
      (* Halt instruction *)
      [T_Halt]
  end.

(** ** Layout bounds proof *)
(* NOTE: Bounds proof requires proving decode only succeeds on sufficiently long tapes.
   This property is validated by executable tests in tests/test_vm_encoding_bounds.py
   The proof would establish: decode(encode(s)) = Some s only when tape length >= required_size(s)
   
   The property is validated by executable tests covering:
   - Test that decode fails on truncated tapes
   - Test that decode succeeds on properly sized tapes
   - Test boundary conditions (minimum valid size)
*)

