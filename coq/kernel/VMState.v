From Coq Require Import List Bool Arith.PeanoNat.
From Coq Require Import Strings.String Strings.Ascii.
Import ListNotations.

(** * Virtual Machine state model closely mirroring [thielecpu.state] *)

Definition ModuleID := nat.
Definition VMAxiom := string.
Definition AxiomSet := list VMAxiom.

(** Regions are represented as duplicate-free lists of natural numbers. *)
Fixpoint nat_list_mem (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: ys => if Nat.eqb x y then true else nat_list_mem x ys
  end.

Definition nat_list_add (xs : list nat) (x : nat) : list nat :=
  if nat_list_mem x xs then xs else x :: xs.

Definition normalize_region (region : list nat) : list nat :=
  fold_left (fun acc n => nat_list_add acc n) region [].

Definition nat_list_subset (xs ys : list nat) : bool :=
  forallb (fun x => nat_list_mem x ys) xs.

Definition nat_list_disjoint (xs ys : list nat) : bool :=
  forallb (fun x => negb (nat_list_mem x ys)) xs.

Definition nat_list_union (xs ys : list nat) : list nat :=
  fold_left (fun acc n => nat_list_add acc n) ys (normalize_region xs).

Definition nat_list_eq (xs ys : list nat) : bool :=
  nat_list_subset xs ys && nat_list_subset ys xs.

Record ModuleState := {
  module_region : list nat;
  module_axioms : AxiomSet
}.

Definition normalize_module (m : ModuleState) : ModuleState :=
  {| module_region := normalize_region m.(module_region);
     module_axioms := m.(module_axioms) |}.

Record PartitionGraph := {
  pg_next_id : ModuleID;
  pg_modules : list (ModuleID * ModuleState)
}.

Definition empty_graph : PartitionGraph :=
  {| pg_next_id := 1;
     pg_modules := [] |}.

Fixpoint graph_lookup_modules
  (modules : list (ModuleID * ModuleState)) (mid : ModuleID)
  : option ModuleState :=
  match modules with
  | [] => None
  | (id, m) :: rest =>
      if Nat.eqb id mid then Some m else graph_lookup_modules rest mid
  end.

Definition graph_lookup (g : PartitionGraph) (mid : ModuleID)
  : option ModuleState :=
  graph_lookup_modules g.(pg_modules) mid.

Fixpoint graph_insert_modules
  (modules : list (ModuleID * ModuleState)) (mid : ModuleID) (m : ModuleState)
  : list (ModuleID * ModuleState) :=
  match modules with
  | [] => [(mid, m)]
  | (id, existing) :: rest =>
      if Nat.eqb id mid
      then (mid, m) :: rest
      else (id, existing) :: graph_insert_modules rest mid m
  end.

Definition graph_update (g : PartitionGraph) (mid : ModuleID) (m : ModuleState)
  : PartitionGraph :=
  {| pg_next_id := g.(pg_next_id);
     pg_modules := graph_insert_modules g.(pg_modules) mid (normalize_module m) |}.

Fixpoint graph_remove_modules
  (modules : list (ModuleID * ModuleState)) (mid : ModuleID)
  : option (list (ModuleID * ModuleState) * ModuleState) :=
  match modules with
  | [] => None
  | (id, m) :: rest =>
      if Nat.eqb id mid
      then Some (rest, m)
      else
        match graph_remove_modules rest mid with
        | None => None
        | Some (rest', removed) => Some ((id, m) :: rest', removed)
        end
  end.

Definition graph_remove (g : PartitionGraph) (mid : ModuleID)
  : option (PartitionGraph * ModuleState) :=
  match graph_remove_modules g.(pg_modules) mid with
  | None => None
  | Some (modules', removed) =>
      Some ({| pg_next_id := g.(pg_next_id); pg_modules := modules' |}, removed)
  end.

Definition graph_add_module (g : PartitionGraph)
  (region : list nat) (axioms : AxiomSet)
  : PartitionGraph * ModuleID :=
  let module := normalize_module {| module_region := region; module_axioms := axioms |} in
  let mid := g.(pg_next_id) in
  ({| pg_next_id := S mid;
      pg_modules := (mid, module) :: g.(pg_modules) |}, mid).

Fixpoint graph_find_region_modules
  (modules : list (ModuleID * ModuleState)) (region : list nat)
  : option ModuleID :=
  match modules with
  | [] => None
  | (id, m) :: rest =>
      if nat_list_eq m.(module_region) region
      then Some id
      else graph_find_region_modules rest region
  end.

Definition graph_find_region (g : PartitionGraph) (region : list nat)
  : option ModuleID :=
  graph_find_region_modules g.(pg_modules) (normalize_region region).

Definition graph_add_axiom (g : PartitionGraph) (mid : ModuleID) (ax : VMAxiom)
  : PartitionGraph :=
  match graph_lookup g mid with
  | None => g
  | Some m =>
      let updated := {| module_region := m.(module_region);
                        module_axioms := m.(module_axioms) ++ [ax] |} in
      graph_update g mid updated
  end.

Definition graph_add_axioms (g : PartitionGraph) (mid : ModuleID)
  (axs : list VMAxiom) : PartitionGraph :=
  fold_left (fun acc ax => graph_add_axiom acc mid ax) axs g.

Definition graph_record_discovery (g : PartitionGraph) (mid : ModuleID)
  (evidence : list VMAxiom) : PartitionGraph :=
  graph_add_axioms g mid evidence.

Definition graph_pnew (g : PartitionGraph) (region : list nat)
  : PartitionGraph * ModuleID :=
  let normalized := normalize_region region in
  match graph_find_region g normalized with
  | Some existing => (g, existing)
  | None => graph_add_module g normalized []
  end.

Definition partition_valid
  (original left right : list nat) : bool :=
  nat_list_subset left original &&
  nat_list_subset right original &&
  nat_list_disjoint left right &&
  nat_list_subset original (nat_list_union left right).

Definition graph_psplit (g : PartitionGraph) (mid : ModuleID)
  (left right : list nat)
  : option (PartitionGraph * ModuleID * ModuleID) :=
  match graph_lookup g mid with
  | None => None
  | Some m =>
      let axioms := m.(module_axioms) in
      let original := m.(module_region) in
      let left_norm := normalize_region left in
      let right_norm := normalize_region right in
      if orb (Nat.eqb (List.length left_norm) 0)
             (Nat.eqb (List.length right_norm) 0)
      then
        let '(g', empty_id) := graph_add_module g [] [] in
        Some (g', mid, empty_id)
      else if partition_valid original left_norm right_norm then
        match graph_remove g mid with
        | None => None
        | Some (g_removed, _) =>
            let '(g_left, left_id) := graph_add_module g_removed left_norm axioms in
            let '(g_right, right_id) := graph_add_module g_left right_norm axioms in
            Some (g_right, left_id, right_id)
        end
      else None
  end.

Definition graph_pmerge (g : PartitionGraph) (m1 m2 : ModuleID)
  : option (PartitionGraph * ModuleID) :=
  if Nat.eqb m1 m2 then None else
  match graph_remove g m1 with
  | None => None
  | Some (g_without_m1, mod1) =>
      match graph_remove g_without_m1 m2 with
      | None => None
      | Some (g_without_both, mod2) =>
          if negb (nat_list_disjoint mod1.(module_region) mod2.(module_region))
          then None
          else
            let union := nat_list_union mod1.(module_region) mod2.(module_region) in
            let combined_axioms := mod1.(module_axioms) ++ mod2.(module_axioms) in
            match graph_find_region g_without_both union with
            | Some existing =>
                match graph_lookup g_without_both existing with
                | None => None
                | Some existing_mod =>
                    let updated := {| module_region := existing_mod.(module_region);
                                      module_axioms := existing_mod.(module_axioms)
                                                      ++ combined_axioms |} in
                    Some (graph_update g_without_both existing updated, existing)
                end
            | None =>
                let '(g', merged_id) :=
                  graph_add_module g_without_both union combined_axioms in
                Some (g', merged_id)
            end
      end
  end.

Record CSRState := {
  csr_cert_addr : nat;
  csr_status : nat;
  csr_err : nat
}.

Definition csr_set_status (csrs : CSRState) (status : nat) : CSRState :=
  {| csr_cert_addr := csrs.(csr_cert_addr);
     csr_status := status;
     csr_err := csrs.(csr_err) |}.

Definition csr_set_err (csrs : CSRState) (err : nat) : CSRState :=
  {| csr_cert_addr := csrs.(csr_cert_addr);
     csr_status := csrs.(csr_status);
     csr_err := err |}.

Definition csr_set_cert_addr (csrs : CSRState) (addr : nat) : CSRState :=
  {| csr_cert_addr := addr;
     csr_status := csrs.(csr_status);
     csr_err := csrs.(csr_err) |}.

Record VMState := {
  vm_graph : PartitionGraph;
  vm_csrs : CSRState;
  vm_pc : nat;
  vm_mu : nat;
  vm_err : bool
}.

Definition advance_pc (s : VMState) : nat := S s.(vm_pc).

Definition ascii_checksum (s : string) : nat :=
  fold_right (fun ch acc => nat_of_ascii ch + acc) 0 (list_ascii_of_string s).

Definition update_state
  (s : VMState) (graph : PartitionGraph) (csrs : CSRState)
  (mu : nat) (err : bool)
  : VMState :=
  {| vm_graph := graph;
     vm_csrs := csrs;
     vm_pc := advance_pc s;
     vm_mu := mu;
     vm_err := err |}.
