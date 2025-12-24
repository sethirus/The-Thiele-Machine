From Coq Require Import List Bool Arith.PeanoNat ZArith.
From Coq Require Import Strings.String Strings.Ascii.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** Minimal, deterministic certificate checkers for the VM kernel.

    These are intended to mirror the Python implementations in
    thielecpu/certcheck.py closely enough for executable isomorphism gates.

    Certificates are currently passed around as raw text (DIMACS CNF for
    formulas, LRAT for UNSAT proofs, and a whitespace-separated assignment
    for SAT models).
*)

Module CertCheck.

  (* ---------- basic string/list utilities ---------- *)

  Fixpoint string_to_list (s : string) : list ascii :=
    match s with
    | EmptyString => []
    | String c s' => c :: string_to_list s'
    end.

  Fixpoint list_to_string (l : list ascii) : string :=
    match l with
    | [] => EmptyString
    | c :: l' => String c (list_to_string l')
    end.

  Definition ascii_nat (c : ascii) : nat := nat_of_ascii c.

  Definition is_space (c : ascii) : bool :=
    match ascii_nat c with
    | 9%nat (* \t *) => true
    | 10%nat (* \n *) => true
    | 13%nat (* \r *) => true
    | 32%nat (* space *) => true
    | _ => false
    end.

  Fixpoint trim_left_list (l : list ascii) : list ascii :=
    match l with
    | [] => []
    | c :: l' => if is_space c then trim_left_list l' else l
    end.

  Definition trim_left (s : string) : string :=
    list_to_string (trim_left_list (string_to_list s)).

  Fixpoint split_lines_aux (l : list ascii) (cur : list ascii) : list (list ascii) :=
    match l with
    | [] => [rev cur]
    | c :: l' =>
        if Nat.eqb (ascii_nat c) 10%nat (* \n *) then
          rev cur :: split_lines_aux l' []
        else
          split_lines_aux l' (c :: cur)
    end.

  Definition split_lines (s : string) : list string :=
    map list_to_string (split_lines_aux (string_to_list s) []).

  Fixpoint split_ws_aux (l : list ascii) (cur : list ascii) : list (list ascii) :=
    match l with
    | [] =>
        match rev cur with
        | [] => []
        | tok => [tok]
        end
    | c :: l' =>
        if is_space c then
          match rev cur with
          | [] => split_ws_aux l' []
          | tok => tok :: split_ws_aux l' []
          end
        else
          split_ws_aux l' (c :: cur)
    end.

  Definition split_ws (s : string) : list string :=
    map list_to_string (split_ws_aux (string_to_list s) []).

  Definition starts_with_char (ch : ascii) (s : string) : bool :=
    match trim_left s with
    | EmptyString => false
    | String c _ => Ascii.eqb c ch
    end.

  (* ---------- integer parsing ---------- *)

  Definition is_digit (c : ascii) : bool :=
    let n := ascii_nat c in
    Nat.leb 48 n && Nat.leb n 57.

  Fixpoint parse_nat_digits (l : list ascii) (acc : nat) : option nat :=
    match l with
    | [] => Some acc
    | c :: l' =>
        if is_digit c then
          let d := Nat.sub (ascii_nat c) 48 in
          parse_nat_digits l' (Nat.add (Nat.mul 10 acc) d)
        else None
    end.

  Definition parse_int (s : string) : option Z :=
    let l := string_to_list (trim_left s) in
    match l with
    | [] => None
    | c :: rest =>
        if Ascii.eqb c (Ascii.ascii_of_nat 45) (* '-' *) then
          match parse_nat_digits rest 0 with
          | Some n => Some (- (Z.of_nat n))
          | None => None
          end
        else if Ascii.eqb c (Ascii.ascii_of_nat 43) (* '+' *) then
          match parse_nat_digits rest 0 with
          | Some n => Some (Z.of_nat n)
          | None => None
          end
        else
          match parse_nat_digits l 0 with
          | Some n => Some (Z.of_nat n)
          | None => None
          end
    end.

  Definition parse_nat (s : string) : option nat :=
    match parse_int s with
    | Some z =>
  (* SAFE: Bounded arithmetic operation with explicit domain *)
        if (z <? 0)%Z then None else Some (Z.to_nat z)
    | None => None
    end.

  (* ---------- DIMACS parsing ---------- *)

  Record dimacs_cnf :=
    { cnf_num_vars : nat;
      cnf_clauses : list (list Z) }.

  Definition take_until_zero (zs : list Z) : list Z :=
    let fix go (l : list Z) (acc : list Z) :=
      match l with
      | [] => rev acc
      | z :: l' => if Z.eqb z 0 then rev acc else go l' (z :: acc)
      end
    in go zs [].

  Definition parse_clause_tokens (toks : list string) : option (list Z) :=
    let ints :=
      let fix go (ts : list string) (acc : list Z) :=
        match ts with
        | [] => Some (rev acc)
        | t :: ts' =>
            match parse_int t with
            | Some z => go ts' (z :: acc)
            | None => None
            end
        end
      in go toks []
    in
    match ints with
    | Some zs => Some (take_until_zero zs)
    | None => None
    end.

  Definition parse_dimacs (text : string) : option dimacs_cnf :=
    let lines := split_lines text in
    let fix go (ls : list string) (num_vars : option nat) (clauses : list (list Z)) :=
      match ls with
      | [] =>
          match num_vars with
          | Some nv => Some {| cnf_num_vars := nv; cnf_clauses := rev clauses |}
          | None => None
          end
      | line :: ls' =>
          let line' := trim_left line in
          match line' with
          | EmptyString => go ls' num_vars clauses
          | String c _ =>
              if Ascii.eqb c (Ascii.ascii_of_nat 99) (* 'c' *) then
                go ls' num_vars clauses
              else if Ascii.eqb c (Ascii.ascii_of_nat 112) (* 'p' *) then
                let toks := split_ws line' in
                match toks with
                | _p :: _cnf :: nv :: _nc :: _ =>
                    match parse_nat nv with
                    | Some nv' => go ls' (Some nv') clauses
                    | None => None
                    end
                | _ => None
                end
              else
                match parse_clause_tokens (split_ws line') with
                | Some cl => go ls' num_vars (cl :: clauses)
                | None => None
                end
          end
      end
    in go lines None [].

  (* ---------- model checking ---------- *)

  Fixpoint lookup_bool (x : nat) (m : list (nat * bool)) : option bool :=
    match m with
    | [] => None
    | (k, v) :: m' => if Nat.eqb k x then Some v else lookup_bool x m'
    end.

  Definition insert_bool (x : nat) (v : bool) (m : list (nat * bool)) : list (nat * bool) :=
    (x, v) :: m.

  Definition remove_prefix_v (s : string) : string :=
    match s with
    | String c rest =>
        if orb (Ascii.eqb c (Ascii.ascii_of_nat 118)) (* 'v' *)
               (Ascii.eqb c (Ascii.ascii_of_nat 86)) (* 'V' *)
        then rest else s
    | _ => s
    end.

  Fixpoint split_on_eq_aux (l : list ascii) (acc : list ascii) : option (list ascii * list ascii) :=
    match l with
    | [] => None
    | c :: l' =>
        if Nat.eqb (ascii_nat c) 61%nat (* '=' *) then
          Some (rev acc, l')
        else
          split_on_eq_aux l' (c :: acc)
    end.

  Definition split_on_eq (s : string) : option (string * string) :=
    match split_on_eq_aux (string_to_list s) [] with
    | Some (l1, l2) => Some (list_to_string l1, list_to_string l2)
    | None => None
    end.

  Definition value_is_false (s : string) : bool :=
    (* Mirrors Python: treat "0", "false", "f" as false; everything else true. *)
    let t := trim_left s in
    orb (String.eqb t "0") (orb (String.eqb t "false") (String.eqb t "f")).

  Definition parse_assignment_token (tok : string) : option (nat * bool) :=
    if String.eqb tok "0" then None
    else
      match split_on_eq tok with
      | Some (lhs, rhs) =>
          match parse_nat (remove_prefix_v lhs) with
          | Some var => Some (var, negb (value_is_false rhs))
          | None => None
          end
      | None =>
          match parse_int tok with
          | Some lit =>
              if Z.eqb lit 0 then None
  (* SAFE: Bounded arithmetic operation with explicit domain *)
              else
                let var := Z.to_nat (Z.abs lit) in
                Some (var, (lit >? 0)%Z)
          | None => None
          end
      end.

  Definition parse_assignment (text : string) : option (list (nat * bool)) :=
    let toks := split_ws text in
    let fix go (ts : list string) (acc : list (nat * bool)) :=
      match ts with
      | [] => Some acc
      | t :: ts' =>
          match parse_assignment_token t with
          | Some (var, v) => go ts' (insert_bool var v acc)
          | None => go ts' acc
          end
      end
    in go toks [].

  Definition clause_satisfied (asgn : list (nat * bool)) (cl : list Z) : bool :=
    let fix go (lits : list Z) : bool :=
      match lits with
  (* SAFE: Bounded arithmetic operation with explicit domain *)
      | [] => false
      | lit :: lits' =>
      (* SAFE: Bounded arithmetic operation with explicit domain *)
          let var := Z.to_nat (Z.abs lit) in
          match lookup_bool var asgn with
          | Some b => if Bool.eqb b (lit >? 0)%Z then true else go lits'
          | None => false
          end
      end
    in go cl.

  Definition check_model (cnf_text : string) (assignment_text : string) : bool :=
    match parse_dimacs cnf_text, parse_assignment assignment_text with
    | Some cnf, Some asgn =>
        if (Nat.ltb (List.length asgn) cnf.(cnf_num_vars)) then false
        else
          forallb (clause_satisfied asgn) cnf.(cnf_clauses)
    | _, _ => false
    end.

  (* ---------- LRAT / RUP checking ---------- *)

  Definition assoc_remove (k : nat) (db : list (nat * list Z)) : list (nat * list Z) :=
    filter (fun kv => negb (Nat.eqb (fst kv) k)) db.

  Definition db_clauses (db : list (nat * list Z)) : list (list Z) :=
    map snd db.

  Definition eval_clause (asgn : list (nat * bool)) (cl : list Z) : (bool * list Z) :=
    let fix go (lits : list Z) (undec : list Z) : (bool * list Z) :=
  (* SAFE: Bounded arithmetic operation with explicit domain *)
      match lits with
      | [] => (false, rev undec)
      | lit :: lits' =>
      (* SAFE: Bounded arithmetic operation with explicit domain *)
          let var := Z.to_nat (Z.abs lit) in
          match lookup_bool var asgn with
          | Some b =>
              if Bool.eqb b (lit >? 0)%Z then (true, []) else go lits' undec
          | None => go lits' (lit :: undec)
          end
      end
    in go cl [].

  Fixpoint unit_conflict_fuel
    (fuel : nat)
    (num_vars : nat)
    (clauses : list (list Z))
    (asgn : list (nat * bool))
    (queue : list Z)
    : bool :=
    match fuel with
    | 0%nat => false
  (* SAFE: Bounded arithmetic operation with explicit domain *)
    | S fuel' =>
        match queue with
        | [] => false
        | lit :: queue' =>
      (* SAFE: Bounded arithmetic operation with explicit domain *)
            let var := Z.to_nat (Z.abs lit) in
            let value := (lit >? 0)%Z in
            match lookup_bool var asgn with
            | Some b =>
                if Bool.eqb b value then
                  unit_conflict_fuel fuel' num_vars clauses asgn queue'
                else true
            | None =>
                let asgn' := insert_bool var value asgn in
                (* scan clauses for conflict / new unit literals *)
                let fix scan (cls : list (list Z)) (q : list Z) : option (list Z) :=
                  match cls with
                  | [] => Some q
                  | cl :: cls' =>
                      let '(sat, undec) := eval_clause asgn' cl in
                      if sat then scan cls' q
                      else
                        match undec with
                        | [] => None
                        | [u] => scan cls' (u :: q)
                        | _ => scan cls' q
                        end
                  end
                in
                match scan clauses queue' with
                | None => true
                | Some q' => unit_conflict_fuel fuel' num_vars clauses asgn' q'
                end
            end
        end
    end.

  Definition unit_conflict
    (num_vars : nat)
    (clauses : list (list Z))
    (assumptions : list Z)
    : bool :=
    let unit_lits :=
      fold_right
        (fun cl acc => match cl with | [u] => u :: acc | _ => acc end)
        []
        clauses
    in
    let queue := (assumptions ++ unit_lits)%list in
    let fuel := (num_vars + List.length queue + 10)%nat in
    unit_conflict_fuel fuel num_vars clauses [] queue.

  Definition verify_rup_clause
    (num_vars : nat)
    (db : list (nat * list Z))
    (clause : list Z)
    : bool :=
    unit_conflict num_vars (db_clauses db) (map Z.opp clause).

  Record lrat_step :=
    { lrat_id : nat;
      lrat_clause : list Z;
      lrat_deletions : list nat;
      lrat_is_delete : bool }.

  Definition parse_nat_list (toks : list string) : option (list nat) :=
    let fix go (ts : list string) (acc : list nat) :=
      match ts with
      | [] => Some (rev acc)
      | t :: ts' =>
          match parse_nat t with
          | Some n => if Nat.eqb n 0%nat then Some (rev acc) else go ts' (n :: acc)
          | None => None
          end
      end
    in go toks [].

  Definition parse_z_list (toks : list string) : option (list Z) :=
    let fix go (ts : list string) (acc : list Z) :=
      match ts with
      | [] => Some (rev acc)
      | t :: ts' =>
          match parse_int t with
          | Some z => if Z.eqb z 0 then Some (rev acc) else go ts' (z :: acc)
          | None => None
          end
      end
    in go toks [].

  Definition drop_until_zero (toks : list string) : list string :=
    let fix go (ts : list string) :=
      match ts with
      | [] => []
      | t :: ts' =>
          if String.eqb t "0" then ts' else go ts'
      end
    in go toks.

  Definition parse_lrat_line (line : string) : option lrat_step :=
    let t := trim_left line in
    if String.eqb t "" then None
    else if starts_with_char (Ascii.ascii_of_nat 99) t (* 'c' *) then None
    else
      let toks := split_ws t in
      match toks with
      | [] => None
      | first :: rest =>
          if String.eqb first "d" then
            match parse_nat_list rest with
            | Some dels =>
                Some {| lrat_id := 0%nat;
                        lrat_clause := [];
                        lrat_deletions := dels;
                        lrat_is_delete := true |}
            | None => None
            end
          else
            match parse_nat first with
            | Some cid =>
                match parse_z_list rest with
                | Some clause =>
                    let after_clause := drop_until_zero rest in
                    let after_hints := drop_until_zero after_clause in
                    match parse_nat_list after_hints with
                    | Some dels =>
                        Some {| lrat_id := cid;
                                lrat_clause := clause;
                                lrat_deletions := dels;
                                lrat_is_delete := false |}
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
      end.

  Fixpoint build_initial_db (clauses : list (list Z)) (idx : nat) : list (nat * list Z) :=
    match clauses with
    | [] => []
    | cl :: cls => (idx, cl) :: build_initial_db cls (S idx)
    end.

  Fixpoint apply_deletions (db : list (nat * list Z)) (dels : list nat) : list (nat * list Z) :=
    match dels with
    | [] => db
    | d :: ds => apply_deletions (assoc_remove d db) ds
    end.

  Fixpoint check_lrat_lines
    (num_vars : nat)
    (lines : list string)
    (db : list (nat * list Z))
    (derived_empty : bool)
    : bool :=
    match lines with
    | [] => derived_empty
    | line :: lines' =>
        match parse_lrat_line line with
        | None => check_lrat_lines num_vars lines' db derived_empty
        | Some st =>
            if st.(lrat_is_delete) then
              check_lrat_lines num_vars lines' (apply_deletions db st.(lrat_deletions)) derived_empty
            else
              if verify_rup_clause num_vars db st.(lrat_clause) then
                let db' := (st.(lrat_id), st.(lrat_clause)) :: apply_deletions db st.(lrat_deletions) in
                let derived_empty' := orb derived_empty (Nat.eqb (List.length st.(lrat_clause)) 0%nat) in
                check_lrat_lines num_vars lines' db' derived_empty'
              else false
        end
    end.

  Definition check_lrat (cnf_text : string) (proof_text : string) : bool :=
    match parse_dimacs cnf_text with
    | None => false
    | Some cnf =>
        let db := build_initial_db cnf.(cnf_clauses) 1%nat in
        check_lrat_lines cnf.(cnf_num_vars) (split_lines proof_text) db false
    end.

End CertCheck.

Export CertCheck.
