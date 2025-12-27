
type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add n m =
   (fun zero succ n -> if n=0 then zero () else succ (n-1))
     (fun _ -> m)
     (fun p -> (fun x -> x + 1) (add p m))
     n
end
include Coq__1

(** val sub : int -> int -> int **)

let rec sub n m =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> n)
    (fun k ->
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> n)
      (fun l -> sub k l)
      m)
    n

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x ((fun x -> x + 1) 0)

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val gtb : z -> z -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val to_nat : z -> int **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> 0

  (** val of_nat : int -> z **)

  let of_nat n =
    (fun zero succ n -> if n=0 then zero () else succ (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Pos.of_succ_nat n0))
      n

  (** val pos_div_eucl : positive -> z -> z*z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let q,r = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then (mul (Zpos (XO XH)) q),r'
      else (add (mul (Zpos (XO XH)) q) (Zpos XH)),(sub r' b)
    | XO a' ->
      let q,r = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then (mul (Zpos (XO XH)) q),r'
      else (add (mul (Zpos (XO XH)) q) (Zpos XH)),(sub r' b)
    | XH -> if leb (Zpos (XO XH)) b then Z0,(Zpos XH) else (Zpos XH),Z0

  (** val div_eucl : z -> z -> z*z **)

  let div_eucl a b =
    match a with
    | Z0 -> Z0,Z0
    | Zpos a' ->
      (match b with
       | Z0 -> Z0,a
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let q,r = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> (opp q),Z0
          | _ -> (opp (add q (Zpos XH))),(add b r)))
    | Zneg a' ->
      (match b with
       | Z0 -> Z0,a
       | Zpos _ ->
         let q,r = pos_div_eucl a' b in
         (match r with
          | Z0 -> (opp q),Z0
          | _ -> (opp (add q (Zpos XH))),(sub b r))
       | Zneg b' -> let q,r = pos_div_eucl a' (Zpos b') in q,(opp r))

  (** val div : z -> z -> z **)

  let div a b =
    let q,_ = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let _,r = div_eucl a b in r

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> Zneg (Pos.div2_up p)

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Pos.iter div2 a p
 end

type q16 = z

(** val q16_ONE : q16 **)

let q16_ONE =
  Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    XH))))))))))))))))

(** val q16_MAX : q16 **)

let q16_MAX =
  Zpos (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI
    (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI
    XH))))))))))))))))))))))))))))))

(** val q16_MIN : q16 **)

let q16_MIN =
  Zneg (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
    XH)))))))))))))))))))))))))))))))

(** val saturate : z -> q16 **)

let saturate x =
  if Z.gtb x q16_MAX then q16_MAX else if Z.ltb x q16_MIN then q16_MIN else x

(** val q16_add : q16 -> q16 -> q16 **)

let q16_add a b =
  saturate (Z.add a b)

(** val q16_sub : q16 -> q16 -> q16 **)

let q16_sub a b =
  saturate (Z.sub a b)

(** val q16_mul : q16 -> q16 -> q16 **)

let q16_mul a b =
  saturate (Z.div (Z.mul a b) q16_ONE)

(** val q16_div : q16 -> q16 -> q16 **)

let q16_div a b =
  if Z.eqb b Z0 then Z0 else saturate (Z.div (Z.mul a q16_ONE) b)

(** val log2_lut : q16 list **)

let log2_lut =
  Z0::((Zpos (XO (XO (XO (XO (XI (XI (XI (XO XH)))))))))::((Zpos (XI (XI (XI
    (XI (XI (XO (XI (XI (XO XH))))))))))::((Zpos (XI (XO (XI (XI (XO (XO (XI
    (XO (XO (XO XH)))))))))))::((Zpos (XI (XO (XO (XI (XI (XI (XO (XI (XI (XO
    XH)))))))))))::((Zpos (XO (XO (XI (XO (XO (XI (XO (XO (XI (XI
    XH)))))))))))::((Zpos (XO (XI (XI (XI (XO (XO (XO (XI (XO (XO (XO
    XH))))))))))))::((Zpos (XO (XI (XI (XO (XI (XI (XI (XI (XI (XO (XO
    XH))))))))))))::((Zpos (XI (XO (XI (XI (XI (XO (XI (XO (XI (XI (XO
    XH))))))))))))::((Zpos (XO (XI (XO (XO (XO (XO (XI (XI (XO (XO (XI
    XH))))))))))))::((Zpos (XO (XI (XI (XO (XO (XI (XO (XO (XO (XI (XI
    XH))))))))))))::((Zpos (XI (XO (XO (XI (XO (XO (XO (XI (XI (XI (XI
    XH))))))))))))::((Zpos (XI (XI (XO (XI (XO (XI (XI (XI (XO (XO (XO (XO
    XH)))))))))))))::((Zpos (XI (XI (XO (XI (XO (XO (XI (XO (XO (XI (XO (XO
    XH)))))))))))))::((Zpos (XO (XI (XO (XI (XO (XI (XO (XI (XI (XI (XO (XO
    XH)))))))))))))::((Zpos (XI (XI (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO
    XH)))))))))))))::((Zpos (XI (XI (XO (XO (XO (XI (XI (XO (XO (XI (XI (XO
    XH)))))))))))))::((Zpos (XO (XI (XI (XI (XI (XI (XO (XI (XI (XI (XI (XO
    XH)))))))))))))::((Zpos (XO (XO (XO (XI (XI (XO (XO (XO (XI (XO (XO (XI
    XH)))))))))))))::((Zpos (XI (XO (XO (XO (XI (XI (XI (XO (XO (XI (XO (XI
    XH)))))))))))))::((Zpos (XO (XO (XO (XI (XO (XO (XI (XI (XI (XI (XO (XI
    XH)))))))))))))::((Zpos (XO (XI (XI (XI (XI (XO (XO (XO (XI (XO (XI (XI
    XH)))))))))))))::((Zpos (XO (XI (XO (XO (XI (XI (XI (XO (XO (XI (XI (XI
    XH)))))))))))))::((Zpos (XO (XI (XI (XO (XO (XO (XI (XI (XI (XI (XI (XI
    XH)))))))))))))::((Zpos (XO (XO (XO (XI (XI (XO (XO (XO (XI (XO (XO (XO
    (XO XH))))))))))))))::((Zpos (XI (XO (XO (XI (XO (XI (XI (XO (XO (XI (XO
    (XO (XO XH))))))))))))))::((Zpos (XI (XO (XO (XI (XI (XI (XO (XI (XI (XI
    (XO (XO (XO XH))))))))))))))::((Zpos (XO (XO (XO (XI (XO (XO (XO (XO (XI
    (XO (XI (XO (XO XH))))))))))))))::((Zpos (XI (XO (XI (XO (XI (XO (XI (XO
    (XO (XI (XI (XO (XO XH))))))))))))))::((Zpos (XO (XI (XO (XO (XO (XI (XO
    (XI (XI (XI (XI (XO (XO XH))))))))))))))::((Zpos (XI (XO (XI (XI (XO (XI
    (XI (XI (XO (XO (XO (XI (XO XH))))))))))))))::((Zpos (XI (XI (XI (XO (XI
    (XI (XO (XO (XO (XI (XO (XI (XO XH))))))))))))))::((Zpos (XO (XO (XO (XO
    (XO (XO (XO (XI (XI (XI (XO (XI (XO XH))))))))))))))::((Zpos (XI (XI (XI
    (XO (XO (XO (XI (XI (XO (XO (XI (XI (XO XH))))))))))))))::((Zpos (XO (XI
    (XI (XI (XO (XO (XO (XO (XO (XI (XI (XI (XO XH))))))))))))))::((Zpos (XI
    (XI (XO (XO (XI (XO (XI (XO (XI (XI (XI (XI (XO XH))))))))))))))::((Zpos
    (XO (XO (XO (XI (XI (XO (XO (XI (XO (XO (XO (XO (XI
    XH))))))))))))))::((Zpos (XI (XI (XO (XI (XI (XO (XI (XI (XI (XO (XO (XO
    (XI XH))))))))))))))::((Zpos (XI (XO (XI (XI (XI (XO (XO (XO (XI (XI (XO
    (XO (XI XH))))))))))))))::((Zpos (XO (XI (XI (XI (XI (XO (XI (XO (XO (XO
    (XI (XO (XI XH))))))))))))))::((Zpos (XO (XI (XI (XI (XI (XO (XO (XI (XI
    (XO (XI (XO (XI XH))))))))))))))::((Zpos (XI (XO (XI (XI (XI (XO (XI (XI
    (XO (XI (XI (XO (XI XH))))))))))))))::((Zpos (XI (XI (XO (XI (XI (XO (XO
    (XO (XO (XO (XO (XI (XI XH))))))))))))))::((Zpos (XO (XO (XO (XI (XI (XO
    (XI (XO (XI (XO (XO (XI (XI XH))))))))))))))::((Zpos (XI (XI (XO (XO (XI
    (XO (XO (XI (XO (XI (XO (XI (XI XH))))))))))))))::((Zpos (XO (XI (XI (XI
    (XO (XO (XI (XI (XI (XI (XO (XI (XI XH))))))))))))))::((Zpos (XO (XO (XO
    (XI (XO (XO (XO (XO (XI (XO (XI (XI (XI XH))))))))))))))::((Zpos (XO (XO
    (XO (XO (XO (XO (XI (XO (XO (XI (XI (XI (XI XH))))))))))))))::((Zpos (XO
    (XO (XO (XI (XI (XI (XI (XO (XI (XI (XI (XI (XI XH))))))))))))))::((Zpos
    (XO (XI (XI (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO (XO
    XH)))))))))))))))::((Zpos (XO (XO (XI (XO (XO (XI (XI (XI (XI (XO (XO (XO
    (XO (XO XH)))))))))))))))::((Zpos (XO (XO (XO (XI (XI (XO (XO (XO (XI (XI
    (XO (XO (XO (XO XH)))))))))))))))::((Zpos (XO (XO (XI (XI (XO (XO (XI (XO
    (XO (XO (XI (XO (XO (XO XH)))))))))))))))::((Zpos (XO (XI (XI (XI (XI (XI
    (XI (XO (XI (XO (XI (XO (XO (XO XH)))))))))))))))::((Zpos (XO (XO (XO (XO
    (XI (XI (XO (XI (XO (XI (XI (XO (XO (XO XH)))))))))))))))::((Zpos (XO (XO
    (XO (XO (XO (XI (XI (XI (XI (XI (XI (XO (XO (XO XH)))))))))))))))::((Zpos
    (XO (XO (XO (XO (XI (XO (XO (XO (XI (XO (XO (XI (XO (XO
    XH)))))))))))))))::((Zpos (XO (XI (XI (XI (XI (XI (XO (XO (XO (XI (XO (XI
    (XO (XO XH)))))))))))))))::((Zpos (XO (XO (XI (XI (XO (XI (XI (XO (XI (XI
    (XO (XI (XO (XO XH)))))))))))))))::((Zpos (XO (XO (XO (XI (XI (XO (XO (XI
    (XO (XO (XI (XI (XO (XO XH)))))))))))))))::((Zpos (XO (XO (XI (XO (XO (XO
    (XI (XI (XI (XO (XI (XI (XO (XO XH)))))))))))))))::((Zpos (XI (XI (XI (XI
    (XO (XI (XI (XI (XO (XI (XI (XI (XO (XO XH)))))))))))))))::((Zpos (XI (XO
    (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XI (XO XH)))))))))))))))::((Zpos
    (XI (XO (XO (XO (XO (XO (XI (XO (XI (XO (XO (XO (XI (XO
    XH)))))))))))))))::((Zpos (XI (XO (XO (XI (XO (XI (XI (XO (XO (XI (XO (XO
    (XI (XO XH)))))))))))))))::((Zpos (XO (XO (XO (XO (XI (XO (XO (XI (XI (XI
    (XO (XO (XI (XO XH)))))))))))))))::((Zpos (XO (XI (XI (XO (XI (XI (XO (XI
    (XO (XO (XI (XO (XI (XO XH)))))))))))))))::((Zpos (XO (XO (XI (XI (XI (XO
    (XI (XI (XI (XO (XI (XO (XI (XO XH)))))))))))))))::((Zpos (XO (XO (XO (XO
    (XO (XO (XO (XO (XI (XI (XI (XO (XI (XO XH)))))))))))))))::((Zpos (XI (XI
    (XO (XO (XO (XI (XO (XO (XO (XO (XO (XI (XI (XO XH)))))))))))))))::((Zpos
    (XO (XI (XI (XO (XO (XO (XI (XO (XI (XO (XO (XI (XI (XO
    XH)))))))))))))))::((Zpos (XI (XI (XI (XO (XO (XI (XI (XO (XO (XI (XO (XI
    (XI (XO XH)))))))))))))))::((Zpos (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI
    (XO (XI (XI (XO XH)))))))))))))))::((Zpos (XO (XO (XO (XI (XO (XI (XO (XI
    (XO (XO (XI (XI (XI (XO XH)))))))))))))))::((Zpos (XI (XI (XI (XO (XO (XO
    (XI (XI (XI (XO (XI (XI (XI (XO XH)))))))))))))))::((Zpos (XI (XO (XI (XO
    (XO (XI (XI (XI (XO (XI (XI (XI (XI (XO XH)))))))))))))))::((Zpos (XO (XI
    (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI XH)))))))))))))))::((Zpos
    (XI (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO (XO (XO (XI
    XH)))))))))))))))::((Zpos (XO (XI (XO (XI (XI (XI (XO (XO (XO (XI (XO (XO
    (XO (XI XH)))))))))))))))::((Zpos (XI (XO (XI (XO (XI (XO (XI (XO (XI (XI
    (XO (XO (XO (XI XH)))))))))))))))::((Zpos (XO (XI (XI (XI (XO (XI (XI (XO
    (XO (XO (XI (XO (XO (XI XH)))))))))))))))::((Zpos (XI (XI (XI (XO (XO (XO
    (XO (XI (XI (XO (XI (XO (XO (XI XH)))))))))))))))::((Zpos (XO (XO (XO (XO
    (XO (XI (XO (XI (XO (XI (XI (XO (XO (XI XH)))))))))))))))::((Zpos (XI (XI
    (XI (XO (XI (XI (XO (XI (XI (XI (XI (XO (XO (XI XH)))))))))))))))::((Zpos
    (XI (XO (XI (XI (XO (XO (XI (XI (XO (XO (XO (XI (XO (XI
    XH)))))))))))))))::((Zpos (XI (XI (XO (XO (XO (XI (XI (XI (XI (XO (XO (XI
    (XO (XI XH)))))))))))))))::((Zpos (XO (XO (XO (XI (XI (XI (XI (XI (XO (XI
    (XO (XI (XO (XI XH)))))))))))))))::((Zpos (XO (XO (XI (XI (XO (XO (XO (XO
    (XO (XO (XI (XI (XO (XI XH)))))))))))))))::((Zpos (XI (XI (XI (XI (XI (XO
    (XO (XO (XI (XO (XI (XI (XO (XI XH)))))))))))))))::((Zpos (XO (XI (XO (XO
    (XI (XI (XO (XO (XO (XI (XI (XI (XO (XI XH)))))))))))))))::((Zpos (XI (XI
    (XO (XO (XO (XO (XI (XO (XI (XI (XI (XI (XO (XI XH)))))))))))))))::((Zpos
    (XO (XO (XI (XO (XI (XO (XI (XO (XO (XO (XO (XO (XI (XI
    XH)))))))))))))))::((Zpos (XO (XO (XI (XO (XO (XI (XI (XO (XI (XO (XO (XO
    (XI (XI XH)))))))))))))))::((Zpos (XO (XO (XI (XO (XI (XI (XI (XO (XO (XI
    (XO (XO (XI (XI XH)))))))))))))))::((Zpos (XO (XI (XO (XO (XO (XO (XO (XI
    (XI (XI (XO (XO (XI (XI XH)))))))))))))))::((Zpos (XI (XO (XO (XO (XI (XO
    (XO (XI (XO (XO (XI (XO (XI (XI XH)))))))))))))))::((Zpos (XO (XI (XI (XI
    (XI (XO (XO (XI (XI (XO (XI (XO (XI (XI XH)))))))))))))))::((Zpos (XO (XI
    (XO (XI (XO (XI (XO (XI (XO (XI (XI (XO (XI (XI XH)))))))))))))))::((Zpos
    (XO (XI (XI (XO (XI (XI (XO (XI (XI (XI (XI (XO (XI (XI
    XH)))))))))))))))::((Zpos (XI (XO (XO (XO (XO (XO (XI (XI (XO (XO (XO (XI
    (XI (XI XH)))))))))))))))::((Zpos (XI (XI (XO (XI (XO (XO (XI (XI (XI (XO
    (XO (XI (XI (XI XH)))))))))))))))::((Zpos (XI (XO (XI (XO (XI (XO (XI (XI
    (XO (XI (XO (XI (XI (XI XH)))))))))))))))::((Zpos (XO (XI (XI (XI (XI (XO
    (XI (XI (XI (XI (XO (XI (XI (XI XH)))))))))))))))::((Zpos (XO (XI (XI (XO
    (XO (XI (XI (XI (XO (XO (XI (XI (XI (XI XH)))))))))))))))::((Zpos (XI (XO
    (XI (XI (XO (XI (XI (XI (XI (XO (XI (XI (XI (XI XH)))))))))))))))::((Zpos
    (XO (XO (XI (XO (XI (XI (XI (XI (XO (XI (XI (XI (XI (XI
    XH)))))))))))))))::((Zpos (XO (XI (XO (XI (XI (XI (XI (XI (XI (XI (XI (XI
    (XI (XI XH)))))))))))))))::((Zpos (XI (XI (XI (XI (XI (XI (XI (XI (XO (XO
    (XO (XO (XO (XO (XO XH))))))))))))))))::((Zpos (XI (XI (XO (XO (XO (XO
    (XO (XO (XO (XI (XO (XO (XO (XO (XO XH))))))))))))))))::((Zpos (XI (XI
    (XI (XO (XO (XO (XO (XO (XI (XI (XO (XO (XO (XO (XO
    XH))))))))))))))))::((Zpos (XO (XI (XO (XI (XO (XO (XO (XO (XO (XO (XI
    (XO (XO (XO (XO XH))))))))))))))))::((Zpos (XI (XO (XI (XI (XO (XO (XO
    (XO (XI (XO (XI (XO (XO (XO (XO XH))))))))))))))))::((Zpos (XO (XI (XI
    (XI (XO (XO (XO (XO (XO (XI (XI (XO (XO (XO (XO
    XH))))))))))))))))::((Zpos (XI (XI (XI (XI (XO (XO (XO (XO (XI (XI (XI
    (XO (XO (XO (XO XH))))))))))))))))::((Zpos (XO (XO (XO (XO (XI (XO (XO
    (XO (XO (XO (XO (XI (XO (XO (XO XH))))))))))))))))::((Zpos (XI (XI (XI
    (XI (XO (XO (XO (XO (XI (XO (XO (XI (XO (XO (XO
    XH))))))))))))))))::((Zpos (XO (XI (XI (XI (XO (XO (XO (XO (XO (XI (XO
    (XI (XO (XO (XO XH))))))))))))))))::((Zpos (XO (XO (XI (XI (XO (XO (XO
    (XO (XI (XI (XO (XI (XO (XO (XO XH))))))))))))))))::((Zpos (XO (XI (XO
    (XI (XO (XO (XO (XO (XO (XO (XI (XI (XO (XO (XO
    XH))))))))))))))))::((Zpos (XI (XI (XI (XO (XO (XO (XO (XO (XI (XO (XI
    (XI (XO (XO (XO XH))))))))))))))))::((Zpos (XI (XI (XO (XO (XO (XO (XO
    (XO (XO (XI (XI (XI (XO (XO (XO XH))))))))))))))))::((Zpos (XI (XI (XI
    (XI (XI (XI (XI (XI (XO (XI (XI (XI (XO (XO (XO
    XH))))))))))))))))::((Zpos (XO (XI (XO (XI (XI (XI (XI (XI (XI (XI (XI
    (XI (XO (XO (XO XH))))))))))))))))::((Zpos (XO (XO (XI (XO (XI (XI (XI
    (XI (XO (XO (XO (XO (XI (XO (XO XH))))))))))))))))::((Zpos (XO (XI (XI
    (XI (XO (XI (XI (XI (XI (XO (XO (XO (XI (XO (XO
    XH))))))))))))))))::((Zpos (XI (XI (XI (XO (XO (XI (XI (XI (XO (XI (XO
    (XO (XI (XO (XO XH))))))))))))))))::((Zpos (XI (XI (XI (XI (XI (XO (XI
    (XI (XI (XI (XO (XO (XI (XO (XO XH))))))))))))))))::((Zpos (XI (XI (XI
    (XO (XI (XO (XI (XI (XO (XO (XI (XO (XI (XO (XO
    XH))))))))))))))))::((Zpos (XO (XI (XI (XI (XO (XO (XI (XI (XI (XO (XI
    (XO (XI (XO (XO XH))))))))))))))))::((Zpos (XI (XO (XI (XO (XO (XO (XI
    (XI (XO (XI (XI (XO (XI (XO (XO XH))))))))))))))))::((Zpos (XI (XI (XO
    (XI (XI (XI (XO (XI (XI (XI (XI (XO (XI (XO (XO
    XH))))))))))))))))::((Zpos (XO (XO (XO (XO (XI (XI (XO (XI (XO (XO (XO
    (XI (XI (XO (XO XH))))))))))))))))::((Zpos (XI (XO (XI (XO (XO (XI (XO
    (XI (XI (XO (XO (XI (XI (XO (XO XH))))))))))))))))::((Zpos (XI (XO (XO
    (XI (XI (XO (XO (XI (XO (XI (XO (XI (XI (XO (XO
    XH))))))))))))))))::((Zpos (XO (XO (XI (XI (XO (XO (XO (XI (XI (XI (XO
    (XI (XI (XO (XO XH))))))))))))))))::((Zpos (XI (XI (XI (XI (XI (XI (XI
    (XO (XO (XO (XI (XI (XI (XO (XO XH))))))))))))))))::((Zpos (XI (XO (XO
    (XO (XI (XI (XI (XO (XI (XO (XI (XI (XI (XO (XO
    XH))))))))))))))))::((Zpos (XI (XI (XO (XO (XO (XI (XI (XO (XO (XI (XI
    (XI (XI (XO (XO XH))))))))))))))))::((Zpos (XO (XO (XI (XO (XI (XO (XI
    (XO (XI (XI (XI (XI (XI (XO (XO XH))))))))))))))))::((Zpos (XI (XO (XI
    (XO (XO (XO (XI (XO (XO (XO (XO (XO (XO (XI (XO
    XH))))))))))))))))::((Zpos (XI (XO (XI (XO (XI (XI (XO (XO (XI (XO (XO
    (XO (XO (XI (XO XH))))))))))))))))::((Zpos (XO (XO (XI (XO (XO (XI (XO
    (XO (XO (XI (XO (XO (XO (XI (XO XH))))))))))))))))::((Zpos (XI (XI (XO
    (XO (XI (XO (XO (XO (XI (XI (XO (XO (XO (XI (XO
    XH))))))))))))))))::((Zpos (XI (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI
    (XO (XO (XI (XO XH))))))))))))))))::((Zpos (XI (XI (XI (XI (XO (XI (XI
    (XI (XO (XO (XI (XO (XO (XI (XO XH))))))))))))))))::((Zpos (XO (XO (XI
    (XI (XI (XO (XI (XI (XI (XO (XI (XO (XO (XI (XO
    XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XO (XO (XI (XI (XO (XI (XI
    (XO (XO (XI (XO XH))))))))))))))))::((Zpos (XO (XO (XI (XO (XI (XI (XO
    (XI (XI (XI (XI (XO (XO (XI (XO XH))))))))))))))))::((Zpos (XO (XO (XO
    (XO (XO (XI (XO (XI (XO (XO (XO (XI (XO (XI (XO
    XH))))))))))))))))::((Zpos (XI (XI (XO (XI (XO (XO (XO (XI (XI (XO (XO
    (XI (XO (XI (XO XH))))))))))))))))::((Zpos (XI (XO (XI (XO (XI (XI (XI
    (XO (XO (XI (XO (XI (XO (XI (XO XH))))))))))))))))::((Zpos (XI (XI (XI
    (XI (XI (XO (XI (XO (XI (XI (XO (XI (XO (XI (XO
    XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XO (XO (XI (XO (XO (XO (XI
    (XI (XO (XI (XO XH))))))))))))))))::((Zpos (XI (XO (XO (XO (XI (XI (XO
    (XO (XI (XO (XI (XI (XO (XI (XO XH))))))))))))))))::((Zpos (XI (XO (XO
    (XI (XI (XO (XO (XO (XO (XI (XI (XI (XO (XI (XO
    XH))))))))))))))))::((Zpos (XI (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI
    (XI (XO (XI (XO XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XO (XI (XI
    (XI (XI (XI (XI (XI (XO (XI (XO XH))))))))))))))))::((Zpos (XI (XI (XI
    (XI (XO (XO (XI (XI (XO (XO (XO (XO (XI (XI (XO
    XH))))))))))))))))::((Zpos (XI (XO (XI (XO (XI (XI (XO (XI (XI (XO (XO
    (XO (XI (XI (XO XH))))))))))))))))::((Zpos (XI (XI (XO (XI (XI (XO (XO
    (XI (XO (XI (XO (XO (XI (XI (XO XH))))))))))))))))::((Zpos (XO (XO (XO
    (XO (XO (XO (XO (XI (XI (XI (XO (XO (XI (XI (XO
    XH))))))))))))))))::((Zpos (XI (XO (XI (XO (XO (XI (XI (XO (XO (XO (XI
    (XO (XI (XI (XO XH))))))))))))))))::((Zpos (XI (XO (XO (XI (XO (XO (XI
    (XO (XI (XO (XI (XO (XI (XI (XO XH))))))))))))))))::((Zpos (XI (XO (XI
    (XI (XO (XI (XO (XO (XO (XI (XI (XO (XI (XI (XO
    XH))))))))))))))))::((Zpos (XO (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI
    (XO (XI (XI (XO XH))))))))))))))))::((Zpos (XI (XI (XO (XO (XI (XI (XI
    (XI (XI (XI (XI (XO (XI (XI (XO XH))))))))))))))))::((Zpos (XI (XO (XI
    (XO (XI (XO (XI (XI (XO (XO (XO (XI (XI (XI (XO
    XH))))))))))))))))::((Zpos (XI (XI (XI (XO (XI (XI (XO (XI (XI (XO (XO
    (XI (XI (XI (XO XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XI (XO (XO
    (XI (XO (XI (XO (XI (XI (XI (XO XH))))))))))))))))::((Zpos (XI (XO (XO
    (XI (XI (XI (XI (XO (XI (XI (XO (XI (XI (XI (XO
    XH))))))))))))))))::((Zpos (XI (XO (XO (XI (XI (XO (XI (XO (XO (XO (XI
    (XI (XI (XI (XO XH))))))))))))))))::((Zpos (XI (XO (XO (XI (XI (XI (XO
    (XO (XI (XO (XI (XI (XI (XI (XO XH))))))))))))))))::((Zpos (XI (XO (XO
    (XI (XI (XO (XO (XO (XO (XI (XI (XI (XI (XI (XO
    XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XI (XI (XI (XI (XO (XI (XI
    (XI (XI (XI (XO XH))))))))))))))))::((Zpos (XO (XI (XI (XO (XI (XO (XI
    (XI (XI (XI (XI (XI (XI (XI (XO XH))))))))))))))))::((Zpos (XO (XO (XI
    (XO (XI (XI (XO (XI (XO (XO (XO (XO (XO (XO (XI
    XH))))))))))))))))::((Zpos (XO (XI (XO (XO (XI (XO (XO (XI (XI (XO (XO
    (XO (XO (XO (XI XH))))))))))))))))::((Zpos (XI (XI (XI (XI (XO (XI (XI
    (XO (XO (XI (XO (XO (XO (XO (XI XH))))))))))))))))::((Zpos (XI (XI (XO
    (XI (XO (XO (XI (XO (XI (XI (XO (XO (XO (XO (XI
    XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XO (XI (XO (XO (XO (XO (XI
    (XO (XO (XO (XI XH))))))))))))))))::((Zpos (XI (XI (XO (XO (XO (XO (XO
    (XO (XI (XO (XI (XO (XO (XO (XI XH))))))))))))))))::((Zpos (XI (XI (XI
    (XI (XI (XO (XI (XI (XI (XO (XI (XO (XO (XO (XI
    XH))))))))))))))))::((Zpos (XI (XO (XO (XI (XI (XI (XO (XI (XO (XI (XI
    (XO (XO (XO (XI XH))))))))))))))))::((Zpos (XO (XO (XI (XO (XI (XO (XO
    (XI (XI (XI (XI (XO (XO (XO (XI XH))))))))))))))))::((Zpos (XO (XI (XI
    (XI (XO (XI (XI (XO (XO (XO (XO (XI (XO (XO (XI
    XH))))))))))))))))::((Zpos (XI (XI (XI (XO (XO (XO (XI (XO (XI (XO (XO
    (XI (XO (XO (XI XH))))))))))))))))::((Zpos (XO (XO (XO (XO (XO (XI (XO
    (XO (XO (XI (XO (XI (XO (XO (XI XH))))))))))))))))::((Zpos (XI (XO (XO
    (XI (XI (XI (XI (XI (XO (XI (XO (XI (XO (XO (XI
    XH))))))))))))))))::((Zpos (XI (XO (XO (XO (XI (XO (XI (XI (XI (XI (XO
    (XI (XO (XO (XI XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XO (XI (XO
    (XI (XO (XO (XI (XI (XO (XO (XI XH))))))))))))))))::((Zpos (XO (XO (XO
    (XO (XO (XO (XO (XI (XI (XO (XI (XI (XO (XO (XI
    XH))))))))))))))))::((Zpos (XO (XI (XI (XO (XI (XO (XI (XO (XO (XI (XI
    (XI (XO (XO (XI XH))))))))))))))))::((Zpos (XI (XO (XI (XI (XO (XI (XO
    (XO (XI (XI (XI (XI (XO (XO (XI XH))))))))))))))))::((Zpos (XO (XI (XO
    (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XO (XI
    XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XI (XO (XI (XI (XO (XO (XO
    (XO (XI (XO (XI XH))))))))))))))))::((Zpos (XI (XO (XI (XI (XO (XI (XO
    (XI (XI (XO (XO (XO (XI (XO (XI XH))))))))))))))))::((Zpos (XI (XO (XO
    (XO (XO (XO (XO (XI (XO (XI (XO (XO (XI (XO (XI
    XH))))))))))))))))::((Zpos (XI (XO (XI (XO (XI (XO (XI (XO (XI (XI (XO
    (XO (XI (XO (XI XH))))))))))))))))::((Zpos (XI (XO (XO (XI (XO (XI (XO
    (XO (XO (XO (XI (XO (XI (XO (XI XH))))))))))))))))::((Zpos (XO (XO (XI
    (XI (XI (XI (XI (XI (XO (XO (XI (XO (XI (XO (XI
    XH))))))))))))))))::((Zpos (XI (XI (XI (XI (XO (XO (XI (XI (XI (XO (XI
    (XO (XI (XO (XI XH))))))))))))))))::((Zpos (XI (XO (XO (XO (XO (XI (XO
    (XI (XO (XI (XI (XO (XI (XO (XI XH))))))))))))))))::((Zpos (XI (XI (XO
    (XO (XI (XI (XI (XO (XI (XI (XI (XO (XI (XO (XI
    XH))))))))))))))))::((Zpos (XI (XO (XI (XO (XO (XO (XI (XO (XO (XO (XO
    (XI (XI (XO (XI XH))))))))))))))))::((Zpos (XO (XI (XI (XO (XI (XO (XO
    (XO (XI (XO (XO (XI (XI (XO (XI XH))))))))))))))))::((Zpos (XI (XI (XI
    (XO (XO (XI (XI (XI (XI (XO (XO (XI (XI (XO (XI
    XH))))))))))))))))::((Zpos (XI (XI (XI (XO (XI (XI (XO (XI (XO (XI (XO
    (XI (XI (XO (XI XH))))))))))))))))::((Zpos (XI (XI (XI (XO (XO (XO (XO
    (XI (XI (XI (XO (XI (XI (XO (XI XH))))))))))))))))::((Zpos (XI (XI (XI
    (XO (XI (XO (XI (XO (XO (XO (XI (XI (XI (XO (XI
    XH))))))))))))))))::((Zpos (XO (XI (XI (XO (XO (XI (XO (XO (XI (XO (XI
    (XI (XI (XO (XI XH))))))))))))))))::((Zpos (XO (XO (XI (XO (XI (XI (XI
    (XI (XI (XO (XI (XI (XI (XO (XI XH))))))))))))))))::((Zpos (XI (XI (XO
    (XO (XO (XO (XI (XI (XO (XI (XI (XI (XI (XO (XI
    XH))))))))))))))))::((Zpos (XI (XO (XO (XO (XI (XO (XO (XI (XI (XI (XI
    (XI (XI (XO (XI XH))))))))))))))))::((Zpos (XO (XI (XI (XI (XI (XO (XI
    (XO (XO (XO (XO (XO (XO (XI (XI XH))))))))))))))))::((Zpos (XI (XI (XO
    (XI (XO (XI (XO (XO (XI (XO (XO (XO (XO (XI (XI
    XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XI (XI (XI (XI (XI (XO (XO
    (XO (XO (XI (XI XH))))))))))))))))::((Zpos (XO (XO (XI (XO (XO (XO (XI
    (XI (XO (XI (XO (XO (XO (XI (XI XH))))))))))))))))::((Zpos (XO (XO (XO
    (XO (XI (XO (XO (XI (XI (XI (XO (XO (XO (XI (XI
    XH))))))))))))))))::((Zpos (XO (XO (XI (XI (XI (XO (XI (XO (XO (XO (XI
    (XO (XO (XI (XI XH))))))))))))))))::((Zpos (XI (XI (XI (XO (XO (XI (XO
    (XO (XI (XO (XI (XO (XO (XI (XI XH))))))))))))))))::((Zpos (XO (XI (XO
    (XO (XI (XI (XI (XI (XI (XO (XI (XO (XO (XI (XI
    XH))))))))))))))))::((Zpos (XO (XO (XI (XI (XI (XI (XO (XI (XO (XI (XI
    (XO (XO (XI (XI XH))))))))))))))))::((Zpos (XO (XI (XI (XO (XO (XO (XO
    (XI (XI (XI (XI (XO (XO (XI (XI XH))))))))))))))))::((Zpos (XO (XO (XO
    (XO (XI (XO (XI (XO (XO (XO (XO (XI (XO (XI (XI
    XH))))))))))))))))::((Zpos (XI (XO (XO (XI (XI (XO (XO (XO (XI (XO (XO
    (XI (XO (XI (XI XH))))))))))))))))::((Zpos (XO (XI (XO (XO (XO (XI (XI
    (XI (XI (XO (XO (XI (XO (XI (XI XH))))))))))))))))::((Zpos (XO (XI (XO
    (XI (XO (XI (XO (XI (XO (XI (XO (XI (XO (XI (XI
    XH))))))))))))))))::((Zpos (XO (XI (XO (XO (XI (XI (XI (XO (XI (XI (XO
    (XI (XO (XI (XI XH))))))))))))))))::((Zpos (XO (XI (XO (XI (XI (XI (XO
    (XO (XO (XO (XI (XI (XO (XI (XI XH))))))))))))))))::((Zpos (XI (XO (XO
    (XO (XO (XO (XO (XO (XI (XO (XI (XI (XO (XI (XI
    XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XO (XO (XI (XI (XI (XO (XI
    (XI (XO (XI (XI XH))))))))))))))))::((Zpos (XI (XI (XI (XI (XO (XO (XO
    (XI (XO (XI (XI (XI (XO (XI (XI XH))))))))))))))))::((Zpos (XI (XO (XI
    (XO (XI (XO (XI (XO (XI (XI (XI (XI (XO (XI (XI
    XH))))))))))))))))::((Zpos (XI (XI (XO (XI (XI (XO (XO (XO (XO (XO (XO
    (XO (XI (XI (XI XH))))))))))))))))::((Zpos (XO (XO (XO (XO (XO (XI (XI
    (XI (XO (XO (XO (XO (XI (XI (XI XH))))))))))))))))::((Zpos (XO (XI (XI
    (XO (XO (XI (XO (XI (XI (XO (XO (XO (XI (XI (XI
    XH))))))))))))))))::((Zpos (XO (XI (XO (XI (XO (XI (XI (XO (XO (XI (XO
    (XO (XI (XI (XI XH))))))))))))))))::((Zpos (XI (XI (XI (XI (XO (XI (XO
    (XO (XI (XI (XO (XO (XI (XI (XI XH))))))))))))))))::((Zpos (XI (XI (XO
    (XO (XI (XI (XI (XI (XI (XI (XO (XO (XI (XI (XI
    XH))))))))))))))))::((Zpos (XI (XI (XI (XO (XI (XI (XO (XI (XO (XO (XI
    (XO (XI (XI (XI XH))))))))))))))))::((Zpos (XO (XI (XO (XI (XI (XI (XI
    (XO (XI (XO (XI (XO (XI (XI (XI XH))))))))))))))))::((Zpos (XI (XO (XI
    (XO (XI (XO (XI (XO (XO (XI (XO (XO (XI (XI (XI
    XH))))))))))))))))::((Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI
    (XO (XI (XI (XI XH))))))))))))))))::((Zpos (XO (XI (XO (XO (XO (XO (XI
    (XI (XI (XI (XI (XO (XI (XI (XI XH))))))))))))))))::((Zpos (XO (XO (XI
    (XO (XO (XO (XO (XI (XO (XO (XO (XI (XI (XI (XI
    XH))))))))))))))))::((Zpos (XO (XI (XI (XO (XO (XO (XI (XO (XI (XO (XO
    (XI (XI (XI (XI XH))))))))))))))))::((Zpos (XI (XI (XI (XO (XO (XO (XO
    (XO (XO (XI (XO (XI (XI (XI (XI XH))))))))))))))))::((Zpos (XO (XO (XO
    (XI (XO (XO (XI (XI (XO (XI (XO (XI (XI (XI (XI
    XH))))))))))))))))::((Zpos (XI (XO (XO (XI (XO (XO (XO (XI (XI (XI (XO
    (XI (XI (XI (XI XH))))))))))))))))::((Zpos (XI (XO (XO (XI (XO (XO (XI
    (XO (XO (XO (XI (XI (XI (XI (XI XH))))))))))))))))::((Zpos (XI (XO (XO
    (XI (XO (XO (XO (XO (XI (XO (XI (XI (XI (XI (XI
    XH))))))))))))))))::((Zpos (XI (XO (XO (XI (XO (XO (XI (XI (XI (XO (XI
    (XI (XI (XI (XI XH))))))))))))))))::((Zpos (XO (XO (XO (XI (XO (XO (XO
    (XI (XO (XI (XI (XI (XI (XI (XI XH))))))))))))))))::((Zpos (XI (XI (XI
    (XO (XO (XO (XI (XO (XI (XI (XI (XI (XI (XI (XI
    XH))))))))))))))))::((Zpos (XO (XI (XI (XO (XO (XO (XO (XO (XO (XO (XO
    (XO (XO (XO (XO (XO XH)))))))))))))))))::((Zpos (XO (XO (XI (XO (XO (XO
    (XI (XI (XO (XO (XO (XO (XO (XO (XO (XO
    XH)))))))))))))))))::[])))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val lut_lookup : int -> q16 list -> q16 **)

let rec lut_lookup index = function
| [] -> Z0
| h::t ->
  ((fun zero succ n -> if n=0 then zero () else succ (n-1))
     (fun _ -> h)
     (fun n -> lut_lookup n t)
     index)

(** val count_leading_zeros_helper : z -> int -> int -> int **)

let rec count_leading_zeros_helper x count fuel =
  (fun zero succ n -> if n=0 then zero () else succ (n-1))
    (fun _ -> count)
    (fun fuel' ->
    if Z.eqb (Z.div x (Z.pow (Zpos (XO XH)) (Zpos (XI (XI (XI (XI XH))))))) Z0
    then count_leading_zeros_helper (Z.mul x (Zpos (XO XH)))
           ((fun x -> x + 1) count) fuel'
    else count)
    fuel

(** val count_leading_zeros : z -> int **)

let count_leading_zeros x =
  if Z.leb x Z0
  then (fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) 0)))))))))))))))))))))))))))))))
  else count_leading_zeros_helper x 0 ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
         0))))))))))))))))))))))))))))))))

(** val extract_lut_index : z -> int **)

let extract_lut_index frac_part =
  Z.to_nat
    (Z.modulo
      (Z.div frac_part (Zpos (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))
      (Zpos (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))

(** val q16_log2 : q16 -> q16 **)

let q16_log2 x =
  if Z.leb x Z0
  then q16_MIN
  else if Z.eqb x q16_ONE
       then Z0
       else let lz = count_leading_zeros x in
            let highest_bit =
              Z.of_nat
                (sub ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) ((fun x -> x + 1) ((fun x -> x + 1)
                  ((fun x -> x + 1) 0))))))))))))))))))))))))))))))) lz)
            in
            let integer_log2 = Z.sub highest_bit (Zpos (XO (XO (XO (XO XH)))))
            in
            let shift_amount = Z.sub highest_bit (Zpos (XO (XO (XO (XO XH)))))
            in
            let normalized =
              if Z.gtb shift_amount Z0
              then Z.div x (Z.shiftl (Zpos XH) shift_amount)
              else if Z.ltb shift_amount Z0
                   then Z.mul x (Z.shiftl (Zpos XH) (Z.opp shift_amount))
                   else x
            in
            let frac_part = Z.max Z0 (Z.sub normalized q16_ONE) in
            let index = extract_lut_index frac_part in
            let frac_log = lut_lookup index log2_lut in
            let result = Z.add (Z.mul integer_log2 q16_ONE) frac_log in
            saturate result

(** val information_gain : z -> z -> q16 **)

let information_gain before after =
  if Z.leb before Z0
  then Z0
  else if Z.leb after Z0
       then q16_MAX
       else if Z.gtb after before
            then Z0
            else if Z.eqb before after
                 then Z0
                 else let ratio = Z.div (Z.mul before q16_ONE) after in
                      q16_log2 ratio

type muAccumulator =
  q16
  (* singleton inductive, whose constructor was Build_MuAccumulator *)

(** val mu_value : muAccumulator -> q16 **)

let mu_value m =
  m

(** val mu_accumulate : muAccumulator -> q16 -> muAccumulator **)

let mu_accumulate acc delta =
  q16_add (mu_value acc) delta
