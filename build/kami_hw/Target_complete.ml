
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val pred : int -> int **)

let pred = fun n -> Stdlib.max 0 (n-1)

(** val add : int -> int -> int **)

let rec add = (+)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  if b1 then b2 else if b2 then false else true

module Nat =
 struct
  (** val div2 : int -> int **)

  let rec div2 = fun n -> n/2
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t1 -> (f a) :: (map f t1)

type t =
| F1 of int
| FS of int * t

type 'a t0 =
| Nil
| Cons of 'a * int * 'a t0

(** val nth : int -> 'a1 t0 -> t -> 'a1 **)

let rec nth _ v p =
  match v with
  | Nil -> assert false (* absurd case *)
  | Cons (x, _, v') ->
    (match p with
     | F1 _ -> x
     | FS (n0, p') -> nth (pred (Stdlib.Int.succ n0)) v' p')

(** val map0 : ('a1 -> 'a2) -> int -> 'a1 t0 -> 'a2 t0 **)

let rec map0 f _ = function
| Nil -> Nil
| Cons (a, n0, v') -> Cons ((f a), n0, (map0 f n0 v'))

(** val ascii_eq : char -> char -> bool **)

let ascii_eq a1 a2 =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b1 b2 b3 b4 b5 b6 b7 b8 ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun c1 c2 c3 c4 c5 c6 c7 c8 ->
      (&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&) ((&&) ((&&) (eqb b1 c1) (eqb b2 c2)) (eqb b3 c3))
                (eqb b4 c4)) (eqb b5 c5)) (eqb b6 c6)) (eqb b7 c7))
        (eqb b8 c8))
      a2)
    a1

(** val string_eq : char list -> char list -> bool **)

let rec string_eq s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | a1::s1' ->
    (match s2 with
     | [] -> false
     | a2::s2' -> (&&) (ascii_eq a1 a2) (string_eq s1' s2'))

(** val mod2 : int -> bool **)

let rec mod2 n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun n0 ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n' -> mod2 n')
      n0)
    n

type word =
| WO
| WS of bool * int * word

(** val natToWord : int -> int -> word **)

let rec natToWord sz n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> WO)
    (fun sz' -> WS ((mod2 n), sz', (natToWord sz' (Nat.div2 n))))
    sz

(** val wzero : int -> word **)

let wzero sz =
  natToWord sz 0

type 'a attribute = { attrName : char list; attrType : 'a }

(** val vector_find' : ('a1 -> bool) -> int -> 'a1 t0 -> __ **)

let rec vector_find' f _ = function
| Nil -> Obj.magic ()
| Cons (h, n1, t1) ->
  if f h
  then Obj.magic (F1 n1)
  else ((fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> Obj.magic (F1 0))
          (fun n2 ->
          Obj.magic (FS ((Stdlib.Int.succ n2),
            (Obj.magic vector_find' f (Stdlib.Int.succ n2) t1))))
          n1)

(** val vector_find : ('a1 -> bool) -> int -> 'a1 t0 -> t **)

let vector_find f n v =
  Obj.magic vector_find' f (Stdlib.Int.succ n) v

type ('a, 'b) ilist =
| Inil
| Icons of 'a * int * 'a t0 * 'b * ('a, 'b) ilist

type 'a vec =
| Vec0 of 'a
| VecNext of int * 'a vec * 'a vec

(** val replicate : 'a1 -> int -> 'a1 vec **)

let rec replicate v n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Vec0 v)
    (fun m -> VecNext (m, (replicate v m), (replicate v m)))
    n

type kind =
| Bool
| Bit of int
| Vector of kind * int
| Struct of int * kind attribute t0
| Array of kind * int

type fullKind =
| SyntaxKind of kind
| NativeKind of __

type constT =
| ConstBool of bool
| ConstBit of int * word
| ConstVector of kind * int * constT vec
| ConstStruct of int * kind attribute t0 * (kind attribute, constT) ilist
| ConstArray of kind * int * constT t0

type constFullT =
| SyntaxConst of kind * constT
| NativeConst of __ * __

(** val vector_repeat : int -> 'a1 -> 'a1 t0 **)

let rec vector_repeat n a =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Nil)
    (fun m -> Cons (a, m, (vector_repeat m a)))
    n

(** val getDefaultConst : kind -> constT **)

let rec getDefaultConst = function
| Bool -> ConstBool false
| Bit n -> ConstBit (n, (wzero n))
| Vector (k0, n) -> ConstVector (k0, n, (replicate (getDefaultConst k0) n))
| Struct (n, ls) ->
  ConstStruct (n, ls,
    (let rec help _ = function
     | Nil -> Inil
     | Cons (x, m, xs) ->
       Icons (x, m, xs, (getDefaultConst x.attrType), (help m xs))
     in help n ls))
| Array (k0, n) -> ConstArray (k0, n, (vector_repeat n (getDefaultConst k0)))

type signatureT = { arg : kind; ret : kind }

type uniBoolOp =
| NegB

type binBoolOp =
| AndB
| OrB

type uniBitOp =
| Inv of int
| Neg of int
| ConstExtract of int * int * int
| Trunc of int * int
| ZeroExtendTrunc of int * int
| SignExtendTrunc of int * int
| TruncLsb of int * int

type binSign =
| SignSS
| SignSU
| SignUU

type binBitOp =
| Add of int
| Sub of int
| Mul of int * binSign
| Div of int * bool
| Rem of int * bool
| Band of int
| Bor of int
| Bxor of int
| Sll of int * int
| Srl of int * int
| Sra of int * int
| Concat of int * int

type binBitBoolOp =
| Lt of int
| Slt of int

type 'ty fullType = __

(** val fieldKind : int -> kind attribute t0 -> t -> kind **)

let fieldKind n ls i =
  nth n (map0 (fun a -> a.attrType) n ls) i

type 'ty expr =
| Var of fullKind * 'ty fullType
| Const of kind * constT
| UniBool of uniBoolOp * 'ty expr
| BinBool of binBoolOp * 'ty expr * 'ty expr
| UniBit of int * int * uniBitOp * 'ty expr
| BinBit of int * int * int * binBitOp * 'ty expr * 'ty expr
| BinBitBool of int * int * binBitBoolOp * 'ty expr * 'ty expr
| ITE of fullKind * 'ty expr * 'ty expr * 'ty expr
| Eq of kind * 'ty expr * 'ty expr
| ReadIndex of int * kind * 'ty expr * 'ty expr
| ReadField of int * kind attribute t0 * t * 'ty expr
| BuildVector of kind * int * 'ty expr vec
| BuildStruct of int * kind attribute t0 * (kind attribute, 'ty expr) ilist
| UpdateVector of int * kind * 'ty expr * 'ty expr * 'ty expr
| ReadArrayIndex of int * kind * int * 'ty expr * 'ty expr
| BuildArray of kind * int * 'ty expr t0
| UpdateArray of kind * int * int * 'ty expr * 'ty expr * 'ty expr

type bitFormat =
| Binary
| Decimal
| Hex

type fullBitFormat = int * bitFormat

type 'ty disp =
| DispBool of fullBitFormat * 'ty expr
| DispBit of fullBitFormat * int * 'ty expr
| DispStruct of int * fullBitFormat t0 * kind attribute t0 * 'ty expr
| DispArray of fullBitFormat * kind * int * 'ty expr

type 'ty actionT =
| MCall of char list * signatureT * 'ty expr * ('ty -> 'ty actionT)
| Let_ of fullKind * 'ty expr * ('ty fullType -> 'ty actionT)
| ReadNondet of fullKind * ('ty fullType -> 'ty actionT)
| ReadReg of char list * fullKind * ('ty fullType -> 'ty actionT)
| WriteReg of char list * fullKind * 'ty expr * 'ty actionT
| IfElse of 'ty expr * kind * 'ty actionT * 'ty actionT * ('ty -> 'ty actionT)
| Assert_ of 'ty expr * 'ty actionT
| Displ of 'ty disp list * 'ty actionT
| Return of 'ty expr

type action = __ -> __ actionT

type methodT = __ -> __ -> __ actionT

type regInitValue =
| RegInitCustom of (fullKind, constFullT) sigT
| RegInitDefault of fullKind

type regInitT = regInitValue attribute

type defMethT = (signatureT, methodT) sigT attribute

(** val void : kind **)

let void =
  Bit 0

type primitiveModule = { pm_name : char list; pm_regInits : regInitT list;
                         pm_rules : action attribute list;
                         pm_methods : defMethT list }

type modules =
| PrimMod of primitiveModule
| Mod of regInitT list * action attribute list * defMethT list
| ConcatMod of modules * modules

(** val fieldAccessor : char list -> 'a1 attribute -> bool **)

let fieldAccessor fn x =
  string_eq fn x.attrName

type moduleElt =
| MERegister of regInitT
| MERule of action attribute
| MEMeth of defMethT

type inModule =
| NilInModule
| ConsInModule of moduleElt * inModule

(** val makeModule' :
    inModule -> (regInitT list * action attribute list) * defMethT list **)

let rec makeModule' = function
| NilInModule -> (([], []), [])
| ConsInModule (e, i) ->
  let (p, imeths) = makeModule' i in
  let (iregs, irules) = p in
  (match e with
   | MERegister mreg -> (((mreg :: iregs), irules), imeths)
   | MERule mrule -> ((iregs, (mrule :: irules)), imeths)
   | MEMeth mmeth -> ((iregs, irules), (mmeth :: imeths)))

(** val makeModule : inModule -> modules **)

let makeModule im =
  let (p, meths) = makeModule' im in
  let (regs, rules) = p in Mod (regs, rules, meths)

(** val makeConst : kind -> constT -> constFullT **)

let makeConst k c =
  SyntaxConst (k, c)

type tyS = int

type exprS = tyS expr

type actionS =
| MCallS of char list * signatureT * exprS * int * actionS
| LetS_ of fullKind * exprS * int * actionS
| ReadNondetS of int * actionS
| ReadRegS of char list * int * actionS
| WriteRegS of char list * fullKind * exprS * actionS
| IfElseS of exprS * kind * actionS * actionS * int * actionS
| AssertS_ of exprS * actionS
| ReturnS of exprS

(** val getActionS : int -> kind -> tyS actionT -> int * actionS **)

let rec getActionS n lret = function
| MCall (meth, s, e, c) ->
  let (m, a') = getActionS (Stdlib.Int.succ n) lret (c n) in
  (m, (MCallS (meth, s, e, n, a')))
| Let_ (lret', e, cn) ->
  let v =
    getActionS (Stdlib.Int.succ n) lret
      (Obj.magic cn
        (match lret' with
         | SyntaxKind _ -> n
         | NativeKind c -> Obj.magic c))
  in
  (match lret' with
   | SyntaxKind _ -> ((fst v), (LetS_ (lret', e, n, (snd v))))
   | NativeKind _ -> (n, (ReturnS (Const (lret, (getDefaultConst lret))))))
| ReadNondet (k, cn) ->
  let v =
    getActionS (Stdlib.Int.succ n) lret
      (Obj.magic cn
        (match k with
         | SyntaxKind _ -> n
         | NativeKind c -> Obj.magic c))
  in
  (match k with
   | SyntaxKind _ -> ((fst v), (ReadNondetS (n, (snd v))))
   | NativeKind _ -> (n, (ReturnS (Const (lret, (getDefaultConst lret))))))
| ReadReg (r, k, cn) ->
  let v =
    getActionS (Stdlib.Int.succ n) lret
      (Obj.magic cn
        (match k with
         | SyntaxKind _ -> n
         | NativeKind c -> Obj.magic c))
  in
  (match k with
   | SyntaxKind _ -> ((fst v), (ReadRegS (r, n, (snd v))))
   | NativeKind _ -> (n, (ReturnS (Const (lret, (getDefaultConst lret))))))
| WriteReg (r, k, e, c) ->
  let (m, a') = getActionS n lret c in (m, (WriteRegS (r, k, e, a')))
| IfElse (e, k, ta, fa, c) ->
  let (tm, ta') = getActionS n k ta in
  let (fm, fa') = getActionS tm k fa in
  let (m, a') = getActionS (Stdlib.Int.succ fm) lret (c fm) in
  (m, (IfElseS (e, k, ta', fa', fm, a')))
| Assert_ (e, c) ->
  let (m, a') = getActionS n lret c in (m, (AssertS_ (e, a')))
| Displ (_, c) -> getActionS n lret c
| Return e -> (n, (ReturnS e))

type methodTS = actionS

type defMethTS = (signatureT, methodTS) sigT attribute

type modulesS =
| PrimModS of char list * signatureT attribute list
| ModS of regInitT list * actionS attribute list * defMethTS list
| ConcatModsS of modulesS * modulesS

(** val getMethS :
    (signatureT, methodT) sigT -> (signatureT, methodTS) sigT **)

let getMethS = function
| ExistT (arg0, meth) ->
  ExistT (arg0,
    (snd (getActionS (Stdlib.Int.succ 0) arg0.ret (Obj.magic meth __ 0))))

(** val getModuleS : modules -> modulesS **)

let rec getModuleS = function
| PrimMod prim ->
  PrimModS (prim.pm_name,
    (map (fun dm -> { attrName = dm.attrName; attrType =
      (projT1 dm.attrType) }) prim.pm_methods))
| Mod (regs, rules, dms) ->
  ModS (regs,
    (map (fun a -> { attrName = a.attrName; attrType =
      (snd (getActionS 0 void ((Obj.magic a).attrType __))) }) rules),
    (map (fun a -> { attrName = a.attrName; attrType =
      (getMethS a.attrType) }) dms))
| ConcatMod (m1, m2) -> ConcatModsS ((getModuleS m1), (getModuleS m2))

(** val mapVec : ('a1 -> 'a2) -> int -> 'a1 vec -> 'a2 vec **)

let rec mapVec map1 _ = function
| Vec0 e -> Vec0 (map1 e)
| VecNext (n', v1, v2) ->
  VecNext (n', (mapVec map1 n' v1), (mapVec map1 n' v2))

type bExpr =
| BVar of int
| BConst of kind * constT
| BUniBool of uniBoolOp * bExpr
| BBinBool of binBoolOp * bExpr * bExpr
| BUniBit of int * int * uniBitOp * bExpr
| BBinBit of int * int * int * binBitOp * bExpr * bExpr
| BBinBitBool of int * int * binBitBoolOp * bExpr * bExpr
| BITE of bExpr * bExpr * bExpr
| BEq of bExpr * bExpr
| BReadIndex of bExpr * bExpr
| BReadField of char list * bExpr
| BBuildVector of int * bExpr vec
| BBuildStruct of int * kind attribute t0 * bExpr attribute list
| BUpdateVector of bExpr * bExpr * bExpr
| BReadReg of char list
| BReadArrayIndex of bExpr * bExpr
| BBuildArray of int * bExpr t0
| BUpdateArray of bExpr * bExpr * bExpr

type bAction =
| BMCall of int * char list * signatureT * bExpr
| BBCall of int * char list * bool * bExpr list
| BLet of int * kind option * bExpr
| BWriteReg of char list * bExpr
| BIfElse of bExpr * int * kind * bAction list * bAction list
| BAssert of bExpr
| BReturn of bExpr

type bRule = bAction list attribute

type bMethod = (signatureT * bAction list) attribute

type bModule =
| BModulePrim of char list * signatureT attribute list
| BModuleB of regInitT list * bRule list * bMethod list

(** val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option **)

let bind oa f =
  match oa with
  | Some a -> f a
  | None -> None

(** val bindVec : int -> 'a1 option vec -> 'a1 vec option **)

let rec bindVec _ = function
| Vec0 oa -> bind oa (fun a -> Some (Vec0 a))
| VecNext (n0, v1, v2) ->
  bind (bindVec n0 v1) (fun bv1 ->
    bind (bindVec n0 v2) (fun bv2 -> Some (VecNext (n0, bv1, bv2))))

(** val bindVector : int -> 'a1 option t0 -> 'a1 t0 option **)

let rec bindVector _ = function
| Nil -> Some Nil
| Cons (a, n, vs) ->
  bind a (fun bv1 ->
    bind (bindVector n vs) (fun bv2 -> Some (Cons (bv1, n, bv2))))

(** val exprSToBExpr : fullKind -> exprS -> bExpr option **)

let rec exprSToBExpr _ = function
| Var (vk, i) ->
  (match vk with
   | SyntaxKind _ -> Some (BVar (Obj.magic i))
   | NativeKind _ -> None)
| Const (k, c) -> Some (BConst (k, c))
| UniBool (op, se) ->
  bind (exprSToBExpr (SyntaxKind Bool) se) (fun be -> Some (BUniBool (op,
    be)))
| BinBool (op, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind Bool) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind Bool) e2) (fun be2 -> Some (BBinBool (op,
      be1, be2))))
| UniBit (n1, n2, op, e0) ->
  bind (exprSToBExpr (SyntaxKind (Bit n1)) e0) (fun be -> Some (BUniBit (n1,
    n2, op, be)))
| BinBit (n1, n2, n3, op, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind (Bit n1)) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind (Bit n2)) e2) (fun be2 -> Some (BBinBit
      (n1, n2, n3, op, be1, be2))))
| BinBitBool (n1, n2, op, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind (Bit n1)) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind (Bit n2)) e2) (fun be2 -> Some
      (BBinBitBool (n1, n2, op, be1, be2))))
| ITE (k0, ce, te, fe) ->
  bind (exprSToBExpr (SyntaxKind Bool) ce) (fun bce ->
    bind (exprSToBExpr k0 te) (fun bte ->
      bind (exprSToBExpr k0 fe) (fun bfe -> Some (BITE (bce, bte, bfe)))))
| Eq (k0, e1, e2) ->
  bind (exprSToBExpr (SyntaxKind k0) e1) (fun be1 ->
    bind (exprSToBExpr (SyntaxKind k0) e2) (fun be2 -> Some (BEq (be1, be2))))
| ReadIndex (i, k0, ie, ve) ->
  bind (exprSToBExpr (SyntaxKind (Bit i)) ie) (fun bie ->
    bind (exprSToBExpr (SyntaxKind (Vector (k0, i))) ve) (fun bve -> Some
      (BReadIndex (bie, bve))))
| ReadField (n, ls, i, e0) ->
  bind (exprSToBExpr (SyntaxKind (Struct (n, ls))) e0) (fun be -> Some
    (BReadField ((nth n (map0 (fun a -> a.attrName) n ls) i), be)))
| BuildVector (n, lgn, v) ->
  bind (bindVec lgn (mapVec (exprSToBExpr (SyntaxKind n)) lgn v)) (fun bv ->
    Some (BBuildVector (lgn, bv)))
| BuildStruct (n, attrs, st) ->
  bind
    (let rec help _ _ = function
     | Inil -> Some []
     | Icons (k, na, vs, h, t1) ->
       (match exprSToBExpr (SyntaxKind k.attrType) h with
        | Some v ->
          bind (help na vs t1) (fun bl -> Some ({ attrName = k.attrName;
            attrType = v } :: bl))
        | None -> None)
     in help n attrs st) (fun bl -> Some (BBuildStruct (n, attrs, bl)))
| UpdateVector (i, k0, ve, ie, ke) ->
  bind (exprSToBExpr (SyntaxKind (Vector (k0, i))) ve) (fun bve ->
    bind (exprSToBExpr (SyntaxKind (Bit i)) ie) (fun bie ->
      bind (exprSToBExpr (SyntaxKind k0) ke) (fun bke -> Some (BUpdateVector
        (bve, bie, bke)))))
| ReadArrayIndex (i, k0, sz, ie, ve) ->
  bind (exprSToBExpr (SyntaxKind (Bit i)) ie) (fun bie ->
    bind (exprSToBExpr (SyntaxKind (Array (k0, (Stdlib.Int.succ sz)))) ve)
      (fun bve -> Some (BReadArrayIndex (bie, bve))))
| BuildArray (n0, n, v) ->
  bind (bindVector n (map0 (exprSToBExpr (SyntaxKind n0)) n v)) (fun bv ->
    Some (BBuildArray (n, bv)))
| UpdateArray (k0, sz, i, ve, ie, ke) ->
  bind (exprSToBExpr (SyntaxKind (Array (k0, (Stdlib.Int.succ sz)))) ve)
    (fun bve ->
    bind (exprSToBExpr (SyntaxKind (Bit i)) ie) (fun bie ->
      bind (exprSToBExpr (SyntaxKind k0) ke) (fun bke -> Some (BUpdateArray
        (bve, bie, bke)))))

(** val actionSToBAction : kind -> actionS -> bAction list option **)

let rec actionSToBAction k = function
| MCallS (name, msig, arge, idx, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr (SyntaxKind msig.arg) arge) (fun be -> Some ((BMCall
      (idx, name, msig, be)) :: bc)))
| LetS_ (lretT', e0, idx, cont) ->
  (match lretT' with
   | SyntaxKind k0 ->
     bind (actionSToBAction k cont) (fun bc ->
       bind (exprSToBExpr (SyntaxKind k0) e0) (fun be -> Some ((BLet (idx,
         (Some k0), be)) :: bc)))
   | NativeKind _ -> None)
| ReadNondetS (_, _) -> None
| ReadRegS (reg, idx, cont) ->
  bind (actionSToBAction k cont) (fun bc -> Some ((BLet (idx, None, (BReadReg
    reg))) :: bc))
| WriteRegS (reg, k0, e0, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr k0 e0) (fun be -> Some ((BWriteReg (reg, be)) :: bc)))
| IfElseS (ce, iretK, ta, fa, idx, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr (SyntaxKind Bool) ce) (fun bce ->
      bind (actionSToBAction iretK ta) (fun bta ->
        bind (actionSToBAction iretK fa) (fun bfa -> Some ((BIfElse (bce,
          idx, iretK, bta, bfa)) :: bc)))))
| AssertS_ (e0, cont) ->
  bind (actionSToBAction k cont) (fun bc ->
    bind (exprSToBExpr (SyntaxKind Bool) e0) (fun be -> Some ((BAssert
      be) :: bc)))
| ReturnS e0 ->
  bind (exprSToBExpr (SyntaxKind k) e0) (fun be -> Some ((BReturn be) :: []))

(** val rulesToBRules :
    actionS attribute list -> bAction list attribute list option **)

let rec rulesToBRules = function
| [] -> Some []
| a :: rs ->
  let { attrName = rn; attrType = rb } = a in
  bind (rulesToBRules rs) (fun brs ->
    bind (actionSToBAction void rb) (fun brb -> Some ({ attrName = rn;
      attrType = brb } :: brs)))

(** val methsToBMethods : defMethTS list -> bMethod list option **)

let rec methsToBMethods = function
| [] -> Some []
| d :: ms ->
  let { attrName = mn; attrType = attrType0 } = d in
  let ExistT (sig0, mb) = attrType0 in
  bind (methsToBMethods ms) (fun bms ->
    bind (actionSToBAction sig0.ret mb) (fun bmb -> Some ({ attrName = mn;
      attrType = (sig0, bmb) } :: bms)))

(** val modulesSToBModules : modulesS -> bModule list option **)

let rec modulesSToBModules = function
| PrimModS (pname, ifc) -> Some ((BModulePrim (pname, ifc)) :: [])
| ModS (regs, rules, dms) ->
  bind (rulesToBRules rules) (fun brules ->
    bind (methsToBMethods dms) (fun bdms -> Some ((BModuleB (regs, brules,
      bdms)) :: [])))
| ConcatModsS (m1, m2) ->
  bind (modulesSToBModules m1) (fun bm1 ->
    bind (modulesSToBModules m2) (fun bm2 -> Some (app bm1 bm2)))

(** val regIdxSz : int **)

let regIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))

(** val memAddrSz : int **)

let memAddrSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))

(** val wordSz : int **)

let wordSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))

(** val instrUpperSz : int **)

let instrUpperSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val instrSz : int **)

let instrSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val formatIdSz : int **)

let formatIdSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))

(** val formatSubtypeSz : int **)

let formatSubtypeSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val descKindFieldSz : int **)

let descKindFieldSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val inlineLenSz : int **)

let inlineLenSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))

(** val opcodeSz : int **)

let opcodeSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))

(** val costSz : int **)

let costSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))

(** val muTensorIdxSz : int **)

let muTensorIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))

(** val fMT_LEGACY : word **)

let fMT_LEGACY =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val fMT_BRANCH_EXT : word **)

let fMT_BRANCH_EXT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val fMT_TENSOR_EXT : word **)

let fMT_TENSOR_EXT =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val fMT_MORPH_INLINE : word **)

let fMT_MORPH_INLINE =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val fMT_DESC : word **)

let fMT_DESC =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val fMT_CERT_INLINE : word **)

let fMT_CERT_INLINE =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val pTableIdxSz : int **)

let pTableIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

(** val pTableNextIdSz : int **)

let pTableNextIdSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))

(** val descIdxSz : int **)

let descIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

(** val descTableNextIdSz : int **)

let descTableNextIdSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))

(** val morphTableIdxSz : int **)

let morphTableIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

(** val morphTableNextIdSz : int **)

let morphTableNextIdSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))

(** val couplingDescIdxSz : int **)

let couplingDescIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

(** val formulaDescIdxSz : int **)

let formulaDescIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

(** val certDescIdxSz : int **)

let certDescIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

(** val descMetaIdxSz : int **)

let descMetaIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

(** val couplingPairIdxSz : int **)

let couplingPairIdxSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))

(** val couplingPairCountSz : int **)

let couplingPairCountSz =
  Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))

(** val aCTIVE_MODULE_INIT : word **)

let aCTIVE_MODULE_INIT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))

(** val pT_NEXT_ID_INIT : word **)

let pT_NEXT_ID_INIT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))

(** val mORPH_NEXT_ID_INIT : word **)

let mORPH_NEXT_ID_INIT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))

(** val dESC_NEXT_ID_INIT : word **)

let dESC_NEXT_ID_INIT =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))

(** val eRR_CHSH_VAL : word **)

let eRR_CHSH_VAL =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_BIANCHI_VAL : word **)

let eRR_BIANCHI_VAL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_LOGIC_VAL : word **)

let eRR_LOGIC_VAL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_LOCALITY_VAL : word **)

let eRR_LOCALITY_VAL =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_PARTITION_VAL : word **)

let eRR_PARTITION_VAL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_COUPLING_INVALID : word **)

let eRR_COUPLING_INVALID =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_COMPOSE_TYPE : word **)

let eRR_COMPOSE_TYPE =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_MORPH_NOT_FOUND : word **)

let eRR_MORPH_NOT_FOUND =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_ISA_VERSION : word **)

let eRR_ISA_VERSION =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_FORMAT_INVALID : word **)

let eRR_FORMAT_INVALID =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_DESC_RANGE : word **)

let eRR_DESC_RANGE =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_INLINE_MALFORMED : word **)

let eRR_INLINE_MALFORMED =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_TABLE_OVERFLOW : word **)

let eRR_TABLE_OVERFLOW =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val eRR_CERT_DESC_INVALID : word **)

let eRR_CERT_DESC_INVALID =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val lOGIC_GATE_KEY : word **)

let lOGIC_GATE_KEY =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val tRAP_VEC_INIT : word **)

let tRAP_VEC_INIT =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val mSTATUS_TURING : word **)

let mSTATUS_TURING =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val mSTATUS_THIELE : word **)

let mSTATUS_THIELE =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val cHSH_X1_SURCHARGE : word **)

let cHSH_X1_SURCHARGE =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val oP_PNEW : word **)

let oP_PNEW =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_PSPLIT : word **)

let oP_PSPLIT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_PMERGE : word **)

let oP_PMERGE =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_LASSERT : word **)

let oP_LASSERT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_LJOIN : word **)

let oP_LJOIN =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_MDLACC : word **)

let oP_MDLACC =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_PDISCOVER : word **)

let oP_PDISCOVER =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_XFER : word **)

let oP_XFER =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_LOAD_IMM : word **)

let oP_LOAD_IMM =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_CHSH_TRIAL : word **)

let oP_CHSH_TRIAL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_XOR_LOAD : word **)

let oP_XOR_LOAD =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_XOR_ADD : word **)

let oP_XOR_ADD =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_XOR_SWAP : word **)

let oP_XOR_SWAP =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_XOR_RANK : word **)

let oP_XOR_RANK =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_EMIT : word **)

let oP_EMIT =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_REVEAL : word **)

let oP_REVEAL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_ORACLE_HALTS : word **)

let oP_ORACLE_HALTS =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_LOAD : word **)

let oP_LOAD =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_STORE : word **)

let oP_STORE =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_ADD : word **)

let oP_ADD =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_SUB : word **)

let oP_SUB =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_JUMP : word **)

let oP_JUMP =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_JNEZ : word **)

let oP_JNEZ =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_CALL : word **)

let oP_CALL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_RET : word **)

let oP_RET =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_READ_PORT : word **)

let oP_READ_PORT =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_HEAP_LOAD : word **)

let oP_HEAP_LOAD =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_HEAP_STORE : word **)

let oP_HEAP_STORE =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_CERTIFY : word **)

let oP_CERTIFY =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_AND : word **)

let oP_AND =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_OR : word **)

let oP_OR =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_SHL : word **)

let oP_SHL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_SHR : word **)

let oP_SHR =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_MUL : word **)

let oP_MUL =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_LUI : word **)

let oP_LUI =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_TENSOR_SET : word **)

let oP_TENSOR_SET =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_TENSOR_GET : word **)

let oP_TENSOR_GET =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_MORPH : word **)

let oP_MORPH =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_COMPOSE : word **)

let oP_COMPOSE =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_MORPH_ID : word **)

let oP_MORPH_ID =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_MORPH_DELETE : word **)

let oP_MORPH_DELETE =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_MORPH_ASSERT : word **)

let oP_MORPH_ASSERT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_MORPH_TENSOR : word **)

let oP_MORPH_TENSOR =
  WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_MORPH_GET : word **)

let oP_MORPH_GET =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))

(** val oP_HALT : word **)

let oP_HALT =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))))))

(** val loadInstrPort : kind attribute t0 **)

let loadInstrPort =
  Cons ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (Bit
    memAddrSz) }, (Stdlib.Int.succ 0), (Cons ({ attrName =
    ('d'::('a'::('t'::('a'::[])))); attrType = (Bit instrSz) }, 0, Nil)))

(** val aPBBusWritePort : kind attribute t0 **)

let aPBBusWritePort =
  Cons ({ attrName = ('a'::('d'::('d'::('r'::[])))); attrType = (Bit
    wordSz) }, (Stdlib.Int.succ 0), (Cons ({ attrName =
    ('d'::('a'::('t'::('a'::[])))); attrType = (Bit instrSz) }, 0, Nil)))

(** val sP_IDX : word **)

let sP_IDX =
  WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))

(** val check_bounds : 'a1 expr -> 'a1 expr -> 'a1 expr **)

let check_bounds addr active_partition_size =
  BinBitBool (wordSz, wordSz, (Lt wordSz), (UniBit (memAddrSz, wordSz,
    (ZeroExtendTrunc (memAddrSz, wordSz)), addr)), active_partition_size)

(** val read_mem : 'a1 expr -> 'a1 expr -> 'a1 expr **)

let read_mem addr memv =
  ReadIndex (memAddrSz, (Bit wordSz), addr, memv)

(** val write_mem : 'a1 expr -> 'a1 expr -> 'a1 expr -> 'a1 expr **)

let write_mem addr val0 memv =
  UpdateVector (memAddrSz, (Bit wordSz), memv, addr, val0)

(** val thieleCore : modules **)

let thieleCore =
  makeModule (ConsInModule ((MERegister { attrName = ('p'::('c'::[]));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName = ('m'::('u'::[])); attrType = (RegInitDefault
    (SyntaxKind (Bit wordSz))) }), (ConsInModule ((MERegister { attrName =
    ('e'::('r'::('r'::[]))); attrType = (RegInitCustom (ExistT ((SyntaxKind
    Bool), (makeConst Bool (ConstBool false))))) }), (ConsInModule
    ((MERegister { attrName = ('h'::('a'::('l'::('t'::('e'::('d'::[]))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false))))) }), (ConsInModule ((MERegister
    { attrName = ('r'::('e'::('g'::('s'::[])))); attrType = (RegInitDefault
    (SyntaxKind (Vector ((Bit wordSz), regIdxSz)))) }), (ConsInModule
    ((MERegister { attrName = ('m'::('e'::('m'::[]))); attrType =
    (RegInitDefault (SyntaxKind (Vector ((Bit wordSz), memAddrSz)))) }),
    (ConsInModule ((MERegister { attrName = ('i'::('m'::('e'::('m'::[]))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit instrSz),
    memAddrSz)))) }), (ConsInModule ((MERegister { attrName =
    ('p'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('_'::('o'::('p'::('s'::[])))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('m'::('d'::('l'::('_'::('o'::('p'::('s'::[]))))))); attrType =
    (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule ((MERegister
    { attrName =
    ('i'::('n'::('f'::('o'::('_'::('g'::('a'::('i'::('n'::[])))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[]))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('o'::('g'::('i'::('c'::('_'::('a'::('c'::('c'::[])))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('c'::('e'::('r'::('t'::('_'::('a'::('d'::('d'::('r'::[])))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('a'::('c'::('t'::('i'::('v'::('e'::('_'::('m'::('o'::('d'::('u'::('l'::('e'::[])))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind (Bit pTableIdxSz)),
    (makeConst (Bit pTableIdxSz) (ConstBit (pTableIdxSz, aCTIVE_MODULE_INIT)))))) }),
    (ConsInModule ((MERegister { attrName =
    ('m'::('s'::('t'::('a'::('t'::('u'::('s'::[]))))))); attrType =
    (RegInitCustom (ExistT ((SyntaxKind (Bit wordSz)),
    (makeConst (Bit wordSz) (ConstBit (wordSz, mSTATUS_THIELE)))))) }),
    (ConsInModule ((MERegister { attrName =
    ('m'::('c'::('y'::('c'::('l'::('e'::('_'::('l'::('o'::[])))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('m'::('c'::('y'::('c'::('l'::('e'::('_'::('h'::('i'::[])))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('m'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('_'::('l'::('o'::[])))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('m'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('_'::('h'::('i'::[])))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('t'::('r'::('a'::('p'::('_'::('v'::('e'::('c'::('t'::('o'::('r'::[])))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind (Bit wordSz)),
    (makeConst (Bit wordSz) (ConstBit (wordSz, tRAP_VEC_INIT)))))) }),
    (ConsInModule ((MERegister { attrName =
    ('c'::('e'::('r'::('t'::('i'::('f'::('i'::('e'::('d'::[])))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false))))) }), (ConsInModule ((MERegister
    { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('p'::('h'::('a'::('s'::('e'::[])))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))) }), (ConsInModule ((MERegister
    { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('k'::('i'::('n'::('d'::[]))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false))))) }), (ConsInModule ((MERegister
    { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('b'::('a'::('s'::('e'::[])))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('b'::('a'::('s'::('e'::[])))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('l'::('e'::('n'::[]))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('l'::('e'::('n'::[]))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('p'::('t'::('r'::[]))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('p'::('t'::('r'::[]))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('b'::('u'::('f'::[]))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))) }), (ConsInModule ((MERegister { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('b'::('u'::('f'::[]))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))) }), (ConsInModule ((MERegister
    { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('l'::('a'::('u'::('s'::('e'::('_'::('s'::('a'::('t'::[]))))))))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false))))) }), (ConsInModule ((MERegister
    { attrName =
    ('b'::('u'::('s'::('_'::('l'::('o'::('a'::('d'::('_'::('i'::('n'::('s'::('t'::('r'::('_'::('a'::('d'::('d'::('r'::[])))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit memAddrSz))) }),
    (ConsInModule ((MERegister { attrName =
    ('b'::('u'::('s'::('_'::('l'::('o'::('a'::('d'::('_'::('i'::('n'::('s'::('t'::('r'::('_'::('d'::('a'::('t'::('a'::[])))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit instrSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('b'::('u'::('s'::('_'::('l'::('o'::('a'::('d'::('_'::('i'::('n'::('s'::('t'::('r'::('_'::('k'::('i'::('c'::('k'::[])))))))))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind Bool),
    (makeConst Bool (ConstBool false))))) }), (ConsInModule ((MERegister
    { attrName =
    ('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[])))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('p'::('t'::('T'::('a'::('b'::('l'::('e'::[]))))))); attrType =
    (RegInitDefault (SyntaxKind (Vector ((Bit wordSz), pTableIdxSz)))) }),
    (ConsInModule ((MERegister { attrName =
    ('p'::('t'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind (Bit pTableNextIdSz)),
    (makeConst (Bit pTableNextIdSz) (ConstBit (pTableNextIdSz,
      pT_NEXT_ID_INIT)))))) }), (ConsInModule ((MERegister { attrName =
    ('m'::('o'::('r'::('p'::('h'::('_'::('s'::('r'::('c'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit pTableIdxSz),
    morphTableIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('m'::('o'::('r'::('p'::('h'::('_'::('d'::('s'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit pTableIdxSz),
    morphTableIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('m'::('o'::('r'::('p'::('h'::('_'::('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit descIdxSz),
    morphTableIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('m'::('o'::('r'::('p'::('h'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector (Bool,
    morphTableIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('m'::('o'::('r'::('p'::('h'::('_'::('i'::('d'::('e'::('n'::('t'::('i'::('t'::('y'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector (Bool,
    morphTableIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('m'::('o'::('r'::('p'::('h'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind (Bit morphTableNextIdSz)),
    (makeConst (Bit morphTableNextIdSz) (ConstBit (morphTableNextIdSz,
      mORPH_NEXT_ID_INIT)))))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('b'::('a'::('s'::('e'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit couplingPairIdxSz),
    couplingDescIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('c'::('o'::('u'::('n'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit
    couplingPairCountSz), couplingDescIdxSz)))) }), (ConsInModule
    ((MERegister { attrName =
    ('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector (Bool,
    couplingDescIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind (Bit descTableNextIdSz)),
    (makeConst (Bit descTableNextIdSz) (ConstBit (descTableNextIdSz,
      dESC_NEXT_ID_INIT)))))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('p'::('a'::('i'::('r'::('_'::('s'::('r'::('c'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    couplingPairIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('p'::('a'::('i'::('r'::('_'::('d'::('s'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    couplingPairIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('p'::('a'::('i'::('r'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector (Bool,
    couplingPairIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('p'::('a'::('i'::('r'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind (Bit descTableNextIdSz)),
    (makeConst (Bit descTableNextIdSz) (ConstBit (descTableNextIdSz,
      dESC_NEXT_ID_INIT)))))) }), (ConsInModule ((MERegister { attrName =
    ('f'::('o'::('r'::('m'::('u'::('l'::('a'::('_'::('d'::('e'::('s'::('c'::('_'::('b'::('a'::('s'::('e'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    formulaDescIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('f'::('o'::('r'::('m'::('u'::('l'::('a'::('_'::('d'::('e'::('s'::('c'::('_'::('c'::('o'::('u'::('n'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    formulaDescIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('f'::('o'::('r'::('m'::('u'::('l'::('a'::('_'::('d'::('e'::('s'::('c'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector (Bool,
    formulaDescIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('f'::('o'::('r'::('m'::('u'::('l'::('a'::('_'::('d'::('e'::('s'::('c'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind (Bit descTableNextIdSz)),
    (makeConst (Bit descTableNextIdSz) (ConstBit (descTableNextIdSz,
      dESC_NEXT_ID_INIT)))))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('e'::('r'::('t'::('_'::('d'::('e'::('s'::('c'::('_'::('b'::('a'::('s'::('e'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    certDescIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('e'::('r'::('t'::('_'::('d'::('e'::('s'::('c'::('_'::('c'::('o'::('u'::('n'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    certDescIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('e'::('r'::('t'::('_'::('d'::('e'::('s'::('c'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector (Bool,
    certDescIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('c'::('e'::('r'::('t'::('_'::('d'::('e'::('s'::('c'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind (Bit descTableNextIdSz)),
    (makeConst (Bit descTableNextIdSz) (ConstBit (descTableNextIdSz,
      dESC_NEXT_ID_INIT)))))) }), (ConsInModule ((MERegister { attrName =
    ('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('s'::('u'::('b'::('t'::('y'::('p'::('e'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit formatSubtypeSz),
    descMetaIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('k'::('i'::('n'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit descKindFieldSz),
    descMetaIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('i'::('n'::('l'::('i'::('n'::('e'::('_'::('l'::('e'::('n'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit inlineLenSz),
    descMetaIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('a'::('u'::('x'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector ((Bit wordSz),
    descMetaIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))));
    attrType = (RegInitDefault (SyntaxKind (Vector (Bool,
    descMetaIdxSz)))) }), (ConsInModule ((MERegister { attrName =
    ('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))))))))));
    attrType = (RegInitCustom (ExistT ((SyntaxKind (Bit descTableNextIdSz)),
    (makeConst (Bit descTableNextIdSz) (ConstBit (descTableNextIdSz,
      dESC_NEXT_ID_INIT)))))) }), (ConsInModule ((MERegister { attrName =
    ('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('0'::('0'::[]))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('0'::('0'::[]))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('0'::('1'::[]))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('0'::('1'::[]))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('1'::('0'::[]))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('1'::('0'::[]))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('1'::('1'::[]))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERegister { attrName =
    ('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('1'::('1'::[]))))))))));
    attrType = (RegInitDefault (SyntaxKind (Bit wordSz))) }), (ConsInModule
    ((MERule { attrName = ('s'::('t'::('e'::('p'::[])))); attrType =
    (fun _ -> ReadReg (('h'::('a'::('l'::('t'::('e'::('d'::[])))))),
    (SyntaxKind Bool), (fun halted_v -> Assert_ ((UniBool (NegB, (Var
    ((SyntaxKind Bool), halted_v)))), (ReadReg (('e'::('r'::('r'::[]))),
    (SyntaxKind Bool), (fun err_v -> Assert_ ((UniBool (NegB, (Var
    ((SyntaxKind Bool), err_v)))), (ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('p'::('h'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (fun lassert_phase_v -> Assert_ ((Eq ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))),
    lassert_phase_v)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))),
    (natToWord (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) 0))))))),
    (ReadReg (('p'::('c'::[])), (SyntaxKind (Bit wordSz)), (fun pc_v ->
    ReadReg (('m'::('u'::[])), (SyntaxKind (Bit wordSz)), (fun mu_v ->
    ReadReg (('r'::('e'::('g'::('s'::[])))), (SyntaxKind (Vector ((Bit
    wordSz), regIdxSz))), (fun regs_v -> ReadReg (('m'::('e'::('m'::[]))),
    (SyntaxKind (Vector ((Bit wordSz), memAddrSz))), (fun mem_v -> ReadReg
    (('i'::('m'::('e'::('m'::[])))), (SyntaxKind (Vector ((Bit instrSz),
    memAddrSz))), (fun imem_v -> ReadReg
    (('p'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('_'::('o'::('p'::('s'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun partition_ops_v -> ReadReg
    (('m'::('d'::('l'::('_'::('o'::('p'::('s'::[]))))))), (SyntaxKind (Bit
    wordSz)), (fun mdl_ops_v -> ReadReg
    (('i'::('n'::('f'::('o'::('_'::('g'::('a'::('i'::('n'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun info_gain_v -> ReadReg
    (('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun error_code_v -> ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('a'::('c'::('c'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun logic_acc_v -> ReadReg
    (('c'::('e'::('r'::('t'::('_'::('a'::('d'::('d'::('r'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun cert_addr_v -> ReadReg
    (('a'::('c'::('t'::('i'::('v'::('e'::('_'::('m'::('o'::('d'::('u'::('l'::('e'::[]))))))))))))),
    (SyntaxKind (Bit pTableIdxSz)), (fun active_module_v -> ReadReg
    (('m'::('s'::('t'::('a'::('t'::('u'::('s'::[]))))))), (SyntaxKind (Bit
    wordSz)), (fun _ -> ReadReg
    (('m'::('c'::('y'::('c'::('l'::('e'::('_'::('l'::('o'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun mcycle_lo_v -> ReadReg
    (('m'::('c'::('y'::('c'::('l'::('e'::('_'::('h'::('i'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun mcycle_hi_v -> ReadReg
    (('m'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('_'::('l'::('o'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (fun minstret_lo_v -> ReadReg
    (('m'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('_'::('h'::('i'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (fun minstret_hi_v -> ReadReg
    (('t'::('r'::('a'::('p'::('_'::('v'::('e'::('c'::('t'::('o'::('r'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (fun trap_vector_v -> ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun mu_tensor_v ->
    ReadReg (('p'::('t'::('T'::('a'::('b'::('l'::('e'::[]))))))), (SyntaxKind
    (Vector ((Bit wordSz), pTableIdxSz))), (fun pt_sizes_v -> ReadReg
    (('p'::('t'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))),
    (SyntaxKind (Bit pTableNextIdSz)), (fun pt_next_id_v -> ReadReg
    (('c'::('e'::('r'::('t'::('i'::('f'::('i'::('e'::('d'::[]))))))))),
    (SyntaxKind Bool), (fun certified_v -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('s'::('r'::('c'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))),
    (SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    (fun morph_src_table_v -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('d'::('s'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))),
    (SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    (fun morph_dst_table_v -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))),
    (SyntaxKind (Vector (Bool, morphTableIdxSz))),
    (fun morph_valid_table_v -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit descIdxSz), morphTableIdxSz))),
    (fun morph_coupling_desc_table_v -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('i'::('d'::('e'::('n'::('t'::('i'::('t'::('y'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))),
    (SyntaxKind (Vector (Bool, morphTableIdxSz))),
    (fun morph_identity_table_v -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))),
    (SyntaxKind (Bit morphTableNextIdSz)), (fun morph_next_id_v -> ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))),
    (SyntaxKind (Vector (Bool, couplingDescIdxSz))),
    (fun coupling_desc_valid_table_v -> ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('c'::('o'::('u'::('n'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit couplingPairCountSz), couplingDescIdxSz))),
    (fun coupling_desc_count_table_v -> ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))))))))))),
    (SyntaxKind (Bit descTableNextIdSz)), (fun coupling_desc_next_id_v ->
    ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('p'::('a'::('i'::('r'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))))))))))),
    (SyntaxKind (Bit descTableNextIdSz)), (fun coupling_pair_next_id_v ->
    ReadReg
    (('f'::('o'::('r'::('m'::('u'::('l'::('a'::('_'::('d'::('e'::('s'::('c'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))),
    (SyntaxKind (Vector (Bool, formulaDescIdxSz))),
    (fun formula_desc_valid_table_v -> ReadReg
    (('f'::('o'::('r'::('m'::('u'::('l'::('a'::('_'::('d'::('e'::('s'::('c'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))))))))))))),
    (SyntaxKind (Bit descTableNextIdSz)), (fun formula_desc_next_id_v ->
    ReadReg
    (('c'::('e'::('r'::('t'::('_'::('d'::('e'::('s'::('c'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))),
    (SyntaxKind (Vector (Bool, certDescIdxSz))),
    (fun cert_desc_valid_table_v -> ReadReg
    (('c'::('e'::('r'::('t'::('_'::('d'::('e'::('s'::('c'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))))))),
    (SyntaxKind (Bit descTableNextIdSz)), (fun cert_desc_next_id_v -> ReadReg
    (('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))),
    (SyntaxKind (Vector (Bool, descMetaIdxSz))),
    (fun desc_meta_valid_table_v -> ReadReg
    (('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))))))),
    (SyntaxKind (Bit descTableNextIdSz)), (fun desc_meta_next_id_v -> ReadReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('0'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun wc_same_00_v -> ReadReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('0'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun wc_diff_00_v -> ReadReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('0'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun wc_same_01_v -> ReadReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('0'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun wc_diff_01_v -> ReadReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('1'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun wc_same_10_v -> ReadReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('1'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun wc_diff_10_v -> ReadReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('1'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun wc_same_11_v -> ReadReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('1'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun wc_diff_11_v -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t1 -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))),
    (fun t2 -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t3 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t4 -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))),
    (fun t5 -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t6 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t7 -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))),
    (fun t8 -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t9 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t10 ->
    Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t11 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t12 ->
    Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t13 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t14 ->
    Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))), (fun t15 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (fun t16 ->
    Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), t1)), (Var
    ((SyntaxKind (Bit wordSz)), t2)))), (Var ((SyntaxKind (Bit wordSz)),
    t3)))), (Var ((SyntaxKind (Bit wordSz)), t4)))), (Var ((SyntaxKind (Bit
    wordSz)), t5)))), (Var ((SyntaxKind (Bit wordSz)), t6)))), (Var
    ((SyntaxKind (Bit wordSz)), t7)))), (Var ((SyntaxKind (Bit wordSz)),
    t8)))), (Var ((SyntaxKind (Bit wordSz)), t9)))), (Var ((SyntaxKind (Bit
    wordSz)), t10)))), (Var ((SyntaxKind (Bit wordSz)), t11)))), (Var
    ((SyntaxKind (Bit wordSz)), t12)))), (Var ((SyntaxKind (Bit wordSz)),
    t13)))), (Var ((SyntaxKind (Bit wordSz)), t14)))), (Var ((SyntaxKind (Bit
    wordSz)), t15)))), (Var ((SyntaxKind (Bit wordSz)), t16)))),
    (fun tensor_total -> Let_ ((SyntaxKind Bool), (BinBitBool (wordSz,
    wordSz, (Lt wordSz), (Var ((SyntaxKind (Bit wordSz)), mu_v)), (Var
    ((SyntaxKind (Bit wordSz)), tensor_total)))), (fun bianchi_violation ->
    Let_ ((SyntaxKind (Bit memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))), memAddrSz, (Trunc (memAddrSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), pc_v)))),
    (fun pc_addr -> Let_ ((SyntaxKind (Bit instrSz)), (ReadIndex (memAddrSz,
    (Bit instrSz), (Var ((SyntaxKind (Bit memAddrSz)), pc_addr)), (Var
    ((SyntaxKind (Vector ((Bit instrSz), memAddrSz))), imem_v)))),
    (fun instr_v -> Let_ ((SyntaxKind (Bit wordSz)), (UniBit
    ((add wordSz instrUpperSz), wordSz, (Trunc (wordSz, instrUpperSz)), (Var
    ((SyntaxKind (Bit instrSz)), instr_v)))), (fun legacy_instr -> Let_
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ
         0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         0))))))))) 0), (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), (ConstExtract ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), 0)), (Var ((SyntaxKind (Bit instrSz)), instr_v)))),
    (fun isa_version -> Let_ ((SyntaxKind (Bit formatIdSz)), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ
         0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         formatIdSz) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))), formatIdSz, (ConstExtract
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    formatIdSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), (Var ((SyntaxKind (Bit instrSz)),
    instr_v)))), (fun format_id -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ
         0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         0))))))))))))))))) (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))),
    (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))), (Var ((SyntaxKind (Bit instrSz)),
    instr_v)))), (fun flags -> Let_ ((SyntaxKind (Bit wordSz)), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))))))))))))))))))))))))))))) wordSz)
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    wordSz, (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))))), wordSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit instrSz)), instr_v)))), (fun ext0 -> Let_ ((SyntaxKind
    (Bit opcodeSz)), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))))))))))))))))))))) (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))) 0),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), 0)), (Var ((SyntaxKind (Bit wordSz)), legacy_instr)))),
    (fun opcode -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))))))))))))) (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))) (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), (Var ((SyntaxKind (Bit wordSz)), legacy_instr)))),
    (fun op_a -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))))) (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))) (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), legacy_instr)))),
    (fun op_b -> Let_ ((SyntaxKind (Bit costSz)), (UniBit
    ((add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0)))))))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Trunc
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))), (Var ((SyntaxKind (Bit
    wordSz)), legacy_instr)))), (fun cost_v -> Let_ ((SyntaxKind (Bit
    formatSubtypeSz)), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))))))))) formatSubtypeSz) 0), formatSubtypeSz,
    (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))), formatSubtypeSz, 0)), (Var ((SyntaxKind
    (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), flags)))), (fun _ -> Let_ ((SyntaxKind (Bit
    descKindFieldSz)), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))))))) descKindFieldSz) (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))),
    descKindFieldSz, (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), descKindFieldSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))), flags)))),
    (fun desc_kind -> Let_ ((SyntaxKind (Bit inlineLenSz)), (UniBit
    ((add inlineLenSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))), inlineLenSz, (Trunc (inlineLenSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))), flags)))),
    (fun inline_len -> Let_ ((SyntaxKind (Bit descIdxSz)), (UniBit
    ((add descIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))), descIdxSz, (Trunc (descIdxSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), ext0)))), (fun primary_desc_id -> Let_
    ((SyntaxKind (Bit descIdxSz)), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))) descIdxSz)
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))), descIdxSz, (ConstExtract ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), descIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), ext0)))), (fun secondary_desc_id -> Let_
    ((SyntaxKind (Bit descTableNextIdSz)), (UniBit (descIdxSz,
    descTableNextIdSz, (ZeroExtendTrunc (descIdxSz, descTableNextIdSz)), (Var
    ((SyntaxKind (Bit descIdxSz)), primary_desc_id)))),
    (fun primary_desc_id_7 -> Let_ ((SyntaxKind (Bit descTableNextIdSz)),
    (UniBit (descIdxSz, descTableNextIdSz, (ZeroExtendTrunc (descIdxSz,
    descTableNextIdSz)), (Var ((SyntaxKind (Bit descIdxSz)),
    secondary_desc_id)))), (fun secondary_desc_id_7 -> Let_ ((SyntaxKind
    Bool),
    (let e1 = Var ((SyntaxKind (Bit descIdxSz)), secondary_desc_id) in
     let e2 = Const ((Bit descIdxSz), (ConstBit (descIdxSz,
       (natToWord descIdxSz 0))))
     in
     UniBool (NegB, (Eq ((Bit descIdxSz), e1, e2)))),
    (fun secondary_desc_present -> Let_ ((SyntaxKind Bool), (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)),
    (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_MORPH)))))), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_COMPOSE)))))))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_MORPH_ID)))))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MORPH_DELETE)))))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MORPH_ASSERT)))))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MORPH_TENSOR)))))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MORPH_GET)))))))), (fun is_morph_opcode -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_LASSERT)))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_LJOIN)))))))),
    (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_EMIT)))))))), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_REVEAL)))))))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_CERTIFY)))))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MORPH_ASSERT)))))))), (fun is_cert_opcode -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (BinBool (OrB, (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_JUMP)))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_JNEZ)))))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_CALL)))))))), (fun is_branch_ext_capable -> Let_ ((SyntaxKind Bool),
    (BinBool (OrB, (BinBool (OrB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_REVEAL)))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_TENSOR_SET)))))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_TENSOR_GET)))))))), (fun is_tensor_ext_capable -> Let_ ((SyntaxKind
    Bool), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB,
    (BinBool (OrB, (Eq ((Bit formatIdSz), (Var ((SyntaxKind (Bit
    formatIdSz)), format_id)), (Const ((Bit formatIdSz), (ConstBit
    (formatIdSz, fMT_LEGACY)))))), (Eq ((Bit formatIdSz), (Var ((SyntaxKind
    (Bit formatIdSz)), format_id)), (Const ((Bit formatIdSz), (ConstBit
    (formatIdSz, fMT_BRANCH_EXT)))))))), (Eq ((Bit formatIdSz), (Var
    ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit formatIdSz),
    (ConstBit (formatIdSz, fMT_TENSOR_EXT)))))))), (Eq ((Bit formatIdSz),
    (Var ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit
    formatIdSz), (ConstBit (formatIdSz, fMT_MORPH_INLINE)))))))), (Eq ((Bit
    formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)), format_id)), (Const
    ((Bit formatIdSz), (ConstBit (formatIdSz, fMT_DESC)))))))), (Eq ((Bit
    formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)), format_id)), (Const
    ((Bit formatIdSz), (ConstBit (formatIdSz, fMT_CERT_INLINE)))))))),
    (fun format_known -> Let_ ((SyntaxKind Bool), (ITE ((SyntaxKind Bool),
    (Eq ((Bit formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)), format_id)),
    (Const ((Bit formatIdSz), (ConstBit (formatIdSz, fMT_LEGACY)))))), (Const
    (Bool, (ConstBool true))), (ITE ((SyntaxKind Bool), (Eq ((Bit
    formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)), format_id)), (Const
    ((Bit formatIdSz), (ConstBit (formatIdSz, fMT_BRANCH_EXT)))))), (Var
    ((SyntaxKind Bool), is_branch_ext_capable)), (ITE ((SyntaxKind Bool), (Eq
    ((Bit formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)), format_id)),
    (Const ((Bit formatIdSz), (ConstBit (formatIdSz, fMT_TENSOR_EXT)))))),
    (Var ((SyntaxKind Bool), is_tensor_ext_capable)), (ITE ((SyntaxKind
    Bool), (Eq ((Bit formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)),
    format_id)), (Const ((Bit formatIdSz), (ConstBit (formatIdSz,
    fMT_MORPH_INLINE)))))), (Var ((SyntaxKind Bool), is_morph_opcode)), (ITE
    ((SyntaxKind Bool), (Eq ((Bit formatIdSz), (Var ((SyntaxKind (Bit
    formatIdSz)), format_id)), (Const ((Bit formatIdSz), (ConstBit
    (formatIdSz, fMT_DESC)))))), (BinBool (OrB, (Var ((SyntaxKind Bool),
    is_morph_opcode)), (Var ((SyntaxKind Bool), is_cert_opcode)))), (ITE
    ((SyntaxKind Bool), (Eq ((Bit formatIdSz), (Var ((SyntaxKind (Bit
    formatIdSz)), format_id)), (Const ((Bit formatIdSz), (ConstBit
    (formatIdSz, fMT_CERT_INLINE)))))), (Var ((SyntaxKind Bool),
    is_cert_opcode)), (Const (Bool, (ConstBool false))))))))))))))),
    (fun format_allowed_for_opcode -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    descKindFieldSz), (Var ((SyntaxKind (Bit descKindFieldSz)), desc_kind)),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))), (fun desc_kind_is_zero -> Let_ ((SyntaxKind Bool), (Eq
    ((Bit descKindFieldSz), (Var ((SyntaxKind (Bit descKindFieldSz)),
    desc_kind)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))))), (fun desc_kind_is_morph -> Let_
    ((SyntaxKind Bool), (Eq ((Bit descKindFieldSz), (Var ((SyntaxKind (Bit
    descKindFieldSz)), desc_kind)), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))),
    (fun desc_kind_is_coupling -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    descKindFieldSz), (Var ((SyntaxKind (Bit descKindFieldSz)), desc_kind)),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))), (fun desc_kind_is_formula -> Let_ ((SyntaxKind Bool),
    (Eq ((Bit descKindFieldSz), (Var ((SyntaxKind (Bit descKindFieldSz)),
    desc_kind)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))))), (fun desc_kind_is_cert -> Let_
    ((SyntaxKind Bool), (Eq ((Bit descKindFieldSz), (Var ((SyntaxKind (Bit
    descKindFieldSz)), desc_kind)), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))),
    (fun desc_kind_is_meta -> Let_ ((SyntaxKind Bool), (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool),
    desc_kind_is_morph)), (Var ((SyntaxKind Bool), desc_kind_is_coupling)))),
    (Var ((SyntaxKind Bool), desc_kind_is_formula)))), (Var ((SyntaxKind
    Bool), desc_kind_is_cert)))), (Var ((SyntaxKind Bool),
    desc_kind_is_meta)))), (fun desc_kind_valid -> Let_ ((SyntaxKind Bool),
    (Eq ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), flags)), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))),
    (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))),
    (natToWord (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0)))))))))))))))) 0))))))), (fun flags_are_zero ->
    Let_ ((SyntaxKind Bool), (Eq ((Bit inlineLenSz), (Var ((SyntaxKind (Bit
    inlineLenSz)), inline_len)), (Const ((Bit inlineLenSz), (ConstBit
    (inlineLenSz, (natToWord inlineLenSz 0))))))), (fun inline_len_zero ->
    Let_ ((SyntaxKind Bool), (BinBitBool (inlineLenSz, inlineLenSz, (Lt
    inlineLenSz), (Const ((Bit inlineLenSz), (ConstBit (inlineLenSz,
    (natToWord inlineLenSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))), (Var ((SyntaxKind (Bit inlineLenSz)),
    inline_len)))), (fun inline_len_too_large -> Let_ ((SyntaxKind Bool),
    (BinBool (AndB, (BinBool (OrB, (BinBool (OrB, (Eq ((Bit formatIdSz), (Var
    ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit formatIdSz),
    (ConstBit (formatIdSz, fMT_LEGACY)))))), (Eq ((Bit formatIdSz), (Var
    ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit formatIdSz),
    (ConstBit (formatIdSz, fMT_BRANCH_EXT)))))))), (Eq ((Bit formatIdSz),
    (Var ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit
    formatIdSz), (ConstBit (formatIdSz, fMT_TENSOR_EXT)))))))), (UniBool
    (NegB, (Var ((SyntaxKind Bool), flags_are_zero)))))),
    (fun reserved_flag_fault -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (BinBool (OrB, (Eq ((Bit formatIdSz), (Var ((SyntaxKind (Bit
    formatIdSz)), format_id)), (Const ((Bit formatIdSz), (ConstBit
    (formatIdSz, fMT_MORPH_INLINE)))))), (Eq ((Bit formatIdSz), (Var
    ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit formatIdSz),
    (ConstBit (formatIdSz, fMT_CERT_INLINE)))))))), (BinBool (OrB, (BinBool
    (OrB, (UniBool (NegB, (Var ((SyntaxKind Bool), desc_kind_is_zero)))),
    (Var ((SyntaxKind Bool), inline_len_zero)))), (Var ((SyntaxKind Bool),
    inline_len_too_large)))))), (fun inline_payload_fault -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (Eq ((Bit formatIdSz), (Var
    ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit formatIdSz),
    (ConstBit (formatIdSz, fMT_DESC)))))), (BinBool (OrB, (UniBool (NegB,
    (Var ((SyntaxKind Bool), inline_len_zero)))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), desc_kind_valid)))))))), (fun desc_flag_fault -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (UniBool (NegB, (BinBitBool
    (descTableNextIdSz, descTableNextIdSz, (Lt descTableNextIdSz), (Var
    ((SyntaxKind (Bit descTableNextIdSz)), primary_desc_id_7)), (Var
    ((SyntaxKind (Bit morphTableNextIdSz)), morph_next_id_v)))))), (UniBool
    (NegB, (ReadIndex (descIdxSz, Bool, (Var ((SyntaxKind (Bit descIdxSz)),
    primary_desc_id)), (Var ((SyntaxKind (Vector (Bool, morphTableIdxSz))),
    morph_valid_table_v)))))))), (fun primary_morph_desc_invalid -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (Var ((SyntaxKind Bool),
    secondary_desc_present)), (BinBool (OrB, (UniBool (NegB, (BinBitBool
    (descTableNextIdSz, descTableNextIdSz, (Lt descTableNextIdSz), (Var
    ((SyntaxKind (Bit descTableNextIdSz)), secondary_desc_id_7)), (Var
    ((SyntaxKind (Bit morphTableNextIdSz)), morph_next_id_v)))))), (UniBool
    (NegB, (ReadIndex (descIdxSz, Bool, (Var ((SyntaxKind (Bit descIdxSz)),
    secondary_desc_id)), (Var ((SyntaxKind (Vector (Bool, morphTableIdxSz))),
    morph_valid_table_v)))))))))), (fun secondary_morph_desc_invalid -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (UniBool (NegB, (BinBitBool
    (descTableNextIdSz, descTableNextIdSz, (Lt descTableNextIdSz), (Var
    ((SyntaxKind (Bit descTableNextIdSz)), primary_desc_id_7)), (Var
    ((SyntaxKind (Bit descTableNextIdSz)), coupling_desc_next_id_v)))))),
    (UniBool (NegB, (ReadIndex (descIdxSz, Bool, (Var ((SyntaxKind (Bit
    descIdxSz)), primary_desc_id)), (Var ((SyntaxKind (Vector (Bool,
    couplingDescIdxSz))), coupling_desc_valid_table_v)))))))),
    (fun primary_coupling_desc_invalid -> Let_ ((SyntaxKind Bool), (BinBool
    (AndB, (Var ((SyntaxKind Bool), secondary_desc_present)), (BinBool (OrB,
    (UniBool (NegB, (BinBitBool (descTableNextIdSz, descTableNextIdSz, (Lt
    descTableNextIdSz), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    secondary_desc_id_7)), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    coupling_desc_next_id_v)))))), (UniBool (NegB, (ReadIndex (descIdxSz,
    Bool, (Var ((SyntaxKind (Bit descIdxSz)), secondary_desc_id)), (Var
    ((SyntaxKind (Vector (Bool, couplingDescIdxSz))),
    coupling_desc_valid_table_v)))))))))),
    (fun secondary_coupling_desc_invalid -> Let_ ((SyntaxKind Bool), (BinBool
    (OrB, (UniBool (NegB, (BinBitBool (descTableNextIdSz, descTableNextIdSz,
    (Lt descTableNextIdSz), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    primary_desc_id_7)), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    formula_desc_next_id_v)))))), (UniBool (NegB, (ReadIndex (descIdxSz,
    Bool, (Var ((SyntaxKind (Bit descIdxSz)), primary_desc_id)), (Var
    ((SyntaxKind (Vector (Bool, formulaDescIdxSz))),
    formula_desc_valid_table_v)))))))), (fun primary_formula_desc_invalid ->
    Let_ ((SyntaxKind Bool), (BinBool (AndB, (Var ((SyntaxKind Bool),
    secondary_desc_present)), (BinBool (OrB, (UniBool (NegB, (BinBitBool
    (descTableNextIdSz, descTableNextIdSz, (Lt descTableNextIdSz), (Var
    ((SyntaxKind (Bit descTableNextIdSz)), secondary_desc_id_7)), (Var
    ((SyntaxKind (Bit descTableNextIdSz)), formula_desc_next_id_v)))))),
    (UniBool (NegB, (ReadIndex (descIdxSz, Bool, (Var ((SyntaxKind (Bit
    descIdxSz)), secondary_desc_id)), (Var ((SyntaxKind (Vector (Bool,
    formulaDescIdxSz))), formula_desc_valid_table_v)))))))))),
    (fun secondary_formula_desc_invalid -> Let_ ((SyntaxKind Bool), (BinBool
    (OrB, (UniBool (NegB, (BinBitBool (descTableNextIdSz, descTableNextIdSz,
    (Lt descTableNextIdSz), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    primary_desc_id_7)), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    cert_desc_next_id_v)))))), (UniBool (NegB, (ReadIndex (descIdxSz, Bool,
    (Var ((SyntaxKind (Bit descIdxSz)), primary_desc_id)), (Var ((SyntaxKind
    (Vector (Bool, certDescIdxSz))), cert_desc_valid_table_v)))))))),
    (fun primary_cert_desc_invalid -> Let_ ((SyntaxKind Bool), (BinBool
    (AndB, (Var ((SyntaxKind Bool), secondary_desc_present)), (BinBool (OrB,
    (UniBool (NegB, (BinBitBool (descTableNextIdSz, descTableNextIdSz, (Lt
    descTableNextIdSz), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    secondary_desc_id_7)), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    cert_desc_next_id_v)))))), (UniBool (NegB, (ReadIndex (descIdxSz, Bool,
    (Var ((SyntaxKind (Bit descIdxSz)), secondary_desc_id)), (Var
    ((SyntaxKind (Vector (Bool, certDescIdxSz))),
    cert_desc_valid_table_v)))))))))), (fun secondary_cert_desc_invalid ->
    Let_ ((SyntaxKind Bool), (BinBool (OrB, (UniBool (NegB, (BinBitBool
    (descTableNextIdSz, descTableNextIdSz, (Lt descTableNextIdSz), (Var
    ((SyntaxKind (Bit descTableNextIdSz)), primary_desc_id_7)), (Var
    ((SyntaxKind (Bit descTableNextIdSz)), desc_meta_next_id_v)))))),
    (UniBool (NegB, (ReadIndex (descIdxSz, Bool, (Var ((SyntaxKind (Bit
    descIdxSz)), primary_desc_id)), (Var ((SyntaxKind (Vector (Bool,
    descMetaIdxSz))), desc_meta_valid_table_v)))))))),
    (fun primary_meta_desc_invalid -> Let_ ((SyntaxKind Bool), (BinBool
    (AndB, (Var ((SyntaxKind Bool), secondary_desc_present)), (BinBool (OrB,
    (UniBool (NegB, (BinBitBool (descTableNextIdSz, descTableNextIdSz, (Lt
    descTableNextIdSz), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    secondary_desc_id_7)), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    desc_meta_next_id_v)))))), (UniBool (NegB, (ReadIndex (descIdxSz, Bool,
    (Var ((SyntaxKind (Bit descIdxSz)), secondary_desc_id)), (Var
    ((SyntaxKind (Vector (Bool, descMetaIdxSz))),
    desc_meta_valid_table_v)))))))))), (fun secondary_meta_desc_invalid ->
    Let_ ((SyntaxKind Bool), (BinBool (AndB, (Eq ((Bit formatIdSz), (Var
    ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit formatIdSz),
    (ConstBit (formatIdSz, fMT_DESC)))))), (BinBool (AndB, (BinBool (OrB,
    (BinBool (OrB, (Var ((SyntaxKind Bool), desc_kind_is_morph)), (Var
    ((SyntaxKind Bool), desc_kind_is_coupling)))), (Var ((SyntaxKind Bool),
    desc_kind_is_meta)))), (BinBool (OrB, (BinBool (OrB, (BinBool (AndB, (Var
    ((SyntaxKind Bool), desc_kind_is_morph)), (BinBool (OrB, (Var
    ((SyntaxKind Bool), primary_morph_desc_invalid)), (Var ((SyntaxKind
    Bool), secondary_morph_desc_invalid)))))), (BinBool (AndB, (Var
    ((SyntaxKind Bool), desc_kind_is_coupling)), (BinBool (OrB, (Var
    ((SyntaxKind Bool), primary_coupling_desc_invalid)), (Var ((SyntaxKind
    Bool), secondary_coupling_desc_invalid)))))))), (BinBool (AndB, (Var
    ((SyntaxKind Bool), desc_kind_is_meta)), (BinBool (OrB, (Var ((SyntaxKind
    Bool), primary_meta_desc_invalid)), (Var ((SyntaxKind Bool),
    secondary_meta_desc_invalid)))))))))))), (fun generic_desc_range_fault ->
    Let_ ((SyntaxKind Bool), (BinBool (AndB, (BinBool (AndB, (Eq ((Bit
    formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)), format_id)), (Const
    ((Bit formatIdSz), (ConstBit (formatIdSz, fMT_DESC)))))), (Var
    ((SyntaxKind Bool), is_cert_opcode)))), (UniBool (NegB, (BinBool (OrB,
    (Var ((SyntaxKind Bool), desc_kind_is_formula)), (Var ((SyntaxKind Bool),
    desc_kind_is_cert)))))))), (fun cert_desc_kind_mismatch -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (BinBool (AndB, (Eq ((Bit
    formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)), format_id)), (Const
    ((Bit formatIdSz), (ConstBit (formatIdSz, fMT_DESC)))))), (Var
    ((SyntaxKind Bool), is_morph_opcode)))), (UniBool (NegB, (BinBool (OrB,
    (BinBool (OrB, (Var ((SyntaxKind Bool), desc_kind_is_morph)), (Var
    ((SyntaxKind Bool), desc_kind_is_coupling)))), (Var ((SyntaxKind Bool),
    desc_kind_is_meta)))))))), (fun morph_desc_kind_mismatch -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (Eq ((Bit formatIdSz), (Var
    ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit formatIdSz),
    (ConstBit (formatIdSz, fMT_DESC)))))), (BinBool (OrB, (BinBool (OrB, (Var
    ((SyntaxKind Bool), cert_desc_kind_mismatch)), (BinBool (AndB, (Var
    ((SyntaxKind Bool), desc_kind_is_formula)), (BinBool (OrB, (Var
    ((SyntaxKind Bool), primary_formula_desc_invalid)), (Var ((SyntaxKind
    Bool), secondary_formula_desc_invalid)))))))), (BinBool (AndB, (Var
    ((SyntaxKind Bool), desc_kind_is_cert)), (BinBool (OrB, (Var ((SyntaxKind
    Bool), primary_cert_desc_invalid)), (Var ((SyntaxKind Bool),
    secondary_cert_desc_invalid)))))))))), (fun cert_desc_invalid -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_MORPH)))))), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_COMPOSE)))))))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_MORPH_ID)))))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MORPH_TENSOR)))))))), (fun morph_alloc_opcode -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (BinBool (AndB, (Var ((SyntaxKind
    Bool), morph_alloc_opcode)), (UniBool (NegB, (BinBitBool
    (morphTableNextIdSz, morphTableNextIdSz, (Lt morphTableNextIdSz), (Var
    ((SyntaxKind (Bit morphTableNextIdSz)), morph_next_id_v)), (Const ((Bit
    morphTableNextIdSz), (ConstBit (morphTableNextIdSz,
    (natToWord morphTableNextIdSz (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (BinBool (AndB, (BinBool (AndB, (BinBool (OrB, (Eq ((Bit formatIdSz),
    (Var ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit
    formatIdSz), (ConstBit (formatIdSz, fMT_MORPH_INLINE)))))), (Eq ((Bit
    formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)), format_id)), (Const
    ((Bit formatIdSz), (ConstBit (formatIdSz, fMT_DESC)))))))), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_MORPH)))))))), (BinBool (OrB, (UniBool
    (NegB, (BinBitBool (descTableNextIdSz, descTableNextIdSz, (Lt
    descTableNextIdSz), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    coupling_desc_next_id_v)), (Const ((Bit descTableNextIdSz), (ConstBit
    (descTableNextIdSz,
    (natToWord descTableNextIdSz (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (UniBool (NegB, (BinBitBool (descTableNextIdSz, descTableNextIdSz, (Lt
    descTableNextIdSz), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    coupling_pair_next_id_v)), (Const ((Bit descTableNextIdSz), (ConstBit
    (descTableNextIdSz,
    (natToWord descTableNextIdSz (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun rich_table_overflow -> Let_ ((SyntaxKind Bool),
    (let e1 = Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), isa_version)
     in
     let e2 = Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))), (ConstBit ((Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS
       (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0)))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (false,
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
       (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))))))
     in
     UniBool (NegB, (Eq ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
     (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
     (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), e1, e2)))),
    (fun isa_version_invalid -> Let_ ((SyntaxKind Bool), (BinBool (OrB,
    (BinBool (OrB, (UniBool (NegB, (Var ((SyntaxKind Bool), format_known)))),
    (UniBool (NegB, (Var ((SyntaxKind Bool), format_allowed_for_opcode)))))),
    (Var ((SyntaxKind Bool), morph_desc_kind_mismatch)))),
    (fun format_invalid -> Let_ ((SyntaxKind Bool), (BinBool (OrB, (BinBool
    (OrB, (Var ((SyntaxKind Bool), reserved_flag_fault)), (Var ((SyntaxKind
    Bool), inline_payload_fault)))), (Var ((SyntaxKind Bool),
    desc_flag_fault)))), (fun inline_malformed -> Let_ ((SyntaxKind Bool),
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (Var ((SyntaxKind Bool), isa_version_invalid)), (Var ((SyntaxKind
    Bool), format_invalid)))), (Var ((SyntaxKind Bool), inline_malformed)))),
    (Var ((SyntaxKind Bool), generic_desc_range_fault)))), (Var ((SyntaxKind
    Bool), rich_table_overflow)))), (Var ((SyntaxKind Bool),
    cert_desc_invalid)))), (fun rich_fault -> Let_ ((SyntaxKind (Bit
    wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    isa_version_invalid)), (Const ((Bit wordSz), (ConstBit (wordSz,
    eRR_ISA_VERSION)))), (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind
    Bool), format_invalid)), (Const ((Bit wordSz), (ConstBit (wordSz,
    eRR_FORMAT_INVALID)))), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), inline_malformed)), (Const ((Bit wordSz), (ConstBit
    (wordSz, eRR_INLINE_MALFORMED)))), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), generic_desc_range_fault)), (Const ((Bit wordSz),
    (ConstBit (wordSz, eRR_DESC_RANGE)))), (ITE ((SyntaxKind (Bit wordSz)),
    (Var ((SyntaxKind Bool), rich_table_overflow)), (Const ((Bit wordSz),
    (ConstBit (wordSz, eRR_TABLE_OVERFLOW)))), (ITE ((SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind Bool), cert_desc_invalid)), (Const ((Bit
    wordSz), (ConstBit (wordSz, eRR_CERT_DESC_INVALID)))), (Var ((SyntaxKind
    (Bit wordSz)), error_code_v)))))))))))))), (fun rich_fault_error_code ->
    Let_ ((SyntaxKind (Bit wordSz)), (UniBit (costSz, wordSz,
    (ZeroExtendTrunc (costSz, wordSz)), (Var ((SyntaxKind (Bit costSz)),
    cost_v)))), (fun cost32 -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ 0))),
    (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ 0))))) (Stdlib.Int.succ 0))
       (Stdlib.Int.succ (Stdlib.Int.succ 0))), (Stdlib.Int.succ 0),
    (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (Stdlib.Int.succ 0),
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), op_a)))), (fun lassert_kind_bit -> Let_ ((SyntaxKind Bool),
    (Eq ((Bit (Stdlib.Int.succ 0)), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    0))), lassert_kind_bit)), (Const ((Bit (Stdlib.Int.succ 0)), (ConstBit
    ((Stdlib.Int.succ 0), (WS (true, 0, WO)))))))), (fun lassert_is_sat ->
    Let_ ((SyntaxKind Bool), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_LASSERT)))))), (fun is_lassert -> Let_ ((SyntaxKind Bool), (BinBool
    (AndB, (Var ((SyntaxKind Bool), is_lassert)), (UniBool (NegB, (Var
    ((SyntaxKind Bool), lassert_is_sat)))))), (fun lassert_unsat_trap -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), mu_v)), (Var ((SyntaxKind (Bit
    wordSz)), cost32)))), (fun new_mu -> Let_ ((SyntaxKind (Bit wordSz)),
    (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit
    wordSz)), pc_v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (fun pc_plus_1 -> Let_
    ((SyntaxKind (Bit regIdxSz)), (UniBit
    ((add regIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    regIdxSz, (Trunc (regIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_a)))),
    (fun dst_idx -> Let_ ((SyntaxKind (Bit regIdxSz)), (UniBit
    ((add regIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    regIdxSz, (Trunc (regIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_b)))),
    (fun src_idx -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ 0)))) (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ 0))))) 0), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (ConstExtract
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), 0)), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_b)))),
    (fun op_b_hi -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (UniBit
    ((add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0)))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))), (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Trunc ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_b)))), (fun op_b_lo ->
    Let_ ((SyntaxKind (Bit regIdxSz)), (UniBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), regIdxSz,
    (ZeroExtendTrunc ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), regIdxSz)), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), op_b_hi)))), (fun rs1_idx -> Let_ ((SyntaxKind (Bit regIdxSz)),
    (UniBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), regIdxSz, (ZeroExtendTrunc ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), regIdxSz)),
    (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), op_b_lo)))), (fun rs2_idx -> Let_ ((SyntaxKind
    (Bit wordSz)), (ReadIndex (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit
    regIdxSz)), rs1_idx)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)))), (fun rs1_val -> Let_ ((SyntaxKind (Bit wordSz)),
    (ReadIndex (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit regIdxSz)),
    rs2_idx)), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))),
    regs_v)))), (fun rs2_val -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex
    (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)),
    (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)))),
    (fun dst_val -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex (regIdxSz,
    (Bit wordSz), (Var ((SyntaxKind (Bit regIdxSz)), src_idx)), (Var
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)))),
    (fun src_val -> Let_ ((SyntaxKind (Bit wordSz)), (UniBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), wordSz, (ZeroExtendTrunc ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), wordSz)), (Var ((SyntaxKind
    (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), op_b)))), (fun imm32 -> Let_ ((SyntaxKind (Bit memAddrSz)),
    (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))), memAddrSz, (Trunc (memAddrSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), src_val)))),
    (fun mem_addr -> Let_ ((SyntaxKind (Bit memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))), memAddrSz, (Trunc (memAddrSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), dst_val)))),
    (fun mem_addr_a -> Let_ ((SyntaxKind (Bit memAddrSz)), (UniBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), memAddrSz, (ZeroExtendTrunc ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), memAddrSz)), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_b)))), (fun mem_addr_imm -> Let_
    ((SyntaxKind (Bit wordSz)),
    (read_mem (Var ((SyntaxKind (Bit memAddrSz)), mem_addr)) (Var
      ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), mem_v))),
    (fun mem_val -> Let_ ((SyntaxKind (Bit wordSz)),
    (read_mem (Var ((SyntaxKind (Bit memAddrSz)), mem_addr_imm)) (Var
      ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), mem_v))),
    (fun mem_val_imm -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex
    (regIdxSz, (Bit wordSz), (Const ((Bit regIdxSz), (ConstBit (regIdxSz,
    sP_IDX)))), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))),
    regs_v)))), (fun sp_val -> Let_ ((SyntaxKind (Bit memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))), memAddrSz, (Trunc (memAddrSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), sp_val)))),
    (fun sp_addr -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz,
    wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), sp_val)), (Const
    ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (fun sp_inc -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Sub
    wordSz), (Var ((SyntaxKind (Bit wordSz)), sp_val)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))),
    (fun sp_dec -> Let_ ((SyntaxKind (Bit memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))), memAddrSz, (Trunc (memAddrSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), sp_dec)))),
    (fun sp_dec_addr -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex
    (pTableIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit pTableIdxSz)),
    active_module_v)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), pt_sizes_v)))), (fun active_region_size -> Let_
    ((SyntaxKind Bool),
    (check_bounds (Var ((SyntaxKind (Bit memAddrSz)), mem_addr)) (Var
      ((SyntaxKind (Bit wordSz)), active_region_size))),
    (fun load_in_bounds -> Let_ ((SyntaxKind Bool),
    (check_bounds (Var ((SyntaxKind (Bit memAddrSz)), mem_addr_a)) (Var
      ((SyntaxKind (Bit wordSz)), active_region_size))),
    (fun store_in_bounds -> Let_ ((SyntaxKind Bool),
    (check_bounds (Var ((SyntaxKind (Bit memAddrSz)), sp_addr)) (Var
      ((SyntaxKind (Bit wordSz)), active_region_size))),
    (fun call_in_bounds -> Let_ ((SyntaxKind Bool),
    (check_bounds (Var ((SyntaxKind (Bit memAddrSz)), sp_dec_addr)) (Var
      ((SyntaxKind (Bit wordSz)), active_region_size))),
    (fun ret_in_bounds -> Let_ ((SyntaxKind Bool), (BinBool (OrB, (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_LOAD)))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_HEAP_LOAD)))))))), (fun is_load_op -> Let_ ((SyntaxKind
    Bool), (BinBool (OrB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_STORE)))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_HEAP_STORE)))))))), (fun is_store_op -> Let_ ((SyntaxKind Bool), (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_CALL)))))), (fun is_call_op ->
    Let_ ((SyntaxKind Bool), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_RET)))))), (fun is_ret_op -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (Var ((SyntaxKind Bool), is_load_op)), (UniBool (NegB, (Var ((SyntaxKind
    Bool), load_in_bounds)))))), (fun load_locality_bad -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (Var ((SyntaxKind Bool), is_store_op)), (UniBool
    (NegB, (Var ((SyntaxKind Bool), store_in_bounds)))))),
    (fun store_locality_bad -> Let_ ((SyntaxKind Bool), (BinBool (AndB, (Var
    ((SyntaxKind Bool), is_call_op)), (UniBool (NegB, (Var ((SyntaxKind
    Bool), call_in_bounds)))))), (fun call_locality_bad -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (Var ((SyntaxKind Bool), is_ret_op)), (UniBool
    (NegB, (Var ((SyntaxKind Bool), ret_in_bounds)))))),
    (fun ret_locality_bad -> Let_ ((SyntaxKind Bool), (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool), load_locality_bad)), (Var
    ((SyntaxKind Bool), store_locality_bad)))), (Var ((SyntaxKind Bool),
    call_locality_bad)))), (Var ((SyntaxKind Bool), ret_locality_bad)))),
    (fun locality_violation -> Let_ ((SyntaxKind Bool), (Eq ((Bit wordSz),
    (Var ((SyntaxKind (Bit wordSz)), logic_acc_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, lOGIC_GATE_KEY)))))), (fun logic_key_ok -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (BinBool (OrB, (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_REVEAL)))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_PDISCOVER)))))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind
    (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_CHSH_TRIAL)))))))), (fun is_high_value_op -> Let_ ((SyntaxKind Bool),
    (BinBool (AndB, (Var ((SyntaxKind Bool), is_high_value_op)), (UniBool
    (NegB, (Var ((SyntaxKind Bool), logic_key_ok)))))),
    (fun high_value_locked -> Let_ ((SyntaxKind Bool), (UniBool (NegB,
    (BinBitBool (pTableNextIdSz, pTableNextIdSz, (Lt pTableNextIdSz), (Var
    ((SyntaxKind (Bit pTableNextIdSz)), pt_next_id_v)), (Const ((Bit
    pTableNextIdSz), (ConstBit (pTableNextIdSz,
    (natToWord pTableNextIdSz (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun ptable_full -> Let_ ((SyntaxKind Bool), (UniBool (NegB, (Var
    ((SyntaxKind Bool), ptable_full)))), (fun ptable_room_one -> Let_
    ((SyntaxKind Bool), (UniBool (NegB, (BinBitBool (pTableNextIdSz,
    pTableNextIdSz, (Lt pTableNextIdSz), (Const ((Bit pTableNextIdSz),
    (ConstBit (pTableNextIdSz,
    (natToWord pTableNextIdSz (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (BinBit (pTableNextIdSz, pTableNextIdSz, pTableNextIdSz, (Add
    pTableNextIdSz), (Var ((SyntaxKind (Bit pTableNextIdSz)), pt_next_id_v)),
    (Const ((Bit pTableNextIdSz), (ConstBit (pTableNextIdSz,
    (natToWord pTableNextIdSz (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))),
    (fun ptable_room_two -> Let_ ((SyntaxKind Bool), (BinBool (AndB, (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_PNEW)))))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), ptable_room_one)))))), (fun pnew_overflow -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_PSPLIT)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    ptable_room_two)))))), (fun psplit_overflow -> Let_ ((SyntaxKind Bool),
    (BinBool (AndB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_PMERGE)))))),
    (UniBool (NegB, (Var ((SyntaxKind Bool), ptable_room_one)))))),
    (fun pmerge_overflow -> Let_ ((SyntaxKind Bool), (BinBool (OrB, (BinBool
    (OrB, (Var ((SyntaxKind Bool), pnew_overflow)), (Var ((SyntaxKind Bool),
    psplit_overflow)))), (Var ((SyntaxKind Bool), pmerge_overflow)))),
    (fun ptable_overflow_violation -> Let_ ((SyntaxKind (Bit pTableIdxSz)),
    (UniBit ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    pTableIdxSz, (Trunc (pTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_b)))),
    (fun pt_probe_idx -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex
    (pTableIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit pTableIdxSz)),
    pt_probe_idx)), (Var ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))),
    pt_sizes_v)))), (fun pt_probe_size -> Let_ ((SyntaxKind (Bit wordSz)),
    (UniBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), wordSz, (ZeroExtendTrunc ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), wordSz)),
    (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_b)))), (fun jnez_target -> Let_
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))), (BinBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))),
    (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))))) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))), (Concat ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_a)), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), op_b)))), (fun jump_target_16 -> Let_ ((SyntaxKind (Bit
    wordSz)), (UniBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))), wordSz, (ZeroExtendTrunc
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), wordSz)), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    jump_target_16)))), (fun jump_target -> Let_ ((SyntaxKind (Bit wordSz)),
    (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    ret_in_bounds)),
    (read_mem (Var ((SyntaxKind (Bit memAddrSz)), sp_dec_addr)) (Var
      ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), mem_v))), (Const
    ((Bit wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))))),
    (fun ret_pc -> Let_ ((SyntaxKind Bool), (Eq ((Bit formatIdSz), (Var
    ((SyntaxKind (Bit formatIdSz)), format_id)), (Const ((Bit formatIdSz),
    (ConstBit (formatIdSz, fMT_MORPH_INLINE)))))), (fun is_morph_inline ->
    Let_ ((SyntaxKind Bool), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MORPH)))))), (Var ((SyntaxKind Bool), is_morph_inline)))),
    (fun is_morph_ext -> Let_ ((SyntaxKind Bool), (BinBool (AndB, (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_COMPOSE)))))), (Var ((SyntaxKind
    Bool), is_morph_inline)))), (fun is_compose_ext -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_MORPH_ID)))))), (Var ((SyntaxKind Bool), is_morph_inline)))),
    (fun is_morph_id_ext -> Let_ ((SyntaxKind Bool), (BinBool (AndB, (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_MORPH_DELETE)))))), (Var
    ((SyntaxKind Bool), is_morph_inline)))), (fun is_morph_delete_ext -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MORPH_GET)))))), (Var ((SyntaxKind Bool),
    is_morph_inline)))), (fun is_morph_get_ext -> Let_ ((SyntaxKind Bool),
    (BinBool (AndB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_MORPH_ASSERT)))))), (Eq ((Bit formatIdSz), (Var ((SyntaxKind (Bit
    formatIdSz)), format_id)), (Const ((Bit formatIdSz), (ConstBit
    (formatIdSz, fMT_CERT_INLINE)))))))), (fun is_morph_assert_ext -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MORPH)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    is_morph_inline)))))), (fun is_morph_legacy -> Let_ ((SyntaxKind Bool),
    (BinBool (AndB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_COMPOSE)))))),
    (UniBool (NegB, (Var ((SyntaxKind Bool), is_morph_inline)))))),
    (fun is_compose_legacy -> Let_ ((SyntaxKind Bool), (BinBool (AndB, (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_MORPH_ID)))))), (UniBool (NegB,
    (Var ((SyntaxKind Bool), is_morph_inline)))))),
    (fun is_morph_id_legacy -> Let_ ((SyntaxKind Bool), (BinBool (AndB, (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_MORPH_DELETE)))))), (UniBool
    (NegB, (Var ((SyntaxKind Bool), is_morph_inline)))))),
    (fun is_morph_delete_legacy -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_MORPH_GET)))))), (UniBool (NegB,
    (Var ((SyntaxKind Bool), is_morph_inline)))))),
    (fun is_morph_get_legacy -> Let_ ((SyntaxKind Bool), (BinBool (AndB, (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_MORPH_ASSERT)))))), (UniBool
    (NegB, (Eq ((Bit formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)),
    format_id)), (Const ((Bit formatIdSz), (ConstBit (formatIdSz,
    fMT_CERT_INLINE)))))))))), (fun is_morph_assert_legacy -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MORPH_TENSOR)))))), (Var ((SyntaxKind Bool),
    is_morph_inline)))), (fun is_morph_tensor_inline -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_MORPH_TENSOR)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    is_morph_inline)))))), (fun _ -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_MORPH_TENSOR)))))),
    (fun is_morph_tensor -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))), pTableIdxSz, (Trunc (pTableIdxSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), ext0)))), (fun ext_morph_dst_mod -> Let_
    ((SyntaxKind (Bit descIdxSz)), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))
         descIdxSz) (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))), descIdxSz, (ConstExtract
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), descIdxSz, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), ext0)))),
    (fun ext_coupling_desc -> Let_ ((SyntaxKind (Bit morphTableIdxSz)),
    (UniBit
    ((add morphTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))), morphTableIdxSz, (Trunc
    (morphTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), ext0)))),
    (fun ext_compose_m2 -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (UniBit
    ((add (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))))))))), (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (Trunc ((Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), ext0)))), (fun ext_get_selector -> Let_
    ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)), ext0)),
    (fun ext_assert_property_checksum -> Let_ ((SyntaxKind (Bit
    pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))), pTableIdxSz,
    (Trunc (pTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_b)))), (fun morph_src_mod_idx -> Let_
    ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))), pTableIdxSz,
    (Trunc (pTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_b)))), (fun morph_identity_mod_idx ->
    Let_ ((SyntaxKind (Bit morphTableIdxSz)), (UniBit
    ((add morphTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    morphTableIdxSz, (Trunc (morphTableIdxSz, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_b)))),
    (fun morph_lookup_idx -> Let_ ((SyntaxKind (Bit morphTableIdxSz)),
    (UniBit ((add morphTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    morphTableIdxSz, (Trunc (morphTableIdxSz, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_a)))),
    (fun morph_delete_idx -> Let_ ((SyntaxKind (Bit morphTableIdxSz)),
    (UniBit ((add morphTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    morphTableIdxSz, (Trunc (morphTableIdxSz, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_a)))),
    (fun morph_assert_idx -> Let_ ((SyntaxKind (Bit morphTableIdxSz)),
    (UniBit ((add morphTableIdxSz (Stdlib.Int.succ 0)), morphTableIdxSz,
    (Trunc (morphTableIdxSz, (Stdlib.Int.succ 0))), (Var ((SyntaxKind (Bit
    morphTableNextIdSz)), morph_next_id_v)))), (fun morph_slot -> Let_
    ((SyntaxKind (Bit wordSz)), (UniBit (morphTableIdxSz, wordSz,
    (ZeroExtendTrunc (morphTableIdxSz, wordSz)), (Var ((SyntaxKind (Bit
    morphTableIdxSz)), morph_slot)))), (fun morph_slot_word -> Let_
    ((SyntaxKind (Bit descTableNextIdSz)), (UniBit (descIdxSz,
    descTableNextIdSz, (ZeroExtendTrunc (descIdxSz, descTableNextIdSz)), (Var
    ((SyntaxKind (Bit descIdxSz)), ext_coupling_desc)))),
    (fun ext_coupling_desc_7 -> Let_ ((SyntaxKind (Bit morphTableNextIdSz)),
    (UniBit (morphTableIdxSz, morphTableNextIdSz, (ZeroExtendTrunc
    (morphTableIdxSz, morphTableNextIdSz)), (Var ((SyntaxKind (Bit
    morphTableIdxSz)), ext_compose_m2)))), (fun ext_compose_m2_7 -> Let_
    ((SyntaxKind (Bit morphTableNextIdSz)), (UniBit (morphTableIdxSz,
    morphTableNextIdSz, (ZeroExtendTrunc (morphTableIdxSz,
    morphTableNextIdSz)), (Var ((SyntaxKind (Bit morphTableIdxSz)),
    morph_lookup_idx)))), (fun morph_lookup_idx_7 -> Let_ ((SyntaxKind (Bit
    morphTableNextIdSz)), (UniBit (morphTableIdxSz, morphTableNextIdSz,
    (ZeroExtendTrunc (morphTableIdxSz, morphTableNextIdSz)), (Var
    ((SyntaxKind (Bit morphTableIdxSz)), morph_delete_idx)))),
    (fun morph_delete_idx_7 -> Let_ ((SyntaxKind (Bit morphTableNextIdSz)),
    (UniBit (morphTableIdxSz, morphTableNextIdSz, (ZeroExtendTrunc
    (morphTableIdxSz, morphTableNextIdSz)), (Var ((SyntaxKind (Bit
    morphTableIdxSz)), morph_assert_idx)))), (fun morph_assert_idx_7 -> Let_
    ((SyntaxKind Bool), (BinBitBool (morphTableNextIdSz, morphTableNextIdSz,
    (Lt morphTableNextIdSz), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    morph_next_id_v)), (Const ((Bit morphTableNextIdSz), (ConstBit
    (morphTableNextIdSz,
    (natToWord morphTableNextIdSz (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun morph_alloc_room -> Let_ ((SyntaxKind Bool),
    (let e1 = ReadIndex (pTableIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit
       pTableIdxSz)), morph_src_mod_idx)), (Var ((SyntaxKind (Vector ((Bit
       wordSz), pTableIdxSz))), pt_sizes_v)))
     in
     let e2 = Const ((Bit wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))
     in
     UniBool (NegB, (Eq ((Bit wordSz), e1, e2)))),
    (fun morph_src_mod_exists -> Let_ ((SyntaxKind Bool),
    (let e1 = ReadIndex (pTableIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit
       pTableIdxSz)), ext_morph_dst_mod)), (Var ((SyntaxKind (Vector ((Bit
       wordSz), pTableIdxSz))), pt_sizes_v)))
     in
     let e2 = Const ((Bit wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))
     in
     UniBool (NegB, (Eq ((Bit wordSz), e1, e2)))),
    (fun morph_dst_mod_exists -> Let_ ((SyntaxKind Bool),
    (let e1 = ReadIndex (pTableIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit
       pTableIdxSz)), morph_identity_mod_idx)), (Var ((SyntaxKind (Vector
       ((Bit wordSz), pTableIdxSz))), pt_sizes_v)))
     in
     let e2 = Const ((Bit wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))
     in
     UniBool (NegB, (Eq ((Bit wordSz), e1, e2)))),
    (fun morph_identity_mod_exists -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    descIdxSz), (Var ((SyntaxKind (Bit descIdxSz)), ext_coupling_desc)),
    (Const ((Bit descIdxSz), (ConstBit (descIdxSz,
    (natToWord descIdxSz 0))))))), (fun inline_coupling_zero -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (BinBitBool (descTableNextIdSz,
    descTableNextIdSz, (Lt descTableNextIdSz), (Var ((SyntaxKind (Bit
    descTableNextIdSz)), ext_coupling_desc_7)), (Var ((SyntaxKind (Bit
    descTableNextIdSz)), coupling_desc_next_id_v)))), (ReadIndex (descIdxSz,
    Bool, (Var ((SyntaxKind (Bit descIdxSz)), ext_coupling_desc)), (Var
    ((SyntaxKind (Vector (Bool, couplingDescIdxSz))),
    coupling_desc_valid_table_v)))))), (fun inline_coupling_valid -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (Var ((SyntaxKind Bool),
    inline_coupling_zero)), (Var ((SyntaxKind Bool),
    inline_coupling_valid)))), (fun inline_coupling_ok -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (BinBitBool (morphTableNextIdSz,
    morphTableNextIdSz, (Lt morphTableNextIdSz), (Var ((SyntaxKind (Bit
    morphTableNextIdSz)), morph_lookup_idx_7)), (Var ((SyntaxKind (Bit
    morphTableNextIdSz)), morph_next_id_v)))), (ReadIndex (morphTableIdxSz,
    Bool, (Var ((SyntaxKind (Bit morphTableIdxSz)), morph_lookup_idx)), (Var
    ((SyntaxKind (Vector (Bool, morphTableIdxSz))),
    morph_valid_table_v)))))), (fun compose_m1_valid -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (BinBitBool (morphTableNextIdSz,
    morphTableNextIdSz, (Lt morphTableNextIdSz), (Var ((SyntaxKind (Bit
    morphTableNextIdSz)), ext_compose_m2_7)), (Var ((SyntaxKind (Bit
    morphTableNextIdSz)), morph_next_id_v)))), (ReadIndex (morphTableIdxSz,
    Bool, (Var ((SyntaxKind (Bit morphTableIdxSz)), ext_compose_m2)), (Var
    ((SyntaxKind (Vector (Bool, morphTableIdxSz))),
    morph_valid_table_v)))))), (fun compose_m2_valid -> Let_ ((SyntaxKind
    (Bit pTableIdxSz)), (ReadIndex (morphTableIdxSz, (Bit pTableIdxSz), (Var
    ((SyntaxKind (Bit morphTableIdxSz)), morph_lookup_idx)), (Var
    ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    morph_src_table_v)))), (fun compose_m1_src -> Let_ ((SyntaxKind (Bit
    pTableIdxSz)), (ReadIndex (morphTableIdxSz, (Bit pTableIdxSz), (Var
    ((SyntaxKind (Bit morphTableIdxSz)), morph_lookup_idx)), (Var
    ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    morph_dst_table_v)))), (fun compose_m1_dst -> Let_ ((SyntaxKind (Bit
    pTableIdxSz)), (ReadIndex (morphTableIdxSz, (Bit pTableIdxSz), (Var
    ((SyntaxKind (Bit morphTableIdxSz)), ext_compose_m2)), (Var ((SyntaxKind
    (Vector ((Bit pTableIdxSz), morphTableIdxSz))), morph_src_table_v)))),
    (fun compose_m2_src -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (ReadIndex
    (morphTableIdxSz, (Bit pTableIdxSz), (Var ((SyntaxKind (Bit
    morphTableIdxSz)), ext_compose_m2)), (Var ((SyntaxKind (Vector ((Bit
    pTableIdxSz), morphTableIdxSz))), morph_dst_table_v)))),
    (fun compose_m2_dst -> Let_ ((SyntaxKind Bool), (Eq ((Bit pTableIdxSz),
    (Var ((SyntaxKind (Bit pTableIdxSz)), compose_m1_dst)), (Var ((SyntaxKind
    (Bit pTableIdxSz)), compose_m2_src)))), (fun compose_endpoints_match ->
    Let_ ((SyntaxKind (Bit morphTableIdxSz)), (Const ((Bit morphTableIdxSz),
    (ConstBit (morphTableIdxSz, (natToWord morphTableIdxSz 0))))),
    (fun morph_zero_idx -> Let_ ((SyntaxKind (Bit morphTableNextIdSz)),
    (Const ((Bit morphTableNextIdSz), (ConstBit (morphTableNextIdSz,
    (natToWord morphTableNextIdSz 0))))), (fun morph_zero_idx_7 -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (BinBitBool (morphTableNextIdSz,
    morphTableNextIdSz, (Lt morphTableNextIdSz), (Var ((SyntaxKind (Bit
    morphTableNextIdSz)), morph_zero_idx_7)), (Var ((SyntaxKind (Bit
    morphTableNextIdSz)), morph_next_id_v)))), (ReadIndex (morphTableIdxSz,
    Bool, (Var ((SyntaxKind (Bit morphTableIdxSz)), morph_zero_idx)), (Var
    ((SyntaxKind (Vector (Bool, morphTableIdxSz))),
    morph_valid_table_v)))))), (fun legacy_compose_m2_valid -> Let_
    ((SyntaxKind (Bit pTableIdxSz)), (ReadIndex (morphTableIdxSz, (Bit
    pTableIdxSz), (Var ((SyntaxKind (Bit morphTableIdxSz)), morph_zero_idx)),
    (Var ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    morph_src_table_v)))), (fun legacy_compose_m2_src -> Let_ ((SyntaxKind
    (Bit pTableIdxSz)), (ReadIndex (morphTableIdxSz, (Bit pTableIdxSz), (Var
    ((SyntaxKind (Bit morphTableIdxSz)), morph_zero_idx)), (Var ((SyntaxKind
    (Vector ((Bit pTableIdxSz), morphTableIdxSz))), morph_dst_table_v)))),
    (fun legacy_compose_m2_dst -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    pTableIdxSz), (Var ((SyntaxKind (Bit pTableIdxSz)), compose_m1_dst)),
    (Var ((SyntaxKind (Bit pTableIdxSz)), legacy_compose_m2_src)))),
    (fun legacy_compose_endpoints_match -> Let_ ((SyntaxKind (Bit
    morphTableIdxSz)), (ITE ((SyntaxKind (Bit morphTableIdxSz)), (Var
    ((SyntaxKind Bool), is_morph_tensor_inline)), (Var ((SyntaxKind (Bit
    morphTableIdxSz)), ext_compose_m2)), (Const ((Bit morphTableIdxSz),
    (ConstBit (morphTableIdxSz, (natToWord morphTableIdxSz 0))))))),
    (fun morph_tensor_g_id -> Let_ ((SyntaxKind (Bit morphTableNextIdSz)),
    (ITE ((SyntaxKind (Bit morphTableNextIdSz)), (Var ((SyntaxKind Bool),
    is_morph_tensor_inline)), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    ext_compose_m2_7)), (Const ((Bit morphTableNextIdSz), (ConstBit
    (morphTableNextIdSz, (natToWord morphTableNextIdSz 0))))))),
    (fun morph_tensor_g_id_7 -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (BinBitBool (morphTableNextIdSz, morphTableNextIdSz, (Lt
    morphTableNextIdSz), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    morph_tensor_g_id_7)), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    morph_next_id_v)))), (ReadIndex (morphTableIdxSz, Bool, (Var ((SyntaxKind
    (Bit morphTableIdxSz)), morph_tensor_g_id)), (Var ((SyntaxKind (Vector
    (Bool, morphTableIdxSz))), morph_valid_table_v)))))),
    (fun morph_tensor_g_valid -> Let_ ((SyntaxKind (Bit pTableIdxSz)),
    (ReadIndex (morphTableIdxSz, (Bit pTableIdxSz), (Var ((SyntaxKind (Bit
    morphTableIdxSz)), morph_tensor_g_id)), (Var ((SyntaxKind (Vector ((Bit
    pTableIdxSz), morphTableIdxSz))), morph_dst_table_v)))),
    (fun morph_tensor_g_dst -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (BinBitBool (morphTableNextIdSz, morphTableNextIdSz, (Lt
    morphTableNextIdSz), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    morph_lookup_idx_7)), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    morph_next_id_v)))), (ReadIndex (morphTableIdxSz, Bool, (Var ((SyntaxKind
    (Bit morphTableIdxSz)), morph_lookup_idx)), (Var ((SyntaxKind (Vector
    (Bool, morphTableIdxSz))), morph_valid_table_v)))))),
    (fun morph_lookup_valid -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (BinBitBool (morphTableNextIdSz, morphTableNextIdSz, (Lt
    morphTableNextIdSz), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    morph_delete_idx_7)), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    morph_next_id_v)))), (ReadIndex (morphTableIdxSz, Bool, (Var ((SyntaxKind
    (Bit morphTableIdxSz)), morph_delete_idx)), (Var ((SyntaxKind (Vector
    (Bool, morphTableIdxSz))), morph_valid_table_v)))))),
    (fun morph_delete_valid -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (BinBitBool (morphTableNextIdSz, morphTableNextIdSz, (Lt
    morphTableNextIdSz), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    morph_assert_idx_7)), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    morph_next_id_v)))), (ReadIndex (morphTableIdxSz, Bool, (Var ((SyntaxKind
    (Bit morphTableIdxSz)), morph_assert_idx)), (Var ((SyntaxKind (Vector
    (Bool, morphTableIdxSz))), morph_valid_table_v)))))),
    (fun morph_assert_valid -> Let_ ((SyntaxKind (Bit pTableIdxSz)),
    (ReadIndex (morphTableIdxSz, (Bit pTableIdxSz), (Var ((SyntaxKind (Bit
    morphTableIdxSz)), morph_lookup_idx)), (Var ((SyntaxKind (Vector ((Bit
    pTableIdxSz), morphTableIdxSz))), morph_src_table_v)))),
    (fun morph_get_src -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (ReadIndex
    (morphTableIdxSz, (Bit pTableIdxSz), (Var ((SyntaxKind (Bit
    morphTableIdxSz)), morph_lookup_idx)), (Var ((SyntaxKind (Vector ((Bit
    pTableIdxSz), morphTableIdxSz))), morph_dst_table_v)))),
    (fun morph_get_dst -> Let_ ((SyntaxKind Bool), (ReadIndex
    (morphTableIdxSz, Bool, (Var ((SyntaxKind (Bit morphTableIdxSz)),
    morph_lookup_idx)), (Var ((SyntaxKind (Vector (Bool, morphTableIdxSz))),
    morph_identity_table_v)))), (fun morph_get_is_identity -> Let_
    ((SyntaxKind (Bit descIdxSz)), (ReadIndex (morphTableIdxSz, (Bit
    descIdxSz), (Var ((SyntaxKind (Bit morphTableIdxSz)), morph_lookup_idx)),
    (Var ((SyntaxKind (Vector ((Bit descIdxSz), morphTableIdxSz))),
    morph_coupling_desc_table_v)))), (fun morph_get_coupling_desc -> Let_
    ((SyntaxKind (Bit descTableNextIdSz)), (UniBit (descIdxSz,
    descTableNextIdSz, (ZeroExtendTrunc (descIdxSz, descTableNextIdSz)), (Var
    ((SyntaxKind (Bit descIdxSz)), morph_get_coupling_desc)))),
    (fun morph_get_coupling_desc_7 -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    descIdxSz), (Var ((SyntaxKind (Bit descIdxSz)),
    morph_get_coupling_desc)), (Const ((Bit descIdxSz), (ConstBit (descIdxSz,
    (natToWord descIdxSz 0))))))), (fun morph_get_coupling_zero -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (BinBitBool (descTableNextIdSz,
    descTableNextIdSz, (Lt descTableNextIdSz), (Var ((SyntaxKind (Bit
    descTableNextIdSz)), morph_get_coupling_desc_7)), (Var ((SyntaxKind (Bit
    descTableNextIdSz)), coupling_desc_next_id_v)))), (ReadIndex (descIdxSz,
    Bool, (Var ((SyntaxKind (Bit descIdxSz)), morph_get_coupling_desc)), (Var
    ((SyntaxKind (Vector (Bool, couplingDescIdxSz))),
    coupling_desc_valid_table_v)))))), (fun morph_get_coupling_valid -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (BinBool (AndB, (BinBool (AndB, (Var
    ((SyntaxKind Bool), is_morph_get_ext)), (Var ((SyntaxKind Bool),
    morph_lookup_valid)))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    morph_get_coupling_zero)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    morph_get_coupling_valid)))))), (fun morph_get_coupling_fault -> Let_
    ((SyntaxKind (Bit couplingPairCountSz)), (ITE ((SyntaxKind (Bit
    couplingPairCountSz)), (Var ((SyntaxKind Bool),
    morph_get_coupling_zero)), (Const ((Bit couplingPairCountSz), (ConstBit
    (couplingPairCountSz, (natToWord couplingPairCountSz 0))))), (ReadIndex
    (descIdxSz, (Bit couplingPairCountSz), (Var ((SyntaxKind (Bit
    descIdxSz)), morph_get_coupling_desc)), (Var ((SyntaxKind (Vector ((Bit
    couplingPairCountSz), couplingDescIdxSz))),
    coupling_desc_count_table_v)))))), (fun morph_get_coupling_count_raw ->
    Let_ ((SyntaxKind (Bit wordSz)), (UniBit (pTableIdxSz, wordSz,
    (ZeroExtendTrunc (pTableIdxSz, wordSz)), (Var ((SyntaxKind (Bit
    pTableIdxSz)), morph_get_src)))), (fun morph_get_src_word -> Let_
    ((SyntaxKind (Bit wordSz)), (UniBit (pTableIdxSz, wordSz,
    (ZeroExtendTrunc (pTableIdxSz, wordSz)), (Var ((SyntaxKind (Bit
    pTableIdxSz)), morph_get_dst)))), (fun morph_get_dst_word -> Let_
    ((SyntaxKind (Bit wordSz)), (UniBit (couplingPairCountSz, wordSz,
    (ZeroExtendTrunc (couplingPairCountSz, wordSz)), (Var ((SyntaxKind (Bit
    couplingPairCountSz)), morph_get_coupling_count_raw)))),
    (fun morph_get_coupling_count -> Let_ ((SyntaxKind (Bit wordSz)), (ITE
    ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    morph_get_is_identity)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz 0))))))),
    (fun morph_get_identity_word -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (ITE ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Var ((SyntaxKind Bool), is_morph_get_ext)), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    ext_get_selector)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (natToWord (Stdlib.Int.succ (Stdlib.Int.succ 0)) 0))))))),
    (fun effective_get_selector -> Let_ ((SyntaxKind (Bit wordSz)), (ITE
    ((SyntaxKind (Bit wordSz)), (Eq ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    effective_get_selector)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))), (Var ((SyntaxKind (Bit
    wordSz)), morph_get_src_word)), (ITE ((SyntaxKind (Bit wordSz)), (Eq
    ((Bit (Stdlib.Int.succ (Stdlib.Int.succ 0))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), effective_get_selector)), (Const
    ((Bit (Stdlib.Int.succ (Stdlib.Int.succ 0))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))), (Var ((SyntaxKind (Bit wordSz)), morph_get_dst_word)), (ITE
    ((SyntaxKind (Bit wordSz)), (Eq ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    effective_get_selector)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))), (Var ((SyntaxKind (Bit
    wordSz)), morph_get_coupling_count)), (Var ((SyntaxKind (Bit wordSz)),
    morph_get_identity_word)))))))), (fun morph_get_value -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (BinBool (AndB, (Var ((SyntaxKind
    Bool), is_morph_ext)), (BinBool (OrB, (BinBool (OrB, (UniBool (NegB, (Var
    ((SyntaxKind Bool), morph_src_mod_exists)))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), morph_dst_mod_exists)))))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), inline_coupling_ok)))))))), (BinBool (AndB, (Var
    ((SyntaxKind Bool), is_morph_id_ext)), (UniBool (NegB, (Var ((SyntaxKind
    Bool), morph_identity_mod_exists)))))))),
    (fun morph_ext_endpoint_fault -> Let_ ((SyntaxKind Bool), (BinBool (OrB,
    (BinBool (AndB, (Var ((SyntaxKind Bool), is_morph_legacy)), (UniBool
    (NegB, (Var ((SyntaxKind Bool), morph_src_mod_exists)))))), (BinBool
    (AndB, (Var ((SyntaxKind Bool), is_morph_id_legacy)), (UniBool (NegB,
    (Var ((SyntaxKind Bool), morph_identity_mod_exists)))))))),
    (fun morph_legacy_endpoint_fault -> Let_ ((SyntaxKind Bool), (BinBool
    (OrB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_compose_ext)), (BinBool
    (OrB, (UniBool (NegB, (Var ((SyntaxKind Bool), compose_m1_valid)))),
    (UniBool (NegB, (Var ((SyntaxKind Bool), compose_m2_valid)))))))),
    (BinBool (AndB, (Var ((SyntaxKind Bool), is_compose_legacy)), (BinBool
    (OrB, (UniBool (NegB, (Var ((SyntaxKind Bool), compose_m1_valid)))),
    (UniBool (NegB, (Var ((SyntaxKind Bool),
    legacy_compose_m2_valid)))))))))), (fun compose_lookup_fault -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (BinBool (AndB, (BinBool (AndB,
    (BinBool (AndB, (Var ((SyntaxKind Bool), is_compose_ext)), (Var
    ((SyntaxKind Bool), compose_m1_valid)))), (Var ((SyntaxKind Bool),
    compose_m2_valid)))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    compose_endpoints_match)))))), (BinBool (AndB, (BinBool (AndB, (BinBool
    (AndB, (Var ((SyntaxKind Bool), is_compose_legacy)), (Var ((SyntaxKind
    Bool), compose_m1_valid)))), (Var ((SyntaxKind Bool),
    legacy_compose_m2_valid)))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    legacy_compose_endpoints_match)))))))), (fun compose_type_fault -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (BinBool (OrB, (Var ((SyntaxKind
    Bool), is_morph_delete_ext)), (Var ((SyntaxKind Bool),
    is_morph_delete_legacy)))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    morph_delete_valid)))))), (fun morph_delete_fault -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (BinBool (OrB, (Var ((SyntaxKind Bool),
    is_morph_get_ext)), (Var ((SyntaxKind Bool), is_morph_get_legacy)))),
    (UniBool (NegB, (Var ((SyntaxKind Bool), morph_lookup_valid)))))),
    (fun morph_get_fault -> Let_ ((SyntaxKind Bool), (BinBool (AndB, (BinBool
    (OrB, (Var ((SyntaxKind Bool), is_morph_assert_ext)), (Var ((SyntaxKind
    Bool), is_morph_assert_legacy)))), (UniBool (NegB, (Var ((SyntaxKind
    Bool), morph_assert_valid)))))), (fun morph_assert_fault -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (Var ((SyntaxKind Bool),
    is_morph_tensor)), (UniBool (NegB, (Var ((SyntaxKind Bool),
    compose_m1_valid)))))), (fun morph_tensor_lookup_fault -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (BinBool (AndB, (Var ((SyntaxKind
    Bool), is_morph_tensor)), (Var ((SyntaxKind Bool), compose_m1_valid)))),
    (UniBool (NegB, (Var ((SyntaxKind Bool), morph_tensor_g_valid)))))),
    (fun morph_tensor_g_fault -> Let_ ((SyntaxKind Bool), (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var ((SyntaxKind
    Bool), morph_ext_endpoint_fault)), (Var ((SyntaxKind Bool),
    morph_legacy_endpoint_fault)))), (Var ((SyntaxKind Bool),
    compose_lookup_fault)))), (Var ((SyntaxKind Bool),
    compose_type_fault)))), (Var ((SyntaxKind Bool), morph_delete_fault)))),
    (Var ((SyntaxKind Bool), morph_get_fault)))), (Var ((SyntaxKind Bool),
    morph_get_coupling_fault)))), (Var ((SyntaxKind Bool),
    morph_assert_fault)))), (Var ((SyntaxKind Bool),
    morph_tensor_lookup_fault)))), (Var ((SyntaxKind Bool),
    morph_tensor_g_fault)))), (fun morph_runtime_fault -> Let_ ((SyntaxKind
    (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    compose_type_fault)), (Const ((Bit wordSz), (ConstBit (wordSz,
    eRR_COMPOSE_TYPE)))), (ITE ((SyntaxKind (Bit wordSz)), (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var
    ((SyntaxKind Bool), compose_lookup_fault)), (Var ((SyntaxKind Bool),
    morph_delete_fault)))), (Var ((SyntaxKind Bool), morph_get_fault)))),
    (Var ((SyntaxKind Bool), morph_assert_fault)))), (Var ((SyntaxKind Bool),
    morph_tensor_lookup_fault)))), (Var ((SyntaxKind Bool),
    morph_tensor_g_fault)))), (Const ((Bit wordSz), (ConstBit (wordSz,
    eRR_MORPH_NOT_FOUND)))), (Const ((Bit wordSz), (ConstBit (wordSz,
    eRR_COUPLING_INVALID)))))))), (fun morph_runtime_error_code -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (BinBool (AndB, (BinBool (AndB,
    (BinBool (AndB, (Var ((SyntaxKind Bool), is_morph_ext)), (Var
    ((SyntaxKind Bool), morph_alloc_room)))), (Var ((SyntaxKind Bool),
    morph_src_mod_exists)))), (Var ((SyntaxKind Bool),
    morph_dst_mod_exists)))), (Var ((SyntaxKind Bool),
    inline_coupling_ok)))), (fun morph_alloc_success -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool),
    is_morph_legacy)), (Var ((SyntaxKind Bool), morph_alloc_room)))), (Var
    ((SyntaxKind Bool), morph_src_mod_exists)))),
    (fun legacy_morph_alloc_success -> Let_ ((SyntaxKind Bool), (BinBool
    (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_morph_id_ext)), (Var
    ((SyntaxKind Bool), morph_alloc_room)))), (Var ((SyntaxKind Bool),
    morph_identity_mod_exists)))), (fun morph_id_success -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool),
    is_morph_id_legacy)), (Var ((SyntaxKind Bool), morph_alloc_room)))), (Var
    ((SyntaxKind Bool), morph_identity_mod_exists)))),
    (fun morph_id_legacy_success -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (BinBool (AndB, (BinBool (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool),
    is_compose_ext)), (Var ((SyntaxKind Bool), morph_alloc_room)))), (Var
    ((SyntaxKind Bool), compose_m1_valid)))), (Var ((SyntaxKind Bool),
    compose_m2_valid)))), (Var ((SyntaxKind Bool),
    compose_endpoints_match)))), (fun compose_success -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (BinBool (AndB, (BinBool (AndB, (BinBool (AndB,
    (Var ((SyntaxKind Bool), is_compose_legacy)), (Var ((SyntaxKind Bool),
    morph_alloc_room)))), (Var ((SyntaxKind Bool), compose_m1_valid)))), (Var
    ((SyntaxKind Bool), legacy_compose_m2_valid)))), (Var ((SyntaxKind Bool),
    legacy_compose_endpoints_match)))), (fun legacy_compose_success -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (BinBool (AndB, (BinBool (AndB, (Var
    ((SyntaxKind Bool), is_morph_tensor)), (Var ((SyntaxKind Bool),
    morph_alloc_room)))), (Var ((SyntaxKind Bool), compose_m1_valid)))), (Var
    ((SyntaxKind Bool), morph_tensor_g_valid)))),
    (fun morph_tensor_success -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (BinBool (AndB, (BinBool (OrB, (Var ((SyntaxKind Bool),
    is_morph_get_ext)), (Var ((SyntaxKind Bool), is_morph_get_legacy)))),
    (Var ((SyntaxKind Bool), morph_lookup_valid)))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), morph_get_coupling_fault)))))),
    (fun morph_get_success -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (BinBool (OrB, (Var ((SyntaxKind Bool), is_morph_delete_ext)), (Var
    ((SyntaxKind Bool), is_morph_delete_legacy)))), (Var ((SyntaxKind Bool),
    morph_delete_valid)))), (fun morph_delete_success -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (BinBool (OrB, (Var ((SyntaxKind Bool),
    is_morph_assert_ext)), (Var ((SyntaxKind Bool),
    is_morph_assert_legacy)))), (Var ((SyntaxKind Bool),
    morph_assert_valid)))), (fun morph_assert_success -> Let_ ((SyntaxKind
    Bool), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool),
    morph_alloc_success)), (Var ((SyntaxKind Bool),
    legacy_morph_alloc_success)))), (Var ((SyntaxKind Bool),
    morph_id_success)))), (Var ((SyntaxKind Bool),
    morph_id_legacy_success)))), (Var ((SyntaxKind Bool),
    compose_success)))), (Var ((SyntaxKind Bool), legacy_compose_success)))),
    (Var ((SyntaxKind Bool), morph_tensor_success)))),
    (fun morph_allocates -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (ITE
    ((SyntaxKind (Bit pTableIdxSz)), (Var ((SyntaxKind Bool),
    morph_alloc_success)), (Var ((SyntaxKind (Bit pTableIdxSz)),
    morph_src_mod_idx)), (ITE ((SyntaxKind (Bit pTableIdxSz)), (Var
    ((SyntaxKind Bool), legacy_morph_alloc_success)), (Var ((SyntaxKind (Bit
    pTableIdxSz)), morph_src_mod_idx)), (ITE ((SyntaxKind (Bit pTableIdxSz)),
    (BinBool (OrB, (Var ((SyntaxKind Bool), morph_id_success)), (Var
    ((SyntaxKind Bool), morph_id_legacy_success)))), (Var ((SyntaxKind (Bit
    pTableIdxSz)), morph_identity_mod_idx)), (ITE ((SyntaxKind (Bit
    pTableIdxSz)), (Var ((SyntaxKind Bool), compose_success)), (Var
    ((SyntaxKind (Bit pTableIdxSz)), compose_m1_src)), (ITE ((SyntaxKind (Bit
    pTableIdxSz)), (Var ((SyntaxKind Bool), legacy_compose_success)), (Var
    ((SyntaxKind (Bit pTableIdxSz)), compose_m1_src)), (ITE ((SyntaxKind (Bit
    pTableIdxSz)), (Var ((SyntaxKind Bool), morph_tensor_success)), (Var
    ((SyntaxKind (Bit pTableIdxSz)), compose_m1_src)), (Var ((SyntaxKind (Bit
    pTableIdxSz)), morph_identity_mod_idx)))))))))))))),
    (fun morph_alloc_src -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (ITE
    ((SyntaxKind (Bit pTableIdxSz)), (Var ((SyntaxKind Bool),
    morph_alloc_success)), (Var ((SyntaxKind (Bit pTableIdxSz)),
    ext_morph_dst_mod)), (ITE ((SyntaxKind (Bit pTableIdxSz)), (Var
    ((SyntaxKind Bool), legacy_morph_alloc_success)), (Var ((SyntaxKind (Bit
    pTableIdxSz)), morph_src_mod_idx)), (ITE ((SyntaxKind (Bit pTableIdxSz)),
    (BinBool (OrB, (Var ((SyntaxKind Bool), morph_id_success)), (Var
    ((SyntaxKind Bool), morph_id_legacy_success)))), (Var ((SyntaxKind (Bit
    pTableIdxSz)), morph_identity_mod_idx)), (ITE ((SyntaxKind (Bit
    pTableIdxSz)), (Var ((SyntaxKind Bool), compose_success)), (Var
    ((SyntaxKind (Bit pTableIdxSz)), compose_m2_dst)), (ITE ((SyntaxKind (Bit
    pTableIdxSz)), (Var ((SyntaxKind Bool), legacy_compose_success)), (Var
    ((SyntaxKind (Bit pTableIdxSz)), legacy_compose_m2_dst)), (ITE
    ((SyntaxKind (Bit pTableIdxSz)), (Var ((SyntaxKind Bool),
    morph_tensor_success)), (Var ((SyntaxKind (Bit pTableIdxSz)),
    morph_tensor_g_dst)), (Var ((SyntaxKind (Bit pTableIdxSz)),
    morph_identity_mod_idx)))))))))))))), (fun morph_alloc_dst -> Let_
    ((SyntaxKind (Bit descIdxSz)), (ITE ((SyntaxKind (Bit descIdxSz)), (Var
    ((SyntaxKind Bool), morph_alloc_success)), (Var ((SyntaxKind (Bit
    descIdxSz)), ext_coupling_desc)), (Const ((Bit descIdxSz), (ConstBit
    (descIdxSz, (natToWord descIdxSz 0))))))), (fun morph_alloc_coupling ->
    Let_ ((SyntaxKind Bool), (BinBool (OrB, (Var ((SyntaxKind Bool),
    morph_id_success)), (Var ((SyntaxKind Bool), morph_id_legacy_success)))),
    (fun morph_alloc_identity -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)),
    rs1_val)), (Var ((SyntaxKind (Bit wordSz)), rs2_val)))),
    (fun add_result -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Sub wordSz), (Var ((SyntaxKind (Bit wordSz)), rs1_val)),
    (Var ((SyntaxKind (Bit wordSz)), rs2_val)))), (fun sub_result -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Band
    wordSz), (Var ((SyntaxKind (Bit wordSz)), rs1_val)), (Var ((SyntaxKind
    (Bit wordSz)), rs2_val)))), (fun and_result -> Let_ ((SyntaxKind (Bit
    wordSz)), (BinBit (wordSz, wordSz, wordSz, (Bor wordSz), (Var
    ((SyntaxKind (Bit wordSz)), rs1_val)), (Var ((SyntaxKind (Bit wordSz)),
    rs2_val)))), (fun or_result -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit
    (wordSz, wordSz, wordSz, (Sll (wordSz, wordSz)), (Var ((SyntaxKind (Bit
    wordSz)), rs1_val)), (Var ((SyntaxKind (Bit wordSz)), rs2_val)))),
    (fun shl_result -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Srl (wordSz, wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    rs1_val)), (Var ((SyntaxKind (Bit wordSz)), rs2_val)))),
    (fun shr_result -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Mul (wordSz, SignUU)), (Var ((SyntaxKind (Bit wordSz)),
    rs1_val)), (Var ((SyntaxKind (Bit wordSz)), rs2_val)))),
    (fun mul_result -> Let_ ((SyntaxKind (Bit wordSz)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))), (fun lui_shift -> Let_ ((SyntaxKind
    (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Sll (wordSz, wordSz)),
    (Var ((SyntaxKind (Bit wordSz)), imm32)), (Var ((SyntaxKind (Bit
    wordSz)), lui_shift)))), (fun lui_result -> Let_ ((SyntaxKind (Bit
    wordSz)), (BinBit (wordSz, wordSz, wordSz, (Bxor wordSz), (Var
    ((SyntaxKind (Bit wordSz)), dst_val)), (Var ((SyntaxKind (Bit wordSz)),
    src_val)))), (fun xor_result -> Let_ ((SyntaxKind Bool),
    (let e1 = Var ((SyntaxKind (Bit wordSz)), dst_val) in
     let e2 = Const ((Bit wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))
     in
     UniBool (NegB, (Eq ((Bit wordSz), e1, e2)))), (fun jnez_taken -> Let_
    ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)), src_val)),
    (fun pop_val -> Let_ ((SyntaxKind (Bit wordSz)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun pop_mask1 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Band wordSz), (Var ((SyntaxKind (Bit wordSz)),
    pop_val)), (Var ((SyntaxKind (Bit wordSz)), pop_mask1)))),
    (fun pop_s1a -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz,
    wordSz, (Band wordSz), (BinBit (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), wordSz, (Srl (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (Var ((SyntaxKind (Bit wordSz)), pop_val)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), pop_mask1)))), (fun pop_s1b -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_s1a)), (Var ((SyntaxKind
    (Bit wordSz)), pop_s1b)))), (fun pop_2 -> Let_ ((SyntaxKind (Bit
    wordSz)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun pop_mask2 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Band wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_2)),
    (Var ((SyntaxKind (Bit wordSz)), pop_mask2)))), (fun pop_n1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Band
    wordSz), (BinBit (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), wordSz, (Srl (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (Var ((SyntaxKind (Bit wordSz)), pop_2)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), pop_mask2)))), (fun pop_n2 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_n1)), (Var ((SyntaxKind
    (Bit wordSz)), pop_n2)))), (fun pop_4 -> Let_ ((SyntaxKind (Bit wordSz)),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun pop_mask3 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Band wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_4)),
    (Var ((SyntaxKind (Bit wordSz)), pop_mask3)))), (fun pop_b1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Band
    wordSz), (BinBit (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), wordSz, (Srl (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (Var ((SyntaxKind (Bit wordSz)), pop_4)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), pop_mask3)))), (fun pop_b2 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_b1)), (Var ((SyntaxKind
    (Bit wordSz)), pop_b2)))), (fun pop_8 -> Let_ ((SyntaxKind (Bit wordSz)),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun pop_mask4 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Band wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_8)),
    (Var ((SyntaxKind (Bit wordSz)), pop_mask4)))), (fun pop_h1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Band
    wordSz), (BinBit (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), wordSz, (Srl (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (Var ((SyntaxKind (Bit wordSz)), pop_8)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), pop_mask4)))), (fun pop_h2 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_h1)), (Var ((SyntaxKind
    (Bit wordSz)), pop_h2)))), (fun pop_16 -> Let_ ((SyntaxKind (Bit
    wordSz)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun pop_mask5 -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Band wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_16)),
    (Var ((SyntaxKind (Bit wordSz)), pop_mask5)))), (fun pop_q1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Band
    wordSz), (BinBit (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), wordSz, (Srl (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (Var ((SyntaxKind (Bit wordSz)), pop_16)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), pop_mask5)))), (fun pop_q2 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), pop_q1)), (Var ((SyntaxKind
    (Bit wordSz)), pop_q2)))), (fun popcount -> Let_ ((SyntaxKind Bool),
    (BinBitBool ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Lt (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (Const
    ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))))))))))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), op_b)))), (fun _ -> Let_ ((SyntaxKind Bool), (BinBitBool
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), (Lt (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))))))))))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), op_a)))), (fun is_x1_trial -> Let_ ((SyntaxKind Bool),
    (BinBool (AndB, (Var ((SyntaxKind Bool), is_x1_trial)), (Eq ((Bit
    wordSz), (Var ((SyntaxKind (Bit wordSz)), tensor_total)), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))))))),
    (fun chsh_cert_missing -> Let_ ((SyntaxKind Bool), (Var ((SyntaxKind
    Bool), chsh_cert_missing)), (fun chsh_bits_bad -> Let_ ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (UniBit
    ((add (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))), (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (Trunc ((Stdlib.Int.succ (Stdlib.Int.succ 0)), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_a)))),
    (fun chsh_settings -> Let_ ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (UniBit
    ((add (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))), (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (Trunc ((Stdlib.Int.succ (Stdlib.Int.succ 0)), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_b)))),
    (fun chsh_outcomes -> Let_ ((SyntaxKind Bool), (BinBool (OrB, (Eq ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), chsh_outcomes)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))), (Eq ((Bit (Stdlib.Int.succ (Stdlib.Int.succ 0))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    chsh_outcomes)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ 0))),
    (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))),
    (fun chsh_outcomes_same -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), chsh_settings)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))), (fun is_bucket_00 -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), chsh_settings)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))), (fun is_bucket_01 -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), chsh_settings)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))), (fun is_bucket_10 -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), chsh_settings)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))), (fun is_bucket_11 -> Let_ ((SyntaxKind (Bit wordSz)),
    (UniBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), wordSz, (ZeroExtendTrunc ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), wordSz)),
    (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_b)))), (fun op_b_32 -> Let_ ((SyntaxKind
    Bool), (BinBool (OrB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_PDISCOVER)))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_EMIT)))))))), (fun is_info_gain_op -> Let_ ((SyntaxKind Bool),
    (BinBool (AndB, (Var ((SyntaxKind Bool), is_info_gain_op)), (BinBitBool
    (wordSz, wordSz, (Lt wordSz), (Var ((SyntaxKind (Bit wordSz)), cost32)),
    (Var ((SyntaxKind (Bit wordSz)), op_b_32)))))), (fun nfi_violation ->
    Let_ ((SyntaxKind Bool), (BinBool (AndB, (BinBool (AndB, (BinBool (AndB,
    (BinBool (AndB, (BinBool (AndB, (BinBool (AndB, (BinBool (AndB, (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_CHSH_TRIAL)))))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), chsh_bits_bad)))))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), bianchi_violation)))))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), locality_violation)))))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), ptable_overflow_violation)))))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), high_value_locked)))))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), nfi_violation)))))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), rich_fault)))))), (fun is_chsh_valid -> Let_
    ((SyntaxKind (Bit muTensorIdxSz)), (UniBit
    ((add muTensorIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))), muTensorIdxSz, (Trunc (muTensorIdxSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), op_a)))),
    (fun legacy_tensor_idx -> Let_ ((SyntaxKind (Bit muTensorIdxSz)), (UniBit
    ((add muTensorIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))))))))))))))), muTensorIdxSz, (Trunc
    (muTensorIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))))))))))))))))))), (Var ((SyntaxKind (Bit
    wordSz)), ext0)))), (fun ext_tensor_idx -> Let_ ((SyntaxKind (Bit
    muTensorIdxSz)), (ITE ((SyntaxKind (Bit muTensorIdxSz)), (BinBool (AndB,
    (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_REVEAL)))))), (Eq ((Bit
    formatIdSz), (Var ((SyntaxKind (Bit formatIdSz)), format_id)), (Const
    ((Bit formatIdSz), (ConstBit (formatIdSz, fMT_TENSOR_EXT)))))))), (Var
    ((SyntaxKind (Bit muTensorIdxSz)), ext_tensor_idx)), (Var ((SyntaxKind
    (Bit muTensorIdxSz)), legacy_tensor_idx)))), (fun tensor_idx -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex (muTensorIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Bit muTensorIdxSz)), tensor_idx)), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))),
    (fun tensor_old -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)),
    tensor_old)), (Var ((SyntaxKind (Bit wordSz)), cost32)))),
    (fun tensor_new_val -> Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind
    (Bit wordSz)), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool),
    bianchi_violation)), (Var ((SyntaxKind Bool), locality_violation)))),
    (Var ((SyntaxKind Bool), ptable_overflow_violation)))), (Var ((SyntaxKind
    Bool), high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))),
    (Var ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind (Bit wordSz)),
    trap_vector_v)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_HALT)))))), (Var ((SyntaxKind (Bit wordSz)),
    pc_v)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_JUMP)))))), (Var ((SyntaxKind (Bit wordSz)), jump_target)),
    (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit opcodeSz), (Var ((SyntaxKind
    (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_CALL)))))), (Var ((SyntaxKind (Bit wordSz)), jump_target)), (ITE
    ((SyntaxKind (Bit wordSz)), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_RET)))))), (Var ((SyntaxKind (Bit wordSz)), ret_pc)), (ITE
    ((SyntaxKind (Bit wordSz)), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_JNEZ)))))), (Var ((SyntaxKind Bool), jnez_taken)))), (Var
    ((SyntaxKind (Bit wordSz)), jnez_target)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_LASSERT)))))),
    (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    lassert_is_sat)), (Var ((SyntaxKind (Bit wordSz)), pc_v)), (Var
    ((SyntaxKind (Bit wordSz)), trap_vector_v)))), (Var ((SyntaxKind (Bit
    wordSz)), pc_plus_1)))))))))))))))), (fun new_pc -> Let_ ((SyntaxKind
    (Vector ((Bit wordSz), regIdxSz))), (UpdateVector (regIdxSz, (Bit
    wordSz), (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector
    ((Bit wordSz), regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)),
    dst_idx)), (Var ((SyntaxKind (Bit wordSz)), src_val)))), (Var
    ((SyntaxKind (Bit regIdxSz)), src_idx)), (Var ((SyntaxKind (Bit wordSz)),
    dst_val)))), (fun swap_regs -> Let_ ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (ITE ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Var
    ((SyntaxKind Bool), morph_allocates)), (UpdateVector (regIdxSz, (Bit
    wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)),
    (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit
    wordSz)), morph_slot_word)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Var ((SyntaxKind Bool), morph_get_success)), (UpdateVector
    (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var
    ((SyntaxKind (Bit wordSz)), morph_get_value)))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), regIdxSz))), regs_v)))))),
    (fun morph_result_regs -> Let_ ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (ITE ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))),
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool), bianchi_violation)), (Var
    ((SyntaxKind Bool), locality_violation)))), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_LOAD_IMM)))))),
    (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit
    wordSz), regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)),
    dst_idx)), (Var ((SyntaxKind (Bit wordSz)), imm32)))), (ITE ((SyntaxKind
    (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_ADD)))))), (UpdateVector (regIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var
    ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit wordSz)),
    add_result)))), (ITE ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_SUB)))))), (UpdateVector
    (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var
    ((SyntaxKind (Bit wordSz)), sub_result)))), (ITE ((SyntaxKind (Vector
    ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_XFER)))))), (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind
    (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit
    regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit wordSz)), src_val)))), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_LOAD)))))), (UpdateVector (regIdxSz, (Bit
    wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)),
    (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit
    wordSz)), mem_val)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_XOR_LOAD)))))),
    (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit
    wordSz), regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)),
    dst_idx)), (Var ((SyntaxKind (Bit wordSz)), mem_val_imm)))), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_XOR_ADD)))))), (UpdateVector (regIdxSz, (Bit
    wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)),
    (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit
    wordSz)), xor_result)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_XOR_SWAP)))))),
    (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), swap_regs)), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_XOR_RANK)))))), (UpdateVector (regIdxSz, (Bit
    wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)),
    (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit
    wordSz)), popcount)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_CALL)))))),
    (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit
    wordSz), regIdxSz))), regs_v)), (Const ((Bit regIdxSz), (ConstBit
    (regIdxSz, sP_IDX)))), (Var ((SyntaxKind (Bit wordSz)), sp_inc)))), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_RET)))))), (UpdateVector (regIdxSz, (Bit wordSz),
    (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Const
    ((Bit regIdxSz), (ConstBit (regIdxSz, sP_IDX)))), (Var ((SyntaxKind (Bit
    wordSz)), sp_dec)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_PDISCOVER)))))), (UpdateVector (regIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var
    ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit wordSz)),
    pt_probe_size)))), (ITE ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))),
    (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_HEAP_LOAD)))))), (UpdateVector
    (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var
    ((SyntaxKind (Bit wordSz)), mem_val)))), (ITE ((SyntaxKind (Vector ((Bit
    wordSz), regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_READ_PORT)))))), (UpdateVector (regIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var
    ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz 0))))))), (ITE ((SyntaxKind (Vector ((Bit
    wordSz), regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_AND)))))), (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind
    (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit
    regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit wordSz)), and_result)))),
    (ITE ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_OR)))))), (UpdateVector (regIdxSz,
    (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))),
    regs_v)), (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind
    (Bit wordSz)), or_result)))), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_SHL)))))),
    (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit
    wordSz), regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)),
    dst_idx)), (Var ((SyntaxKind (Bit wordSz)), shl_result)))), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_SHR)))))), (UpdateVector (regIdxSz, (Bit wordSz),
    (Var ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var
    ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit wordSz)),
    shr_result)))), (ITE ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_MUL)))))), (UpdateVector
    (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var
    ((SyntaxKind (Bit wordSz)), mul_result)))), (ITE ((SyntaxKind (Vector
    ((Bit wordSz), regIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_LUI)))))), (UpdateVector (regIdxSz, (Bit wordSz), (Var ((SyntaxKind
    (Vector ((Bit wordSz), regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit
    regIdxSz)), dst_idx)), (Var ((SyntaxKind (Bit wordSz)), lui_result)))),
    (ITE ((SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_TENSOR_GET)))))), (UpdateVector
    (regIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz),
    regIdxSz))), regs_v)), (Var ((SyntaxKind (Bit regIdxSz)), dst_idx)), (Var
    ((SyntaxKind (Bit wordSz)), tensor_old)))), (Var ((SyntaxKind (Vector
    ((Bit wordSz), regIdxSz))),
    morph_result_regs)))))))))))))))))))))))))))))))))))))))))))))),
    (fun new_regs -> Let_ ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))),
    (ITE ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (Var ((SyntaxKind Bool), bianchi_violation)), (Var ((SyntaxKind
    Bool), locality_violation)))), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    memAddrSz))), mem_v)), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    memAddrSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_STORE)))))),
    (write_mem (Var ((SyntaxKind (Bit memAddrSz)), mem_addr_a)) (Var
      ((SyntaxKind (Bit wordSz)), src_val)) (Var ((SyntaxKind (Vector ((Bit
      wordSz), memAddrSz))), mem_v))), (ITE ((SyntaxKind (Vector ((Bit
    wordSz), memAddrSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_CALL)))))),
    (write_mem (Var ((SyntaxKind (Bit memAddrSz)), sp_addr)) (Var
      ((SyntaxKind (Bit wordSz)), pc_plus_1)) (Var ((SyntaxKind (Vector ((Bit
      wordSz), memAddrSz))), mem_v))), (ITE ((SyntaxKind (Vector ((Bit
    wordSz), memAddrSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_HEAP_STORE)))))),
    (write_mem (Var ((SyntaxKind (Bit memAddrSz)), mem_addr_a)) (Var
      ((SyntaxKind (Bit wordSz)), src_val)) (Var ((SyntaxKind (Vector ((Bit
      wordSz), memAddrSz))), mem_v))), (Var ((SyntaxKind (Vector ((Bit
    wordSz), memAddrSz))), mem_v)))))))))), (fun new_mem -> Let_ ((SyntaxKind
    Bool), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var
    ((SyntaxKind Bool), locality_violation)), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_HALT)))))))), (fun new_halted ->
    Let_ ((SyntaxKind Bool), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var
    ((SyntaxKind Bool), locality_violation)), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_CHSH_TRIAL)))))), (Var ((SyntaxKind Bool),
    chsh_bits_bad)))))), (Var ((SyntaxKind Bool), lassert_unsat_trap)))),
    (fun new_err -> Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind Bool), bianchi_violation)), (Const ((Bit
    wordSz), (ConstBit (wordSz, eRR_BIANCHI_VAL)))), (ITE ((SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind Bool), locality_violation)), (Const ((Bit
    wordSz), (ConstBit (wordSz, eRR_LOCALITY_VAL)))), (ITE ((SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind Bool), ptable_overflow_violation)), (Const
    ((Bit wordSz), (ConstBit (wordSz, eRR_PARTITION_VAL)))), (ITE
    ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool), nfi_violation)),
    (Const ((Bit wordSz), (ConstBit (wordSz, eRR_LOGIC_VAL)))), (ITE
    ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool), rich_fault)), (Var
    ((SyntaxKind (Bit wordSz)), rich_fault_error_code)), (ITE ((SyntaxKind
    (Bit wordSz)), (Var ((SyntaxKind Bool), morph_runtime_fault)), (Var
    ((SyntaxKind (Bit wordSz)), morph_runtime_error_code)), (ITE ((SyntaxKind
    (Bit wordSz)), (Var ((SyntaxKind Bool), high_value_locked)), (Const ((Bit
    wordSz), (ConstBit (wordSz, eRR_LOGIC_VAL)))), (ITE ((SyntaxKind (Bit
    wordSz)), (BinBool (AndB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_CHSH_TRIAL)))))), (Var ((SyntaxKind Bool), chsh_bits_bad)))), (Const
    ((Bit wordSz), (ConstBit (wordSz, eRR_CHSH_VAL)))), (ITE ((SyntaxKind
    (Bit wordSz)), (Var ((SyntaxKind Bool), lassert_unsat_trap)), (Const
    ((Bit wordSz), (ConstBit (wordSz, eRR_LOGIC_VAL)))), (Var ((SyntaxKind
    (Bit wordSz)), error_code_v)))))))))))))))))))), (fun new_error_code ->
    Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_CERTIFY)))))), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), mu_v)), (Var ((SyntaxKind (Bit
    wordSz)), cost32)))), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_MORPH_ASSERT)))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit
    wordSz)), mu_v)), (Var ((SyntaxKind (Bit wordSz)), cost32)))), (Const
    ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_LASSERT)))))),
    (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit
    wordSz)), new_mu)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (ITE ((SyntaxKind (Bit
    wordSz)), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_EMIT)))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_REVEAL)))))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_LJOIN)))))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_READ_PORT)))))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), new_mu)), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var ((SyntaxKind
    (Bit wordSz)), new_mu)))))))))), (fun rich_fault_mu -> Let_ ((SyntaxKind
    (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_ORACLE_HALTS)))))), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), mu_v)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))))))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))))),
    (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))),
    (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))))))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (ITE ((SyntaxKind (Bit wordSz)), (BinBool (AndB, (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_CHSH_TRIAL)))))), (Var ((SyntaxKind Bool),
    is_x1_trial)))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), new_mu)), (Const ((Bit wordSz), (ConstBit
    (wordSz, cHSH_X1_SURCHARGE)))))), (ITE ((SyntaxKind (Bit wordSz)), (Eq
    ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const
    ((Bit opcodeSz), (ConstBit (opcodeSz, oP_CERTIFY)))))), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), mu_v)), (Var ((SyntaxKind (Bit
    wordSz)), cost32)))), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_MORPH_ASSERT)))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit
    wordSz)), mu_v)), (Var ((SyntaxKind (Bit wordSz)), cost32)))), (Const
    ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_LASSERT)))))),
    (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    lassert_is_sat)), (Var ((SyntaxKind (Bit wordSz)), mu_v)), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)),
    new_mu)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))))), (ITE ((SyntaxKind (Bit
    wordSz)), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_EMIT)))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_REVEAL)))))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_LJOIN)))))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_READ_PORT)))))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), new_mu)), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var ((SyntaxKind
    (Bit wordSz)), new_mu)))))))))))))), (fun normal_step_mu -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (OrB, (BinBool (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool),
    bianchi_violation)), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind (Bit wordSz)), mu_v)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), rich_fault)), (Var ((SyntaxKind (Bit wordSz)),
    rich_fault_mu)), (Var ((SyntaxKind (Bit wordSz)), normal_step_mu)))))),
    (fun final_mu -> Let_ ((SyntaxKind Bool), (ITE ((SyntaxKind Bool),
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool), bianchi_violation)), (Var
    ((SyntaxKind Bool), locality_violation)))), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind Bool), certified_v)), (ITE
    ((SyntaxKind Bool), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_CERTIFY)))))), (Const (Bool, (ConstBool true))), (Var ((SyntaxKind
    Bool), certified_v)))))), (fun new_certified -> Let_ ((SyntaxKind (Bit
    pTableIdxSz)), (UniBit ((add pTableIdxSz (Stdlib.Int.succ 0)),
    pTableIdxSz, (Trunc (pTableIdxSz, (Stdlib.Int.succ 0))), (Var
    ((SyntaxKind (Bit pTableNextIdSz)), pt_next_id_v)))), (fun pt_slot ->
    Let_ ((SyntaxKind (Bit wordSz)), (UniBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), wordSz,
    (ZeroExtendTrunc ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), wordSz)), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), op_a)))), (fun pnew_region_size -> Let_ ((SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), (UpdateVector (pTableIdxSz, (Bit wordSz),
    (Var ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), pt_sizes_v)),
    (Var ((SyntaxKind (Bit pTableIdxSz)), pt_slot)), (Var ((SyntaxKind (Bit
    wordSz)), pnew_region_size)))), (fun pt_after_pnew -> Let_ ((SyntaxKind
    (Bit pTableNextIdSz)), (BinBit (pTableNextIdSz, pTableNextIdSz,
    pTableNextIdSz, (Add pTableNextIdSz), (Var ((SyntaxKind (Bit
    pTableNextIdSz)), pt_next_id_v)), (Const ((Bit pTableNextIdSz), (ConstBit
    (pTableNextIdSz, (natToWord pTableNextIdSz (Stdlib.Int.succ 0)))))))),
    (fun next_after_pnew -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))), pTableIdxSz,
    (Trunc (pTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_a)))), (fun psplit_id -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex (pTableIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Bit pTableIdxSz)), psplit_id)), (Var ((SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), pt_sizes_v)))), (fun psplit_orig_sz ->
    Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), wordSz, (Srl (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (Var
    ((SyntaxKind (Bit wordSz)), psplit_orig_sz)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))),
    (fun psplit_left_sz -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz,
    wordSz, wordSz, (Sub wordSz), (Var ((SyntaxKind (Bit wordSz)),
    psplit_orig_sz)), (Var ((SyntaxKind (Bit wordSz)), psplit_left_sz)))),
    (fun psplit_right_sz -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ 0)), pTableIdxSz, (Trunc (pTableIdxSz,
    (Stdlib.Int.succ 0))), (Var ((SyntaxKind (Bit pTableNextIdSz)),
    pt_next_id_v)))), (fun psplit_slot1 -> Let_ ((SyntaxKind (Bit
    pTableIdxSz)), (UniBit ((add pTableIdxSz (Stdlib.Int.succ 0)),
    pTableIdxSz, (Trunc (pTableIdxSz, (Stdlib.Int.succ 0))), (BinBit
    (pTableNextIdSz, pTableNextIdSz, pTableNextIdSz, (Add pTableNextIdSz),
    (Var ((SyntaxKind (Bit pTableNextIdSz)), pt_next_id_v)), (Const ((Bit
    pTableNextIdSz), (ConstBit (pTableNextIdSz,
    (natToWord pTableNextIdSz (Stdlib.Int.succ 0)))))))))),
    (fun psplit_slot2 -> Let_ ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), (UpdateVector (pTableIdxSz, (Bit wordSz), (UpdateVector
    (pTableIdxSz, (Bit wordSz), (UpdateVector (pTableIdxSz, (Bit wordSz),
    (Var ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))), pt_sizes_v)),
    (Var ((SyntaxKind (Bit pTableIdxSz)), psplit_id)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz 0))))))), (Var ((SyntaxKind (Bit
    pTableIdxSz)), psplit_slot1)), (Var ((SyntaxKind (Bit wordSz)),
    psplit_left_sz)))), (Var ((SyntaxKind (Bit pTableIdxSz)), psplit_slot2)),
    (Var ((SyntaxKind (Bit wordSz)), psplit_right_sz)))),
    (fun pt_after_psplit -> Let_ ((SyntaxKind (Bit pTableNextIdSz)), (BinBit
    (pTableNextIdSz, pTableNextIdSz, pTableNextIdSz, (Add pTableNextIdSz),
    (Var ((SyntaxKind (Bit pTableNextIdSz)), pt_next_id_v)), (Const ((Bit
    pTableNextIdSz), (ConstBit (pTableNextIdSz,
    (natToWord pTableNextIdSz (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))),
    (fun next_after_psplit -> Let_ ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))), pTableIdxSz,
    (Trunc (pTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_a)))), (fun pmerge_m1 -> Let_
    ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ 0))), pTableIdxSz,
    (Trunc (pTableIdxSz, (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))))), op_b)))), (fun pmerge_m2 -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex (pTableIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Bit pTableIdxSz)), pmerge_m1)), (Var ((SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), pt_sizes_v)))), (fun pmerge_m1_sz -> Let_
    ((SyntaxKind (Bit wordSz)), (ReadIndex (pTableIdxSz, (Bit wordSz), (Var
    ((SyntaxKind (Bit pTableIdxSz)), pmerge_m2)), (Var ((SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), pt_sizes_v)))), (fun pmerge_m2_sz -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), pmerge_m1_sz)), (Var
    ((SyntaxKind (Bit wordSz)), pmerge_m2_sz)))), (fun pmerge_merged_sz ->
    Let_ ((SyntaxKind (Bit pTableIdxSz)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ 0)), pTableIdxSz, (Trunc (pTableIdxSz,
    (Stdlib.Int.succ 0))), (Var ((SyntaxKind (Bit pTableNextIdSz)),
    pt_next_id_v)))), (fun pmerge_slot -> Let_ ((SyntaxKind (Vector ((Bit
    wordSz), pTableIdxSz))), (UpdateVector (pTableIdxSz, (Bit wordSz),
    (UpdateVector (pTableIdxSz, (Bit wordSz), (UpdateVector (pTableIdxSz,
    (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))),
    pt_sizes_v)), (Var ((SyntaxKind (Bit pTableIdxSz)), pmerge_m1)), (Const
    ((Bit wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))))), (Var
    ((SyntaxKind (Bit pTableIdxSz)), pmerge_m2)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz 0))))))), (Var ((SyntaxKind (Bit
    pTableIdxSz)), pmerge_slot)), (Var ((SyntaxKind (Bit wordSz)),
    pmerge_merged_sz)))), (fun pt_after_pmerge -> Let_ ((SyntaxKind (Bit
    pTableNextIdSz)), (BinBit (pTableNextIdSz, pTableNextIdSz,
    pTableNextIdSz, (Add pTableNextIdSz), (Var ((SyntaxKind (Bit
    pTableNextIdSz)), pt_next_id_v)), (Const ((Bit pTableNextIdSz), (ConstBit
    (pTableNextIdSz, (natToWord pTableNextIdSz (Stdlib.Int.succ 0)))))))),
    (fun next_after_pmerge -> Let_ ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), (ITE ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))),
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool),
    bianchi_violation)), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool), rich_fault)))),
    (Var ((SyntaxKind Bool), morph_runtime_fault)))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), pTableIdxSz))), pt_sizes_v)), (ITE ((SyntaxKind
    (Vector ((Bit wordSz), pTableIdxSz))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_PNEW)))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), pt_after_pnew)), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_PSPLIT)))))),
    (Var ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))),
    pt_after_psplit)), (ITE ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_PMERGE)))))),
    (Var ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))),
    pt_after_pmerge)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), pt_sizes_v)))))))))), (fun new_pt_sizes -> Let_
    ((SyntaxKind (Bit pTableNextIdSz)), (ITE ((SyntaxKind (Bit
    pTableNextIdSz)), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var
    ((SyntaxKind Bool), bianchi_violation)), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool), rich_fault)))),
    (Var ((SyntaxKind Bool), morph_runtime_fault)))), (Var ((SyntaxKind (Bit
    pTableNextIdSz)), pt_next_id_v)), (ITE ((SyntaxKind (Bit
    pTableNextIdSz)), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)),
    opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_PNEW)))))),
    (Var ((SyntaxKind (Bit pTableNextIdSz)), next_after_pnew)), (ITE
    ((SyntaxKind (Bit pTableNextIdSz)), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_PSPLIT)))))), (Var ((SyntaxKind (Bit pTableNextIdSz)),
    next_after_psplit)), (ITE ((SyntaxKind (Bit pTableNextIdSz)), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_PMERGE)))))), (Var ((SyntaxKind (Bit
    pTableNextIdSz)), next_after_pmerge)), (Var ((SyntaxKind (Bit
    pTableNextIdSz)), pt_next_id_v)))))))))), (fun new_pt_next_id -> Let_
    ((SyntaxKind Bool), (BinBool (OrB, (BinBool (OrB, (Eq ((Bit opcodeSz),
    (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz),
    (ConstBit (opcodeSz, oP_PNEW)))))), (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_PSPLIT)))))))), (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit
    opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit (opcodeSz,
    oP_PMERGE)))))))), (fun is_partition_op -> Let_ ((SyntaxKind (Bit
    wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool (AndB, (BinBool
    (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_partition_op)),
    (UniBool (NegB, (Var ((SyntaxKind Bool), bianchi_violation)))))),
    (UniBool (NegB, (Var ((SyntaxKind Bool), rich_fault)))))), (UniBool
    (NegB, (Var ((SyntaxKind Bool), morph_runtime_fault)))))), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)),
    partition_ops_v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var ((SyntaxKind (Bit
    wordSz)), partition_ops_v)))), (fun new_partition_ops -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (AndB, (BinBool (AndB, (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_MDLACC)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    bianchi_violation)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    rich_fault)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    morph_runtime_fault)))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (Var ((SyntaxKind (Bit wordSz)), mdl_ops_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), mdl_ops_v)))), (fun new_mdl_ops -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (AndB, (BinBool (AndB, (BinBool (AndB, (BinBool (AndB, (BinBool (AndB,
    (BinBool (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool),
    is_info_gain_op)), (UniBool (NegB, (Var ((SyntaxKind Bool),
    bianchi_violation)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    locality_violation)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    high_value_locked)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    nfi_violation)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    rich_fault)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    morph_runtime_fault)))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (Var ((SyntaxKind (Bit wordSz)), info_gain_v)), (Var ((SyntaxKind (Bit
    wordSz)), op_b_32)))), (Var ((SyntaxKind (Bit wordSz)), info_gain_v)))),
    (fun new_info_gain -> Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind
    (Bit wordSz)), (BinBool (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool),
    is_chsh_valid)), (Var ((SyntaxKind Bool), is_bucket_00)))), (Var
    ((SyntaxKind Bool), chsh_outcomes_same)))), (BinBit (wordSz, wordSz,
    wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), wc_same_00_v)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var ((SyntaxKind (Bit
    wordSz)), wc_same_00_v)))), (fun new_wc_same_00 -> Let_ ((SyntaxKind (Bit
    wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool (AndB, (BinBool
    (AndB, (Var ((SyntaxKind Bool), is_chsh_valid)), (Var ((SyntaxKind Bool),
    is_bucket_00)))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    chsh_outcomes_same)))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (Var ((SyntaxKind (Bit wordSz)), wc_diff_00_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), wc_diff_00_v)))), (fun new_wc_diff_00 -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_chsh_valid)), (Var
    ((SyntaxKind Bool), is_bucket_01)))), (Var ((SyntaxKind Bool),
    chsh_outcomes_same)))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (Var ((SyntaxKind (Bit wordSz)), wc_same_01_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), wc_same_01_v)))), (fun new_wc_same_01 -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_chsh_valid)), (Var
    ((SyntaxKind Bool), is_bucket_01)))), (UniBool (NegB, (Var ((SyntaxKind
    Bool), chsh_outcomes_same)))))), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), wc_diff_01_v)), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))),
    (Var ((SyntaxKind (Bit wordSz)), wc_diff_01_v)))), (fun new_wc_diff_01 ->
    Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)),
    (BinBool (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_chsh_valid)),
    (Var ((SyntaxKind Bool), is_bucket_10)))), (Var ((SyntaxKind Bool),
    chsh_outcomes_same)))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (Var ((SyntaxKind (Bit wordSz)), wc_same_10_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), wc_same_10_v)))), (fun new_wc_same_10 -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_chsh_valid)), (Var
    ((SyntaxKind Bool), is_bucket_10)))), (UniBool (NegB, (Var ((SyntaxKind
    Bool), chsh_outcomes_same)))))), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), wc_diff_10_v)), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))),
    (Var ((SyntaxKind (Bit wordSz)), wc_diff_10_v)))), (fun new_wc_diff_10 ->
    Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)),
    (BinBool (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_chsh_valid)),
    (Var ((SyntaxKind Bool), is_bucket_11)))), (Var ((SyntaxKind Bool),
    chsh_outcomes_same)))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz),
    (Var ((SyntaxKind (Bit wordSz)), wc_same_11_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), wc_same_11_v)))), (fun new_wc_same_11 -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_chsh_valid)), (Var
    ((SyntaxKind Bool), is_bucket_11)))), (UniBool (NegB, (Var ((SyntaxKind
    Bool), chsh_outcomes_same)))))), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), wc_diff_11_v)), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))),
    (Var ((SyntaxKind (Bit wordSz)), wc_diff_11_v)))), (fun new_wc_diff_11 ->
    Let_ ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (ITE
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (BinBool (AndB,
    (BinBool (AndB, (BinBool (AndB, (BinBool (AndB, (Eq ((Bit opcodeSz), (Var
    ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit opcodeSz), (ConstBit
    (opcodeSz, oP_REVEAL)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    bianchi_violation)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    high_value_locked)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    rich_fault)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    morph_runtime_fault)))))), (UpdateVector (muTensorIdxSz, (Bit wordSz),
    (Var ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)),
    (Var ((SyntaxKind (Bit muTensorIdxSz)), tensor_idx)), (Var ((SyntaxKind
    (Bit wordSz)), tensor_new_val)))), (ITE ((SyntaxKind (Vector ((Bit
    wordSz), muTensorIdxSz))), (BinBool (AndB, (BinBool (AndB, (BinBool
    (AndB, (Eq ((Bit opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)),
    (Const ((Bit opcodeSz), (ConstBit (opcodeSz, oP_TENSOR_SET)))))),
    (UniBool (NegB, (Var ((SyntaxKind Bool), bianchi_violation)))))),
    (UniBool (NegB, (Var ((SyntaxKind Bool), rich_fault)))))), (UniBool
    (NegB, (Var ((SyntaxKind Bool), morph_runtime_fault)))))), (UpdateVector
    (muTensorIdxSz, (Bit wordSz), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)), (Var ((SyntaxKind (Bit muTensorIdxSz)),
    tensor_idx)), (Var ((SyntaxKind (Bit wordSz)), src_val)))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))))),
    (fun new_mu_tensor -> Let_ ((SyntaxKind (Vector ((Bit pTableIdxSz),
    morphTableIdxSz))), (ITE ((SyntaxKind (Vector ((Bit pTableIdxSz),
    morphTableIdxSz))), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool),
    bianchi_violation)), (Var ((SyntaxKind Bool), locality_violation)))),
    (Var ((SyntaxKind Bool), ptable_overflow_violation)))), (Var ((SyntaxKind
    Bool), high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))),
    (Var ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind (Vector ((Bit pTableIdxSz),
    morphTableIdxSz))), morph_src_table_v)), (ITE ((SyntaxKind (Vector ((Bit
    pTableIdxSz), morphTableIdxSz))), (Var ((SyntaxKind Bool),
    morph_allocates)), (UpdateVector (morphTableIdxSz, (Bit pTableIdxSz),
    (Var ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    morph_src_table_v)), (Var ((SyntaxKind (Bit morphTableIdxSz)),
    morph_slot)), (Var ((SyntaxKind (Bit pTableIdxSz)), morph_alloc_src)))),
    (Var ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    morph_src_table_v)))))), (fun new_morph_src_table -> Let_ ((SyntaxKind
    (Vector ((Bit pTableIdxSz), morphTableIdxSz))), (ITE ((SyntaxKind (Vector
    ((Bit pTableIdxSz), morphTableIdxSz))), (BinBool (OrB, (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var
    ((SyntaxKind Bool), bianchi_violation)), (Var ((SyntaxKind Bool),
    locality_violation)))), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind (Vector ((Bit pTableIdxSz),
    morphTableIdxSz))), morph_dst_table_v)), (ITE ((SyntaxKind (Vector ((Bit
    pTableIdxSz), morphTableIdxSz))), (Var ((SyntaxKind Bool),
    morph_allocates)), (UpdateVector (morphTableIdxSz, (Bit pTableIdxSz),
    (Var ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    morph_dst_table_v)), (Var ((SyntaxKind (Bit morphTableIdxSz)),
    morph_slot)), (Var ((SyntaxKind (Bit pTableIdxSz)), morph_alloc_dst)))),
    (Var ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    morph_dst_table_v)))))), (fun new_morph_dst_table -> Let_ ((SyntaxKind
    (Vector ((Bit descIdxSz), morphTableIdxSz))), (ITE ((SyntaxKind (Vector
    ((Bit descIdxSz), morphTableIdxSz))), (BinBool (OrB, (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var
    ((SyntaxKind Bool), bianchi_violation)), (Var ((SyntaxKind Bool),
    locality_violation)))), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind (Vector ((Bit descIdxSz),
    morphTableIdxSz))), morph_coupling_desc_table_v)), (ITE ((SyntaxKind
    (Vector ((Bit descIdxSz), morphTableIdxSz))), (Var ((SyntaxKind Bool),
    morph_allocates)), (UpdateVector (morphTableIdxSz, (Bit descIdxSz), (Var
    ((SyntaxKind (Vector ((Bit descIdxSz), morphTableIdxSz))),
    morph_coupling_desc_table_v)), (Var ((SyntaxKind (Bit morphTableIdxSz)),
    morph_slot)), (Var ((SyntaxKind (Bit descIdxSz)),
    morph_alloc_coupling)))), (Var ((SyntaxKind (Vector ((Bit descIdxSz),
    morphTableIdxSz))), morph_coupling_desc_table_v)))))),
    (fun new_morph_coupling_desc_table -> Let_ ((SyntaxKind (Vector (Bool,
    morphTableIdxSz))), (ITE ((SyntaxKind (Vector (Bool, morphTableIdxSz))),
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool), bianchi_violation)), (Var
    ((SyntaxKind Bool), locality_violation)))), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind (Vector (Bool,
    morphTableIdxSz))), morph_identity_table_v)), (ITE ((SyntaxKind (Vector
    (Bool, morphTableIdxSz))), (Var ((SyntaxKind Bool), morph_allocates)),
    (UpdateVector (morphTableIdxSz, Bool, (Var ((SyntaxKind (Vector (Bool,
    morphTableIdxSz))), morph_identity_table_v)), (Var ((SyntaxKind (Bit
    morphTableIdxSz)), morph_slot)), (Var ((SyntaxKind Bool),
    morph_alloc_identity)))), (Var ((SyntaxKind (Vector (Bool,
    morphTableIdxSz))), morph_identity_table_v)))))),
    (fun new_morph_identity_table -> Let_ ((SyntaxKind (Vector (Bool,
    morphTableIdxSz))), (ITE ((SyntaxKind (Vector (Bool, morphTableIdxSz))),
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool), bianchi_violation)), (Var
    ((SyntaxKind Bool), locality_violation)))), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind (Vector (Bool,
    morphTableIdxSz))), morph_valid_table_v)), (ITE ((SyntaxKind (Vector
    (Bool, morphTableIdxSz))), (Var ((SyntaxKind Bool), morph_allocates)),
    (UpdateVector (morphTableIdxSz, Bool, (Var ((SyntaxKind (Vector (Bool,
    morphTableIdxSz))), morph_valid_table_v)), (Var ((SyntaxKind (Bit
    morphTableIdxSz)), morph_slot)), (Const (Bool, (ConstBool true))))), (ITE
    ((SyntaxKind (Vector (Bool, morphTableIdxSz))), (Var ((SyntaxKind Bool),
    morph_delete_success)), (UpdateVector (morphTableIdxSz, Bool, (Var
    ((SyntaxKind (Vector (Bool, morphTableIdxSz))), morph_valid_table_v)),
    (Var ((SyntaxKind (Bit morphTableIdxSz)), morph_delete_idx)), (Const
    (Bool, (ConstBool false))))), (Var ((SyntaxKind (Vector (Bool,
    morphTableIdxSz))), morph_valid_table_v)))))))),
    (fun new_morph_valid_table -> Let_ ((SyntaxKind (Bit
    morphTableNextIdSz)), (ITE ((SyntaxKind (Bit morphTableNextIdSz)),
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool), bianchi_violation)), (Var
    ((SyntaxKind Bool), locality_violation)))), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind (Bit morphTableNextIdSz)),
    morph_next_id_v)), (ITE ((SyntaxKind (Bit morphTableNextIdSz)), (Var
    ((SyntaxKind Bool), morph_allocates)), (BinBit (morphTableNextIdSz,
    morphTableNextIdSz, morphTableNextIdSz, (Add morphTableNextIdSz), (Var
    ((SyntaxKind (Bit morphTableNextIdSz)), morph_next_id_v)), (Const ((Bit
    morphTableNextIdSz), (ConstBit (morphTableNextIdSz,
    (natToWord morphTableNextIdSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit morphTableNextIdSz)), morph_next_id_v)))))),
    (fun new_morph_next_id -> Let_ ((SyntaxKind (Bit wordSz)), (ITE
    ((SyntaxKind (Bit wordSz)), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB,
    (Var ((SyntaxKind Bool), bianchi_violation)), (Var ((SyntaxKind Bool),
    locality_violation)))), (Var ((SyntaxKind Bool), rich_fault)))), (Var
    ((SyntaxKind Bool), morph_runtime_fault)))), (Var ((SyntaxKind (Bit
    wordSz)), logic_acc_v)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_LASSERT)))))), (BinBit (wordSz,
    wordSz, wordSz, (Bxor wordSz), (Var ((SyntaxKind (Bit wordSz)),
    logic_acc_v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    lOGIC_GATE_KEY)))))), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit
    opcodeSz), (Var ((SyntaxKind (Bit opcodeSz)), opcode)), (Const ((Bit
    opcodeSz), (ConstBit (opcodeSz, oP_ORACLE_HALTS)))))), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)),
    logic_acc_v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var ((SyntaxKind (Bit
    wordSz)), logic_acc_v)))))))), (fun new_logic_acc -> Let_ ((SyntaxKind
    (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var
    ((SyntaxKind Bool), bianchi_violation)), (Var ((SyntaxKind Bool),
    locality_violation)))), (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))), (Var ((SyntaxKind Bool),
    high_value_locked)))), (Var ((SyntaxKind Bool), nfi_violation)))), (Var
    ((SyntaxKind Bool), rich_fault)))), (Var ((SyntaxKind Bool),
    morph_runtime_fault)))), (Var ((SyntaxKind (Bit wordSz)), cert_addr_v)),
    (ITE ((SyntaxKind (Bit wordSz)), (BinBool (AndB, (Var ((SyntaxKind Bool),
    is_morph_assert_ext)), (Var ((SyntaxKind Bool), morph_assert_success)))),
    (Var ((SyntaxKind (Bit wordSz)), ext_assert_property_checksum)), (ITE
    ((SyntaxKind (Bit wordSz)), (BinBool (AndB, (Var ((SyntaxKind Bool),
    is_morph_assert_legacy)), (Var ((SyntaxKind Bool),
    morph_assert_success)))), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz 0))))), (Var ((SyntaxKind (Bit wordSz)),
    cert_addr_v)))))))), (fun new_cert_addr -> Let_ ((SyntaxKind (Bit
    wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), mcycle_lo_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))),
    (fun mcycle_lo_next -> Let_ ((SyntaxKind Bool), (Eq ((Bit wordSz), (Var
    ((SyntaxKind (Bit wordSz)), mcycle_lo_next)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz 0))))))), (fun mcycle_lo_wrap ->
    Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), mcycle_lo_wrap)), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), mcycle_hi_v)), (Const
    ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var ((SyntaxKind (Bit
    wordSz)), mcycle_hi_v)))), (fun mcycle_hi_next -> Let_ ((SyntaxKind
    Bool), (BinBool (AndB, (BinBool (AndB, (BinBool (AndB, (BinBool (AndB,
    (BinBool (AndB, (UniBool (NegB, (Var ((SyntaxKind Bool),
    locality_violation)))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    ptable_overflow_violation)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    high_value_locked)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    nfi_violation)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    rich_fault)))))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    morph_runtime_fault)))))), (fun retire_this_step -> Let_ ((SyntaxKind
    (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    retire_this_step)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), minstret_lo_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), minstret_lo_v)))), (fun minstret_lo_inc ->
    Let_ ((SyntaxKind Bool), (BinBool (AndB, (Var ((SyntaxKind Bool),
    retire_this_step)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)),
    minstret_lo_inc)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz 0))))))))), (fun minstret_lo_wrap -> Let_ ((SyntaxKind
    (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    minstret_lo_wrap)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), minstret_hi_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), minstret_hi_v)))), (fun minstret_hi_next ->
    Let_ ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), logic_key_ok)), (Const ((Bit wordSz), (ConstBit
    (wordSz, mSTATUS_THIELE)))), (Const ((Bit wordSz), (ConstBit (wordSz,
    mSTATUS_TURING)))))), (fun new_mstatus -> WriteReg (('p'::('c'::[])),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)), new_pc)),
    (WriteReg (('m'::('u'::[])), (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind
    (Bit wordSz)), final_mu)), (WriteReg (('r'::('e'::('g'::('s'::[])))),
    (SyntaxKind (Vector ((Bit wordSz), regIdxSz))), (Var ((SyntaxKind (Vector
    ((Bit wordSz), regIdxSz))), new_regs)), (WriteReg
    (('m'::('e'::('m'::[]))), (SyntaxKind (Vector ((Bit wordSz),
    memAddrSz))), (Var ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))),
    new_mem)), (WriteReg (('h'::('a'::('l'::('t'::('e'::('d'::[])))))),
    (SyntaxKind Bool), (Var ((SyntaxKind Bool), new_halted)), (WriteReg
    (('e'::('r'::('r'::[]))), (SyntaxKind Bool), (Var ((SyntaxKind Bool),
    new_err)), (WriteReg
    (('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_error_code)), (WriteReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('a'::('c'::('c'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_logic_acc)), (WriteReg
    (('c'::('e'::('r'::('t'::('_'::('a'::('d'::('d'::('r'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_cert_addr)), (WriteReg
    (('m'::('s'::('t'::('a'::('t'::('u'::('s'::[]))))))), (SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind (Bit wordSz)), new_mstatus)), (WriteReg
    (('m'::('c'::('y'::('c'::('l'::('e'::('_'::('l'::('o'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    mcycle_lo_next)), (WriteReg
    (('m'::('c'::('y'::('c'::('l'::('e'::('_'::('h'::('i'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    mcycle_hi_next)), (WriteReg
    (('m'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('_'::('l'::('o'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    minstret_lo_inc)), (WriteReg
    (('m'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('_'::('h'::('i'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    minstret_hi_next)), (WriteReg
    (('p'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('_'::('o'::('p'::('s'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_partition_ops)), (WriteReg
    (('m'::('d'::('l'::('_'::('o'::('p'::('s'::[]))))))), (SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind (Bit wordSz)), new_mdl_ops)), (WriteReg
    (('i'::('n'::('f'::('o'::('_'::('g'::('a'::('i'::('n'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_info_gain)), (WriteReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), new_mu_tensor)), (WriteReg
    (('p'::('t'::('T'::('a'::('b'::('l'::('e'::[]))))))), (SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    pTableIdxSz))), new_pt_sizes)), (WriteReg
    (('p'::('t'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))),
    (SyntaxKind (Bit pTableNextIdSz)), (Var ((SyntaxKind (Bit
    pTableNextIdSz)), new_pt_next_id)), (WriteReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('s'::('r'::('c'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))),
    (SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))), (Var
    ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    new_morph_src_table)), (WriteReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('d'::('s'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))),
    (SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))), (Var
    ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))),
    new_morph_dst_table)), (WriteReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit descIdxSz), morphTableIdxSz))), (Var
    ((SyntaxKind (Vector ((Bit descIdxSz), morphTableIdxSz))),
    new_morph_coupling_desc_table)), (WriteReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('i'::('d'::('e'::('n'::('t'::('i'::('t'::('y'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))),
    (SyntaxKind (Vector (Bool, morphTableIdxSz))), (Var ((SyntaxKind (Vector
    (Bool, morphTableIdxSz))), new_morph_identity_table)), (WriteReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))),
    (SyntaxKind (Vector (Bool, morphTableIdxSz))), (Var ((SyntaxKind (Vector
    (Bool, morphTableIdxSz))), new_morph_valid_table)), (WriteReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))),
    (SyntaxKind (Bit morphTableNextIdSz)), (Var ((SyntaxKind (Bit
    morphTableNextIdSz)), new_morph_next_id)), (WriteReg
    (('c'::('e'::('r'::('t'::('i'::('f'::('i'::('e'::('d'::[]))))))))),
    (SyntaxKind Bool), (Var ((SyntaxKind Bool), new_certified)), (WriteReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('0'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_wc_same_00)), (WriteReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('0'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_wc_diff_00)), (WriteReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('0'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_wc_same_01)), (WriteReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('0'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_wc_diff_01)), (WriteReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('1'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_wc_same_10)), (WriteReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('1'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_wc_diff_10)), (WriteReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('1'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_wc_same_11)), (WriteReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('1'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_wc_diff_11)), (Let_ ((SyntaxKind (Bit wordSz)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz 0))))), (fun lassert_zero ->
    WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('p'::('h'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ITE ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (BinBool (AndB, (BinBool (AndB, (Var
    ((SyntaxKind Bool), is_lassert)), (Var ((SyntaxKind Bool),
    lassert_is_sat)))), (UniBool (NegB, (Var ((SyntaxKind Bool),
    rich_fault)))))), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))), (Const
    ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('k'::('i'::('n'::('d'::[])))))))))))),
    (SyntaxKind Bool), (ITE ((SyntaxKind Bool), (BinBool (AndB, (Var
    ((SyntaxKind Bool), is_lassert)), (UniBool (NegB, (Var ((SyntaxKind
    Bool), rich_fault)))))), (Var ((SyntaxKind Bool), lassert_is_sat)),
    (Const (Bool, (ConstBool false))))), (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('b'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_lassert)), (Var
    ((SyntaxKind Bool), lassert_is_sat)))), (UniBool (NegB, (Var ((SyntaxKind
    Bool), rich_fault)))))), (Var ((SyntaxKind (Bit wordSz)), dst_val)), (Var
    ((SyntaxKind (Bit wordSz)), lassert_zero)))), (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('b'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_lassert)), (Var
    ((SyntaxKind Bool), lassert_is_sat)))), (UniBool (NegB, (Var ((SyntaxKind
    Bool), rich_fault)))))), (Var ((SyntaxKind (Bit wordSz)), src_val)), (Var
    ((SyntaxKind (Bit wordSz)), lassert_zero)))), (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('p'::('t'::('r'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (BinBool
    (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), is_lassert)), (Var
    ((SyntaxKind Bool), lassert_is_sat)))), (UniBool (NegB, (Var ((SyntaxKind
    Bool), rich_fault)))))), (Var ((SyntaxKind (Bit wordSz)), cost32)), (Var
    ((SyntaxKind (Bit wordSz)), lassert_zero)))), (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('p'::('t'::('r'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    lassert_zero)), (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('l'::('e'::('n'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    lassert_zero)), (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('l'::('e'::('n'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    lassert_zero)), (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('l'::('a'::('u'::('s'::('e'::('_'::('s'::('a'::('t'::[])))))))))))))))))),
    (SyntaxKind Bool), (Const (Bool, (ConstBool false))), (Return (Const
    (void,
    (getDefaultConst void)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }),
    (ConsInModule ((MERule { attrName =
    ('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('s'::('m'::[])))))))))));
    attrType = (fun _ -> ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('p'::('h'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (fun lassert_phase_v -> Assert_
    ((let e1 = Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
        (Stdlib.Int.succ 0))))), lassert_phase_v)
      in
      let e2 = Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        0)))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
        0))),
        (natToWord (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))) 0))))
      in
      UniBool (NegB, (Eq ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0)))), e1, e2)))), (ReadReg (('m'::('e'::('m'::[]))),
    (SyntaxKind (Vector ((Bit wordSz), memAddrSz))), (fun mem_v -> ReadReg
    (('m'::('u'::[])), (SyntaxKind (Bit wordSz)), (fun mu_v -> ReadReg
    (('p'::('c'::[])), (SyntaxKind (Bit wordSz)), (fun pc_v -> ReadReg
    (('t'::('r'::('a'::('p'::('_'::('v'::('e'::('c'::('t'::('o'::('r'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (fun trap_vector_v -> ReadReg
    (('e'::('r'::('r'::[]))), (SyntaxKind Bool), (fun err_v -> ReadReg
    (('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun error_code_v -> ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('b'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun lassert_fbase_v -> ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('b'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun lassert_cbase_v -> ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('l'::('e'::('n'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (fun lassert_flen_v -> ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('l'::('e'::('n'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (fun lassert_clen_v -> ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('p'::('t'::('r'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (fun lassert_fptr_v -> ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('p'::('t'::('r'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (fun lassert_cptr_v -> ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('l'::('a'::('u'::('s'::('e'::('_'::('s'::('a'::('t'::[])))))))))))))))))),
    (SyntaxKind Bool), (fun lassert_clause_sat_v -> Let_ ((SyntaxKind (Bit
    memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))), memAddrSz, (Trunc (memAddrSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)),
    lassert_fbase_v)))), (fun fbase_a0 -> Let_ ((SyntaxKind (Bit memAddrSz)),
    (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))), memAddrSz, (Trunc (memAddrSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), lassert_fbase_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))),
    (fun fbase_a2 -> Let_ ((SyntaxKind (Bit wordSz)),
    (read_mem (Var ((SyntaxKind (Bit memAddrSz)), fbase_a0)) (Var
      ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), mem_v))),
    (fun hdr_flen -> Let_ ((SyntaxKind (Bit wordSz)),
    (read_mem (Var ((SyntaxKind (Bit memAddrSz)), fbase_a2)) (Var
      ((SyntaxKind (Vector ((Bit wordSz), memAddrSz))), mem_v))),
    (fun hdr_nclauses -> Let_ ((SyntaxKind (Bit memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))), memAddrSz, (Trunc (memAddrSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), lassert_fptr_v)))),
    (fun fptr_a -> Let_ ((SyntaxKind (Bit wordSz)),
    (read_mem (Var ((SyntaxKind (Bit memAddrSz)), fptr_a)) (Var ((SyntaxKind
      (Vector ((Bit wordSz), memAddrSz))), mem_v))), (fun literal -> Let_
    ((SyntaxKind (Bit (Stdlib.Int.succ 0))), (UniBit
    ((add
       (add (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
         0))))))))))))))))))))))))))))))) (Stdlib.Int.succ 0)) 0),
    (Stdlib.Int.succ 0), (ConstExtract ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))))))))))))))))))))))))))))), (Stdlib.Int.succ 0),
    0)), (Var ((SyntaxKind (Bit wordSz)), literal)))), (fun lit_sign -> Let_
    ((SyntaxKind Bool), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)),
    literal)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz 0))))))), (fun lit_is_zero -> Let_ ((SyntaxKind Bool),
    (BinBool (AndB, (Eq ((Bit (Stdlib.Int.succ 0)), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ 0))), lit_sign)), (Const ((Bit (Stdlib.Int.succ 0)),
    (ConstBit ((Stdlib.Int.succ 0), (WS (true, 0, WO)))))))), (UniBool (NegB,
    (Var ((SyntaxKind Bool), lit_is_zero)))))), (fun lit_is_neg -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), lit_is_neg)), (BinBit (wordSz, wordSz, wordSz, (Sub
    wordSz), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz 0))))), (Var ((SyntaxKind (Bit wordSz)), literal)))),
    (Var ((SyntaxKind (Bit wordSz)), literal)))), (fun lit_abs -> Let_
    ((SyntaxKind (Bit memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))), memAddrSz, (Trunc (memAddrSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), lassert_cbase_v)), (Var ((SyntaxKind (Bit
    wordSz)), lit_abs)))))), (fun caddr -> Let_ ((SyntaxKind (Bit wordSz)),
    (read_mem (Var ((SyntaxKind (Bit memAddrSz)), caddr)) (Var ((SyntaxKind
      (Vector ((Bit wordSz), memAddrSz))), mem_v))), (fun asgn_word -> Let_
    ((SyntaxKind Bool),
    (let e1 = Var ((SyntaxKind (Bit wordSz)), asgn_word) in
     let e2 = Const ((Bit wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))
     in
     UniBool (NegB, (Eq ((Bit wordSz), e1, e2)))), (fun asgn_t -> Let_
    ((SyntaxKind Bool), (BinBool (AndB, (UniBool (NegB, (Var ((SyntaxKind
    Bool), lit_is_zero)))), (ITE ((SyntaxKind Bool), (Var ((SyntaxKind Bool),
    lit_is_neg)), (UniBool (NegB, (Var ((SyntaxKind Bool), asgn_t)))), (Var
    ((SyntaxKind Bool), asgn_t)))))), (fun lit_sat -> Let_ ((SyntaxKind
    Bool), (Eq ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), lassert_phase_v)), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (fun is_phase1 -> Let_ ((SyntaxKind Bool), (Eq ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Var
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), lassert_phase_v)), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))),
    (fun is_phase2 -> Let_ ((SyntaxKind Bool), (BinBool (AndB, (Var
    ((SyntaxKind Bool), is_phase2)), (Var ((SyntaxKind Bool),
    lit_is_zero)))), (fun end_of_clause -> Let_ ((SyntaxKind Bool), (UniBool
    (NegB, (BinBitBool (wordSz, wordSz, (Lt wordSz), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))), (Var
    ((SyntaxKind (Bit wordSz)), lassert_clen_v)))))), (fun last_clause ->
    Let_ ((SyntaxKind Bool), (BinBool (AndB, (Var ((SyntaxKind Bool),
    end_of_clause)), (UniBool (NegB, (Var ((SyntaxKind Bool),
    lassert_clause_sat_v)))))), (fun clause_fail -> Let_ ((SyntaxKind Bool),
    (BinBool (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), end_of_clause)),
    (Var ((SyntaxKind Bool), lassert_clause_sat_v)))), (Var ((SyntaxKind
    Bool), last_clause)))), (fun all_done -> Let_ ((SyntaxKind Bool),
    (BinBool (AndB, (BinBool (AndB, (Var ((SyntaxKind Bool), end_of_clause)),
    (Var ((SyntaxKind Bool), lassert_clause_sat_v)))), (UniBool (NegB, (Var
    ((SyntaxKind Bool), last_clause)))))), (fun clause_ok_cont -> Let_
    ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    lassert_cptr_v)), (fun cost_v -> Let_ ((SyntaxKind (Bit wordSz)), (BinBit
    (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))), wordSz, (Sll
    (wordSz, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), lassert_flen_v)), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))))))))), (fun flen_x8 ->
    Let_ ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), mu_v)),
    (Var ((SyntaxKind (Bit wordSz)), flen_x8)))), (Var ((SyntaxKind (Bit
    wordSz)), cost_v)))), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (fun mu_success -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var ((SyntaxKind
    (Bit wordSz)), mu_v)), (Var ((SyntaxKind (Bit wordSz)), cost_v)))),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))))), (fun mu_fail -> Let_
    ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ITE ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (Var ((SyntaxKind Bool), is_phase1)), (Const
    ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))), (ITE ((SyntaxKind (Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (BinBool (OrB, (Var
    ((SyntaxKind Bool), all_done)), (Var ((SyntaxKind Bool), clause_fail)))),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))),
    (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS
    (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))))), (fun next_phase -> Let_ ((SyntaxKind
    (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    is_phase1)), (Var ((SyntaxKind (Bit wordSz)), hdr_flen)), (Var
    ((SyntaxKind (Bit wordSz)), lassert_flen_v)))), (fun next_flen -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), is_phase1)), (Var ((SyntaxKind (Bit wordSz)),
    hdr_nclauses)), (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    clause_ok_cont)), (BinBit (wordSz, wordSz, wordSz, (Sub wordSz), (Var
    ((SyntaxKind (Bit wordSz)), lassert_clen_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (Var
    ((SyntaxKind (Bit wordSz)), lassert_clen_v)))))), (fun next_clen -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), is_phase1)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), lassert_fbase_v)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      0)))))))))), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (Var
    ((SyntaxKind (Bit wordSz)), lassert_fptr_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))))),
    (fun next_fptr -> Let_ ((SyntaxKind Bool), (ITE ((SyntaxKind Bool), (Var
    ((SyntaxKind Bool), is_phase1)), (Const (Bool, (ConstBool false))), (ITE
    ((SyntaxKind Bool), (Var ((SyntaxKind Bool), end_of_clause)), (Const
    (Bool, (ConstBool false))), (ITE ((SyntaxKind Bool), (Var ((SyntaxKind
    Bool), lit_sat)), (Const (Bool, (ConstBool true))), (Var ((SyntaxKind
    Bool), lassert_clause_sat_v)))))))), (fun next_clause_sat -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), all_done)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (Var ((SyntaxKind (Bit wordSz)), pc_v)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))))), (ITE
    ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool), clause_fail)), (Var
    ((SyntaxKind (Bit wordSz)), trap_vector_v)), (Var ((SyntaxKind (Bit
    wordSz)), pc_v)))))), (fun new_pc -> Let_ ((SyntaxKind (Bit wordSz)),
    (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool), all_done)),
    (Var ((SyntaxKind (Bit wordSz)), mu_success)), (ITE ((SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind Bool), clause_fail)), (Var ((SyntaxKind (Bit
    wordSz)), mu_fail)), (Var ((SyntaxKind (Bit wordSz)), mu_v)))))),
    (fun new_mu -> Let_ ((SyntaxKind Bool), (ITE ((SyntaxKind Bool), (Var
    ((SyntaxKind Bool), clause_fail)), (Const (Bool, (ConstBool true))), (Var
    ((SyntaxKind Bool), err_v)))), (fun new_err -> Let_ ((SyntaxKind (Bit
    wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    clause_fail)), (Const ((Bit wordSz), (ConstBit (wordSz,
    eRR_LOGIC_VAL)))), (Var ((SyntaxKind (Bit wordSz)), error_code_v)))),
    (fun new_error_code_fsm -> WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('p'::('h'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), next_phase)), (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('l'::('e'::('n'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)), next_flen)),
    (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('l'::('e'::('n'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)), next_clen)),
    (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('p'::('t'::('r'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)), next_fptr)),
    (WriteReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('l'::('a'::('u'::('s'::('e'::('_'::('s'::('a'::('t'::[])))))))))))))))))),
    (SyntaxKind Bool), (Var ((SyntaxKind Bool), next_clause_sat)), (WriteReg
    (('p'::('c'::[])), (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit
    wordSz)), new_pc)), (WriteReg (('m'::('u'::[])), (SyntaxKind (Bit
    wordSz)), (Var ((SyntaxKind (Bit wordSz)), new_mu)), (WriteReg
    (('e'::('r'::('r'::[]))), (SyntaxKind Bool), (Var ((SyntaxKind Bool),
    new_err)), (WriteReg
    (('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    new_error_code_fsm)), (Return (Const (void,
    (getDefaultConst void)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('l'::('o'::('a'::('d'::('I'::('n'::('s'::('t'::('r'::[])))))))));
    attrType = (ExistT ({ arg = (Struct ((Stdlib.Int.succ (Stdlib.Int.succ
    0)), loadInstrPort)); ret = void }, (fun _ arg0 -> ReadReg
    (('i'::('m'::('e'::('m'::[])))), (SyntaxKind (Vector ((Bit instrSz),
    memAddrSz))), (fun imem_v -> Let_ ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) loadInstrPort
      (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
        (Stdlib.Int.succ 0) loadInstrPort))), (ReadField ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), loadInstrPort,
    (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
      (Stdlib.Int.succ 0) loadInstrPort), (Var ((SyntaxKind (Struct
    ((Stdlib.Int.succ (Stdlib.Int.succ 0)), loadInstrPort))), arg0)))),
    (fun addr_v -> Let_ ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) loadInstrPort
      (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
        (Stdlib.Int.succ 0) loadInstrPort))), (ReadField ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), loadInstrPort,
    (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
      (Stdlib.Int.succ 0) loadInstrPort), (Var ((SyntaxKind (Struct
    ((Stdlib.Int.succ (Stdlib.Int.succ 0)), loadInstrPort))), arg0)))),
    (fun data_v -> WriteReg (('i'::('m'::('e'::('m'::[])))), (SyntaxKind
    (Vector ((Bit instrSz), memAddrSz))), (UpdateVector (memAddrSz, (Bit
    instrSz), (Var ((SyntaxKind (Vector ((Bit instrSz), memAddrSz))),
    imem_v)), (Var ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) loadInstrPort
      (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
        (Stdlib.Int.succ 0) loadInstrPort))), addr_v)), (Var ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) loadInstrPort
      (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
        (Stdlib.Int.succ 0) loadInstrPort))), data_v)))), (Return (Const
    (void, (getDefaultConst void)))))))))))))) }), (ConsInModule ((MEMeth
    { attrName = ('g'::('e'::('t'::('P'::('C'::[]))))); attrType = (ExistT
    ({ arg = void; ret = (Bit wordSz) }, (fun _ _ -> ReadReg
    (('p'::('c'::[])), (SyntaxKind (Bit wordSz)), (fun v -> Return (Var
    ((SyntaxKind (Bit wordSz)), v))))))) }), (ConsInModule ((MEMeth
    { attrName = ('g'::('e'::('t'::('M'::('u'::[]))))); attrType = (ExistT
    ({ arg = void; ret = (Bit wordSz) }, (fun _ _ -> ReadReg
    (('m'::('u'::[])), (SyntaxKind (Bit wordSz)), (fun v -> Return (Var
    ((SyntaxKind (Bit wordSz)), v))))))) }), (ConsInModule ((MEMeth
    { attrName = ('g'::('e'::('t'::('E'::('r'::('r'::[])))))); attrType =
    (ExistT ({ arg = void; ret = Bool }, (fun _ _ -> ReadReg
    (('e'::('r'::('r'::[]))), (SyntaxKind Bool), (fun v -> Return (Var
    ((SyntaxKind Bool), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('H'::('a'::('l'::('t'::('e'::('d'::[])))))))));
    attrType = (ExistT ({ arg = void; ret = Bool }, (fun _ _ -> ReadReg
    (('h'::('a'::('l'::('t'::('e'::('d'::[])))))), (SyntaxKind Bool),
    (fun v -> Return (Var ((SyntaxKind Bool), v))))))) }), (ConsInModule
    ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('e'::('r'::('t'::('i'::('f'::('i'::('e'::('d'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = Bool }, (fun _ _ -> ReadReg
    (('c'::('e'::('r'::('t'::('i'::('f'::('i'::('e'::('d'::[]))))))))),
    (SyntaxKind Bool), (fun v -> Return (Var ((SyntaxKind Bool), v))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('W'::('c'::('S'::('a'::('m'::('e'::('0'::('0'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('0'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('W'::('c'::('D'::('i'::('f'::('f'::('0'::('0'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('0'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('W'::('c'::('S'::('a'::('m'::('e'::('0'::('1'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('0'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('W'::('c'::('D'::('i'::('f'::('f'::('0'::('1'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('0'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('W'::('c'::('S'::('a'::('m'::('e'::('1'::('0'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('1'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('W'::('c'::('D'::('i'::('f'::('f'::('1'::('0'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('1'::('0'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('W'::('c'::('S'::('a'::('m'::('e'::('1'::('1'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('w'::('c'::('_'::('s'::('a'::('m'::('e'::('_'::('1'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('W'::('c'::('D'::('i'::('f'::('f'::('1'::('1'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('w'::('c'::('_'::('d'::('i'::('f'::('f'::('_'::('1'::('1'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('P'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('O'::('p'::('s'::[])))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('p'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('_'::('o'::('p'::('s'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('d'::('l'::('O'::('p'::('s'::[])))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg (('m'::('d'::('l'::('_'::('o'::('p'::('s'::[]))))))), (SyntaxKind
    (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit wordSz)),
    v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('I'::('n'::('f'::('o'::('G'::('a'::('i'::('n'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('i'::('n'::('f'::('o'::('_'::('g'::('a'::('i'::('n'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('E'::('r'::('r'::('o'::('r'::('C'::('o'::('d'::('e'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('s'::('t'::('a'::('t'::('u'::('s'::[]))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg (('m'::('s'::('t'::('a'::('t'::('u'::('s'::[]))))))), (SyntaxKind
    (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit wordSz)),
    v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('c'::('y'::('c'::('l'::('e'::('L'::('o'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('c'::('y'::('c'::('l'::('e'::('_'::('l'::('o'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('c'::('y'::('c'::('l'::('e'::('H'::('i'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('c'::('y'::('c'::('l'::('e'::('_'::('h'::('i'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('L'::('o'::[])))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('_'::('l'::('o'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('H'::('i'::[])))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('_'::('h'::('i'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('o'::('g'::('i'::('c'::('A'::('c'::('c'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('a'::('c'::('c'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('e'::('r'::('t'::('A'::('d'::('d'::('r'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('c'::('e'::('r'::('t'::('_'::('a'::('d'::('d'::('r'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('u'::('T'::('e'::('n'::('s'::('o'::('r'::('0'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun t1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (fun s -> Return (Var ((SyntaxKind (Bit
    wordSz)), s))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('u'::('T'::('e'::('n'::('s'::('o'::('r'::('1'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun t1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (fun s -> Return (Var ((SyntaxKind (Bit
    wordSz)), s))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('u'::('T'::('e'::('n'::('s'::('o'::('r'::('2'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun t1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (fun s -> Return (Var ((SyntaxKind (Bit
    wordSz)), s))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('u'::('T'::('e'::('n'::('s'::('o'::('r'::('3'::[]))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun t1 -> Let_
    ((SyntaxKind (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (fun s -> Return (Var ((SyntaxKind (Bit
    wordSz)), s))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('s'::('e'::('t'::('A'::('c'::('t'::('i'::('v'::('e'::('M'::('o'::('d'::('u'::('l'::('e'::[])))))))))))))));
    attrType = (ExistT ({ arg = (Bit pTableIdxSz); ret = void },
    (fun _ mid -> WriteReg
    (('a'::('c'::('t'::('i'::('v'::('e'::('_'::('m'::('o'::('d'::('u'::('l'::('e'::[]))))))))))))),
    (SyntaxKind (Bit pTableIdxSz)), (Var ((SyntaxKind (Bit pTableIdxSz)),
    mid)), (Return (Const (void, (getDefaultConst void)))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('s'::('e'::('t'::('T'::('r'::('a'::('p'::('V'::('e'::('c'::('t'::('o'::('r'::[])))))))))))));
    attrType = (ExistT ({ arg = (Bit wordSz); ret = void }, (fun _ tv ->
    WriteReg
    (('t'::('r'::('a'::('p'::('_'::('v'::('e'::('c'::('t'::('o'::('r'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)), tv)), (Return
    (Const (void, (getDefaultConst void)))))))) }), (ConsInModule ((MEMeth
    { attrName =
    ('a'::('p'::('b'::('R'::('e'::('a'::('d'::('D'::('a'::('t'::('a'::[])))))))))));
    attrType = (ExistT ({ arg = (Bit wordSz); ret = (Bit wordSz) },
    (fun _ addr -> ReadReg (('p'::('c'::[])), (SyntaxKind (Bit wordSz)),
    (fun pc_v -> ReadReg (('m'::('u'::[])), (SyntaxKind (Bit wordSz)),
    (fun mu_v -> ReadReg (('e'::('r'::('r'::[]))), (SyntaxKind Bool),
    (fun err_v -> ReadReg (('h'::('a'::('l'::('t'::('e'::('d'::[])))))),
    (SyntaxKind Bool), (fun halted_v -> ReadReg
    (('p'::('a'::('r'::('t'::('i'::('t'::('i'::('o'::('n'::('_'::('o'::('p'::('s'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun partition_ops_v -> ReadReg
    (('m'::('d'::('l'::('_'::('o'::('p'::('s'::[]))))))), (SyntaxKind (Bit
    wordSz)), (fun mdl_ops_v -> ReadReg
    (('i'::('n'::('f'::('o'::('_'::('g'::('a'::('i'::('n'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun info_gain_v -> ReadReg
    (('e'::('r'::('r'::('o'::('r'::('_'::('c'::('o'::('d'::('e'::[])))))))))),
    (SyntaxKind (Bit wordSz)), (fun error_code_v -> ReadReg
    (('m'::('s'::('t'::('a'::('t'::('u'::('s'::[]))))))), (SyntaxKind (Bit
    wordSz)), (fun mstatus_v -> ReadReg
    (('m'::('c'::('y'::('c'::('l'::('e'::('_'::('l'::('o'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun mcycle_lo_v -> ReadReg
    (('m'::('c'::('y'::('c'::('l'::('e'::('_'::('h'::('i'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun mcycle_hi_v -> ReadReg
    (('m'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('_'::('l'::('o'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (fun minstret_lo_v -> ReadReg
    (('m'::('i'::('n'::('s'::('t'::('r'::('e'::('t'::('_'::('h'::('i'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (fun minstret_hi_v -> ReadReg
    (('l'::('o'::('g'::('i'::('c'::('_'::('a'::('c'::('c'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun logic_acc_v -> ReadReg
    (('c'::('e'::('r'::('t'::('_'::('a'::('d'::('d'::('r'::[]))))))))),
    (SyntaxKind (Bit wordSz)), (fun cert_addr_v -> ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun mu_tensor_v ->
    ReadReg
    (('p'::('t'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))),
    (SyntaxKind (Bit pTableNextIdSz)), (fun pt_next_id_v -> ReadReg
    (('p'::('t'::('T'::('a'::('b'::('l'::('e'::[]))))))), (SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), (fun pt_sizes_v -> Let_ ((SyntaxKind (Bit
    wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz,
    wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add
    wordSz), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))))), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))))), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))))), (fun mu_tensor0 -> Let_ ((SyntaxKind
    (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))))), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (false, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))))), (fun mu_tensor1 -> Let_ ((SyntaxKind
    (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))))), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))))), (fun mu_tensor2 -> Let_ ((SyntaxKind
    (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), mu_tensor_v)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))))), (ReadIndex ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz),
    (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ
    (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0), (WS (true, 0,
    WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), mu_tensor_v)))))), (fun mu_tensor3 -> Let_ ((SyntaxKind
    (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (Var ((SyntaxKind (Bit wordSz)), mu_tensor0)), (Var
    ((SyntaxKind (Bit wordSz)), mu_tensor1)))), (Var ((SyntaxKind (Bit
    wordSz)), mu_tensor2)))), (Var ((SyntaxKind (Bit wordSz)),
    mu_tensor3)))), (fun tensor_total -> Let_ ((SyntaxKind Bool), (BinBitBool
    (wordSz, wordSz, (Lt wordSz), (Var ((SyntaxKind (Bit wordSz)), mu_v)),
    (Var ((SyntaxKind (Bit wordSz)), tensor_total)))),
    (fun bianchi_alarm_v -> Let_ ((SyntaxKind (Bit wordSz)), (UniBit
    (pTableNextIdSz, wordSz, (ZeroExtendTrunc (pTableNextIdSz, wordSz)), (Var
    ((SyntaxKind (Bit pTableNextIdSz)), pt_next_id_v)))),
    (fun pt_next_id32 -> Let_ ((SyntaxKind (Bit wordSz)), (ReadIndex
    (pTableIdxSz, (Bit wordSz), (Const ((Bit pTableIdxSz), (ConstBit
    (pTableIdxSz, (natToWord pTableIdxSz 0))))), (Var ((SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), pt_sizes_v)))), (fun pt_size0 -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit
    wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz 0))))))), (Var ((SyntaxKind (Bit
    wordSz)), pc_v)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit wordSz),
    (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz), (ConstBit
    (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))), (Var ((SyntaxKind (Bit wordSz)), mu_v)),
    (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind
    (Bit wordSz)), addr)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))), (ITE ((SyntaxKind (Bit wordSz)),
    (Var ((SyntaxKind Bool), err_v)), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))))), (ITE ((SyntaxKind
    (Bit wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)),
    addr)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))), (ITE ((SyntaxKind (Bit wordSz)),
    (Var ((SyntaxKind Bool), halted_v)), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))))), (ITE ((SyntaxKind
    (Bit wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)),
    addr)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))), (Var ((SyntaxKind (Bit
    wordSz)), partition_ops_v)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit
    wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))), (Var ((SyntaxKind (Bit
    wordSz)), mdl_ops_v)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit
    wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))), (Var ((SyntaxKind
    (Bit wordSz)), info_gain_v)), (ITE ((SyntaxKind (Bit wordSz)), (Eq ((Bit
    wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), error_code_v)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), mstatus_v)), (ITE ((SyntaxKind (Bit wordSz)),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), mcycle_lo_v)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), mcycle_hi_v)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Var ((SyntaxKind (Bit wordSz)), minstret_lo_v)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Var ((SyntaxKind (Bit wordSz)), minstret_hi_v)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Var ((SyntaxKind (Bit wordSz)), logic_acc_v)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), cert_addr_v)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Var ((SyntaxKind (Bit wordSz)), mu_tensor0)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Var ((SyntaxKind (Bit wordSz)), mu_tensor1)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Var ((SyntaxKind (Bit wordSz)), mu_tensor2)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Var ((SyntaxKind (Bit wordSz)), mu_tensor3)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (ITE ((SyntaxKind (Bit wordSz)), (Var ((SyntaxKind Bool),
    bianchi_alarm_v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz 0))))))), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Var ((SyntaxKind (Bit wordSz)), pt_next_id32)), (ITE ((SyntaxKind (Bit
    wordSz)), (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)),
    (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Var ((SyntaxKind (Bit wordSz)), pt_size0)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz 0))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun rdata -> Return (Var ((SyntaxKind (Bit wordSz)),
    rdata))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('a'::('p'::('b'::('R'::('e'::('a'::('d'::('E'::('r'::('r'::[]))))))))));
    attrType = (ExistT ({ arg = (Bit wordSz); ret = Bool }, (fun _ addr ->
    Let_ ((SyntaxKind Bool), (BinBool (OrB, (BinBool (OrB, (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool
    (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Eq
    ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0))))))), (Eq ((Bit
    wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))), (Eq ((Bit wordSz), (Var ((SyntaxKind
    (Bit wordSz)), addr)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))), (Eq ((Bit wordSz), (Var
    ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz), (ConstBit
    (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))), (Eq ((Bit wordSz), (Var
    ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz), (ConstBit
    (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))), (Eq ((Bit wordSz), (Var
    ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz), (ConstBit
    (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))), (Eq ((Bit wordSz),
    (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz), (ConstBit
    (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))), (Eq ((Bit wordSz),
    (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz), (ConstBit
    (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))), (Eq ((Bit
    wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))), (Eq ((Bit
    wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))), (Eq
    ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ 0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), (Eq
    ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Eq ((Bit wordSz), (Var ((SyntaxKind (Bit wordSz)), addr)), (Const ((Bit
    wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun is_readable -> Return (UniBool (NegB, (Var ((SyntaxKind Bool),
    is_readable))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('a'::('p'::('b'::('W'::('r'::('i'::('t'::('e'::[])))))))); attrType =
    (ExistT ({ arg = (Struct ((Stdlib.Int.succ (Stdlib.Int.succ 0)),
    aPBBusWritePort)); ret = Bool }, (fun _ arg0 -> ReadReg
    (('i'::('m'::('e'::('m'::[])))), (SyntaxKind (Vector ((Bit instrSz),
    memAddrSz))), (fun imem_v -> ReadReg
    (('a'::('c'::('t'::('i'::('v'::('e'::('_'::('m'::('o'::('d'::('u'::('l'::('e'::[]))))))))))))),
    (SyntaxKind (Bit pTableIdxSz)), (fun active_module_v -> ReadReg
    (('t'::('r'::('a'::('p'::('_'::('v'::('e'::('c'::('t'::('o'::('r'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (fun trap_vector_v -> ReadReg
    (('b'::('u'::('s'::('_'::('l'::('o'::('a'::('d'::('_'::('i'::('n'::('s'::('t'::('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))))))))))),
    (SyntaxKind (Bit memAddrSz)), (fun bus_load_instr_addr_v -> ReadReg
    (('b'::('u'::('s'::('_'::('l'::('o'::('a'::('d'::('_'::('i'::('n'::('s'::('t'::('r'::('_'::('d'::('a'::('t'::('a'::[]))))))))))))))))))),
    (SyntaxKind (Bit instrSz)), (fun bus_load_instr_data_v -> ReadReg
    (('b'::('u'::('s'::('_'::('l'::('o'::('a'::('d'::('_'::('i'::('n'::('s'::('t'::('r'::('_'::('k'::('i'::('c'::('k'::[]))))))))))))))))))),
    (SyntaxKind Bool), (fun bus_load_instr_kick_v -> Let_ ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
      (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
        (Stdlib.Int.succ 0) aPBBusWritePort))), (ReadField ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), aPBBusWritePort,
    (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
      (Stdlib.Int.succ 0) aPBBusWritePort), (Var ((SyntaxKind (Struct
    ((Stdlib.Int.succ (Stdlib.Int.succ 0)), aPBBusWritePort))), arg0)))),
    (fun addr -> Let_ ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
      (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
        (Stdlib.Int.succ 0) aPBBusWritePort))), (ReadField ((Stdlib.Int.succ
    (Stdlib.Int.succ 0)), aPBBusWritePort,
    (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
      (Stdlib.Int.succ 0) aPBBusWritePort), (Var ((SyntaxKind (Struct
    ((Stdlib.Int.succ (Stdlib.Int.succ 0)), aPBBusWritePort))), arg0)))),
    (fun data -> Let_ ((SyntaxKind (Bit wordSz)), (UniBit
    ((add wordSz instrUpperSz), wordSz, (Trunc (wordSz, instrUpperSz)), (Var
    ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
      (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
        (Stdlib.Int.succ 0) aPBBusWritePort))), data)))), (fun data32 -> Let_
    ((SyntaxKind Bool), (Eq
    ((fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
       (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
         (Stdlib.Int.succ 0) aPBBusWritePort)), (Var ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
      (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
        (Stdlib.Int.succ 0) aPBBusWritePort))), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun wr_load_instr_addr -> Let_ ((SyntaxKind Bool), (Eq
    ((fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
       (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
         (Stdlib.Int.succ 0) aPBBusWritePort)), (Var ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
      (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
        (Stdlib.Int.succ 0) aPBBusWritePort))), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun wr_load_instr_data -> Let_ ((SyntaxKind Bool), (Eq
    ((fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
       (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
         (Stdlib.Int.succ 0) aPBBusWritePort)), (Var ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
      (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
        (Stdlib.Int.succ 0) aPBBusWritePort))), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun wr_load_instr_kick -> Let_ ((SyntaxKind Bool), (Eq
    ((fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
       (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
         (Stdlib.Int.succ 0) aPBBusWritePort)), (Var ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
      (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
        (Stdlib.Int.succ 0) aPBBusWritePort))), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun wr_set_active_module -> Let_ ((SyntaxKind Bool), (Eq
    ((fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
       (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
         (Stdlib.Int.succ 0) aPBBusWritePort)), (Var ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
      (vector_find (fieldAccessor ('a'::('d'::('d'::('r'::[])))))
        (Stdlib.Int.succ 0) aPBBusWritePort))), addr)), (Const ((Bit wordSz),
    (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
      (Stdlib.Int.succ
      0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fun wr_set_trap_vector -> Let_ ((SyntaxKind Bool), (BinBool (OrB,
    (BinBool (OrB, (BinBool (OrB, (BinBool (OrB, (Var ((SyntaxKind Bool),
    wr_load_instr_addr)), (Var ((SyntaxKind Bool), wr_load_instr_data)))),
    (Var ((SyntaxKind Bool), wr_load_instr_kick)))), (Var ((SyntaxKind Bool),
    wr_set_active_module)))), (Var ((SyntaxKind Bool),
    wr_set_trap_vector)))), (fun wr_any -> Let_ ((SyntaxKind (Bit
    memAddrSz)), (UniBit
    ((add memAddrSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ 0))))))))))))))))), memAddrSz, (Trunc (memAddrSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))))))))), (Var ((SyntaxKind (Bit wordSz)), data32)))),
    (fun data_mem_addr -> Let_ ((SyntaxKind (Bit instrSz)), (Var ((SyntaxKind
    (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
      (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
        (Stdlib.Int.succ 0) aPBBusWritePort))), data)), (fun data_instr ->
    Let_ ((SyntaxKind Bool),
    (let e1 = Var ((SyntaxKind
       (fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
         (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
           (Stdlib.Int.succ 0) aPBBusWritePort))), data)
     in
     let e2 = Const ((Bit instrSz), (ConstBit (instrSz,
       (natToWord instrSz 0))))
     in
     UniBool (NegB, (Eq
     ((fieldKind (Stdlib.Int.succ (Stdlib.Int.succ 0)) aPBBusWritePort
        (vector_find (fieldAccessor ('d'::('a'::('t'::('a'::[])))))
          (Stdlib.Int.succ 0) aPBBusWritePort)), e1, e2)))),
    (fun data_nonzero -> Let_ ((SyntaxKind (Bit memAddrSz)), (ITE
    ((SyntaxKind (Bit memAddrSz)), (Var ((SyntaxKind Bool),
    wr_load_instr_addr)), (Var ((SyntaxKind (Bit memAddrSz)),
    data_mem_addr)), (Var ((SyntaxKind (Bit memAddrSz)),
    bus_load_instr_addr_v)))), (fun next_load_instr_addr -> Let_ ((SyntaxKind
    (Bit instrSz)), (ITE ((SyntaxKind (Bit instrSz)), (Var ((SyntaxKind
    Bool), wr_load_instr_data)), (Var ((SyntaxKind (Bit instrSz)),
    data_instr)), (Var ((SyntaxKind (Bit instrSz)),
    bus_load_instr_data_v)))), (fun next_load_instr_data -> Let_ ((SyntaxKind
    Bool), (ITE ((SyntaxKind Bool), (Var ((SyntaxKind Bool),
    wr_load_instr_kick)), (Var ((SyntaxKind Bool), data_nonzero)), (Var
    ((SyntaxKind Bool), bus_load_instr_kick_v)))),
    (fun next_load_instr_kick -> Let_ ((SyntaxKind Bool), (BinBool (AndB,
    (Var ((SyntaxKind Bool), wr_load_instr_kick)), (Var ((SyntaxKind Bool),
    data_nonzero)))), (fun do_instr_commit -> Let_ ((SyntaxKind (Vector ((Bit
    instrSz), memAddrSz))), (ITE ((SyntaxKind (Vector ((Bit instrSz),
    memAddrSz))), (Var ((SyntaxKind Bool), do_instr_commit)), (UpdateVector
    (memAddrSz, (Bit instrSz), (Var ((SyntaxKind (Vector ((Bit instrSz),
    memAddrSz))), imem_v)), (Var ((SyntaxKind (Bit memAddrSz)),
    next_load_instr_addr)), (Var ((SyntaxKind (Bit instrSz)),
    next_load_instr_data)))), (Var ((SyntaxKind (Vector ((Bit instrSz),
    memAddrSz))), imem_v)))), (fun next_imem -> Let_ ((SyntaxKind (Bit
    pTableIdxSz)), (ITE ((SyntaxKind (Bit pTableIdxSz)), (Var ((SyntaxKind
    Bool), wr_set_active_module)), (UniBit
    ((add pTableIdxSz (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
       0))))))))))))))))))))))))))), pTableIdxSz, (Trunc (pTableIdxSz,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))))))))))))))))))), (Var
    ((SyntaxKind (Bit wordSz)), data32)))), (Var ((SyntaxKind (Bit
    pTableIdxSz)), active_module_v)))), (fun next_active_module -> Let_
    ((SyntaxKind (Bit wordSz)), (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), wr_set_trap_vector)), (Var ((SyntaxKind (Bit
    wordSz)), data32)), (Var ((SyntaxKind (Bit wordSz)), trap_vector_v)))),
    (fun next_trap_vector -> WriteReg (('i'::('m'::('e'::('m'::[])))),
    (SyntaxKind (Vector ((Bit instrSz), memAddrSz))), (Var ((SyntaxKind
    (Vector ((Bit instrSz), memAddrSz))), next_imem)), (WriteReg
    (('b'::('u'::('s'::('_'::('l'::('o'::('a'::('d'::('_'::('i'::('n'::('s'::('t'::('r'::('_'::('a'::('d'::('d'::('r'::[]))))))))))))))))))),
    (SyntaxKind (Bit memAddrSz)), (Var ((SyntaxKind (Bit memAddrSz)),
    next_load_instr_addr)), (WriteReg
    (('b'::('u'::('s'::('_'::('l'::('o'::('a'::('d'::('_'::('i'::('n'::('s'::('t'::('r'::('_'::('d'::('a'::('t'::('a'::[]))))))))))))))))))),
    (SyntaxKind (Bit instrSz)), (Var ((SyntaxKind (Bit instrSz)),
    next_load_instr_data)), (WriteReg
    (('b'::('u'::('s'::('_'::('l'::('o'::('a'::('d'::('_'::('i'::('n'::('s'::('t'::('r'::('_'::('k'::('i'::('c'::('k'::[]))))))))))))))))))),
    (SyntaxKind Bool), (Var ((SyntaxKind Bool), next_load_instr_kick)),
    (WriteReg
    (('a'::('c'::('t'::('i'::('v'::('e'::('_'::('m'::('o'::('d'::('u'::('l'::('e'::[]))))))))))))),
    (SyntaxKind (Bit pTableIdxSz)), (Var ((SyntaxKind (Bit pTableIdxSz)),
    next_active_module)), (WriteReg
    (('t'::('r'::('a'::('p'::('_'::('v'::('e'::('c'::('t'::('o'::('r'::[]))))))))))),
    (SyntaxKind (Bit wordSz)), (Var ((SyntaxKind (Bit wordSz)),
    next_trap_vector)), (Return (UniBool (NegB, (Var ((SyntaxKind Bool),
    wr_any))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('B'::('i'::('a'::('n'::('c'::('h'::('i'::('A'::('l'::('a'::('r'::('m'::[])))))))))))))));
    attrType = (ExistT ({ arg = void; ret = Bool }, (fun _ _ -> ReadReg
    (('m'::('u'::('_'::('t'::('e'::('n'::('s'::('o'::('r'::[]))))))))),
    (SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), (fun t1 -> ReadReg
    (('m'::('u'::[])), (SyntaxKind (Bit wordSz)), (fun m -> Let_ ((SyntaxKind
    (Bit wordSz)), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (BinBit (wordSz, wordSz, wordSz, (Add wordSz), (BinBit
    (wordSz, wordSz, wordSz, (Add wordSz), (BinBit (wordSz, wordSz, wordSz,
    (Add wordSz), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (false, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (false, (Stdlib.Int.succ 0),
    (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (false, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (ReadIndex
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit ((Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (WS (true,
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), (WS (false,
    (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true, (Stdlib.Int.succ 0),
    (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind (Vector ((Bit wordSz),
    muTensorIdxSz))), t1)))))), (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (ConstBit ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (WS (false, (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)),
    (WS (true, (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var
    ((SyntaxKind (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))),
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))), (Bit wordSz), (Const ((Bit (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))), (ConstBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), (WS (true, (Stdlib.Int.succ (Stdlib.Int.succ 0)), (WS (true,
    (Stdlib.Int.succ 0), (WS (true, 0, WO)))))))))))), (Var ((SyntaxKind
    (Vector ((Bit wordSz), muTensorIdxSz))), t1)))))), (fun total -> Return
    (BinBitBool (wordSz, wordSz, (Lt wordSz), (Var ((SyntaxKind (Bit
    wordSz)), m)), (Var ((SyntaxKind (Bit wordSz)), total))))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('P'::('t'::('N'::('e'::('x'::('t'::('I'::('d'::[])))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('p'::('t'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))),
    (SyntaxKind (Bit pTableNextIdSz)), (fun v -> Let_ ((SyntaxKind (Bit
    wordSz)), (UniBit (pTableNextIdSz, wordSz, (ZeroExtendTrunc
    (pTableNextIdSz, wordSz)), (Var ((SyntaxKind (Bit pTableNextIdSz)),
    v)))), (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)),
    v32))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('P'::('t'::('S'::('i'::('z'::('e'::[])))))))));
    attrType = (ExistT ({ arg = (Bit pTableIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('p'::('t'::('T'::('a'::('b'::('l'::('e'::[]))))))), (SyntaxKind (Vector
    ((Bit wordSz), pTableIdxSz))), (fun pt_sizes_v -> Return (ReadIndex
    (pTableIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit pTableIdxSz)), idx)),
    (Var ((SyntaxKind (Vector ((Bit wordSz), pTableIdxSz))),
    pt_sizes_v))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('o'::('r'::('p'::('h'::('N'::('e'::('x'::('t'::('I'::('d'::[]))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))),
    (SyntaxKind (Bit morphTableNextIdSz)), (fun v -> Let_ ((SyntaxKind (Bit
    wordSz)), (UniBit (morphTableNextIdSz, wordSz, (ZeroExtendTrunc
    (morphTableNextIdSz, wordSz)), (Var ((SyntaxKind (Bit
    morphTableNextIdSz)), v)))), (fun v32 -> Return (Var ((SyntaxKind (Bit
    wordSz)), v32))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('o'::('r'::('p'::('h'::('S'::('r'::('c'::[])))))))))));
    attrType = (ExistT ({ arg = (Bit morphTableIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('s'::('r'::('c'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))),
    (SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))), (fun tbl ->
    Let_ ((SyntaxKind (Bit wordSz)), (UniBit (pTableIdxSz, wordSz,
    (ZeroExtendTrunc (pTableIdxSz, wordSz)), (ReadIndex (morphTableIdxSz,
    (Bit pTableIdxSz), (Var ((SyntaxKind (Bit morphTableIdxSz)), idx)), (Var
    ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))), tbl)))))),
    (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)), v32))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('o'::('r'::('p'::('h'::('D'::('s'::('t'::[])))))))))));
    attrType = (ExistT ({ arg = (Bit morphTableIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('d'::('s'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))),
    (SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))), (fun tbl ->
    Let_ ((SyntaxKind (Bit wordSz)), (UniBit (pTableIdxSz, wordSz,
    (ZeroExtendTrunc (pTableIdxSz, wordSz)), (ReadIndex (morphTableIdxSz,
    (Bit pTableIdxSz), (Var ((SyntaxKind (Bit morphTableIdxSz)), idx)), (Var
    ((SyntaxKind (Vector ((Bit pTableIdxSz), morphTableIdxSz))), tbl)))))),
    (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)), v32))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('o'::('r'::('p'::('h'::('C'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('D'::('e'::('s'::('c'::[]))))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit morphTableIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit descIdxSz), morphTableIdxSz))), (fun tbl ->
    Let_ ((SyntaxKind (Bit wordSz)), (UniBit (descIdxSz, wordSz,
    (ZeroExtendTrunc (descIdxSz, wordSz)), (ReadIndex (morphTableIdxSz, (Bit
    descIdxSz), (Var ((SyntaxKind (Bit morphTableIdxSz)), idx)), (Var
    ((SyntaxKind (Vector ((Bit descIdxSz), morphTableIdxSz))), tbl)))))),
    (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)), v32))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('o'::('r'::('p'::('h'::('V'::('a'::('l'::('i'::('d'::[])))))))))))));
    attrType = (ExistT ({ arg = (Bit morphTableIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))),
    (SyntaxKind (Vector (Bool, morphTableIdxSz))), (fun tbl -> Return (ITE
    ((SyntaxKind (Bit wordSz)), (ReadIndex (morphTableIdxSz, Bool, (Var
    ((SyntaxKind (Bit morphTableIdxSz)), idx)), (Var ((SyntaxKind (Vector
    (Bool, morphTableIdxSz))), tbl)))), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0)))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('M'::('o'::('r'::('p'::('h'::('I'::('d'::('e'::('n'::('t'::('i'::('t'::('y'::[]))))))))))))))));
    attrType = (ExistT ({ arg = (Bit morphTableIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('m'::('o'::('r'::('p'::('h'::('_'::('i'::('d'::('e'::('n'::('t'::('i'::('t'::('y'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))),
    (SyntaxKind (Vector (Bool, morphTableIdxSz))), (fun tbl -> Return (ITE
    ((SyntaxKind (Bit wordSz)), (ReadIndex (morphTableIdxSz, Bool, (Var
    ((SyntaxKind (Bit morphTableIdxSz)), idx)), (Var ((SyntaxKind (Vector
    (Bool, morphTableIdxSz))), tbl)))), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0)))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('D'::('e'::('s'::('c'::('B'::('a'::('s'::('e'::[])))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit couplingDescIdxSz); ret = (Bit
    wordSz) }, (fun _ idx -> ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('b'::('a'::('s'::('e'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit couplingPairIdxSz), couplingDescIdxSz))),
    (fun tbl -> Let_ ((SyntaxKind (Bit wordSz)), (UniBit (couplingPairIdxSz,
    wordSz, (ZeroExtendTrunc (couplingPairIdxSz, wordSz)), (ReadIndex
    (couplingDescIdxSz, (Bit couplingPairIdxSz), (Var ((SyntaxKind (Bit
    couplingDescIdxSz)), idx)), (Var ((SyntaxKind (Vector ((Bit
    couplingPairIdxSz), couplingDescIdxSz))), tbl)))))), (fun v32 -> Return
    (Var ((SyntaxKind (Bit wordSz)), v32))))))))) }), (ConsInModule ((MEMeth
    { attrName =
    ('g'::('e'::('t'::('C'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('D'::('e'::('s'::('c'::('C'::('o'::('u'::('n'::('t'::[]))))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit couplingDescIdxSz); ret = (Bit
    wordSz) }, (fun _ idx -> ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('c'::('o'::('u'::('n'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit couplingPairCountSz), couplingDescIdxSz))),
    (fun tbl -> Let_ ((SyntaxKind (Bit wordSz)), (UniBit
    (couplingPairCountSz, wordSz, (ZeroExtendTrunc (couplingPairCountSz,
    wordSz)), (ReadIndex (couplingDescIdxSz, (Bit couplingPairCountSz), (Var
    ((SyntaxKind (Bit couplingDescIdxSz)), idx)), (Var ((SyntaxKind (Vector
    ((Bit couplingPairCountSz), couplingDescIdxSz))), tbl)))))), (fun v32 ->
    Return (Var ((SyntaxKind (Bit wordSz)), v32))))))))) }), (ConsInModule
    ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('D'::('e'::('s'::('c'::('V'::('a'::('l'::('i'::('d'::[]))))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit couplingDescIdxSz); ret = (Bit
    wordSz) }, (fun _ idx -> ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))),
    (SyntaxKind (Vector (Bool, couplingDescIdxSz))), (fun tbl -> Return (ITE
    ((SyntaxKind (Bit wordSz)), (ReadIndex (couplingDescIdxSz, Bool, (Var
    ((SyntaxKind (Bit couplingDescIdxSz)), idx)), (Var ((SyntaxKind (Vector
    (Bool, couplingDescIdxSz))), tbl)))), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0)))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('D'::('e'::('s'::('c'::('N'::('e'::('x'::('t'::('I'::('d'::[])))))))))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('d'::('e'::('s'::('c'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))))))))))),
    (SyntaxKind (Bit descTableNextIdSz)), (fun v -> Let_ ((SyntaxKind (Bit
    wordSz)), (UniBit (descTableNextIdSz, wordSz, (ZeroExtendTrunc
    (descTableNextIdSz, wordSz)), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    v)))), (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)),
    v32))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('P'::('a'::('i'::('r'::('S'::('r'::('c'::[]))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit couplingPairIdxSz); ret = (Bit
    wordSz) }, (fun _ idx -> ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('p'::('a'::('i'::('r'::('_'::('s'::('r'::('c'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit wordSz), couplingPairIdxSz))), (fun tbl ->
    Return (ReadIndex (couplingPairIdxSz, (Bit wordSz), (Var ((SyntaxKind
    (Bit couplingPairIdxSz)), idx)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    couplingPairIdxSz))), tbl))))))))) }), (ConsInModule ((MEMeth
    { attrName =
    ('g'::('e'::('t'::('C'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('P'::('a'::('i'::('r'::('D'::('s'::('t'::[]))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit couplingPairIdxSz); ret = (Bit
    wordSz) }, (fun _ idx -> ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('p'::('a'::('i'::('r'::('_'::('d'::('s'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit wordSz), couplingPairIdxSz))), (fun tbl ->
    Return (ReadIndex (couplingPairIdxSz, (Bit wordSz), (Var ((SyntaxKind
    (Bit couplingPairIdxSz)), idx)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    couplingPairIdxSz))), tbl))))))))) }), (ConsInModule ((MEMeth
    { attrName =
    ('g'::('e'::('t'::('C'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('P'::('a'::('i'::('r'::('V'::('a'::('l'::('i'::('d'::[]))))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit couplingPairIdxSz); ret = (Bit
    wordSz) }, (fun _ idx -> ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('p'::('a'::('i'::('r'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))))),
    (SyntaxKind (Vector (Bool, couplingPairIdxSz))), (fun tbl -> Return (ITE
    ((SyntaxKind (Bit wordSz)), (ReadIndex (couplingPairIdxSz, Bool, (Var
    ((SyntaxKind (Bit couplingPairIdxSz)), idx)), (Var ((SyntaxKind (Vector
    (Bool, couplingPairIdxSz))), tbl)))), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0)))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('P'::('a'::('i'::('r'::('N'::('e'::('x'::('t'::('I'::('d'::[])))))))))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('c'::('o'::('u'::('p'::('l'::('i'::('n'::('g'::('_'::('p'::('a'::('i'::('r'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))))))))))),
    (SyntaxKind (Bit descTableNextIdSz)), (fun v -> Let_ ((SyntaxKind (Bit
    wordSz)), (UniBit (descTableNextIdSz, wordSz, (ZeroExtendTrunc
    (descTableNextIdSz, wordSz)), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    v)))), (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)),
    v32))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('F'::('o'::('r'::('m'::('u'::('l'::('a'::('D'::('e'::('s'::('c'::('B'::('a'::('s'::('e'::[]))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit formulaDescIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('f'::('o'::('r'::('m'::('u'::('l'::('a'::('_'::('d'::('e'::('s'::('c'::('_'::('b'::('a'::('s'::('e'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit wordSz), formulaDescIdxSz))), (fun tbl ->
    Return (ReadIndex (formulaDescIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit
    formulaDescIdxSz)), idx)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    formulaDescIdxSz))), tbl))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('F'::('o'::('r'::('m'::('u'::('l'::('a'::('D'::('e'::('s'::('c'::('C'::('o'::('u'::('n'::('t'::[])))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit formulaDescIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('f'::('o'::('r'::('m'::('u'::('l'::('a'::('_'::('d'::('e'::('s'::('c'::('_'::('c'::('o'::('u'::('n'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit wordSz), formulaDescIdxSz))), (fun tbl ->
    Return (ReadIndex (formulaDescIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit
    formulaDescIdxSz)), idx)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    formulaDescIdxSz))), tbl))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('F'::('o'::('r'::('m'::('u'::('l'::('a'::('D'::('e'::('s'::('c'::('V'::('a'::('l'::('i'::('d'::[])))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit formulaDescIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('f'::('o'::('r'::('m'::('u'::('l'::('a'::('_'::('d'::('e'::('s'::('c'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))),
    (SyntaxKind (Vector (Bool, formulaDescIdxSz))), (fun tbl -> Return (ITE
    ((SyntaxKind (Bit wordSz)), (ReadIndex (formulaDescIdxSz, Bool, (Var
    ((SyntaxKind (Bit formulaDescIdxSz)), idx)), (Var ((SyntaxKind (Vector
    (Bool, formulaDescIdxSz))), tbl)))), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0)))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('F'::('o'::('r'::('m'::('u'::('l'::('a'::('D'::('e'::('s'::('c'::('N'::('e'::('x'::('t'::('I'::('d'::[]))))))))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('f'::('o'::('r'::('m'::('u'::('l'::('a'::('_'::('d'::('e'::('s'::('c'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[])))))))))))))))))))),
    (SyntaxKind (Bit descTableNextIdSz)), (fun v -> Let_ ((SyntaxKind (Bit
    wordSz)), (UniBit (descTableNextIdSz, wordSz, (ZeroExtendTrunc
    (descTableNextIdSz, wordSz)), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    v)))), (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)),
    v32))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('e'::('r'::('t'::('D'::('e'::('s'::('c'::('B'::('a'::('s'::('e'::[])))))))))))))));
    attrType = (ExistT ({ arg = (Bit certDescIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('c'::('e'::('r'::('t'::('_'::('d'::('e'::('s'::('c'::('_'::('b'::('a'::('s'::('e'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))),
    (SyntaxKind (Vector ((Bit wordSz), certDescIdxSz))), (fun tbl -> Return
    (ReadIndex (certDescIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit
    certDescIdxSz)), idx)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    certDescIdxSz))), tbl))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('e'::('r'::('t'::('D'::('e'::('s'::('c'::('C'::('o'::('u'::('n'::('t'::[]))))))))))))))));
    attrType = (ExistT ({ arg = (Bit certDescIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('c'::('e'::('r'::('t'::('_'::('d'::('e'::('s'::('c'::('_'::('c'::('o'::('u'::('n'::('t'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit wordSz), certDescIdxSz))), (fun tbl -> Return
    (ReadIndex (certDescIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit
    certDescIdxSz)), idx)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    certDescIdxSz))), tbl))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('e'::('r'::('t'::('D'::('e'::('s'::('c'::('V'::('a'::('l'::('i'::('d'::[]))))))))))))))));
    attrType = (ExistT ({ arg = (Bit certDescIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('c'::('e'::('r'::('t'::('_'::('d'::('e'::('s'::('c'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))),
    (SyntaxKind (Vector (Bool, certDescIdxSz))), (fun tbl -> Return (ITE
    ((SyntaxKind (Bit wordSz)), (ReadIndex (certDescIdxSz, Bool, (Var
    ((SyntaxKind (Bit certDescIdxSz)), idx)), (Var ((SyntaxKind (Vector
    (Bool, certDescIdxSz))), tbl)))), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0)))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('C'::('e'::('r'::('t'::('D'::('e'::('s'::('c'::('N'::('e'::('x'::('t'::('I'::('d'::[])))))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('c'::('e'::('r'::('t'::('_'::('d'::('e'::('s'::('c'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))))))),
    (SyntaxKind (Bit descTableNextIdSz)), (fun v -> Let_ ((SyntaxKind (Bit
    wordSz)), (UniBit (descTableNextIdSz, wordSz, (ZeroExtendTrunc
    (descTableNextIdSz, wordSz)), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    v)))), (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)),
    v32))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('D'::('e'::('s'::('c'::('M'::('e'::('t'::('a'::('S'::('u'::('b'::('t'::('y'::('p'::('e'::[]))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit descMetaIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('s'::('u'::('b'::('t'::('y'::('p'::('e'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit formatSubtypeSz), descMetaIdxSz))), (fun tbl ->
    Let_ ((SyntaxKind (Bit wordSz)), (UniBit (formatSubtypeSz, wordSz,
    (ZeroExtendTrunc (formatSubtypeSz, wordSz)), (ReadIndex (descMetaIdxSz,
    (Bit formatSubtypeSz), (Var ((SyntaxKind (Bit descMetaIdxSz)), idx)),
    (Var ((SyntaxKind (Vector ((Bit formatSubtypeSz), descMetaIdxSz))),
    tbl)))))), (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)),
    v32))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('D'::('e'::('s'::('c'::('M'::('e'::('t'::('a'::('K'::('i'::('n'::('d'::[])))))))))))))));
    attrType = (ExistT ({ arg = (Bit descMetaIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('k'::('i'::('n'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))),
    (SyntaxKind (Vector ((Bit descKindFieldSz), descMetaIdxSz))), (fun tbl ->
    Let_ ((SyntaxKind (Bit wordSz)), (UniBit (descKindFieldSz, wordSz,
    (ZeroExtendTrunc (descKindFieldSz, wordSz)), (ReadIndex (descMetaIdxSz,
    (Bit descKindFieldSz), (Var ((SyntaxKind (Bit descMetaIdxSz)), idx)),
    (Var ((SyntaxKind (Vector ((Bit descKindFieldSz), descMetaIdxSz))),
    tbl)))))), (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)),
    v32))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('D'::('e'::('s'::('c'::('M'::('e'::('t'::('a'::('I'::('n'::('l'::('i'::('n'::('e'::('L'::('e'::('n'::[]))))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit descMetaIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('i'::('n'::('l'::('i'::('n'::('e'::('_'::('l'::('e'::('n'::('_'::('t'::('a'::('b'::('l'::('e'::[])))))))))))))))))))))))))),
    (SyntaxKind (Vector ((Bit inlineLenSz), descMetaIdxSz))), (fun tbl ->
    Let_ ((SyntaxKind (Bit wordSz)), (UniBit (inlineLenSz, wordSz,
    (ZeroExtendTrunc (inlineLenSz, wordSz)), (ReadIndex (descMetaIdxSz, (Bit
    inlineLenSz), (Var ((SyntaxKind (Bit descMetaIdxSz)), idx)), (Var
    ((SyntaxKind (Vector ((Bit inlineLenSz), descMetaIdxSz))), tbl)))))),
    (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)), v32))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('D'::('e'::('s'::('c'::('M'::('e'::('t'::('a'::('A'::('u'::('x'::[]))))))))))))));
    attrType = (ExistT ({ arg = (Bit descMetaIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('a'::('u'::('x'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))),
    (SyntaxKind (Vector ((Bit wordSz), descMetaIdxSz))), (fun tbl -> Return
    (ReadIndex (descMetaIdxSz, (Bit wordSz), (Var ((SyntaxKind (Bit
    descMetaIdxSz)), idx)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    descMetaIdxSz))), tbl))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('D'::('e'::('s'::('c'::('M'::('e'::('t'::('a'::('V'::('a'::('l'::('i'::('d'::[]))))))))))))))));
    attrType = (ExistT ({ arg = (Bit descMetaIdxSz); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('v'::('a'::('l'::('i'::('d'::('_'::('t'::('a'::('b'::('l'::('e'::[]))))))))))))))))))))),
    (SyntaxKind (Vector (Bool, descMetaIdxSz))), (fun tbl -> Return (ITE
    ((SyntaxKind (Bit wordSz)), (ReadIndex (descMetaIdxSz, Bool, (Var
    ((SyntaxKind (Bit descMetaIdxSz)), idx)), (Var ((SyntaxKind (Vector
    (Bool, descMetaIdxSz))), tbl)))), (Const ((Bit wordSz), (ConstBit
    (wordSz, (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit
    wordSz), (ConstBit (wordSz, (natToWord wordSz 0)))))))))))) }),
    (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('D'::('e'::('s'::('c'::('M'::('e'::('t'::('a'::('N'::('e'::('x'::('t'::('I'::('d'::[])))))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('d'::('e'::('s'::('c'::('_'::('m'::('e'::('t'::('a'::('_'::('n'::('e'::('x'::('t'::('_'::('i'::('d'::[]))))))))))))))))),
    (SyntaxKind (Bit descTableNextIdSz)), (fun v -> Let_ ((SyntaxKind (Bit
    wordSz)), (UniBit (descTableNextIdSz, wordSz, (ZeroExtendTrunc
    (descTableNextIdSz, wordSz)), (Var ((SyntaxKind (Bit descTableNextIdSz)),
    v)))), (fun v32 -> Return (Var ((SyntaxKind (Bit wordSz)),
    v32))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('P'::('h'::('a'::('s'::('e'::[])))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('p'::('h'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))), (fun v -> Let_ ((SyntaxKind (Bit wordSz)), (UniBit
    ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))), wordSz,
    (ZeroExtendTrunc ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))), wordSz)), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0))))), v)))), (fun v32 -> Return (Var ((SyntaxKind (Bit
    wordSz)), v32))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('K'::('i'::('n'::('d'::[]))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('k'::('i'::('n'::('d'::[])))))))))))),
    (SyntaxKind Bool), (fun v -> Return (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz 0)))))))))))) }), (ConsInModule
    ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('F'::('B'::('a'::('s'::('e'::[])))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('b'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('C'::('B'::('a'::('s'::('e'::[])))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('b'::('a'::('s'::('e'::[]))))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('F'::('L'::('e'::('n'::[]))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('l'::('e'::('n'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('C'::('L'::('e'::('n'::[]))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('l'::('e'::('n'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('F'::('P'::('t'::('r'::[]))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('p'::('t'::('r'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('C'::('P'::('t'::('r'::[]))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('p'::('t'::('r'::[])))))))))))),
    (SyntaxKind (Bit wordSz)), (fun v -> Return (Var ((SyntaxKind (Bit
    wordSz)), v))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('C'::('l'::('a'::('u'::('s'::('e'::('S'::('a'::('t'::[])))))))))))))))))));
    attrType = (ExistT ({ arg = void; ret = (Bit wordSz) }, (fun _ _ ->
    ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('l'::('a'::('u'::('s'::('e'::('_'::('s'::('a'::('t'::[])))))))))))))))))),
    (SyntaxKind Bool), (fun v -> Return (ITE ((SyntaxKind (Bit wordSz)), (Var
    ((SyntaxKind Bool), v)), (Const ((Bit wordSz), (ConstBit (wordSz,
    (natToWord wordSz (Stdlib.Int.succ 0)))))), (Const ((Bit wordSz),
    (ConstBit (wordSz, (natToWord wordSz 0)))))))))))) }), (ConsInModule
    ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('F'::('b'::('u'::('f'::('W'::('o'::('r'::('d'::[]))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))); ret = (Bit wordSz) },
    (fun _ idx -> ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('f'::('b'::('u'::('f'::[])))))))))))),
    (SyntaxKind (Vector ((Bit wordSz), (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), (fun tbl -> Return
    (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ 0)))))))), (Bit wordSz), (Var ((SyntaxKind (Bit
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))), idx)), (Var ((SyntaxKind (Vector ((Bit wordSz),
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0))))))))))), tbl))))))))) }), (ConsInModule ((MEMeth { attrName =
    ('g'::('e'::('t'::('L'::('a'::('s'::('s'::('e'::('r'::('t'::('C'::('b'::('u'::('f'::('W'::('o'::('r'::('d'::[]))))))))))))))))));
    attrType = (ExistT ({ arg = (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))); ret =
    (Bit wordSz) }, (fun _ idx -> ReadReg
    (('l'::('a'::('s'::('s'::('e'::('r'::('t'::('_'::('c'::('b'::('u'::('f'::[])))))))))))),
    (SyntaxKind (Vector ((Bit wordSz), (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0)))))))))))),
    (fun tbl -> Return (ReadIndex ((Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))), (Bit
    wordSz), (Var ((SyntaxKind (Bit (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ 0))))))))))), idx)),
    (Var ((SyntaxKind (Vector ((Bit wordSz), (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ (Stdlib.Int.succ
    0)))))))))))), tbl))))))))) }),
    NilInModule))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val thieleCoreS : modulesS **)

let thieleCoreS =
  getModuleS thieleCore

(** val thieleCoreB : bModule list option **)

let thieleCoreB =
  modulesSToBModules thieleCoreS

(** val thieleBusTopB : bModule list option **)

let thieleBusTopB =
  thieleCoreB

(** val canonical_cpu_module : bModule list option **)

let canonical_cpu_module =
  thieleBusTopB

(** val targetB : int -> bModule list option **)

let targetB _ =
  canonical_cpu_module
