
type __ = Obj.t

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val pred : int -> int

val add : int -> int -> int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val div2 : int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

type t =
| F1 of int
| FS of int * t

type 'a t0 =
| Nil
| Cons of 'a * int * 'a t0

val nth : int -> 'a1 t0 -> t -> 'a1

val map0 : ('a1 -> 'a2) -> int -> 'a1 t0 -> 'a2 t0

val ascii_eq : char -> char -> bool

val string_eq : char list -> char list -> bool

val mod2 : int -> bool

type word =
| WO
| WS of bool * int * word

val natToWord : int -> int -> word

val wzero : int -> word

type 'a attribute = { attrName : char list; attrType : 'a }

val vector_find' : ('a1 -> bool) -> int -> 'a1 t0 -> __

val vector_find : ('a1 -> bool) -> int -> 'a1 t0 -> t

type ('a, 'b) ilist =
| Inil
| Icons of 'a * int * 'a t0 * 'b * ('a, 'b) ilist

type 'a vec =
| Vec0 of 'a
| VecNext of int * 'a vec * 'a vec

val replicate : 'a1 -> int -> 'a1 vec

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

val vector_repeat : int -> 'a1 -> 'a1 t0

val getDefaultConst : kind -> constT

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

val fieldKind : int -> kind attribute t0 -> t -> kind

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

val void : kind

type primitiveModule = { pm_name : char list; pm_regInits : regInitT list;
                         pm_rules : action attribute list;
                         pm_methods : defMethT list }

type modules =
| PrimMod of primitiveModule
| Mod of regInitT list * action attribute list * defMethT list
| ConcatMod of modules * modules

val fieldAccessor : char list -> 'a1 attribute -> bool

type moduleElt =
| MERegister of regInitT
| MERule of action attribute
| MEMeth of defMethT

type inModule =
| NilInModule
| ConsInModule of moduleElt * inModule

val makeModule' :
  inModule -> (regInitT list * action attribute list) * defMethT list

val makeModule : inModule -> modules

val makeConst : kind -> constT -> constFullT

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

val getActionS : int -> kind -> tyS actionT -> int * actionS

type methodTS = actionS

type defMethTS = (signatureT, methodTS) sigT attribute

type modulesS =
| PrimModS of char list * signatureT attribute list
| ModS of regInitT list * actionS attribute list * defMethTS list
| ConcatModsS of modulesS * modulesS

val getMethS : (signatureT, methodT) sigT -> (signatureT, methodTS) sigT

val getModuleS : modules -> modulesS

val mapVec : ('a1 -> 'a2) -> int -> 'a1 vec -> 'a2 vec

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

val bind : 'a1 option -> ('a1 -> 'a2 option) -> 'a2 option

val bindVec : int -> 'a1 option vec -> 'a1 vec option

val bindVector : int -> 'a1 option t0 -> 'a1 t0 option

val exprSToBExpr : fullKind -> exprS -> bExpr option

val actionSToBAction : kind -> actionS -> bAction list option

val rulesToBRules :
  actionS attribute list -> bAction list attribute list option

val methsToBMethods : defMethTS list -> bMethod list option

val modulesSToBModules : modulesS -> bModule list option

val regIdxSz : int

val memAddrSz : int

val wordSz : int

val opcodeSz : int

val costSz : int

val muTensorIdxSz : int

val eRR_CHSH_VAL : word

val eRR_BIANCHI_VAL : word

val oP_PNEW : word

val oP_PSPLIT : word

val oP_PMERGE : word

val oP_MDLACC : word

val oP_PDISCOVER : word

val oP_XFER : word

val oP_LOAD_IMM : word

val oP_XOR_LOAD : word

val oP_XOR_ADD : word

val oP_XOR_SWAP : word

val oP_XOR_RANK : word

val oP_EMIT : word

val oP_REVEAL : word

val oP_LOAD : word

val oP_STORE : word

val oP_ADD : word

val oP_SUB : word

val oP_JUMP : word

val oP_JNEZ : word

val oP_CALL : word

val oP_RET : word

val oP_HALT : word

val instrSz : int

val loadInstrPort : kind attribute t0

val sP_IDX : word

val thieleCore : modules

val thieleCoreS : modulesS

val thieleCoreB : bModule list option
