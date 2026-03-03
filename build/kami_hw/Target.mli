
type __ = Obj.t

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

val pred : int -> int

val add : int -> int -> int

val mul : int -> int -> int

val eqb : int -> int -> bool

val pow : int -> int -> int

val tail_add : int -> int -> int

val tail_addmul : int -> int -> int -> int

val tail_mul : int -> int -> int

val of_uint_acc : uint -> int -> int

val of_uint : uint -> int

val of_hex_uint_acc : uint0 -> int -> int

val of_hex_uint : uint0 -> int

val of_num_uint : uint1 -> int

val eqb0 : bool -> bool -> bool

module Nat :
 sig
  val div2 : int -> int
 end

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

type t =
| F1 of int
| FS of int * t

type 'a t0 =
| Nil1
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

val pTableIdxSz : int

val pTableNextIdSz : int

val aCTIVE_MODULE_INIT : word

val pT_NEXT_ID_INIT : word

val eRR_CHSH_VAL : word

val eRR_BIANCHI_VAL : word

val eRR_LOGIC_VAL : word

val eRR_LOCALITY_VAL : word

val eRR_PARTITION_VAL : word

val lOGIC_GATE_KEY : word

val tRAP_VEC_INIT : word

val mSTATUS_TURING : word

val mSTATUS_THIELE : word

val cHSH_X1_SURCHARGE : word

val oP_PNEW : word

val oP_PSPLIT : word

val oP_PMERGE : word

val oP_LASSERT : word

val oP_LJOIN : word

val oP_MDLACC : word

val oP_PDISCOVER : word

val oP_XFER : word

val oP_LOAD_IMM : word

val oP_CHSH_TRIAL : word

val oP_XOR_LOAD : word

val oP_XOR_ADD : word

val oP_XOR_SWAP : word

val oP_XOR_RANK : word

val oP_EMIT : word

val oP_REVEAL : word

val oP_ORACLE_HALTS : word

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

val logicRespPort : kind attribute t0

val aPBBusWritePort : kind attribute t0

val sP_IDX : word

val check_bounds : 'a1 expr -> 'a1 expr -> 'a1 expr

val mem_read_tree_aux : int -> int -> 'a1 expr -> 'a1 expr -> 'a1 expr

val read_mem : 'a1 expr -> 'a1 expr -> 'a1 expr

val mem_write_tree_aux :
  int -> int -> 'a1 expr -> 'a1 expr -> 'a1 expr -> 'a1 expr

val write_mem : 'a1 expr -> 'a1 expr -> 'a1 expr -> 'a1 expr

val thieleCore : modules

val thieleCoreS : modulesS

val thieleCoreB : bModule list option

type moduleID = int

type vMAxiom = char list

type axiomSet = vMAxiom list

type moduleState = { module_region : int list; module_axioms : axiomSet }

type partitionGraph = { pg_next_id : moduleID;
                        pg_modules : (moduleID * moduleState) list }

type cSRState = { csr_cert_addr : int; csr_status : int; csr_err : int }

type vMState = { vm_graph : partitionGraph; vm_csrs : cSRState;
                 vm_regs : int list; vm_mem : int list; vm_pc : int;
                 vm_mu : int; vm_mu_tensor : int list; vm_err : bool }

type kamiSnapshot = { snap_pc : int; snap_mu : int; snap_err : bool;
                      snap_halted : bool; snap_regs : (int -> int);
                      snap_mem : (int -> int); snap_partition_ops : int;
                      snap_mdl_ops : int; snap_info_gain : int;
                      snap_error_code : int; snap_mu_tensor : (int -> int);
                      snap_pt_sizes : (int -> int); snap_pt_next_id : 
                      int }

val snapshot_regs_to_list : (int -> int) -> int list

val snapshot_mem_to_list : (int -> int) -> int list

val snapshot_tensor_to_list : (int -> int) -> int list

val default_csrs : cSRState

val filtermap : ('a1 -> 'a2 option) -> 'a1 list -> 'a2 list

val snap_pt_to_graph : int -> (int -> int) -> partitionGraph

val abs_phase1 : kamiSnapshot -> vMState

type busReg =
| BusRegPc
| BusRegMu
| BusRegErr
| BusRegHalted
| BusRegPartitionOps
| BusRegMdlOps
| BusRegInfoGain
| BusRegErrorCode
| BusRegMstatus
| BusRegMcycleLo
| BusRegMcycleHi
| BusRegMinstretLo
| BusRegMinstretHi
| BusRegLogicAcc
| BusRegLogicReqValid
| BusRegLogicReqOpcode
| BusRegLogicReqPayload
| BusRegMuTensor0
| BusRegMuTensor1
| BusRegMuTensor2
| BusRegMuTensor3
| BusRegBianchiAlarm
| BusRegPtNextId
| BusRegPtSize
| BusRegLoadInstrAddr
| BusRegLoadInstrData
| BusRegLoadInstrKick
| BusRegSetLogicRespValid
| BusRegSetLogicRespError
| BusRegSetLogicRespValue
| BusRegSetActiveModule
| BusRegSetTrapVector

val decodeBusReg : int -> busReg option

val busRegReadable : busReg -> bool

val busRegWritable : busReg -> bool

type busCoreView = { view_pc : int; view_mu : int; view_err : bool;
                     view_halted : bool; view_partition_ops : int;
                     view_mdl_ops : int; view_info_gain : int;
                     view_error_code : int; view_mstatus : int;
                     view_mcycle_lo : int; view_mcycle_hi : int;
                     view_minstret_lo : int; view_minstret_hi : int;
                     view_logic_acc : int; view_logic_req_valid : bool;
                     view_logic_req_opcode : int;
                     view_logic_req_payload : int; view_mu_tensor0 : 
                     int; view_mu_tensor1 : int; view_mu_tensor2 : int;
                     view_mu_tensor3 : int; view_bianchi_alarm : bool;
                     view_pt_next_id : int; view_pt_size : (int -> int) }

val bool_to_nat : bool -> int

val busRegReadValue : busCoreView -> busReg -> int option

val busRead : busCoreView -> int -> int option

type busShadowRegs = { sh_load_instr_addr : int; sh_load_instr_data : 
                       int; sh_load_instr_kick : bool;
                       sh_logic_resp_valid : bool;
                       sh_logic_resp_error : bool; sh_logic_resp_value : 
                       int; sh_active_module : int; sh_trap_vector : 
                       int }

type busWrapperState = { bw_core : kamiSnapshot; bw_shadow : busShadowRegs }

val busWriteShadow : busShadowRegs -> busReg -> int -> busShadowRegs

val busWrite : busWrapperState -> int -> int -> busWrapperState

val coreViewOfSnapshot : kamiSnapshot -> busCoreView

type busOp =
| BusOpRead of int
| BusOpWrite of int * int

val bus_step : busWrapperState -> busOp -> busWrapperState

val thieleBusTopB : bModule list option

val canonical_cpu_module : bModule list option

val canonical_snapshot_to_vm : kamiSnapshot -> vMState

type canonical_refinement_relation = __
