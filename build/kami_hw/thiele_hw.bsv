import Vector::*;
import BuildVector::*;
import RegFile::*;
import RegFileZero::*;
import FIFO::*;
import FIFOF::*;
import MulDiv::*;
import SpecialFIFOs::*;
typedef struct { Bit#(7) addr; Bit#(128) data;  } Struct1 deriving(Eq, Bits);
typedef struct { Bit#(32) addr; Bit#(128) data;  } Struct2 deriving(Eq, Bits);

interface Module1;
    method Action loadInstr (Struct1 x_0);
    method ActionValue#(Bit#(32)) getPC ();
    method ActionValue#(Bit#(32)) getMu ();
    method ActionValue#(Bool) getErr ();
    method ActionValue#(Bool) getHalted ();
    method ActionValue#(Bool) getCertified ();
    method ActionValue#(Bit#(32)) getWcSame00 ();
    method ActionValue#(Bit#(32)) getWcDiff00 ();
    method ActionValue#(Bit#(32)) getWcSame01 ();
    method ActionValue#(Bit#(32)) getWcDiff01 ();
    method ActionValue#(Bit#(32)) getWcSame10 ();
    method ActionValue#(Bit#(32)) getWcDiff10 ();
    method ActionValue#(Bit#(32)) getWcSame11 ();
    method ActionValue#(Bit#(32)) getWcDiff11 ();
    method ActionValue#(Bit#(32)) getPartitionOps ();
    method ActionValue#(Bit#(32)) getMdlOps ();
    method ActionValue#(Bit#(32)) getInfoGain ();
    method ActionValue#(Bit#(32)) getErrorCode ();
    method ActionValue#(Bit#(32)) getMstatus ();
    method ActionValue#(Bit#(32)) getMcycleLo ();
    method ActionValue#(Bit#(32)) getMcycleHi ();
    method ActionValue#(Bit#(32)) getMinstretLo ();
    method ActionValue#(Bit#(32)) getMinstretHi ();
    method ActionValue#(Bit#(32)) getLogicAcc ();
    method ActionValue#(Bit#(32)) getCertAddr ();
    method ActionValue#(Bit#(32)) getMuTensor0 ();
    method ActionValue#(Bit#(32)) getMuTensor1 ();
    method ActionValue#(Bit#(32)) getMuTensor2 ();
    method ActionValue#(Bit#(32)) getMuTensor3 ();
    method Action setActiveModule (Bit#(6) x_0);
    method Action setTrapVector (Bit#(32) x_0);
    method ActionValue#(Bit#(32)) apbReadData (Bit#(32) x_0);
    method ActionValue#(Bool) apbReadErr (Bit#(32) x_0);
    method ActionValue#(Bool) apbWrite (Struct2 x_0);
    method ActionValue#(Bool) getBianchiAlarm ();
    method ActionValue#(Bit#(32)) getPtNextId ();
    method ActionValue#(Bit#(32)) getPtSize (Bit#(6) x_0);
    method ActionValue#(Bit#(32)) getMorphNextId ();
    method ActionValue#(Bit#(32)) getMorphSrc (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getMorphDst (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getMorphCouplingDesc (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getMorphValid (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getMorphIdentity (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getCouplingDescBase (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getCouplingDescCount (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getCouplingDescValid (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getCouplingDescNextId ();
    method ActionValue#(Bit#(32)) getCouplingPairSrc (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getCouplingPairDst (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getCouplingPairValid (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getCouplingPairNextId ();
    method ActionValue#(Bit#(32)) getFormulaDescBase (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getFormulaDescCount (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getFormulaDescValid (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getFormulaDescNextId ();
    method ActionValue#(Bit#(32)) getCertDescBase (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getCertDescCount (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getCertDescValid (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getCertDescNextId ();
    method ActionValue#(Bit#(32)) getDescMetaSubtype (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getDescMetaKind (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getDescMetaInlineLen (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getDescMetaAux (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getDescMetaValid (Bit#(4) x_0);
    method ActionValue#(Bit#(32)) getDescMetaNextId ();
    method ActionValue#(Bit#(32)) getLassertPhase ();
    method ActionValue#(Bit#(32)) getLassertKind ();
    method ActionValue#(Bit#(32)) getLassertFBase ();
    method ActionValue#(Bit#(32)) getLassertCBase ();
    method ActionValue#(Bit#(32)) getLassertFLen ();
    method ActionValue#(Bit#(32)) getLassertCLen ();
    method ActionValue#(Bit#(32)) getLassertFPtr ();
    method ActionValue#(Bit#(32)) getLassertCPtr ();
    method ActionValue#(Bit#(32)) getLassertClauseSat ();
    method ActionValue#(Bit#(32)) getLassertFbufWord (Bit#(6) x_0);
    method ActionValue#(Bit#(32)) getLassertCbufWord (Bit#(6) x_0);
    
endinterface

module mkModule1 (Module1);
    Reg#(Bit#(32)) pc <- mkReg(unpack(0));
    Reg#(Bit#(32)) mu <- mkReg(unpack(0));Reg#(Bool) err <- mkReg(False);
    Reg#(Bool) halted <- mkReg(False);
    Reg#(Vector#(16, Bit#(32))) regs <- mkReg(unpack(0));
    Reg#(Vector#(128, Bit#(32))) mem <- mkReg(unpack(0));
    Reg#(Vector#(128, Bit#(128))) imem <- mkReg(unpack(0));
    Reg#(Bit#(32)) partition_ops <- mkReg(unpack(0));
    Reg#(Bit#(32)) mdl_ops <- mkReg(unpack(0));
    Reg#(Bit#(32)) info_gain <- mkReg(unpack(0));
    Reg#(Bit#(32)) error_code <- mkReg(unpack(0));
    Reg#(Bit#(32)) logic_acc <- mkReg(unpack(0));
    Reg#(Bit#(32)) cert_addr <- mkReg(unpack(0));
    Reg#(Bit#(6)) active_module <- mkReg(6'h1);
    Reg#(Bit#(32)) mstatus <- mkReg(32'h1);
    Reg#(Bit#(32)) mcycle_lo <- mkReg(unpack(0));
    Reg#(Bit#(32)) mcycle_hi <- mkReg(unpack(0));
    Reg#(Bit#(32)) minstret_lo <- mkReg(unpack(0));
    Reg#(Bit#(32)) minstret_hi <- mkReg(unpack(0));
    Reg#(Bit#(32)) trap_vector <- mkReg(32'hf00);
    Reg#(Bool) certified <- mkReg(False);
    Reg#(Bit#(3)) lassert_phase <- mkReg(unpack(0));
    Reg#(Bool) lassert_kind <- mkReg(False);
    Reg#(Bit#(32)) lassert_fbase <- mkReg(unpack(0));
    Reg#(Bit#(32)) lassert_cbase <- mkReg(unpack(0));
    Reg#(Bit#(32)) lassert_flen <- mkReg(unpack(0));
    Reg#(Bit#(32)) lassert_clen <- mkReg(unpack(0));
    Reg#(Bit#(32)) lassert_nvars <- mkReg(unpack(0));
    Reg#(Bit#(32)) lassert_fptr <- mkReg(unpack(0));
    Reg#(Bit#(32)) lassert_cptr <- mkReg(unpack(0));
    Reg#(Vector#(64, Bit#(32))) lassert_fbuf <- mkReg(unpack(0));
    Reg#(Vector#(64, Bit#(32))) lassert_cbuf <- mkReg(unpack(0));
    Reg#(Bool) lassert_clause_sat <- mkReg(False);
    Reg#(Bool) lassert_counter_clause_sat <- mkReg(False);
    Reg#(Bool) lassert_counter_seen_fail <- mkReg(False);
    Reg#(Bit#(7)) bus_load_instr_addr <- mkReg(unpack(0));
    Reg#(Bit#(128)) bus_load_instr_data <- mkReg(unpack(0));
    Reg#(Bool) bus_load_instr_kick <- mkReg(False);
    Reg#(Vector#(16, Bit#(32))) mu_tensor <- mkReg(unpack(0));
    Reg#(Vector#(64, Bit#(32))) ptTable <- mkReg(unpack(0));
    Reg#(Bit#(7)) pt_next_id <- mkReg(7'h1);
    Reg#(Vector#(16, Bit#(6))) morph_src_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bit#(6))) morph_dst_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bit#(4))) morph_coupling_desc_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bool)) morph_valid_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bool)) morph_identity_table <- mkReg(unpack(0));
    Reg#(Bit#(5)) morph_next_id <- mkReg(5'h1);
    Reg#(Vector#(16, Bit#(4))) coupling_desc_base_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bit#(5))) coupling_desc_count_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bool)) coupling_desc_valid_table <- mkReg(unpack(0));
    Reg#(Bit#(5)) coupling_desc_next_id <- mkReg(5'h0);
    Reg#(Vector#(16, Bit#(32))) coupling_pair_src_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bit#(32))) coupling_pair_dst_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bool)) coupling_pair_valid_table <- mkReg(unpack(0));
    Reg#(Bit#(5)) coupling_pair_next_id <- mkReg(5'h0);
    Reg#(Vector#(16, Bit#(32))) formula_desc_base_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bit#(32))) formula_desc_count_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bool)) formula_desc_valid_table <- mkReg(unpack(0));
    Reg#(Bit#(5)) formula_desc_next_id <- mkReg(5'h0);
    Reg#(Vector#(16, Bit#(32))) cert_desc_base_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bit#(32))) cert_desc_count_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bool)) cert_desc_valid_table <- mkReg(unpack(0));
    Reg#(Bit#(5)) cert_desc_next_id <- mkReg(5'h0);
    Reg#(Vector#(16, Bit#(4))) desc_meta_subtype_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bit#(4))) desc_meta_kind_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bit#(8))) desc_meta_inline_len_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bit#(32))) desc_meta_aux_table <- mkReg(unpack(0));
    Reg#(Vector#(16, Bool)) desc_meta_valid_table <- mkReg(unpack(0));
    Reg#(Bit#(5)) desc_meta_next_id <- mkReg(5'h0);
    Reg#(Bit#(32)) wc_same_00 <- mkReg(unpack(0));
    Reg#(Bit#(32)) wc_diff_00 <- mkReg(unpack(0));
    Reg#(Bit#(32)) wc_same_01 <- mkReg(unpack(0));
    Reg#(Bit#(32)) wc_diff_01 <- mkReg(unpack(0));
    Reg#(Bit#(32)) wc_same_10 <- mkReg(unpack(0));
    Reg#(Bit#(32)) wc_diff_10 <- mkReg(unpack(0));
    Reg#(Bit#(32)) wc_same_11 <- mkReg(unpack(0));
    Reg#(Bit#(32)) wc_diff_11 <- mkReg(unpack(0));
    
    rule step;
        let x_0 = (halted);
        when (! (x_0), noAction);
        let x_1 = (err);
        when (! (x_1), noAction);
        let x_2 = (lassert_phase);
        when ((x_2) == ((Bit#(3))'(3'h0)), noAction);
        let x_3 = (pc);
        let x_4 = (mu);
        let x_5 = (regs);
        let x_6 = (mem);
        let x_7 = (imem);
        let x_8 = (partition_ops);
        let x_9 = (mdl_ops);
        let x_10 = (info_gain);
        let x_11 = (error_code);
        let x_12 = (logic_acc);
        let x_13 = (cert_addr);
        let x_14 = (active_module);
        let x_15 = (mstatus);
        let x_16 = (mcycle_lo);
        let x_17 = (mcycle_hi);
        let x_18 = (minstret_lo);
        let x_19 = (minstret_hi);
        let x_20 = (trap_vector);
        let x_21 = (mu_tensor);
        let x_22 = (ptTable);
        let x_23 = (pt_next_id);
        let x_24 = (certified);
        let x_25 = (morph_src_table);
        let x_26 = (morph_dst_table);
        let x_27 = (morph_valid_table);
        let x_28 = (morph_coupling_desc_table);
        let x_29 = (morph_identity_table);
        let x_30 = (morph_next_id);
        let x_31 = (coupling_desc_valid_table);
        let x_32 = (coupling_desc_count_table);
        let x_33 = (coupling_desc_next_id);
        let x_34 = (coupling_pair_next_id);
        let x_35 = (formula_desc_valid_table);
        let x_36 = (formula_desc_next_id);
        let x_37 = (cert_desc_valid_table);
        let x_38 = (cert_desc_next_id);
        let x_39 = (desc_meta_valid_table);
        let x_40 = (desc_meta_next_id);
        let x_41 = (wc_same_00);
        let x_42 = (wc_diff_00);
        let x_43 = (wc_same_01);
        let x_44 = (wc_diff_01);
        let x_45 = (wc_same_10);
        let x_46 = (wc_diff_10);
        let x_47 = (wc_same_11);
        let x_48 = (wc_diff_11);
        Bit#(32) x_49 = ((x_21)[(Bit#(4))'(4'h0)]);
        Bit#(32) x_50 = ((x_21)[(Bit#(4))'(4'h1)]);
        Bit#(32) x_51 = ((x_21)[(Bit#(4))'(4'h2)]);
        Bit#(32) x_52 = ((x_21)[(Bit#(4))'(4'h3)]);
        Bit#(32) x_53 = ((x_21)[(Bit#(4))'(4'h4)]);
        Bit#(32) x_54 = ((x_21)[(Bit#(4))'(4'h5)]);
        Bit#(32) x_55 = ((x_21)[(Bit#(4))'(4'h6)]);
        Bit#(32) x_56 = ((x_21)[(Bit#(4))'(4'h7)]);
        Bit#(32) x_57 = ((x_21)[(Bit#(4))'(4'h8)]);
        Bit#(32) x_58 = ((x_21)[(Bit#(4))'(4'h9)]);
        Bit#(32) x_59 = ((x_21)[(Bit#(4))'(4'ha)]);
        Bit#(32) x_60 = ((x_21)[(Bit#(4))'(4'hb)]);
        Bit#(32) x_61 = ((x_21)[(Bit#(4))'(4'hc)]);
        Bit#(32) x_62 = ((x_21)[(Bit#(4))'(4'hd)]);
        Bit#(32) x_63 = ((x_21)[(Bit#(4))'(4'he)]);
        Bit#(32) x_64 = ((x_21)[(Bit#(4))'(4'hf)]);
        Bit#(32) x_65 = ((((((((((((((((x_49) + (x_50)) + (x_51)) + (x_52)) +
        (x_53)) + (x_54)) + (x_55)) + (x_56)) + (x_57)) + (x_58)) + (x_59)) +
        (x_60)) + (x_61)) + (x_62)) + (x_63)) + (x_64));
        Bool x_66 = ((x_4) < (x_65));
        Bit#(7) x_67 = ((x_3)[6:0]);
        Bit#(128) x_68 = ((x_7)[x_67]);
        Bit#(32) x_69 = ((x_68)[31:0]);
        Bit#(8) x_70 = ((x_68)[127:120]);
        Bit#(8) x_71 = ((x_68)[119:112]);
        Bit#(16) x_72 = ((x_68)[111:96]);
        Bit#(32) x_73 = ((x_68)[63:32]);
        Bit#(8) x_74 = ((x_69)[31:24]);
        Bit#(8) x_75 = ((x_69)[23:16]);
        Bit#(8) x_76 = ((x_69)[15:8]);
        Bit#(8) x_77 = ((x_69)[7:0]);
        Bit#(4) x_78 = ((x_72)[15:12]);
        Bit#(4) x_79 = ((x_72)[11:8]);
        Bit#(8) x_80 = ((x_72)[7:0]);
        Bit#(4) x_81 = ((x_73)[3:0]);
        Bit#(4) x_82 = ((x_73)[9:6]);
        Bit#(5) x_83 = (zeroExtend(x_81));
        Bit#(5) x_84 = (zeroExtend(x_82));
        Bool x_85 = (! ((x_82) == ((Bit#(4))'(4'h0))));
        Bool x_86 = ((((((((x_74) == ((Bit#(8))'(8'h27))) || ((x_74) ==
        ((Bit#(8))'(8'h28)))) || ((x_74) == ((Bit#(8))'(8'h29)))) || ((x_74)
        == ((Bit#(8))'(8'h2a)))) || ((x_74) == ((Bit#(8))'(8'h2b)))) ||
        ((x_74) == ((Bit#(8))'(8'h2c)))) || ((x_74) == ((Bit#(8))'(8'h2d))));
        
        Bool x_87 = (((((((x_74) == ((Bit#(8))'(8'h3))) || ((x_74) ==
        ((Bit#(8))'(8'h4)))) || ((x_74) == ((Bit#(8))'(8'he)))) || ((x_74) ==
        ((Bit#(8))'(8'hf)))) || ((x_74) == ((Bit#(8))'(8'h1e)))) || ((x_74)
        == ((Bit#(8))'(8'h2b))));
        Bool x_88 = ((((x_74) == ((Bit#(8))'(8'h15))) || ((x_74) ==
        ((Bit#(8))'(8'h16)))) || ((x_74) == ((Bit#(8))'(8'h17))));
        Bool x_89 = ((((x_74) == ((Bit#(8))'(8'hf))) || ((x_74) ==
        ((Bit#(8))'(8'h25)))) || ((x_74) == ((Bit#(8))'(8'h26))));
        Bool x_90 = (((((((x_71) == ((Bit#(8))'(8'h0))) || ((x_71) ==
        ((Bit#(8))'(8'h1)))) || ((x_71) == ((Bit#(8))'(8'h2)))) || ((x_71) ==
        ((Bit#(8))'(8'h3)))) || ((x_71) == ((Bit#(8))'(8'h4)))) || ((x_71) ==
        ((Bit#(8))'(8'h5))));
        Bool x_91 = (((x_71) == ((Bit#(8))'(8'h0)) ? ((Bool)'(True)) :
        (((x_71) == ((Bit#(8))'(8'h1)) ? (x_88) : (((x_71) ==
        ((Bit#(8))'(8'h2)) ? (x_89) : (((x_71) == ((Bit#(8))'(8'h3)) ? (x_86)
        : (((x_71) == ((Bit#(8))'(8'h4)) ? ((x_86) || (x_87)) : (((x_71) ==
        ((Bit#(8))'(8'h5)) ? (x_87) : ((Bool)'(False))))))))))))));
        Bool x_92 = ((x_79) == ((Bit#(4))'(4'h0)));
        Bool x_93 = ((x_79) == ((Bit#(4))'(4'h0)));
        Bool x_94 = ((x_79) == ((Bit#(4))'(4'h1)));
        Bool x_95 = ((x_79) == ((Bit#(4))'(4'h2)));
        Bool x_96 = ((x_79) == ((Bit#(4))'(4'h3)));
        Bool x_97 = ((x_79) == ((Bit#(4))'(4'h4)));
        Bool x_98 = (((((x_93) || (x_94)) || (x_95)) || (x_96)) || (x_97));
        
        Bool x_99 = ((x_72) == ((Bit#(16))'(16'h0)));
        Bool x_100 = ((x_80) == ((Bit#(8))'(8'h0)));
        Bool x_101 = (((Bit#(8))'(8'h8)) < (x_80));
        Bool x_102 = (((((x_71) == ((Bit#(8))'(8'h0))) || ((x_71) ==
        ((Bit#(8))'(8'h1)))) || ((x_71) == ((Bit#(8))'(8'h2)))) && (!
        (x_99)));
        Bool x_103 = ((((x_71) == ((Bit#(8))'(8'h3))) || ((x_71) ==
        ((Bit#(8))'(8'h5)))) && (((! (x_92)) || (x_100)) || (x_101)));
        Bool x_104 = (((x_71) == ((Bit#(8))'(8'h4))) && ((! (x_100)) || (!
        (x_98))));
        Bool x_105 = ((! ((x_83) < (x_30))) || (! ((x_27)[x_81])));
        Bool x_106 = ((x_85) && ((! ((x_84) < (x_30))) || (!
        ((x_27)[x_82]))));
        Bool x_107 = ((! ((x_83) < (x_33))) || (! ((x_31)[x_81])));
        Bool x_108 = ((x_85) && ((! ((x_84) < (x_33))) || (!
        ((x_31)[x_82]))));
        Bool x_109 = ((! ((x_83) < (x_36))) || (! ((x_35)[x_81])));
        Bool x_110 = ((x_85) && ((! ((x_84) < (x_36))) || (!
        ((x_35)[x_82]))));
        Bool x_111 = ((! ((x_83) < (x_38))) || (! ((x_37)[x_81])));
        Bool x_112 = ((x_85) && ((! ((x_84) < (x_38))) || (!
        ((x_37)[x_82]))));
        Bool x_113 = ((! ((x_83) < (x_40))) || (! ((x_39)[x_81])));
        Bool x_114 = ((x_85) && ((! ((x_84) < (x_40))) || (!
        ((x_39)[x_82]))));
        Bool x_115 = (((x_71) == ((Bit#(8))'(8'h4))) && ((((x_93) || (x_94))
        || (x_97)) && ((((x_93) && ((x_105) || (x_106))) || ((x_94) &&
        ((x_107) || (x_108)))) || ((x_97) && ((x_113) || (x_114))))));
        Bool x_116 = ((((x_71) == ((Bit#(8))'(8'h4))) && (x_87)) && (!
        ((x_95) || (x_96))));
        Bool x_117 = ((((x_71) == ((Bit#(8))'(8'h4))) && (x_86)) && (!
        (((x_93) || (x_94)) || (x_97))));
        Bool x_118 = (((x_71) == ((Bit#(8))'(8'h4))) && (((x_116) || ((x_95)
        && ((x_109) || (x_110)))) || ((x_96) && ((x_111) || (x_112)))));
        Bool x_119 = (((((x_74) == ((Bit#(8))'(8'h27))) || ((x_74) ==
        ((Bit#(8))'(8'h28)))) || ((x_74) == ((Bit#(8))'(8'h29)))) || ((x_74)
        == ((Bit#(8))'(8'h2c))));
        Bool x_120 = (((x_119) && (! ((x_30) < ((Bit#(5))'(5'h10))))) ||
        (((((x_71) == ((Bit#(8))'(8'h3))) || ((x_71) == ((Bit#(8))'(8'h4))))
        && ((x_74) == ((Bit#(8))'(8'h27)))) && ((! ((x_33) <
        ((Bit#(5))'(5'h10)))) || (! ((x_34) < ((Bit#(5))'(5'h10)))))));
        Bool x_121 = (! ((x_70) == ((Bit#(8))'(8'h2))));
        Bool x_122 = (((! (x_90)) || (! (x_91))) || (x_117));
        Bool x_123 = (((x_102) || (x_103)) || (x_104));
        Bool x_124 = ((((((x_121) || (x_122)) || (x_123)) || (x_115)) ||
        (x_120)) || (x_118));
        Bit#(32) x_125 = ((x_121 ? ((Bit#(32))'(32'hbadc0010)) : ((x_122 ?
        ((Bit#(32))'(32'hbadc0011)) : ((x_123 ? ((Bit#(32))'(32'hbadc0013)) :
        ((x_115 ? ((Bit#(32))'(32'hbadc0012)) : ((x_120 ?
        ((Bit#(32))'(32'hbadc0014)) : ((x_118 ? ((Bit#(32))'(32'hbadc0015)) :
        (x_11)))))))))))));
        Bit#(32) x_126 = (zeroExtend(x_77));
        Bit#(32) x_127 = (zeroExtend(x_76));
        Bit#(32) x_128 = (((((x_74) == ((Bit#(8))'(8'he))) || ((x_74) ==
        ((Bit#(8))'(8'hf)))) || ((x_74) == ((Bit#(8))'(8'h1a))) ? (x_127) :
        ((Bit#(32))'(32'h0))));
        Bit#(32) x_129 = ((((x_4) + (x_128)) + (x_126)) +
        ((Bit#(32))'(32'h1)));
        Bit#(1) x_130 = ((x_75)[5:5]);
        Bool x_131 = ((x_130) == ((Bit#(1))'(1'h1)));
        Bool x_132 = ((x_74) == ((Bit#(8))'(8'h3)));
        Bool x_133 = ((x_132) && (! (x_131)));
        Bit#(32) x_134 = ((x_4) + (x_126));
        Bit#(32) x_135 = ((x_3) + ((Bit#(32))'(32'h1)));
        Bit#(4) x_136 = ((x_75)[3:0]);
        Bit#(4) x_137 = ((x_76)[3:0]);
        Bit#(4) x_138 = ((x_76)[7:4]);
        Bit#(4) x_139 = ((x_76)[3:0]);
        Bit#(4) x_140 = (truncate(x_138));
        Bit#(4) x_141 = (truncate(x_139));
        Bit#(32) x_142 = ((x_5)[x_140]);
        Bit#(32) x_143 = ((x_5)[x_141]);
        Bit#(32) x_144 = ((x_5)[x_136]);
        Bit#(32) x_145 = ((x_5)[x_137]);
        Bit#(32) x_146 = (zeroExtend(x_76));
        Bit#(7) x_147 = ((x_145)[6:0]);
        Bit#(7) x_148 = ((x_144)[6:0]);
        Bit#(7) x_149 = (truncate(x_76));
        Bit#(32) x_150 = ((x_6)[x_147]);
        Bit#(32) x_151 = ((x_6)[x_149]);
        Bit#(32) x_152 = ((x_5)[(Bit#(4))'(4'hf)]);
        Bit#(7) x_153 = ((x_152)[6:0]);
        Bit#(32) x_154 = ((x_152) + ((Bit#(32))'(32'h1)));
        Bit#(32) x_155 = ((x_152) - ((Bit#(32))'(32'h1)));
        Bit#(7) x_156 = ((x_155)[6:0]);
        Bit#(32) x_157 = ((x_22)[x_14]);
        Bool x_158 = ((zeroExtend(x_147)) < (x_157));
        Bool x_159 = ((zeroExtend(x_148)) < (x_157));
        Bool x_160 = ((zeroExtend(x_153)) < (x_157));
        Bool x_161 = ((zeroExtend(x_156)) < (x_157));
        Bool x_162 = (((x_74) == ((Bit#(8))'(8'h11))) || ((x_74) ==
        ((Bit#(8))'(8'h1c))));
        Bool x_163 = (((x_74) == ((Bit#(8))'(8'h12))) || ((x_74) ==
        ((Bit#(8))'(8'h1d))));
        Bool x_164 = ((x_74) == ((Bit#(8))'(8'h17)));
        Bool x_165 = ((x_74) == ((Bit#(8))'(8'h18)));
        Bool x_166 = ((x_162) && (! (x_158)));
        Bool x_167 = ((x_163) && (! (x_159)));
        Bool x_168 = ((x_164) && (! (x_160)));
        Bool x_169 = ((x_165) && (! (x_161)));
        Bool x_170 = ((((x_166) || (x_167)) || (x_168)) || (x_169));
        Bool x_171 = ((x_12) == ((Bit#(32))'(32'hcafeeace)));
        Bool x_172 = ((((x_74) == ((Bit#(8))'(8'hf))) || ((x_74) ==
        ((Bit#(8))'(8'h6)))) || ((x_74) == ((Bit#(8))'(8'h9))));
        Bool x_173 = ((x_172) && (! (x_171)));
        Bool x_174 = (! ((x_23) < ((Bit#(7))'(7'h40))));
        Bool x_175 = (! (x_174));
        Bool x_176 = (! (((Bit#(7))'(7'h40)) < ((x_23) +
        ((Bit#(7))'(7'h2)))));
        Bool x_177 = (((x_74) == ((Bit#(8))'(8'h0))) && (! (x_175)));
        Bool x_178 = (((x_74) == ((Bit#(8))'(8'h1))) && (! (x_176)));
        Bool x_179 = (((x_74) == ((Bit#(8))'(8'h2))) && (! (x_175)));
        Bool x_180 = (((x_177) || (x_178)) || (x_179));
        Bit#(6) x_181 = ((x_76)[5:0]);
        Bit#(32) x_182 = ((x_22)[x_181]);
        Bit#(32) x_183 = (zeroExtend(x_76));
        Bit#(16) x_184 = ({(x_75),(x_76)});
        Bit#(32) x_185 = (zeroExtend(x_184));
        Bit#(32) x_186 = ((x_161 ? ((x_6)[x_156]) : ((Bit#(32))'(32'h0))));
        
        Bool x_187 = ((x_71) == ((Bit#(8))'(8'h3)));
        Bool x_188 = (((x_74) == ((Bit#(8))'(8'h27))) && (x_187));
        Bool x_189 = (((x_74) == ((Bit#(8))'(8'h28))) && (x_187));
        Bool x_190 = (((x_74) == ((Bit#(8))'(8'h29))) && (x_187));
        Bool x_191 = (((x_74) == ((Bit#(8))'(8'h2a))) && (x_187));
        Bool x_192 = (((x_74) == ((Bit#(8))'(8'h2d))) && (x_187));
        Bool x_193 = (((x_74) == ((Bit#(8))'(8'h2b))) && ((x_71) ==
        ((Bit#(8))'(8'h5))));
        Bool x_194 = (((x_74) == ((Bit#(8))'(8'h27))) && (! (x_187)));
        Bool x_195 = (((x_74) == ((Bit#(8))'(8'h28))) && (! (x_187)));
        Bool x_196 = (((x_74) == ((Bit#(8))'(8'h29))) && (! (x_187)));
        Bool x_197 = (((x_74) == ((Bit#(8))'(8'h2a))) && (! (x_187)));
        Bool x_198 = (((x_74) == ((Bit#(8))'(8'h2d))) && (! (x_187)));
        Bool x_199 = (((x_74) == ((Bit#(8))'(8'h2b))) && (! ((x_71) ==
        ((Bit#(8))'(8'h5)))));
        Bool x_200 = (((x_74) == ((Bit#(8))'(8'h2c))) && (x_187));
        Bool x_201 = (((x_74) == ((Bit#(8))'(8'h2c))) && (! (x_187)));
        Bool x_202 = ((x_74) == ((Bit#(8))'(8'h2c)));
        Bit#(6) x_203 = ((x_73)[5:0]);
        Bit#(4) x_204 = ((x_73)[9:6]);
        Bit#(4) x_205 = ((x_73)[3:0]);
        Bit#(2) x_206 = ((x_73)[1:0]);
        Bit#(32) x_207 = (x_73);
        Bit#(6) x_208 = ((x_76)[5:0]);
        Bit#(6) x_209 = ((x_76)[5:0]);
        Bit#(4) x_210 = ((x_76)[3:0]);
        Bit#(4) x_211 = ((x_75)[3:0]);
        Bit#(4) x_212 = ((x_75)[3:0]);
        Bit#(4) x_213 = ((x_30)[3:0]);
        Bit#(32) x_214 = (zeroExtend(x_213));
        Bit#(5) x_215 = (zeroExtend(x_204));
        Bit#(5) x_216 = (zeroExtend(x_205));
        Bit#(5) x_217 = (zeroExtend(x_210));
        Bit#(5) x_218 = (zeroExtend(x_211));
        Bit#(5) x_219 = (zeroExtend(x_212));
        Bool x_220 = ((x_30) < ((Bit#(5))'(5'h10)));
        Bool x_221 = (! (((x_22)[x_208]) == ((Bit#(32))'(32'h0))));
        Bool x_222 = (! (((x_22)[x_203]) == ((Bit#(32))'(32'h0))));
        Bool x_223 = (! (((x_22)[x_209]) == ((Bit#(32))'(32'h0))));
        Bool x_224 = ((x_204) == ((Bit#(4))'(4'h0)));
        Bool x_225 = (((x_215) < (x_33)) && ((x_31)[x_204]));
        Bool x_226 = ((x_224) || (x_225));
        Bool x_227 = (((x_217) < (x_30)) && ((x_27)[x_210]));
        Bool x_228 = (((x_216) < (x_30)) && ((x_27)[x_205]));
        Bit#(6) x_229 = ((x_25)[x_210]);
        Bit#(6) x_230 = ((x_26)[x_210]);
        Bit#(6) x_231 = ((x_25)[x_205]);
        Bit#(6) x_232 = ((x_26)[x_205]);
        Bool x_233 = ((x_230) == (x_231));
        Bit#(4) x_234 = ((Bit#(4))'(4'h0));
        Bit#(5) x_235 = ((Bit#(5))'(5'h0));
        Bool x_236 = (((x_235) < (x_30)) && ((x_27)[x_234]));
        Bit#(6) x_237 = ((x_25)[x_234]);
        Bit#(6) x_238 = ((x_26)[x_234]);
        Bool x_239 = ((x_230) == (x_237));
        Bit#(4) x_240 = ((x_200 ? (x_205) : ((Bit#(4))'(4'h0))));
        Bit#(5) x_241 = ((x_200 ? (x_216) : ((Bit#(5))'(5'h0))));
        Bool x_242 = (((x_241) < (x_30)) && ((x_27)[x_240]));
        Bit#(6) x_243 = ((x_26)[x_240]);
        Bool x_244 = (((x_217) < (x_30)) && ((x_27)[x_210]));
        Bool x_245 = (((x_218) < (x_30)) && ((x_27)[x_211]));
        Bool x_246 = (((x_219) < (x_30)) && ((x_27)[x_212]));
        Bit#(6) x_247 = ((x_25)[x_210]);
        Bit#(6) x_248 = ((x_26)[x_210]);
        Bool x_249 = ((x_29)[x_210]);
        Bit#(4) x_250 = ((x_28)[x_210]);
        Bit#(5) x_251 = (zeroExtend(x_250));
        Bool x_252 = ((x_250) == ((Bit#(4))'(4'h0)));
        Bool x_253 = (((x_251) < (x_33)) && ((x_31)[x_250]));
        Bool x_254 = ((((x_192) && (x_244)) && (! (x_252))) && (! (x_253)));
        
        Bit#(5) x_255 = ((x_252 ? ((Bit#(5))'(5'h0)) : ((x_32)[x_250])));
        
        Bit#(32) x_256 = (zeroExtend(x_247));
        Bit#(32) x_257 = (zeroExtend(x_248));
        Bit#(32) x_258 = (zeroExtend(x_255));
        Bit#(32) x_259 = ((x_249 ? ((Bit#(32))'(32'h1)) :
        ((Bit#(32))'(32'h0))));
        Bit#(2) x_260 = ((x_192 ? (x_206) : ((Bit#(2))'(2'h0))));
        Bit#(32) x_261 = (((x_260) == ((Bit#(2))'(2'h0)) ? (x_256) :
        (((x_260) == ((Bit#(2))'(2'h1)) ? (x_257) : (((x_260) ==
        ((Bit#(2))'(2'h2)) ? (x_258) : (x_259)))))));
        Bool x_262 = (((x_188) && (((! (x_221)) || (! (x_222))) || (!
        (x_226)))) || ((x_190) && (! (x_223))));
        Bool x_263 = (((x_194) && (! (x_221))) || ((x_196) && (! (x_223))));
        
        Bool x_264 = (((x_189) && ((! (x_227)) || (! (x_228)))) || ((x_195)
        && ((! (x_227)) || (! (x_236)))));
        Bool x_265 = (((((x_189) && (x_227)) && (x_228)) && (! (x_233))) ||
        ((((x_195) && (x_227)) && (x_236)) && (! (x_239))));
        Bool x_266 = (((x_191) || (x_197)) && (! (x_245)));
        Bool x_267 = (((x_192) || (x_198)) && (! (x_244)));
        Bool x_268 = (((x_193) || (x_199)) && (! (x_246)));
        Bool x_269 = ((x_202) && (! (x_227)));
        Bool x_270 = (((x_202) && (x_227)) && (! (x_242)));
        Bool x_271 = ((((((((((x_262) || (x_263)) || (x_264)) || (x_265)) ||
        (x_266)) || (x_267)) || (x_254)) || (x_268)) || (x_269)) || (x_270));
        
        Bit#(32) x_272 = ((x_265 ? ((Bit#(32))'(32'hbadc0001)) :
        (((((((x_264) || (x_266)) || (x_267)) || (x_268)) || (x_269)) ||
        (x_270) ? ((Bit#(32))'(32'hbadc0003)) :
        ((Bit#(32))'(32'hbadc0000))))));
        Bool x_273 = (((((x_188) && (x_220)) && (x_221)) && (x_222)) &&
        (x_226));
        Bool x_274 = (((x_194) && (x_220)) && (x_221));
        Bool x_275 = (((x_190) && (x_220)) && (x_223));
        Bool x_276 = (((x_196) && (x_220)) && (x_223));
        Bool x_277 = (((((x_189) && (x_220)) && (x_227)) && (x_228)) &&
        (x_233));
        Bool x_278 = (((((x_195) && (x_220)) && (x_227)) && (x_236)) &&
        (x_239));
        Bool x_279 = ((((x_202) && (x_220)) && (x_227)) && (x_242));
        Bool x_280 = ((((x_192) || (x_198)) && (x_244)) && (! (x_254)));
        Bool x_281 = (((x_191) || (x_197)) && (x_245));
        Bool x_282 = (((x_193) || (x_199)) && (x_246));
        Bool x_283 = (((((((x_273) || (x_274)) || (x_275)) || (x_276)) ||
        (x_277)) || (x_278)) || (x_279));
        Bit#(6) x_284 = ((x_273 ? (x_208) : ((x_274 ? (x_208) : (((x_275) ||
        (x_276) ? (x_209) : ((x_277 ? (x_229) : ((x_278 ? (x_229) : ((x_279 ?
        (x_229) : (x_209)))))))))))));
        Bit#(6) x_285 = ((x_273 ? (x_203) : ((x_274 ? (x_208) : (((x_275) ||
        (x_276) ? (x_209) : ((x_277 ? (x_232) : ((x_278 ? (x_238) : ((x_279 ?
        (x_243) : (x_209)))))))))))));
        Bit#(4) x_286 = ((x_273 ? (x_204) : ((Bit#(4))'(4'h0))));
        Bool x_287 = ((x_275) || (x_276));
        Bit#(32) x_288 = ((x_142) + (x_143));
        Bit#(32) x_289 = ((x_142) - (x_143));
        Bit#(32) x_290 = ((x_142) & (x_143));
        Bit#(32) x_291 = ((x_142) | (x_143));
        Bit#(32) x_292 = ((x_142) << (x_143));
        Bit#(32) x_293 = ((x_142) >> (x_143));
        Bit#(32) x_294 = (multiply_unsigned ((x_142), (x_143)));
        Bit#(32) x_295 = ((Bit#(32))'(32'h8));
        Bit#(32) x_296 = ((x_146) << (x_295));
        Bit#(32) x_297 = ((x_144) ^ (x_145));
        Bool x_298 = (! ((x_144) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_299 = (x_145);
        Bit#(32) x_300 = ((Bit#(32))'(32'h55555555));
        Bit#(32) x_301 = ((x_299) & (x_300));
        Bit#(32) x_302 = (((x_299) >> ((Bit#(6))'(6'h1))) & (x_300));
        Bit#(32) x_303 = ((x_301) + (x_302));
        Bit#(32) x_304 = ((Bit#(32))'(32'h33333333));
        Bit#(32) x_305 = ((x_303) & (x_304));
        Bit#(32) x_306 = (((x_303) >> ((Bit#(6))'(6'h2))) & (x_304));
        Bit#(32) x_307 = ((x_305) + (x_306));
        Bit#(32) x_308 = ((Bit#(32))'(32'hf0f0f0f));
        Bit#(32) x_309 = ((x_307) & (x_308));
        Bit#(32) x_310 = (((x_307) >> ((Bit#(6))'(6'h4))) & (x_308));
        Bit#(32) x_311 = ((x_309) + (x_310));
        Bit#(32) x_312 = ((Bit#(32))'(32'hff00ff));
        Bit#(32) x_313 = ((x_311) & (x_312));
        Bit#(32) x_314 = (((x_311) >> ((Bit#(6))'(6'h8))) & (x_312));
        Bit#(32) x_315 = ((x_313) + (x_314));
        Bit#(32) x_316 = ((Bit#(32))'(32'hffff));
        Bit#(32) x_317 = ((x_315) & (x_316));
        Bit#(32) x_318 = (((x_315) >> ((Bit#(6))'(6'h10))) & (x_316));
        
        Bit#(32) x_319 = ((x_317) + (x_318));
        Bool x_320 = (((Bit#(8))'(8'h3)) < (x_76));
        Bool x_321 = (((Bit#(8))'(8'h1)) < (x_75));
        Bool x_322 = ((x_321) && ((x_65) == ((Bit#(32))'(32'h0))));
        Bool x_323 = (x_322);
        Bit#(2) x_324 = ((x_75)[1:0]);
        Bit#(2) x_325 = ((x_76)[1:0]);
        Bool x_326 = (((x_325) == ((Bit#(2))'(2'h0))) || ((x_325) ==
        ((Bit#(2))'(2'h3))));
        Bool x_327 = ((x_324) == ((Bit#(2))'(2'h0)));
        Bool x_328 = ((x_324) == ((Bit#(2))'(2'h1)));
        Bool x_329 = ((x_324) == ((Bit#(2))'(2'h2)));
        Bool x_330 = ((x_324) == ((Bit#(2))'(2'h3)));
        Bool x_331 = (((x_74) == ((Bit#(8))'(8'h6))) || ((x_74) ==
        ((Bit#(8))'(8'he))));
        Bool x_332 = ((x_74) == ((Bit#(8))'(8'h6)));
        Bool x_333 = ((x_332) && ((x_126) < (x_127)));
        Bool x_334 = (((((((((x_74) == ((Bit#(8))'(8'h9))) && (! (x_323))) &&
        (! (x_66))) && (! (x_170))) && (! (x_180))) && (! (x_173))) && (!
        (x_333))) && (! (x_124)));
        Bit#(4) x_335 = ((x_75)[3:0]);
        Bit#(4) x_336 = ((x_73)[3:0]);
        Bit#(4) x_337 = ((((x_74) == ((Bit#(8))'(8'hf))) && ((x_71) ==
        ((Bit#(8))'(8'h2))) ? (x_336) : (x_335)));
        Bit#(32) x_338 = ((x_21)[x_337]);
        Bit#(32) x_339 = ((x_338) + (x_127));
        Bit#(32) x_340 = ((((((((x_66) || (x_170)) || (x_180)) || (x_173)) ||
        (x_333)) || (x_124)) || (x_271) ? (x_20) : (((x_74) ==
        ((Bit#(8))'(8'hff)) ? (x_3) : (((x_74) == ((Bit#(8))'(8'h15)) ?
        (x_185) : (((x_74) == ((Bit#(8))'(8'h17)) ? (x_185) : (((x_74) ==
        ((Bit#(8))'(8'h18)) ? (x_186) : ((((x_74) == ((Bit#(8))'(8'h16))) &&
        (x_298) ? (x_183) : (((x_74) == ((Bit#(8))'(8'h3)) ? ((x_131 ? (x_3)
        : (x_20))) : (x_135)))))))))))))));
        Vector#(16, Bit#(32)) x_341 = (update (update (x_5, x_136, x_145),
        x_137, x_144));
        Vector#(16, Bit#(32)) x_342 = ((x_283 ? (update (x_5, x_136, x_214))
        : ((x_280 ? (update (x_5, x_136, x_261)) : (x_5)))));
        
        Vector#(16, Bit#(32)) x_343 = ((((((((x_66) || (x_170)) || (x_180))
        || (x_173)) || (x_333)) || (x_124)) || (x_271) ? (x_5) : (((x_74) ==
        ((Bit#(8))'(8'h8)) ? (update (x_5, x_136, x_146)) : (((x_74) ==
        ((Bit#(8))'(8'h13)) ? (update (x_5, x_136, x_288)) : (((x_74) ==
        ((Bit#(8))'(8'h14)) ? (update (x_5, x_136, x_289)) : (((x_74) ==
        ((Bit#(8))'(8'h7)) ? (update (x_5, x_136, x_145)) : (((x_74) ==
        ((Bit#(8))'(8'h11)) ? (update (x_5, x_136, x_150)) : (((x_74) ==
        ((Bit#(8))'(8'ha)) ? (update (x_5, x_136, x_151)) : (((x_74) ==
        ((Bit#(8))'(8'hb)) ? (update (x_5, x_136, x_297)) : (((x_74) ==
        ((Bit#(8))'(8'hc)) ? (x_341) : (((x_74) == ((Bit#(8))'(8'hd)) ?
        (update (x_5, x_136, x_319)) : (((x_74) == ((Bit#(8))'(8'h17)) ?
        (update (x_5, (Bit#(4))'(4'hf), x_154)) : (((x_74) ==
        ((Bit#(8))'(8'h18)) ? (update (x_5, (Bit#(4))'(4'hf), x_155)) :
        (((x_74) == ((Bit#(8))'(8'h6)) ? (update (x_5, x_136, x_182)) :
        (((x_74) == ((Bit#(8))'(8'h1c)) ? (update (x_5, x_136, x_150)) :
        (((x_74) == ((Bit#(8))'(8'h1a)) ? (update (x_5, x_136,
        (Bit#(32))'(32'h0))) : (((x_74) == ((Bit#(8))'(8'h1f)) ? (update
        (x_5, x_136, x_290)) : (((x_74) == ((Bit#(8))'(8'h20)) ? (update
        (x_5, x_136, x_291)) : (((x_74) == ((Bit#(8))'(8'h21)) ? (update
        (x_5, x_136, x_292)) : (((x_74) == ((Bit#(8))'(8'h22)) ? (update
        (x_5, x_136, x_293)) : (((x_74) == ((Bit#(8))'(8'h23)) ? (update
        (x_5, x_136, x_294)) : (((x_74) == ((Bit#(8))'(8'h24)) ? (update
        (x_5, x_136, x_296)) : (((x_74) == ((Bit#(8))'(8'h26)) ? (update
        (x_5, x_136, x_338)) :
        (x_342)))))))))))))))))))))))))))))))))))))))))))));
        
        Vector#(128, Bit#(32)) x_344 = ((((((((x_66) || (x_170)) || (x_180))
        || (x_173)) || (x_333)) || (x_124)) || (x_271) ? (x_6) : (((x_74) ==
        ((Bit#(8))'(8'h12)) ? (update (x_6, x_148, x_145)) : (((x_74) ==
        ((Bit#(8))'(8'h17)) ? (update (x_6, x_153, x_135)) : (((x_74) ==
        ((Bit#(8))'(8'h1d)) ? (update (x_6, x_148, x_145)) : (x_6)))))))));
        
        Bool x_345 = (((((x_170) || (x_180)) || (x_173)) || (x_333)) ||
        ((x_74) == ((Bit#(8))'(8'hff))));
        Bool x_346 = ((((((((x_170) || (x_180)) || (x_173)) || (x_333)) ||
        (x_124)) || (x_271)) || (((x_74) == ((Bit#(8))'(8'h9))) && (x_323)))
        || (x_133));
        Bit#(32) x_347 = ((x_66 ? ((Bit#(32))'(32'hb1a4c81)) : ((x_170 ?
        ((Bit#(32))'(32'hbadc0de)) : ((x_180 ? ((Bit#(32))'(32'hbadf001d)) :
        ((x_333 ? ((Bit#(32))'(32'hc43471a1)) : ((x_124 ? (x_125) : ((x_271 ?
        (x_272) : ((x_173 ? ((Bit#(32))'(32'hc43471a1)) : ((((x_74) ==
        ((Bit#(8))'(8'h9))) && (x_323) ? ((Bit#(32))'(32'hbadc45c)) : ((x_133
        ? ((Bit#(32))'(32'hc43471a1)) : (x_11)))))))))))))))))));
        Bit#(32) x_348 = (((x_74) == ((Bit#(8))'(8'h1e)) ? (((x_4) + (x_126))
        + ((Bit#(32))'(32'h1))) : (((x_74) == ((Bit#(8))'(8'h2b)) ? (((x_4) +
        (x_126)) + ((Bit#(32))'(32'h1))) : (((x_74) == ((Bit#(8))'(8'h3)) ?
        ((x_134) + ((Bit#(32))'(32'h1))) : (((((x_74) == ((Bit#(8))'(8'he)))
        || ((x_74) == ((Bit#(8))'(8'hf)))) || ((x_74) == ((Bit#(8))'(8'h1a)))
        ? (x_129) : (((x_74) == ((Bit#(8))'(8'h4)) ? ((x_134) +
        ((Bit#(32))'(32'h1))) : (x_134)))))))))));
        Bit#(32) x_349 = ((((x_74) == ((Bit#(8))'(8'h9))) && (x_321) ?
        ((x_134) + ((Bit#(32))'(32'h100))) : (((x_74) == ((Bit#(8))'(8'h1e))
        ? (((x_4) + (x_126)) + ((Bit#(32))'(32'h1))) : (((x_74) ==
        ((Bit#(8))'(8'h2b)) ? (((x_4) + (x_126)) + ((Bit#(32))'(32'h1))) :
        (((x_74) == ((Bit#(8))'(8'h3)) ? ((x_131 ? (x_4) : ((x_134) +
        ((Bit#(32))'(32'h1))))) : (((((x_74) == ((Bit#(8))'(8'he))) ||
        ((x_74) == ((Bit#(8))'(8'hf)))) || ((x_74) == ((Bit#(8))'(8'h1a))) ?
        (x_129) : (((x_74) == ((Bit#(8))'(8'h4)) ? ((x_134) +
        ((Bit#(32))'(32'h1))) : (x_134)))))))))))));
        Bit#(32) x_350 = (((((x_66) || (x_180)) || (x_173)) || (x_333) ?
        (x_4) : ((x_124 ? (x_348) : (x_349)))));
        Bool x_351 = ((((((((x_66) || (x_170)) || (x_180)) || (x_173)) ||
        (x_333)) || (x_124)) || (x_271) ? (x_24) : (((x_74) ==
        ((Bit#(8))'(8'h1e)) ? ((Bool)'(True)) : (x_24)))));
        Bit#(6) x_352 = ((x_23)[5:0]);
        Bit#(32) x_353 = (zeroExtend(x_75));
        Vector#(64, Bit#(32)) x_354 = (update (x_22, x_352, x_353));
        Bit#(7) x_355 = ((x_23) + ((Bit#(7))'(7'h1)));
        Bit#(6) x_356 = ((x_75)[5:0]);
        Bit#(32) x_357 = ((x_22)[x_356]);
        Bit#(32) x_358 = ((x_357) >> ((Bit#(5))'(5'h1)));
        Bit#(32) x_359 = ((x_357) - (x_358));
        Bit#(6) x_360 = ((x_23)[5:0]);
        Bit#(6) x_361 = (((x_23) + ((Bit#(7))'(7'h1)))[5:0]);
        
        Vector#(64, Bit#(32)) x_362 = (update (update (update (x_22, x_356,
        (Bit#(32))'(32'h0)), x_360, x_358), x_361, x_359));
        Bit#(7) x_363 = ((x_23) + ((Bit#(7))'(7'h2)));
        Bit#(6) x_364 = ((x_75)[5:0]);
        Bit#(6) x_365 = ((x_76)[5:0]);
        Bit#(32) x_366 = ((x_22)[x_364]);
        Bit#(32) x_367 = ((x_22)[x_365]);
        Bit#(32) x_368 = ((x_366) + (x_367));
        Bit#(6) x_369 = ((x_23)[5:0]);
        Vector#(64, Bit#(32)) x_370 = (update (update (update (x_22, x_364,
        (Bit#(32))'(32'h0)), x_365, (Bit#(32))'(32'h0)), x_369, x_368));
        
        Bit#(7) x_371 = ((x_23) + ((Bit#(7))'(7'h1)));
        Vector#(64, Bit#(32)) x_372 = (((((x_66) || (x_180)) || (x_124)) ||
        (x_271) ? (x_22) : (((x_74) == ((Bit#(8))'(8'h0)) ? (x_354) :
        (((x_74) == ((Bit#(8))'(8'h1)) ? (x_362) : (((x_74) ==
        ((Bit#(8))'(8'h2)) ? (x_370) : (x_22)))))))));
        Bit#(7) x_373 = (((((x_66) || (x_180)) || (x_124)) || (x_271) ?
        (x_23) : (((x_74) == ((Bit#(8))'(8'h0)) ? (x_355) : (((x_74) ==
        ((Bit#(8))'(8'h1)) ? (x_363) : (((x_74) == ((Bit#(8))'(8'h2)) ?
        (x_371) : (x_23)))))))));
        Bool x_374 = ((((x_74) == ((Bit#(8))'(8'h0))) || ((x_74) ==
        ((Bit#(8))'(8'h1)))) || ((x_74) == ((Bit#(8))'(8'h2))));
        Bit#(32) x_375 = (((((x_374) && (! (x_66))) && (! (x_124))) && (!
        (x_271)) ? ((x_8) + ((Bit#(32))'(32'h1))) : (x_8)));
        Bit#(32) x_376 = ((((((x_74) == ((Bit#(8))'(8'h5))) && (! (x_66))) &&
        (! (x_124))) && (! (x_271)) ? ((x_9) + ((Bit#(32))'(32'h1))) :
        (x_9)));
        Bit#(32) x_377 = (((((((((x_331) && (! (x_66))) && (! (x_170))) && (!
        (x_180))) && (! (x_173))) && (! (x_333))) && (! (x_124))) && (!
        (x_271)) ? ((x_10) + (x_127)) : (x_10)));
        Bit#(32) x_378 = ((((x_334) && (x_327)) && (x_326) ? ((x_41) +
        ((Bit#(32))'(32'h1))) : (x_41)));
        Bit#(32) x_379 = ((((x_334) && (x_327)) && (! (x_326)) ? ((x_42) +
        ((Bit#(32))'(32'h1))) : (x_42)));
        Bit#(32) x_380 = ((((x_334) && (x_328)) && (x_326) ? ((x_43) +
        ((Bit#(32))'(32'h1))) : (x_43)));
        Bit#(32) x_381 = ((((x_334) && (x_328)) && (! (x_326)) ? ((x_44) +
        ((Bit#(32))'(32'h1))) : (x_44)));
        Bit#(32) x_382 = ((((x_334) && (x_329)) && (x_326) ? ((x_45) +
        ((Bit#(32))'(32'h1))) : (x_45)));
        Bit#(32) x_383 = ((((x_334) && (x_329)) && (! (x_326)) ? ((x_46) +
        ((Bit#(32))'(32'h1))) : (x_46)));
        Bit#(32) x_384 = ((((x_334) && (x_330)) && (x_326) ? ((x_47) +
        ((Bit#(32))'(32'h1))) : (x_47)));
        Bit#(32) x_385 = ((((x_334) && (x_330)) && (! (x_326)) ? ((x_48) +
        ((Bit#(32))'(32'h1))) : (x_48)));
        Vector#(16, Bit#(32)) x_386 = (((((((x_74) == ((Bit#(8))'(8'hf))) &&
        (! (x_66))) && (! (x_173))) && (! (x_124))) && (! (x_271)) ? (update
        (x_21, x_337, x_339)) : ((((((x_74) == ((Bit#(8))'(8'h25))) && (!
        (x_66))) && (! (x_124))) && (! (x_271)) ? (update (x_21, x_337,
        x_145)) : (x_21)))));
        Vector#(16, Bit#(6)) x_387 = ((((((((x_66) || (x_170)) || (x_180)) ||
        (x_173)) || (x_333)) || (x_124)) || (x_271) ? (x_25) : ((x_283 ?
        (update (x_25, x_213, x_284)) : (x_25)))));
        Vector#(16, Bit#(6)) x_388 = ((((((((x_66) || (x_170)) || (x_180)) ||
        (x_173)) || (x_333)) || (x_124)) || (x_271) ? (x_26) : ((x_283 ?
        (update (x_26, x_213, x_285)) : (x_26)))));
        Vector#(16, Bit#(4)) x_389 = ((((((((x_66) || (x_170)) || (x_180)) ||
        (x_173)) || (x_333)) || (x_124)) || (x_271) ? (x_28) : ((x_283 ?
        (update (x_28, x_213, x_286)) : (x_28)))));
        Vector#(16, Bool) x_390 = ((((((((x_66) || (x_170)) || (x_180)) ||
        (x_173)) || (x_333)) || (x_124)) || (x_271) ? (x_29) : ((x_283 ?
        (update (x_29, x_213, x_287)) : (x_29)))));
        Vector#(16, Bool) x_391 = ((((((((x_66) || (x_170)) || (x_180)) ||
        (x_173)) || (x_333)) || (x_124)) || (x_271) ? (x_27) : ((x_283 ?
        (update (x_27, x_213, (Bool)'(True))) : ((x_281 ? (update (x_27,
        x_211, (Bool)'(False))) : (x_27)))))));
        Bit#(5) x_392 = ((((((((x_66) || (x_170)) || (x_180)) || (x_173)) ||
        (x_333)) || (x_124)) || (x_271) ? (x_30) : ((x_283 ? ((x_30) +
        ((Bit#(5))'(5'h1))) : (x_30)))));
        Bit#(32) x_393 = (((((x_66) || (x_170)) || (x_124)) || (x_271) ?
        (x_12) : (((x_74) == ((Bit#(8))'(8'h3)) ? ((x_12) ^
        ((Bit#(32))'(32'hcafeeace))) : (x_12)))));
        Bit#(32) x_394 = ((((((((x_66) || (x_170)) || (x_180)) || (x_173)) ||
        (x_333)) || (x_124)) || (x_271) ? (x_13) : (((x_193) && (x_282) ?
        (x_207) : (((x_199) && (x_282) ? ((Bit#(32))'(32'h0)) : (x_13)))))));
        
        Bit#(32) x_395 = ((x_16) + ((Bit#(32))'(32'h1)));
        Bool x_396 = ((x_395) == ((Bit#(32))'(32'h0)));
        Bit#(32) x_397 = ((x_396 ? ((x_17) + ((Bit#(32))'(32'h1))) :
        (x_17)));
        Bool x_398 = ((((((! (x_170)) && (! (x_180))) && (! (x_173))) && (!
        (x_333))) && (! (x_124))) && (! (x_271)));
        Bit#(32) x_399 = ((x_398 ? ((x_18) + ((Bit#(32))'(32'h1))) :
        (x_18)));
        Bool x_400 = ((x_398) && ((x_399) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_401 = ((x_400 ? ((x_19) + ((Bit#(32))'(32'h1))) :
        (x_19)));
        Bit#(32) x_402 = ((x_171 ? ((Bit#(32))'(32'h1)) :
        ((Bit#(32))'(32'h0))));
        pc <= x_340;
        mu <= x_350;
        regs <= x_343;
        mem <= x_344;
        halted <= x_345;
        err <= x_346;
        error_code <= x_347;
        logic_acc <= x_393;
        cert_addr <= x_394;
        mstatus <= x_402;
        mcycle_lo <= x_395;
        mcycle_hi <= x_397;
        minstret_lo <= x_399;
        minstret_hi <= x_401;
        partition_ops <= x_375;
        mdl_ops <= x_376;
        info_gain <= x_377;
        mu_tensor <= x_386;
        ptTable <= x_372;
        pt_next_id <= x_373;
        morph_src_table <= x_387;
        morph_dst_table <= x_388;
        morph_coupling_desc_table <= x_389;
        morph_identity_table <= x_390;
        morph_valid_table <= x_391;
        morph_next_id <= x_392;
        certified <= x_351;
        wc_same_00 <= x_378;
        wc_diff_00 <= x_379;
        wc_same_01 <= x_380;
        wc_diff_01 <= x_381;
        wc_same_10 <= x_382;
        wc_diff_10 <= x_383;
        wc_same_11 <= x_384;
        wc_diff_11 <= x_385;
        Bit#(32) x_403 = ((Bit#(32))'(32'h0));
        lassert_phase <= (((x_132) && (x_131)) && (! (x_124)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)));
        lassert_kind <= ((x_132) && (! (x_124)) ? (x_131) :
        ((Bool)'(False)));
        lassert_fbase <= (((x_132) && (x_131)) && (! (x_124)) ? (x_144) :
        (x_403));
        lassert_cbase <= (((x_132) && (x_131)) && (! (x_124)) ? (x_145) :
        (x_403));
        lassert_cptr <= (((x_132) && (x_131)) && (! (x_124)) ? (x_126) :
        (x_403));
        lassert_fptr <= x_403;
        lassert_flen <= x_403;
        lassert_clen <= x_403;
        lassert_nvars <= x_403;
        lassert_clause_sat <= (Bool)'(False);
        lassert_counter_clause_sat <= (Bool)'(False);
        
        lassert_counter_seen_fail <= (Bool)'(False);
        
    endrule
    
    rule lassert_fsm_header;
        let x_0 = (lassert_phase);
        when ((x_0) == ((Bit#(3))'(3'h1)), noAction);
        let x_1 = (mem);
        let x_2 = (lassert_fbase);
        Bit#(7) x_3 = ((x_2)[6:0]);
        Bit#(7) x_4 = (((x_2) + ((Bit#(32))'(32'h1)))[6:0]);
        Bit#(7) x_5 = (((x_2) + ((Bit#(32))'(32'h2)))[6:0]);
        Bit#(32) x_6 = ((x_1)[x_3]);
        Bit#(32) x_7 = ((x_1)[x_4]);
        Bit#(32) x_8 = ((x_1)[x_5]);
        lassert_phase <= (Bit#(3))'(3'h2);
        lassert_flen <= x_6;
        lassert_clen <= x_8;
        lassert_nvars <= x_7;
        lassert_fptr <= (x_2) + ((Bit#(32))'(32'h3));
        lassert_clause_sat <= (Bool)'(False);
        lassert_counter_clause_sat <= (Bool)'(False);
        
        lassert_counter_seen_fail <= (Bool)'(False);
        
    endrule
    
    rule lassert_fsm_scan;
        let x_0 = (lassert_phase);
        when ((x_0) == ((Bit#(3))'(3'h2)), noAction);
        let x_1 = (mem);
        let x_2 = (mu);
        let x_3 = (pc);
        let x_4 = (trap_vector);
        let x_5 = (err);
        let x_6 = (error_code);
        let x_7 = (lassert_cbase);
        let x_8 = (lassert_flen);
        let x_9 = (lassert_clen);
        let x_10 = (lassert_nvars);
        let x_11 = (lassert_fptr);
        let x_12 = (lassert_cptr);
        let x_13 = (lassert_clause_sat);
        let x_14 = (lassert_counter_clause_sat);
        let x_15 = (lassert_counter_seen_fail);
        Bit#(7) x_16 = ((x_11)[6:0]);
        Bit#(32) x_17 = ((x_1)[x_16]);
        Bit#(1) x_18 = ((x_17)[31:31]);
        Bool x_19 = ((x_17) == ((Bit#(32))'(32'h0)));
        Bool x_20 = (((x_18) == ((Bit#(1))'(1'h1))) && (! (x_19)));
        Bit#(32) x_21 = ((x_20 ? (((Bit#(32))'(32'h0)) - (x_17)) : (x_17)));
        
        Bit#(7) x_22 = (((x_7) + (x_21))[6:0]);
        Bit#(7) x_23 = ((((x_7) + (x_10)) + (x_21))[6:0]);
        Bit#(32) x_24 = ((x_1)[x_22]);
        Bit#(32) x_25 = ((x_1)[x_23]);
        Bool x_26 = (! ((x_24) == ((Bit#(32))'(32'h0))));
        Bool x_27 = (! ((x_25) == ((Bit#(32))'(32'h0))));
        Bool x_28 = ((! (x_19)) && ((x_20 ? (! (x_26)) : (x_26))));
        Bool x_29 = ((! (x_19)) && ((x_20 ? (! (x_27)) : (x_27))));
        Bool x_30 = (x_19);
        Bool x_31 = (! (((Bit#(32))'(32'h1)) < (x_9)));
        Bool x_32 = ((x_30) && (! (x_13)));
        Bool x_33 = ((x_30) && (! (x_14)));
        Bool x_34 = ((x_15) || (x_33));
        Bool x_35 = ((((x_30) && (x_13)) && (x_31)) && (! (x_34)));
        Bool x_36 = ((x_32) || (x_35));
        Bool x_37 = ((((x_30) && (x_13)) && (x_31)) && (x_34));
        Bool x_38 = (((x_30) && (x_13)) && (! (x_31)));
        Bit#(32) x_39 = (x_12);
        Bit#(32) x_40 = ((x_8) << ((Bit#(6))'(6'h3)));
        Bit#(32) x_41 = ((((x_2) + (x_40)) + (x_39)) + ((Bit#(32))'(32'h1)));
        
        Bit#(32) x_42 = ((((x_2) + (x_40)) + (x_39)) + ((Bit#(32))'(32'h1)));
        
        Bit#(3) x_43 = (((x_37) || (x_36) ? ((Bit#(3))'(3'h0)) :
        ((Bit#(3))'(3'h2))));
        Bit#(32) x_44 = ((x_38 ? ((x_9) - ((Bit#(32))'(32'h1))) : (x_9)));
        
        Bit#(32) x_45 = ((x_11) + ((Bit#(32))'(32'h1)));
        Bool x_46 = ((x_30 ? ((Bool)'(False)) : ((x_28 ? ((Bool)'(True)) :
        (x_13)))));
        Bool x_47 = ((x_30 ? ((Bool)'(False)) : ((x_29 ? ((Bool)'(True)) :
        (x_14)))));
        Bool x_48 = (x_34);
        Bit#(32) x_49 = ((x_37 ? ((x_3) + ((Bit#(32))'(32'h1))) : ((x_36 ?
        (x_4) : (x_3)))));
        Bit#(32) x_50 = ((x_37 ? (x_41) : ((x_36 ? (x_42) : (x_2)))));
        Bool x_51 = ((x_36 ? ((Bool)'(True)) : (x_5)));
        Bit#(32) x_52 = ((x_36 ? ((Bit#(32))'(32'hc43471a1)) : (x_6)));
        
        lassert_phase <= x_43;
        lassert_clen <= x_44;
        lassert_fptr <= x_45;
        lassert_clause_sat <= x_46;
        lassert_counter_clause_sat <= x_47;
        lassert_counter_seen_fail <= x_48;
        pc <= x_49;
        mu <= x_50;
        err <= x_51;
        error_code <= x_52;
        
    endrule
    
    
    method Action loadInstr (Struct1 x_0);
        let x_1 = (imem);
        Bit#(7) x_2 = ((x_0).addr);
        Bit#(128) x_3 = ((x_0).data);
        imem <= update (x_1, x_2, x_3);
        
    endmethod
    
    method ActionValue#(Bit#(32)) getPC ();let x_1 = (pc);
                                           return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getMu ();let x_1 = (mu);
                                           return x_1;
    endmethod
    
    method ActionValue#(Bool) getErr ();let x_1 = (err);
                                        return x_1;
    endmethod
    
    method ActionValue#(Bool) getHalted ();let x_1 = (halted);
                                           return x_1;
    endmethod
    
    method ActionValue#(Bool) getCertified ();
        let x_1 = (certified);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getWcSame00 ();
        let x_1 = (wc_same_00);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getWcDiff00 ();
        let x_1 = (wc_diff_00);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getWcSame01 ();
        let x_1 = (wc_same_01);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getWcDiff01 ();
        let x_1 = (wc_diff_01);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getWcSame10 ();
        let x_1 = (wc_same_10);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getWcDiff10 ();
        let x_1 = (wc_diff_10);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getWcSame11 ();
        let x_1 = (wc_same_11);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getWcDiff11 ();
        let x_1 = (wc_diff_11);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getPartitionOps ();
        let x_1 = (partition_ops);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getMdlOps ();
        let x_1 = (mdl_ops);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getInfoGain ();
        let x_1 = (info_gain);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getErrorCode ();
        let x_1 = (error_code);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getMstatus ();
        let x_1 = (mstatus);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getMcycleLo ();
        let x_1 = (mcycle_lo);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getMcycleHi ();
        let x_1 = (mcycle_hi);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getMinstretLo ();
        let x_1 = (minstret_lo);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getMinstretHi ();
        let x_1 = (minstret_hi);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getLogicAcc ();
        let x_1 = (logic_acc);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getCertAddr ();
        let x_1 = (cert_addr);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getMuTensor0 ();
        let x_1 = (mu_tensor);
        Bit#(32) x_2 = (((((x_1)[(Bit#(4))'(4'h0)]) +
        ((x_1)[(Bit#(4))'(4'h1)])) + ((x_1)[(Bit#(4))'(4'h2)])) +
        ((x_1)[(Bit#(4))'(4'h3)]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getMuTensor1 ();
        let x_1 = (mu_tensor);
        Bit#(32) x_2 = (((((x_1)[(Bit#(4))'(4'h4)]) +
        ((x_1)[(Bit#(4))'(4'h5)])) + ((x_1)[(Bit#(4))'(4'h6)])) +
        ((x_1)[(Bit#(4))'(4'h7)]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getMuTensor2 ();
        let x_1 = (mu_tensor);
        Bit#(32) x_2 = (((((x_1)[(Bit#(4))'(4'h8)]) +
        ((x_1)[(Bit#(4))'(4'h9)])) + ((x_1)[(Bit#(4))'(4'ha)])) +
        ((x_1)[(Bit#(4))'(4'hb)]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getMuTensor3 ();
        let x_1 = (mu_tensor);
        Bit#(32) x_2 = (((((x_1)[(Bit#(4))'(4'hc)]) +
        ((x_1)[(Bit#(4))'(4'hd)])) + ((x_1)[(Bit#(4))'(4'he)])) +
        ((x_1)[(Bit#(4))'(4'hf)]));
        return x_2;
    endmethod
    
    method Action setActiveModule (Bit#(6) x_0);active_module <= x_0;
                                                
    endmethod
    
    method Action setTrapVector (Bit#(32) x_0);trap_vector <= x_0;
                                               
    endmethod
    
    method ActionValue#(Bit#(32)) apbReadData (Bit#(32) x_0);
        let x_1 = (pc);
        let x_2 = (mu);
        let x_3 = (err);
        let x_4 = (halted);
        let x_5 = (partition_ops);
        let x_6 = (mdl_ops);
        let x_7 = (info_gain);
        let x_8 = (error_code);
        let x_9 = (mstatus);
        let x_10 = (mcycle_lo);
        let x_11 = (mcycle_hi);
        let x_12 = (minstret_lo);
        let x_13 = (minstret_hi);
        let x_14 = (logic_acc);
        let x_15 = (cert_addr);
        let x_16 = (mu_tensor);
        let x_17 = (pt_next_id);
        let x_18 = (ptTable);
        Bit#(32) x_19 = (((((x_16)[(Bit#(4))'(4'h0)]) +
        ((x_16)[(Bit#(4))'(4'h1)])) + ((x_16)[(Bit#(4))'(4'h2)])) +
        ((x_16)[(Bit#(4))'(4'h3)]));
        Bit#(32) x_20 = (((((x_16)[(Bit#(4))'(4'h4)]) +
        ((x_16)[(Bit#(4))'(4'h5)])) + ((x_16)[(Bit#(4))'(4'h6)])) +
        ((x_16)[(Bit#(4))'(4'h7)]));
        Bit#(32) x_21 = (((((x_16)[(Bit#(4))'(4'h8)]) +
        ((x_16)[(Bit#(4))'(4'h9)])) + ((x_16)[(Bit#(4))'(4'ha)])) +
        ((x_16)[(Bit#(4))'(4'hb)]));
        Bit#(32) x_22 = (((((x_16)[(Bit#(4))'(4'hc)]) +
        ((x_16)[(Bit#(4))'(4'hd)])) + ((x_16)[(Bit#(4))'(4'he)])) +
        ((x_16)[(Bit#(4))'(4'hf)]));
        Bit#(32) x_23 = ((((x_19) + (x_20)) + (x_21)) + (x_22));
        Bool x_24 = ((x_2) < (x_23));
        Bit#(32) x_25 = (zeroExtend(x_17));
        Bit#(32) x_26 = ((x_18)[(Bit#(6))'(6'h0)]);
        Bit#(32) x_27 = (((x_0) == ((Bit#(32))'(32'h0)) ? (x_1) : (((x_0) ==
        ((Bit#(32))'(32'h4)) ? (x_2) : (((x_0) == ((Bit#(32))'(32'h8)) ?
        ((x_3 ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)))) : (((x_0) ==
        ((Bit#(32))'(32'hc)) ? ((x_4 ? ((Bit#(32))'(32'h1)) :
        ((Bit#(32))'(32'h0)))) : (((x_0) == ((Bit#(32))'(32'h10)) ? (x_5) :
        (((x_0) == ((Bit#(32))'(32'h14)) ? (x_6) : (((x_0) ==
        ((Bit#(32))'(32'h18)) ? (x_7) : (((x_0) == ((Bit#(32))'(32'h1c)) ?
        (x_8) : (((x_0) == ((Bit#(32))'(32'h20)) ? (x_9) : (((x_0) ==
        ((Bit#(32))'(32'h24)) ? (x_10) : (((x_0) == ((Bit#(32))'(32'h28)) ?
        (x_11) : (((x_0) == ((Bit#(32))'(32'h2c)) ? (x_12) : (((x_0) ==
        ((Bit#(32))'(32'h30)) ? (x_13) : (((x_0) == ((Bit#(32))'(32'h34)) ?
        (x_14) : (((x_0) == ((Bit#(32))'(32'h38)) ? (x_15) : (((x_0) ==
        ((Bit#(32))'(32'h44)) ? (x_19) : (((x_0) == ((Bit#(32))'(32'h48)) ?
        (x_20) : (((x_0) == ((Bit#(32))'(32'h4c)) ? (x_21) : (((x_0) ==
        ((Bit#(32))'(32'h50)) ? (x_22) : (((x_0) == ((Bit#(32))'(32'h54)) ?
        ((x_24 ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)))) : (((x_0) ==
        ((Bit#(32))'(32'h58)) ? (x_25) : (((x_0) == ((Bit#(32))'(32'h5c)) ?
        (x_26) :
        ((Bit#(32))'(32'h0))))))))))))))))))))))))))))))))))))))))))))));
        
        return x_27;
    endmethod
    
    method ActionValue#(Bool) apbReadErr (Bit#(32) x_0);
        Bool x_1 = (((((((((((((((((((((((x_0) == ((Bit#(32))'(32'h0))) ||
        ((x_0) == ((Bit#(32))'(32'h4)))) || ((x_0) == ((Bit#(32))'(32'h8))))
        || ((x_0) == ((Bit#(32))'(32'hc)))) || ((x_0) ==
        ((Bit#(32))'(32'h10)))) || ((x_0) == ((Bit#(32))'(32'h14)))) ||
        ((x_0) == ((Bit#(32))'(32'h18)))) || ((x_0) ==
        ((Bit#(32))'(32'h1c)))) || ((x_0) == ((Bit#(32))'(32'h20)))) ||
        ((x_0) == ((Bit#(32))'(32'h24)))) || ((x_0) ==
        ((Bit#(32))'(32'h28)))) || ((x_0) == ((Bit#(32))'(32'h2c)))) ||
        ((x_0) == ((Bit#(32))'(32'h30)))) || ((x_0) ==
        ((Bit#(32))'(32'h34)))) || ((x_0) == ((Bit#(32))'(32'h38)))) ||
        ((x_0) == ((Bit#(32))'(32'h44)))) || ((x_0) ==
        ((Bit#(32))'(32'h48)))) || ((x_0) == ((Bit#(32))'(32'h4c)))) ||
        ((x_0) == ((Bit#(32))'(32'h50)))) || ((x_0) ==
        ((Bit#(32))'(32'h54)))) || ((x_0) == ((Bit#(32))'(32'h58)))) ||
        ((x_0) == ((Bit#(32))'(32'h5c))));
        return ! (x_1);
    endmethod
    
    method ActionValue#(Bool) apbWrite (Struct2 x_0);
        let x_1 = (imem);
        let x_2 = (active_module);
        let x_3 = (trap_vector);
        let x_4 = (bus_load_instr_addr);
        let x_5 = (bus_load_instr_data);
        let x_6 = (bus_load_instr_kick);
        Bit#(32) x_7 = ((x_0).addr);
        Bit#(128) x_8 = ((x_0).data);
        Bit#(32) x_9 = ((x_8)[31:0]);
        Bool x_10 = ((x_7) == ((Bit#(32))'(32'h80)));
        Bool x_11 = ((x_7) == ((Bit#(32))'(32'h84)));
        Bool x_12 = ((x_7) == ((Bit#(32))'(32'h88)));
        Bool x_13 = ((x_7) == ((Bit#(32))'(32'h98)));
        Bool x_14 = ((x_7) == ((Bit#(32))'(32'h9c)));
        Bool x_15 = (((((x_10) || (x_11)) || (x_12)) || (x_13)) || (x_14));
        
        Bit#(7) x_16 = ((x_9)[6:0]);
        Bit#(128) x_17 = (x_8);
        Bool x_18 = (! ((x_8) == ((Bit#(128))'(128'h0))));
        Bit#(7) x_19 = ((x_10 ? (x_16) : (x_4)));
        Bit#(128) x_20 = ((x_11 ? (x_17) : (x_5)));
        Bool x_21 = ((x_12 ? (x_18) : (x_6)));
        Bool x_22 = ((x_12) && (x_18));
        Vector#(128, Bit#(128)) x_23 = ((x_22 ? (update (x_1, x_19, x_20)) :
        (x_1)));
        Bit#(6) x_24 = ((x_13 ? ((x_9)[5:0]) : (x_2)));
        Bit#(32) x_25 = ((x_14 ? (x_9) : (x_3)));
        imem <= x_23;
        bus_load_instr_addr <= x_19;
        bus_load_instr_data <= x_20;
        bus_load_instr_kick <= x_21;
        active_module <= x_24;
        trap_vector <= x_25;
        return ! (x_15);
    endmethod
    
    method ActionValue#(Bool) getBianchiAlarm ();
        let x_1 = (mu_tensor);
        let x_2 = (mu);
        Bit#(32) x_3 = (((((((((((((((((x_1)[(Bit#(4))'(4'h0)]) +
        ((x_1)[(Bit#(4))'(4'h1)])) + ((x_1)[(Bit#(4))'(4'h2)])) +
        ((x_1)[(Bit#(4))'(4'h3)])) + ((x_1)[(Bit#(4))'(4'h4)])) +
        ((x_1)[(Bit#(4))'(4'h5)])) + ((x_1)[(Bit#(4))'(4'h6)])) +
        ((x_1)[(Bit#(4))'(4'h7)])) + ((x_1)[(Bit#(4))'(4'h8)])) +
        ((x_1)[(Bit#(4))'(4'h9)])) + ((x_1)[(Bit#(4))'(4'ha)])) +
        ((x_1)[(Bit#(4))'(4'hb)])) + ((x_1)[(Bit#(4))'(4'hc)])) +
        ((x_1)[(Bit#(4))'(4'hd)])) + ((x_1)[(Bit#(4))'(4'he)])) +
        ((x_1)[(Bit#(4))'(4'hf)]));
        return (x_2) < (x_3);
    endmethod
    
    method ActionValue#(Bit#(32)) getPtNextId ();
        let x_1 = (pt_next_id);
        Bit#(32) x_2 = (zeroExtend(x_1));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getPtSize (Bit#(6) x_0);
        let x_1 = (ptTable);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(32)) getMorphNextId ();
        let x_1 = (morph_next_id);
        Bit#(32) x_2 = (zeroExtend(x_1));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getMorphSrc (Bit#(4) x_0);
        let x_1 = (morph_src_table);
        Bit#(32) x_2 = (zeroExtend((x_1)[x_0]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getMorphDst (Bit#(4) x_0);
        let x_1 = (morph_dst_table);
        Bit#(32) x_2 = (zeroExtend((x_1)[x_0]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getMorphCouplingDesc (Bit#(4) x_0);
        let x_1 = (morph_coupling_desc_table);
        Bit#(32) x_2 = (zeroExtend((x_1)[x_0]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getMorphValid (Bit#(4) x_0);
        let x_1 = (morph_valid_table);
        return ((x_1)[x_0] ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)));

    endmethod
    
    method ActionValue#(Bit#(32)) getMorphIdentity (Bit#(4) x_0);
        let x_1 = (morph_identity_table);
        return ((x_1)[x_0] ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)));

    endmethod
    
    method ActionValue#(Bit#(32)) getCouplingDescBase (Bit#(4) x_0);
        let x_1 = (coupling_desc_base_table);
        Bit#(32) x_2 = (zeroExtend((x_1)[x_0]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getCouplingDescCount (Bit#(4) x_0);
        let x_1 = (coupling_desc_count_table);
        Bit#(32) x_2 = (zeroExtend((x_1)[x_0]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getCouplingDescValid (Bit#(4) x_0);
        let x_1 = (coupling_desc_valid_table);
        return ((x_1)[x_0] ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)));

    endmethod
    
    method ActionValue#(Bit#(32)) getCouplingDescNextId ();
        let x_1 = (coupling_desc_next_id);
        Bit#(32) x_2 = (zeroExtend(x_1));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getCouplingPairSrc (Bit#(4) x_0);
        let x_1 = (coupling_pair_src_table);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(32)) getCouplingPairDst (Bit#(4) x_0);
        let x_1 = (coupling_pair_dst_table);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(32)) getCouplingPairValid (Bit#(4) x_0);
        let x_1 = (coupling_pair_valid_table);
        return ((x_1)[x_0] ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)));

    endmethod
    
    method ActionValue#(Bit#(32)) getCouplingPairNextId ();
        let x_1 = (coupling_pair_next_id);
        Bit#(32) x_2 = (zeroExtend(x_1));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getFormulaDescBase (Bit#(4) x_0);
        let x_1 = (formula_desc_base_table);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(32)) getFormulaDescCount (Bit#(4) x_0);
        let x_1 = (formula_desc_count_table);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(32)) getFormulaDescValid (Bit#(4) x_0);
        let x_1 = (formula_desc_valid_table);
        return ((x_1)[x_0] ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)));

    endmethod
    
    method ActionValue#(Bit#(32)) getFormulaDescNextId ();
        let x_1 = (formula_desc_next_id);
        Bit#(32) x_2 = (zeroExtend(x_1));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getCertDescBase (Bit#(4) x_0);
        let x_1 = (cert_desc_base_table);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(32)) getCertDescCount (Bit#(4) x_0);
        let x_1 = (cert_desc_count_table);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(32)) getCertDescValid (Bit#(4) x_0);
        let x_1 = (cert_desc_valid_table);
        return ((x_1)[x_0] ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)));

    endmethod
    
    method ActionValue#(Bit#(32)) getCertDescNextId ();
        let x_1 = (cert_desc_next_id);
        Bit#(32) x_2 = (zeroExtend(x_1));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getDescMetaSubtype (Bit#(4) x_0);
        let x_1 = (desc_meta_subtype_table);
        Bit#(32) x_2 = (zeroExtend((x_1)[x_0]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getDescMetaKind (Bit#(4) x_0);
        let x_1 = (desc_meta_kind_table);
        Bit#(32) x_2 = (zeroExtend((x_1)[x_0]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getDescMetaInlineLen (Bit#(4) x_0);
        let x_1 = (desc_meta_inline_len_table);
        Bit#(32) x_2 = (zeroExtend((x_1)[x_0]));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getDescMetaAux (Bit#(4) x_0);
        let x_1 = (desc_meta_aux_table);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(32)) getDescMetaValid (Bit#(4) x_0);
        let x_1 = (desc_meta_valid_table);
        return ((x_1)[x_0] ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)));

    endmethod
    
    method ActionValue#(Bit#(32)) getDescMetaNextId ();
        let x_1 = (desc_meta_next_id);
        Bit#(32) x_2 = (zeroExtend(x_1));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertPhase ();
        let x_1 = (lassert_phase);
        Bit#(32) x_2 = (zeroExtend(x_1));
        return x_2;
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertKind ();
        let x_1 = (lassert_kind);
        return (x_1 ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)));
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertFBase ();
        let x_1 = (lassert_fbase);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertCBase ();
        let x_1 = (lassert_cbase);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertFLen ();
        let x_1 = (lassert_flen);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertCLen ();
        let x_1 = (lassert_clen);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertFPtr ();
        let x_1 = (lassert_fptr);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertCPtr ();
        let x_1 = (lassert_cptr);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertClauseSat ();
        let x_1 = (lassert_clause_sat);
        return (x_1 ? ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)));
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertFbufWord (Bit#(6) x_0);
        let x_1 = (lassert_fbuf);
        return (x_1)[x_0];
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertCbufWord (Bit#(6) x_0);
        let x_1 = (lassert_cbuf);
        return (x_1)[x_0];
    endmethod
    
endmodule

module mkThieleCPU (ThieleCPU);Module1 m1 <- mkModule1 ();
                               
endmodule
