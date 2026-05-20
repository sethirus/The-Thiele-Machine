import Vector::*;
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
    RegFile#(Bit#(7), Bit#(32)) mem <- mkRegFileFullZero();
    RegFile#(Bit#(7), Bit#(128)) imem <- mkRegFileFullZero();
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
    RegFile#(Bit#(6), Bit#(32)) lassert_fbuf <- mkRegFileFullZero();
    RegFile#(Bit#(6), Bit#(32)) lassert_cbuf <- mkRegFileFullZero();
    Reg#(Bool) lassert_clause_sat <- mkReg(False);
    Reg#(Bool) lassert_counter_clause_sat <- mkReg(False);
    Reg#(Bool) lassert_counter_seen_fail <- mkReg(False);
    Reg#(Bit#(5)) chsh_phase <- mkReg(unpack(0));
    Reg#(Bit#(64)) chsh_n00 <- mkReg(unpack(0));
    Reg#(Bit#(64)) chsh_n01 <- mkReg(unpack(0));
    Reg#(Bit#(64)) chsh_n10 <- mkReg(unpack(0));
    Reg#(Bit#(64)) chsh_n11 <- mkReg(unpack(0));
    Reg#(Bit#(64)) chsh_d00 <- mkReg(unpack(0));
    Reg#(Bit#(64)) chsh_d01 <- mkReg(unpack(0));
    Reg#(Bit#(64)) chsh_d10 <- mkReg(unpack(0));
    Reg#(Bit#(64)) chsh_d11 <- mkReg(unpack(0));
    Reg#(Bool) chsh_sign00 <- mkReg(False);
    Reg#(Bool) chsh_sign01 <- mkReg(False);
    Reg#(Bool) chsh_sign10 <- mkReg(False);
    Reg#(Bool) chsh_sign11 <- mkReg(False);
    Reg#(Bit#(128)) chsh_n00sq <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_n01sq <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_n10sq <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_n11sq <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_d00sq <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_d01sq <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_d10sq <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_d11sq <- mkReg(unpack(0));
    Reg#(Bit#(256)) chsh_A_pos <- mkReg(unpack(0));
    Reg#(Bit#(256)) chsh_A_neg_a <- mkReg(unpack(0));
    Reg#(Bit#(256)) chsh_A_neg_b <- mkReg(unpack(0));
    Reg#(Bit#(256)) chsh_B_pos <- mkReg(unpack(0));
    Reg#(Bit#(256)) chsh_B_neg_a <- mkReg(unpack(0));
    Reg#(Bit#(256)) chsh_B_neg_b <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_d00d01 <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_n10n11 <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_d10d11 <- mkReg(unpack(0));
    Reg#(Bit#(128)) chsh_n00n01 <- mkReg(unpack(0));
    Reg#(Bit#(256)) chsh_abs_C1 <- mkReg(unpack(0));
    Reg#(Bit#(256)) chsh_abs_C2 <- mkReg(unpack(0));
    Reg#(Bit#(384)) chsh_C_sq <- mkReg(unpack(0));
    Reg#(Bit#(384)) chsh_A_times_B <- mkReg(unpack(0));
    Reg#(Bool) chsh_check_result <- mkReg(False);
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
        let x_3 = (chsh_phase);
        when ((x_3) == ((Bit#(5))'(5'h0)), noAction);
        let x_4 = (chsh_check_result);
        let x_5 = (pc);
        let x_6 = (mu);
        let x_7 = (regs);

        let x_10 = (partition_ops);
        let x_11 = (mdl_ops);
        let x_12 = (info_gain);
        let x_13 = (error_code);
        let x_14 = (logic_acc);
        let x_15 = (cert_addr);
        let x_16 = (active_module);
        let x_17 = (mstatus);
        let x_18 = (mcycle_lo);
        let x_19 = (mcycle_hi);
        let x_20 = (minstret_lo);
        let x_21 = (minstret_hi);
        let x_22 = (trap_vector);
        let x_23 = (mu_tensor);
        let x_24 = (ptTable);
        let x_25 = (pt_next_id);
        let x_26 = (certified);
        let x_27 = (morph_src_table);
        let x_28 = (morph_dst_table);
        let x_29 = (morph_valid_table);
        let x_30 = (morph_coupling_desc_table);
        let x_31 = (morph_identity_table);
        let x_32 = (morph_next_id);
        let x_33 = (coupling_desc_valid_table);
        let x_34 = (coupling_desc_count_table);
        let x_35 = (coupling_desc_next_id);
        let x_36 = (coupling_pair_next_id);
        let x_37 = (formula_desc_valid_table);
        let x_38 = (formula_desc_next_id);
        let x_39 = (cert_desc_valid_table);
        let x_40 = (cert_desc_next_id);
        let x_41 = (desc_meta_valid_table);
        let x_42 = (desc_meta_next_id);
        let x_43 = (wc_same_00);
        let x_44 = (wc_diff_00);
        let x_45 = (wc_same_01);
        let x_46 = (wc_diff_01);
        let x_47 = (wc_same_10);
        let x_48 = (wc_diff_10);
        let x_49 = (wc_same_11);
        let x_50 = (wc_diff_11);
        Bit#(32) x_51 = ((x_23)[(Bit#(4))'(4'h0)]);
        Bit#(32) x_52 = ((x_23)[(Bit#(4))'(4'h1)]);
        Bit#(32) x_53 = ((x_23)[(Bit#(4))'(4'h2)]);
        Bit#(32) x_54 = ((x_23)[(Bit#(4))'(4'h3)]);
        Bit#(32) x_55 = ((x_23)[(Bit#(4))'(4'h4)]);
        Bit#(32) x_56 = ((x_23)[(Bit#(4))'(4'h5)]);
        Bit#(32) x_57 = ((x_23)[(Bit#(4))'(4'h6)]);
        Bit#(32) x_58 = ((x_23)[(Bit#(4))'(4'h7)]);
        Bit#(32) x_59 = ((x_23)[(Bit#(4))'(4'h8)]);
        Bit#(32) x_60 = ((x_23)[(Bit#(4))'(4'h9)]);
        Bit#(32) x_61 = ((x_23)[(Bit#(4))'(4'ha)]);
        Bit#(32) x_62 = ((x_23)[(Bit#(4))'(4'hb)]);
        Bit#(32) x_63 = ((x_23)[(Bit#(4))'(4'hc)]);
        Bit#(32) x_64 = ((x_23)[(Bit#(4))'(4'hd)]);
        Bit#(32) x_65 = ((x_23)[(Bit#(4))'(4'he)]);
        Bit#(32) x_66 = ((x_23)[(Bit#(4))'(4'hf)]);
        Bit#(32) x_67 = ((((((((((((((((x_51) + (x_52)) + (x_53)) + (x_54)) +
        (x_55)) + (x_56)) + (x_57)) + (x_58)) + (x_59)) + (x_60)) + (x_61)) +
        (x_62)) + (x_63)) + (x_64)) + (x_65)) + (x_66));
        Bool x_68 = ((x_6) < (x_67));
        Bit#(7) x_69 = ((x_5)[6:0]);
        Bit#(128) x_70 = (imem.sub(x_69));
        Bit#(32) x_71 = ((x_70)[31:0]);
        Bit#(8) x_72 = ((x_70)[127:120]);
        Bit#(8) x_73 = ((x_70)[119:112]);
        Bit#(16) x_74 = ((x_70)[111:96]);
        Bit#(32) x_75 = ((x_70)[63:32]);
        Bit#(8) x_76 = ((x_71)[31:24]);
        Bit#(8) x_77 = ((x_71)[23:16]);
        Bit#(8) x_78 = ((x_71)[15:8]);
        Bit#(8) x_79 = ((x_71)[7:0]);
        Bit#(4) x_80 = ((x_74)[15:12]);
        Bit#(4) x_81 = ((x_74)[11:8]);
        Bit#(8) x_82 = ((x_74)[7:0]);
        Bit#(4) x_83 = ((x_75)[3:0]);
        Bit#(4) x_84 = ((x_75)[9:6]);
        Bit#(5) x_85 = (zeroExtend(x_83));
        Bit#(5) x_86 = (zeroExtend(x_84));
        Bool x_87 = (! ((x_84) == ((Bit#(4))'(4'h0))));
        Bool x_88 = ((((((((x_76) == ((Bit#(8))'(8'h27))) || ((x_76) ==
        ((Bit#(8))'(8'h28)))) || ((x_76) == ((Bit#(8))'(8'h29)))) || ((x_76)
        == ((Bit#(8))'(8'h2a)))) || ((x_76) == ((Bit#(8))'(8'h2b)))) ||
        ((x_76) == ((Bit#(8))'(8'h2c)))) || ((x_76) == ((Bit#(8))'(8'h2d))));
        
        Bool x_89 = ((((((((x_76) == ((Bit#(8))'(8'h3))) || ((x_76) ==
        ((Bit#(8))'(8'h4)))) || ((x_76) == ((Bit#(8))'(8'he)))) || ((x_76) ==
        ((Bit#(8))'(8'hf)))) || ((x_76) == ((Bit#(8))'(8'h1e)))) || ((x_76)
        == ((Bit#(8))'(8'h2b)))) || ((x_76) == ((Bit#(8))'(8'h2e))));
        Bool x_90 = ((((x_76) == ((Bit#(8))'(8'h15))) || ((x_76) ==
        ((Bit#(8))'(8'h16)))) || ((x_76) == ((Bit#(8))'(8'h17))));
        Bool x_91 = ((((x_76) == ((Bit#(8))'(8'hf))) || ((x_76) ==
        ((Bit#(8))'(8'h25)))) || ((x_76) == ((Bit#(8))'(8'h26))));
        Bool x_92 = (((((((x_73) == ((Bit#(8))'(8'h0))) || ((x_73) ==
        ((Bit#(8))'(8'h1)))) || ((x_73) == ((Bit#(8))'(8'h2)))) || ((x_73) ==
        ((Bit#(8))'(8'h3)))) || ((x_73) == ((Bit#(8))'(8'h4)))) || ((x_73) ==
        ((Bit#(8))'(8'h5))));
        Bool x_93 = (((x_73) == ((Bit#(8))'(8'h0)) ? ((Bool)'(True)) :
        (((x_73) == ((Bit#(8))'(8'h1)) ? (x_90) : (((x_73) ==
        ((Bit#(8))'(8'h2)) ? (x_91) : (((x_73) == ((Bit#(8))'(8'h3)) ? (x_88)
        : (((x_73) == ((Bit#(8))'(8'h4)) ? ((x_88) || (x_89)) : (((x_73) ==
        ((Bit#(8))'(8'h5)) ? (x_89) : ((Bool)'(False))))))))))))));
        Bool x_94 = ((x_81) == ((Bit#(4))'(4'h0)));
        Bool x_95 = ((x_81) == ((Bit#(4))'(4'h0)));
        Bool x_96 = ((x_81) == ((Bit#(4))'(4'h1)));
        Bool x_97 = ((x_81) == ((Bit#(4))'(4'h2)));
        Bool x_98 = ((x_81) == ((Bit#(4))'(4'h3)));
        Bool x_99 = ((x_81) == ((Bit#(4))'(4'h4)));
        Bool x_100 = (((((x_95) || (x_96)) || (x_97)) || (x_98)) || (x_99));
        
        Bool x_101 = ((x_74) == ((Bit#(16))'(16'h0)));
        Bool x_102 = ((x_82) == ((Bit#(8))'(8'h0)));
        Bool x_103 = (((Bit#(8))'(8'h8)) < (x_82));
        Bool x_104 = (((((x_73) == ((Bit#(8))'(8'h0))) || ((x_73) ==
        ((Bit#(8))'(8'h1)))) || ((x_73) == ((Bit#(8))'(8'h2)))) && (!
        (x_101)));
        Bool x_105 = ((((x_73) == ((Bit#(8))'(8'h3))) || ((x_73) ==
        ((Bit#(8))'(8'h5)))) && (((! (x_94)) || (x_102)) || (x_103)));
        Bool x_106 = (((x_73) == ((Bit#(8))'(8'h4))) && ((! (x_102)) || (!
        (x_100))));
        Bool x_107 = ((! ((x_85) < (x_32))) || (! ((x_29)[x_83])));
        Bool x_108 = ((x_87) && ((! ((x_86) < (x_32))) || (!
        ((x_29)[x_84]))));
        Bool x_109 = ((! ((x_85) < (x_35))) || (! ((x_33)[x_83])));
        Bool x_110 = ((x_87) && ((! ((x_86) < (x_35))) || (!
        ((x_33)[x_84]))));
        Bool x_111 = ((! ((x_85) < (x_38))) || (! ((x_37)[x_83])));
        Bool x_112 = ((x_87) && ((! ((x_86) < (x_38))) || (!
        ((x_37)[x_84]))));
        Bool x_113 = ((! ((x_85) < (x_40))) || (! ((x_39)[x_83])));
        Bool x_114 = ((x_87) && ((! ((x_86) < (x_40))) || (!
        ((x_39)[x_84]))));
        Bool x_115 = ((! ((x_85) < (x_42))) || (! ((x_41)[x_83])));
        Bool x_116 = ((x_87) && ((! ((x_86) < (x_42))) || (!
        ((x_41)[x_84]))));
        Bool x_117 = (((x_73) == ((Bit#(8))'(8'h4))) && ((((x_95) || (x_96))
        || (x_99)) && ((((x_95) && ((x_107) || (x_108))) || ((x_96) &&
        ((x_109) || (x_110)))) || ((x_99) && ((x_115) || (x_116))))));
        Bool x_118 = ((((x_73) == ((Bit#(8))'(8'h4))) && (x_89)) && (!
        ((x_97) || (x_98))));
        Bool x_119 = ((((x_73) == ((Bit#(8))'(8'h4))) && (x_88)) && (!
        (((x_95) || (x_96)) || (x_99))));
        Bool x_120 = (((x_73) == ((Bit#(8))'(8'h4))) && (((x_118) || ((x_97)
        && ((x_111) || (x_112)))) || ((x_98) && ((x_113) || (x_114)))));
        Bool x_121 = (((((x_76) == ((Bit#(8))'(8'h27))) || ((x_76) ==
        ((Bit#(8))'(8'h28)))) || ((x_76) == ((Bit#(8))'(8'h29)))) || ((x_76)
        == ((Bit#(8))'(8'h2c))));
        Bool x_122 = (((x_121) && (! ((x_32) < ((Bit#(5))'(5'h10))))) ||
        (((((x_73) == ((Bit#(8))'(8'h3))) || ((x_73) == ((Bit#(8))'(8'h4))))
        && ((x_76) == ((Bit#(8))'(8'h27)))) && ((! ((x_35) <
        ((Bit#(5))'(5'h10)))) || (! ((x_36) < ((Bit#(5))'(5'h10)))))));
        Bool x_123 = (! ((x_72) == ((Bit#(8))'(8'h2))));
        Bool x_124 = (((! (x_92)) || (! (x_93))) || (x_119));
        Bool x_125 = (((x_104) || (x_105)) || (x_106));
        Bool x_126 = ((((((x_123) || (x_124)) || (x_125)) || (x_117)) ||
        (x_122)) || (x_120));
        Bit#(32) x_127 = ((x_123 ? ((Bit#(32))'(32'hbadc0010)) : ((x_124 ?
        ((Bit#(32))'(32'hbadc0011)) : ((x_125 ? ((Bit#(32))'(32'hbadc0013)) :
        ((x_117 ? ((Bit#(32))'(32'hbadc0012)) : ((x_122 ?
        ((Bit#(32))'(32'hbadc0014)) : ((x_120 ? ((Bit#(32))'(32'hbadc0015)) :
        (x_13)))))))))))));
        Bit#(32) x_128 = (zeroExtend(x_79));
        Bit#(32) x_129 = (zeroExtend(x_78));
        Bit#(32) x_130 = (((((x_76) == ((Bit#(8))'(8'he))) || ((x_76) ==
        ((Bit#(8))'(8'hf)))) || ((x_76) == ((Bit#(8))'(8'h1a))) ? (x_129) :
        ((Bit#(32))'(32'h0))));
        Bit#(32) x_131 = ((((x_6) + (x_130)) + (x_128)) +
        ((Bit#(32))'(32'h1)));
        Bit#(1) x_132 = ((x_77)[5:5]);
        Bool x_133 = ((x_132) == ((Bit#(1))'(1'h1)));
        Bool x_134 = ((x_76) == ((Bit#(8))'(8'h3)));
        Bool x_135 = ((x_134) && (! (x_133)));
        Bit#(32) x_136 = ((x_6) + (x_128));
        Bit#(32) x_137 = ((x_5) + ((Bit#(32))'(32'h1)));
        Bit#(4) x_138 = ((x_77)[3:0]);
        Bit#(4) x_139 = ((x_78)[3:0]);
        Bit#(4) x_140 = ((x_78)[7:4]);
        Bit#(4) x_141 = ((x_78)[3:0]);
        Bit#(4) x_142 = (truncate(x_140));
        Bit#(4) x_143 = (truncate(x_141));
        Bit#(32) x_144 = ((x_7)[x_142]);
        Bit#(32) x_145 = ((x_7)[x_143]);
        Bit#(32) x_146 = ((x_7)[x_138]);
        Bit#(32) x_147 = ((x_7)[x_139]);
        Bit#(32) x_148 = (zeroExtend(x_78));
        Bit#(7) x_149 = ((x_147)[6:0]);
        Bit#(7) x_150 = ((x_146)[6:0]);
        Bit#(7) x_151 = (truncate(x_78));
        Bit#(32) x_152 = (mem.sub(x_149));
        Bit#(32) x_153 = (mem.sub(x_151));
        Bit#(32) x_154 = ((x_7)[(Bit#(4))'(4'hf)]);
        Bit#(7) x_155 = ((x_154)[6:0]);
        Bit#(32) x_156 = ((x_154) + ((Bit#(32))'(32'h1)));
        Bit#(32) x_157 = ((x_154) - ((Bit#(32))'(32'h1)));
        Bit#(7) x_158 = ((x_157)[6:0]);
        Bit#(32) x_159 = ((x_24)[x_16]);
        Bool x_160 = ((zeroExtend(x_149)) < (x_159));
        Bool x_161 = ((zeroExtend(x_150)) < (x_159));
        Bool x_162 = ((zeroExtend(x_155)) < (x_159));
        Bool x_163 = ((zeroExtend(x_158)) < (x_159));
        Bool x_164 = (((x_76) == ((Bit#(8))'(8'h11))) || ((x_76) ==
        ((Bit#(8))'(8'h1c))));
        Bool x_165 = (((x_76) == ((Bit#(8))'(8'h12))) || ((x_76) ==
        ((Bit#(8))'(8'h1d))));
        Bool x_166 = ((x_76) == ((Bit#(8))'(8'h17)));
        Bool x_167 = ((x_76) == ((Bit#(8))'(8'h18)));
        Bool x_168 = ((x_164) && (! (x_160)));
        Bool x_169 = ((x_165) && (! (x_161)));
        Bool x_170 = ((x_166) && (! (x_162)));
        Bool x_171 = ((x_167) && (! (x_163)));
        Bool x_172 = ((((x_168) || (x_169)) || (x_170)) || (x_171));
        Bool x_173 = ((x_14) == ((Bit#(32))'(32'hcafeeace)));
        Bool x_174 = ((((x_76) == ((Bit#(8))'(8'hf))) || ((x_76) ==
        ((Bit#(8))'(8'h6)))) || ((x_76) == ((Bit#(8))'(8'h9))));
        Bool x_175 = ((x_174) && (! (x_173)));
        Bool x_176 = (! ((x_25) < ((Bit#(7))'(7'h40))));
        Bool x_177 = (! (x_176));
        Bool x_178 = (! (((Bit#(7))'(7'h40)) < ((x_25) +
        ((Bit#(7))'(7'h2)))));
        Bool x_179 = (((x_76) == ((Bit#(8))'(8'h0))) && (! (x_177)));
        Bool x_180 = (((x_76) == ((Bit#(8))'(8'h1))) && (! (x_178)));
        Bool x_181 = (((x_76) == ((Bit#(8))'(8'h2))) && (! (x_177)));
        Bool x_182 = (((x_179) || (x_180)) || (x_181));
        Bit#(6) x_183 = ((x_78)[5:0]);
        Bit#(32) x_184 = ((x_24)[x_183]);
        Bit#(32) x_185 = (zeroExtend(x_78));
        Bit#(16) x_186 = ({(x_77),(x_78)});
        Bit#(32) x_187 = (zeroExtend(x_186));
        Bit#(32) x_188 = ((x_163 ? (mem.sub(x_158)) : ((Bit#(32))'(32'h0))));
        
        Bool x_189 = ((x_73) == ((Bit#(8))'(8'h3)));
        Bool x_190 = (((x_76) == ((Bit#(8))'(8'h27))) && (x_189));
        Bool x_191 = (((x_76) == ((Bit#(8))'(8'h28))) && (x_189));
        Bool x_192 = (((x_76) == ((Bit#(8))'(8'h29))) && (x_189));
        Bool x_193 = (((x_76) == ((Bit#(8))'(8'h2a))) && (x_189));
        Bool x_194 = (((x_76) == ((Bit#(8))'(8'h2d))) && (x_189));
        Bool x_195 = (((x_76) == ((Bit#(8))'(8'h2b))) && ((x_73) ==
        ((Bit#(8))'(8'h5))));
        Bool x_196 = (((x_76) == ((Bit#(8))'(8'h27))) && (! (x_189)));
        Bool x_197 = (((x_76) == ((Bit#(8))'(8'h28))) && (! (x_189)));
        Bool x_198 = (((x_76) == ((Bit#(8))'(8'h29))) && (! (x_189)));
        Bool x_199 = (((x_76) == ((Bit#(8))'(8'h2a))) && (! (x_189)));
        Bool x_200 = (((x_76) == ((Bit#(8))'(8'h2d))) && (! (x_189)));
        Bool x_201 = (((x_76) == ((Bit#(8))'(8'h2b))) && (! ((x_73) ==
        ((Bit#(8))'(8'h5)))));
        Bool x_202 = (((x_76) == ((Bit#(8))'(8'h2c))) && (x_189));
        Bool x_203 = (((x_76) == ((Bit#(8))'(8'h2c))) && (! (x_189)));
        Bool x_204 = ((x_76) == ((Bit#(8))'(8'h2c)));
        Bit#(6) x_205 = ((x_75)[5:0]);
        Bit#(4) x_206 = ((x_75)[9:6]);
        Bit#(4) x_207 = ((x_75)[3:0]);
        Bit#(2) x_208 = ((x_75)[1:0]);
        Bit#(32) x_209 = (x_75);
        Bit#(6) x_210 = ((x_78)[5:0]);
        Bit#(6) x_211 = ((x_78)[5:0]);
        Bit#(4) x_212 = ((x_78)[3:0]);
        Bit#(4) x_213 = ((x_77)[3:0]);
        Bit#(4) x_214 = ((x_77)[3:0]);
        Bit#(4) x_215 = ((x_32)[3:0]);
        Bit#(32) x_216 = (zeroExtend(x_215));
        Bit#(5) x_217 = (zeroExtend(x_206));
        Bit#(5) x_218 = (zeroExtend(x_207));
        Bit#(5) x_219 = (zeroExtend(x_212));
        Bit#(5) x_220 = (zeroExtend(x_213));
        Bit#(5) x_221 = (zeroExtend(x_214));
        Bool x_222 = ((x_32) < ((Bit#(5))'(5'h10)));
        Bool x_223 = (! (((x_24)[x_210]) == ((Bit#(32))'(32'h0))));
        Bool x_224 = (! (((x_24)[x_205]) == ((Bit#(32))'(32'h0))));
        Bool x_225 = (! (((x_24)[x_211]) == ((Bit#(32))'(32'h0))));
        Bool x_226 = ((x_206) == ((Bit#(4))'(4'h0)));
        Bool x_227 = (((x_217) < (x_35)) && ((x_33)[x_206]));
        Bool x_228 = ((x_226) || (x_227));
        Bool x_229 = (((x_219) < (x_32)) && ((x_29)[x_212]));
        Bool x_230 = (((x_218) < (x_32)) && ((x_29)[x_207]));
        Bit#(6) x_231 = ((x_27)[x_212]);
        Bit#(6) x_232 = ((x_28)[x_212]);
        Bit#(6) x_233 = ((x_27)[x_207]);
        Bit#(6) x_234 = ((x_28)[x_207]);
        Bool x_235 = ((x_232) == (x_233));
        Bit#(4) x_236 = ((Bit#(4))'(4'h0));
        Bit#(5) x_237 = ((Bit#(5))'(5'h0));
        Bool x_238 = (((x_237) < (x_32)) && ((x_29)[x_236]));
        Bit#(6) x_239 = ((x_27)[x_236]);
        Bit#(6) x_240 = ((x_28)[x_236]);
        Bool x_241 = ((x_232) == (x_239));
        Bit#(4) x_242 = ((x_202 ? (x_207) : ((Bit#(4))'(4'h0))));
        Bit#(5) x_243 = ((x_202 ? (x_218) : ((Bit#(5))'(5'h0))));
        Bool x_244 = (((x_243) < (x_32)) && ((x_29)[x_242]));
        Bit#(6) x_245 = ((x_28)[x_242]);
        Bool x_246 = (((x_219) < (x_32)) && ((x_29)[x_212]));
        Bool x_247 = (((x_220) < (x_32)) && ((x_29)[x_213]));
        Bool x_248 = (((x_221) < (x_32)) && ((x_29)[x_214]));
        Bit#(6) x_249 = ((x_27)[x_212]);
        Bit#(6) x_250 = ((x_28)[x_212]);
        Bool x_251 = ((x_31)[x_212]);
        Bit#(4) x_252 = ((x_30)[x_212]);
        Bit#(5) x_253 = (zeroExtend(x_252));
        Bool x_254 = ((x_252) == ((Bit#(4))'(4'h0)));
        Bool x_255 = (((x_253) < (x_35)) && ((x_33)[x_252]));
        Bool x_256 = ((((x_194) && (x_246)) && (! (x_254))) && (! (x_255)));
        
        Bit#(5) x_257 = ((x_254 ? ((Bit#(5))'(5'h0)) : ((x_34)[x_252])));
        
        Bit#(32) x_258 = (zeroExtend(x_249));
        Bit#(32) x_259 = (zeroExtend(x_250));
        Bit#(32) x_260 = (zeroExtend(x_257));
        Bit#(32) x_261 = ((x_251 ? ((Bit#(32))'(32'h1)) :
        ((Bit#(32))'(32'h0))));
        Bit#(2) x_262 = ((x_194 ? (x_208) : ((Bit#(2))'(2'h0))));
        Bit#(32) x_263 = (((x_262) == ((Bit#(2))'(2'h0)) ? (x_258) :
        (((x_262) == ((Bit#(2))'(2'h1)) ? (x_259) : (((x_262) ==
        ((Bit#(2))'(2'h2)) ? (x_260) : (x_261)))))));
        Bool x_264 = (((x_190) && (((! (x_223)) || (! (x_224))) || (!
        (x_228)))) || ((x_192) && (! (x_225))));
        Bool x_265 = (((x_196) && (! (x_223))) || ((x_198) && (! (x_225))));
        
        Bool x_266 = (((x_191) && ((! (x_229)) || (! (x_230)))) || ((x_197)
        && ((! (x_229)) || (! (x_238)))));
        Bool x_267 = (((((x_191) && (x_229)) && (x_230)) && (! (x_235))) ||
        ((((x_197) && (x_229)) && (x_238)) && (! (x_241))));
        Bool x_268 = (((x_193) || (x_199)) && (! (x_247)));
        Bool x_269 = (((x_194) || (x_200)) && (! (x_246)));
        Bool x_270 = (((x_195) || (x_201)) && (! (x_248)));
        Bool x_271 = ((x_204) && (! (x_229)));
        Bool x_272 = (((x_204) && (x_229)) && (! (x_244)));
        Bool x_273 = ((((((((((x_264) || (x_265)) || (x_266)) || (x_267)) ||
        (x_268)) || (x_269)) || (x_256)) || (x_270)) || (x_271)) || (x_272));
        
        Bit#(32) x_274 = ((x_267 ? ((Bit#(32))'(32'hbadc0001)) :
        (((((((x_266) || (x_268)) || (x_269)) || (x_270)) || (x_271)) ||
        (x_272) ? ((Bit#(32))'(32'hbadc0003)) :
        ((Bit#(32))'(32'hbadc0000))))));
        Bool x_275 = (((((x_190) && (x_222)) && (x_223)) && (x_224)) &&
        (x_228));
        Bool x_276 = (((x_196) && (x_222)) && (x_223));
        Bool x_277 = (((x_192) && (x_222)) && (x_225));
        Bool x_278 = (((x_198) && (x_222)) && (x_225));
        Bool x_279 = (((((x_191) && (x_222)) && (x_229)) && (x_230)) &&
        (x_235));
        Bool x_280 = (((((x_197) && (x_222)) && (x_229)) && (x_238)) &&
        (x_241));
        Bool x_281 = ((((x_204) && (x_222)) && (x_229)) && (x_244));
        Bool x_282 = ((((x_194) || (x_200)) && (x_246)) && (! (x_256)));
        Bool x_283 = (((x_193) || (x_199)) && (x_247));
        Bool x_284 = (((x_195) || (x_201)) && (x_248));
        Bool x_285 = (((((((x_275) || (x_276)) || (x_277)) || (x_278)) ||
        (x_279)) || (x_280)) || (x_281));
        Bit#(6) x_286 = ((x_275 ? (x_210) : ((x_276 ? (x_210) : (((x_277) ||
        (x_278) ? (x_211) : ((x_279 ? (x_231) : ((x_280 ? (x_231) : ((x_281 ?
        (x_231) : (x_211)))))))))))));
        Bit#(6) x_287 = ((x_275 ? (x_205) : ((x_276 ? (x_210) : (((x_277) ||
        (x_278) ? (x_211) : ((x_279 ? (x_234) : ((x_280 ? (x_240) : ((x_281 ?
        (x_245) : (x_211)))))))))))));
        Bit#(4) x_288 = ((x_275 ? (x_206) : ((Bit#(4))'(4'h0))));
        Bool x_289 = ((x_277) || (x_278));
        Bit#(32) x_290 = ((x_144) + (x_145));
        Bit#(32) x_291 = ((x_144) - (x_145));
        Bit#(32) x_292 = ((x_144) & (x_145));
        Bit#(32) x_293 = ((x_144) | (x_145));
        Bit#(32) x_294 = ((x_144) << (x_145));
        Bit#(32) x_295 = ((x_144) >> (x_145));
        Bit#(32) x_296 = (multiply_unsigned ((x_144), (x_145)));
        Bit#(32) x_297 = ((Bit#(32))'(32'h8));
        Bit#(32) x_298 = ((x_148) << (x_297));
        Bit#(32) x_299 = ((x_146) ^ (x_147));
        Bool x_300 = (! ((x_146) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_301 = (x_147);
        Bit#(32) x_302 = ((Bit#(32))'(32'h55555555));
        Bit#(32) x_303 = ((x_301) & (x_302));
        Bit#(32) x_304 = (((x_301) >> ((Bit#(6))'(6'h1))) & (x_302));
        Bit#(32) x_305 = ((x_303) + (x_304));
        Bit#(32) x_306 = ((Bit#(32))'(32'h33333333));
        Bit#(32) x_307 = ((x_305) & (x_306));
        Bit#(32) x_308 = (((x_305) >> ((Bit#(6))'(6'h2))) & (x_306));
        Bit#(32) x_309 = ((x_307) + (x_308));
        Bit#(32) x_310 = ((Bit#(32))'(32'hf0f0f0f));
        Bit#(32) x_311 = ((x_309) & (x_310));
        Bit#(32) x_312 = (((x_309) >> ((Bit#(6))'(6'h4))) & (x_310));
        Bit#(32) x_313 = ((x_311) + (x_312));
        Bit#(32) x_314 = ((Bit#(32))'(32'hff00ff));
        Bit#(32) x_315 = ((x_313) & (x_314));
        Bit#(32) x_316 = (((x_313) >> ((Bit#(6))'(6'h8))) & (x_314));
        Bit#(32) x_317 = ((x_315) + (x_316));
        Bit#(32) x_318 = ((Bit#(32))'(32'hffff));
        Bit#(32) x_319 = ((x_317) & (x_318));
        Bit#(32) x_320 = (((x_317) >> ((Bit#(6))'(6'h10))) & (x_318));
        
        Bit#(32) x_321 = ((x_319) + (x_320));
        Bool x_322 = (((Bit#(8))'(8'h3)) < (x_78));
        Bool x_323 = (((Bit#(8))'(8'h1)) < (x_77));
        Bool x_324 = ((x_323) && ((x_67) == ((Bit#(32))'(32'h0))));
        Bool x_325 = (x_324);
        Bit#(2) x_326 = ((x_77)[1:0]);
        Bit#(2) x_327 = ((x_78)[1:0]);
        Bool x_328 = (((x_327) == ((Bit#(2))'(2'h0))) || ((x_327) ==
        ((Bit#(2))'(2'h3))));
        Bool x_329 = ((x_326) == ((Bit#(2))'(2'h0)));
        Bool x_330 = ((x_326) == ((Bit#(2))'(2'h1)));
        Bool x_331 = ((x_326) == ((Bit#(2))'(2'h2)));
        Bool x_332 = ((x_326) == ((Bit#(2))'(2'h3)));
        Bool x_333 = (((x_76) == ((Bit#(8))'(8'h6))) || ((x_76) ==
        ((Bit#(8))'(8'he))));
        Bool x_334 = ((x_76) == ((Bit#(8))'(8'h6)));
        Bool x_335 = ((x_334) && ((x_128) < (x_129)));
        Bool x_336 = (((((((((x_76) == ((Bit#(8))'(8'h9))) && (! (x_325))) &&
        (! (x_68))) && (! (x_172))) && (! (x_182))) && (! (x_175))) && (!
        (x_335))) && (! (x_126)));
        Bool x_337 = ((x_76) == ((Bit#(8))'(8'h2e)));
        Bit#(64) x_338 = (zeroExtend(x_43));
        Bit#(64) x_339 = (zeroExtend(x_44));
        Bit#(64) x_340 = (zeroExtend(x_45));
        Bit#(64) x_341 = (zeroExtend(x_46));
        Bit#(64) x_342 = (zeroExtend(x_47));
        Bit#(64) x_343 = (zeroExtend(x_48));
        Bit#(64) x_344 = (zeroExtend(x_49));
        Bit#(64) x_345 = (zeroExtend(x_50));
        Bit#(64) x_346 = ((x_338) + (x_339));
        Bit#(64) x_347 = ((x_340) + (x_341));
        Bit#(64) x_348 = ((x_342) + (x_343));
        Bit#(64) x_349 = ((x_344) + (x_345));
        Bool x_350 = ((x_338) < (x_339));
        Bool x_351 = ((x_340) < (x_341));
        Bool x_352 = ((x_342) < (x_343));
        Bool x_353 = ((x_344) < (x_345));
        Bit#(64) x_354 = ((x_350 ? ((x_339) - (x_338)) : ((x_338) -
        (x_339))));
        Bit#(64) x_355 = ((x_351 ? ((x_341) - (x_340)) : ((x_340) -
        (x_341))));
        Bit#(64) x_356 = ((x_352 ? ((x_343) - (x_342)) : ((x_342) -
        (x_343))));
        Bit#(64) x_357 = ((x_353 ? ((x_345) - (x_344)) : ((x_344) -
        (x_345))));
        Bool x_358 = ((((! ((x_346) == ((Bit#(64))'(64'h0)))) && (! ((x_347)
        == ((Bit#(64))'(64'h0))))) && (! ((x_348) == ((Bit#(64))'(64'h0)))))
        && (! ((x_349) == ((Bit#(64))'(64'h0)))));
        Bool x_359 = (x_4);
        Bool x_360 = ((Bool)'(False));
        Bit#(4) x_361 = ((x_77)[3:0]);
        Bit#(4) x_362 = ((x_75)[3:0]);
        Bit#(4) x_363 = ((((x_76) == ((Bit#(8))'(8'hf))) && ((x_73) ==
        ((Bit#(8))'(8'h2))) ? (x_362) : (x_361)));
        Bit#(32) x_364 = ((x_23)[x_363]);
        Bit#(32) x_365 = ((x_364) + (x_129));
        Bit#(32) x_366 = ((((((((x_68) || (x_172)) || (x_182)) || (x_175)) ||
        (x_335)) || (x_126)) || (x_273) ? (x_22) : (((x_76) ==
        ((Bit#(8))'(8'hff)) ? (x_5) : (((x_76) == ((Bit#(8))'(8'h15)) ?
        (x_187) : (((x_76) == ((Bit#(8))'(8'h17)) ? (x_187) : (((x_76) ==
        ((Bit#(8))'(8'h18)) ? (x_188) : ((((x_76) == ((Bit#(8))'(8'h16))) &&
        (x_300) ? (x_185) : (((x_76) == ((Bit#(8))'(8'h3)) ? ((x_133 ? (x_5)
        : (x_22))) : ((x_360 ? (x_22) : (x_137)))))))))))))))));
        
        Vector#(16, Bit#(32)) x_367 = (update (update (x_7, x_138, x_147),
        x_139, x_146));
        Vector#(16, Bit#(32)) x_368 = ((x_285 ? (update (x_7, x_138, x_216))
        : ((x_282 ? (update (x_7, x_138, x_263)) : (x_7)))));
        
        Vector#(16, Bit#(32)) x_369 = ((((((((x_68) || (x_172)) || (x_182))
        || (x_175)) || (x_335)) || (x_126)) || (x_273) ? (x_7) : (((x_76) ==
        ((Bit#(8))'(8'h8)) ? (update (x_7, x_138, x_148)) : (((x_76) ==
        ((Bit#(8))'(8'h13)) ? (update (x_7, x_138, x_290)) : (((x_76) ==
        ((Bit#(8))'(8'h14)) ? (update (x_7, x_138, x_291)) : (((x_76) ==
        ((Bit#(8))'(8'h7)) ? (update (x_7, x_138, x_147)) : (((x_76) ==
        ((Bit#(8))'(8'h11)) ? (update (x_7, x_138, x_152)) : (((x_76) ==
        ((Bit#(8))'(8'ha)) ? (update (x_7, x_138, x_153)) : (((x_76) ==
        ((Bit#(8))'(8'hb)) ? (update (x_7, x_138, x_299)) : (((x_76) ==
        ((Bit#(8))'(8'hc)) ? (x_367) : (((x_76) == ((Bit#(8))'(8'hd)) ?
        (update (x_7, x_138, x_321)) : (((x_76) == ((Bit#(8))'(8'h17)) ?
        (update (x_7, (Bit#(4))'(4'hf), x_156)) : (((x_76) ==
        ((Bit#(8))'(8'h18)) ? (update (x_7, (Bit#(4))'(4'hf), x_157)) :
        (((x_76) == ((Bit#(8))'(8'h6)) ? (update (x_7, x_138, x_184)) :
        (((x_76) == ((Bit#(8))'(8'h1c)) ? (update (x_7, x_138, x_152)) :
        (((x_76) == ((Bit#(8))'(8'h1a)) ? (update (x_7, x_138,
        (Bit#(32))'(32'h0))) : (((x_76) == ((Bit#(8))'(8'h1f)) ? (update
        (x_7, x_138, x_292)) : (((x_76) == ((Bit#(8))'(8'h20)) ? (update
        (x_7, x_138, x_293)) : (((x_76) == ((Bit#(8))'(8'h21)) ? (update
        (x_7, x_138, x_294)) : (((x_76) == ((Bit#(8))'(8'h22)) ? (update
        (x_7, x_138, x_295)) : (((x_76) == ((Bit#(8))'(8'h23)) ? (update
        (x_7, x_138, x_296)) : (((x_76) == ((Bit#(8))'(8'h24)) ? (update
        (x_7, x_138, x_298)) : (((x_76) == ((Bit#(8))'(8'h26)) ? (update
        (x_7, x_138, x_364)) :
        (x_368)))))))))))))))))))))))))))))))))))))))))))));

        Bool x_371 = (((((x_172) || (x_182)) || (x_175)) || (x_335)) ||
        ((x_76) == ((Bit#(8))'(8'hff))));
        Bool x_372 = (((((((((x_172) || (x_182)) || (x_175)) || (x_335)) ||
        (x_126)) || (x_273)) || (((x_76) == ((Bit#(8))'(8'h9))) && (x_325)))
        || (x_135)) || (x_360));
        Bit#(32) x_373 = ((x_68 ? ((Bit#(32))'(32'hb1a4c81)) : ((x_172 ?
        ((Bit#(32))'(32'hbadc0de)) : ((x_182 ? ((Bit#(32))'(32'hbadf001d)) :
        ((x_335 ? ((Bit#(32))'(32'hc43471a1)) : ((x_126 ? (x_127) : ((x_273 ?
        (x_274) : ((x_175 ? ((Bit#(32))'(32'hc43471a1)) : ((((x_76) ==
        ((Bit#(8))'(8'h9))) && (x_325) ? ((Bit#(32))'(32'hbadc45c)) : ((x_135
        ? ((Bit#(32))'(32'hc43471a1)) : ((x_360 ? ((Bit#(32))'(32'hbadc45c))
        : (x_13)))))))))))))))))))));
        Bit#(32) x_374 = (((x_76) == ((Bit#(8))'(8'h1e)) ? (((x_6) + (x_128))
        + ((Bit#(32))'(32'h1))) : (((x_76) == ((Bit#(8))'(8'h2b)) ? (((x_6) +
        (x_128)) + ((Bit#(32))'(32'h1))) : (((x_76) == ((Bit#(8))'(8'h2e)) ?
        (((x_6) + (x_128)) + ((Bit#(32))'(32'h1))) : (((x_76) ==
        ((Bit#(8))'(8'h3)) ? ((x_136) + ((Bit#(32))'(32'h1))) : (((((x_76) ==
        ((Bit#(8))'(8'he))) || ((x_76) == ((Bit#(8))'(8'hf)))) || ((x_76) ==
        ((Bit#(8))'(8'h1a))) ? (x_131) : (((x_76) == ((Bit#(8))'(8'h4)) ?
        ((x_136) + ((Bit#(32))'(32'h1))) : (x_136)))))))))))));
        Bit#(32) x_375 = ((((x_76) == ((Bit#(8))'(8'h9))) && (x_323) ?
        ((x_136) + ((Bit#(32))'(32'h100))) : (((x_76) == ((Bit#(8))'(8'h1e))
        ? (((x_6) + (x_128)) + ((Bit#(32))'(32'h1))) : (((x_76) ==
        ((Bit#(8))'(8'h2b)) ? (((x_6) + (x_128)) + ((Bit#(32))'(32'h1))) :
        (((x_76) == ((Bit#(8))'(8'h2e)) ? (((x_6) + (x_128)) +
        ((Bit#(32))'(32'h1))) : (((x_76) == ((Bit#(8))'(8'h3)) ? ((x_133 ?
        (x_6) : ((x_136) + ((Bit#(32))'(32'h1))))) : (((((x_76) ==
        ((Bit#(8))'(8'he))) || ((x_76) == ((Bit#(8))'(8'hf)))) || ((x_76) ==
        ((Bit#(8))'(8'h1a))) ? (x_131) : (((x_76) == ((Bit#(8))'(8'h4)) ?
        ((x_136) + ((Bit#(32))'(32'h1))) : (x_136)))))))))))))));
        Bit#(32) x_376 = (((((x_68) || (x_182)) || (x_175)) || (x_335) ?
        (x_6) : ((x_126 ? (x_374) : (x_375)))));
        Bool x_377 = ((((((((x_68) || (x_172)) || (x_182)) || (x_175)) ||
        (x_335)) || (x_126)) || (x_273) ? (x_26) : (((x_76) ==
        ((Bit#(8))'(8'h1e)) ? ((Bool)'(True)) : (x_26)))));
        Bit#(6) x_378 = ((x_25)[5:0]);
        Bit#(32) x_379 = (zeroExtend(x_77));
        Vector#(64, Bit#(32)) x_380 = (update (x_24, x_378, x_379));
        Bit#(7) x_381 = ((x_25) + ((Bit#(7))'(7'h1)));
        Bit#(6) x_382 = ((x_77)[5:0]);
        Bit#(32) x_383 = ((x_24)[x_382]);
        Bit#(32) x_384 = ((x_383) >> ((Bit#(5))'(5'h1)));
        Bit#(32) x_385 = ((x_383) - (x_384));
        Bit#(6) x_386 = ((x_25)[5:0]);
        Bit#(6) x_387 = (((x_25) + ((Bit#(7))'(7'h1)))[5:0]);
        
        Vector#(64, Bit#(32)) x_388 = (update (update (update (x_24, x_382,
        (Bit#(32))'(32'h0)), x_386, x_384), x_387, x_385));
        Bit#(7) x_389 = ((x_25) + ((Bit#(7))'(7'h2)));
        Bit#(6) x_390 = ((x_77)[5:0]);
        Bit#(6) x_391 = ((x_78)[5:0]);
        Bit#(32) x_392 = ((x_24)[x_390]);
        Bit#(32) x_393 = ((x_24)[x_391]);
        Bit#(32) x_394 = ((x_392) + (x_393));
        Bit#(6) x_395 = ((x_25)[5:0]);
        Vector#(64, Bit#(32)) x_396 = (update (update (update (x_24, x_390,
        (Bit#(32))'(32'h0)), x_391, (Bit#(32))'(32'h0)), x_395, x_394));
        
        Bit#(7) x_397 = ((x_25) + ((Bit#(7))'(7'h1)));
        Vector#(64, Bit#(32)) x_398 = (((((x_68) || (x_182)) || (x_126)) ||
        (x_273) ? (x_24) : (((x_76) == ((Bit#(8))'(8'h0)) ? (x_380) :
        (((x_76) == ((Bit#(8))'(8'h1)) ? (x_388) : (((x_76) ==
        ((Bit#(8))'(8'h2)) ? (x_396) : (x_24)))))))));
        Bit#(7) x_399 = (((((x_68) || (x_182)) || (x_126)) || (x_273) ?
        (x_25) : (((x_76) == ((Bit#(8))'(8'h0)) ? (x_381) : (((x_76) ==
        ((Bit#(8))'(8'h1)) ? (x_389) : (((x_76) == ((Bit#(8))'(8'h2)) ?
        (x_397) : (x_25)))))))));
        Bool x_400 = ((((x_76) == ((Bit#(8))'(8'h0))) || ((x_76) ==
        ((Bit#(8))'(8'h1)))) || ((x_76) == ((Bit#(8))'(8'h2))));
        Bit#(32) x_401 = (((((x_400) && (! (x_68))) && (! (x_126))) && (!
        (x_273)) ? ((x_10) + ((Bit#(32))'(32'h1))) : (x_10)));
        Bit#(32) x_402 = ((((((x_76) == ((Bit#(8))'(8'h5))) && (! (x_68))) &&
        (! (x_126))) && (! (x_273)) ? ((x_11) + ((Bit#(32))'(32'h1))) :
        (x_11)));
        Bit#(32) x_403 = (((((((((x_333) && (! (x_68))) && (! (x_172))) && (!
        (x_182))) && (! (x_175))) && (! (x_335))) && (! (x_126))) && (!
        (x_273)) ? ((x_12) + (x_129)) : (x_12)));
        Bit#(32) x_404 = ((((x_336) && (x_329)) && (x_328) ? ((x_43) +
        ((Bit#(32))'(32'h1))) : (x_43)));
        Bit#(32) x_405 = ((((x_336) && (x_329)) && (! (x_328)) ? ((x_44) +
        ((Bit#(32))'(32'h1))) : (x_44)));
        Bit#(32) x_406 = ((((x_336) && (x_330)) && (x_328) ? ((x_45) +
        ((Bit#(32))'(32'h1))) : (x_45)));
        Bit#(32) x_407 = ((((x_336) && (x_330)) && (! (x_328)) ? ((x_46) +
        ((Bit#(32))'(32'h1))) : (x_46)));
        Bit#(32) x_408 = ((((x_336) && (x_331)) && (x_328) ? ((x_47) +
        ((Bit#(32))'(32'h1))) : (x_47)));
        Bit#(32) x_409 = ((((x_336) && (x_331)) && (! (x_328)) ? ((x_48) +
        ((Bit#(32))'(32'h1))) : (x_48)));
        Bit#(32) x_410 = ((((x_336) && (x_332)) && (x_328) ? ((x_49) +
        ((Bit#(32))'(32'h1))) : (x_49)));
        Bit#(32) x_411 = ((((x_336) && (x_332)) && (! (x_328)) ? ((x_50) +
        ((Bit#(32))'(32'h1))) : (x_50)));
        Vector#(16, Bit#(32)) x_412 = (((((((x_76) == ((Bit#(8))'(8'hf))) &&
        (! (x_68))) && (! (x_175))) && (! (x_126))) && (! (x_273)) ? (update
        (x_23, x_363, x_365)) : ((((((x_76) == ((Bit#(8))'(8'h25))) && (!
        (x_68))) && (! (x_126))) && (! (x_273)) ? (update (x_23, x_363,
        x_147)) : (x_23)))));
        Vector#(16, Bit#(6)) x_413 = ((((((((x_68) || (x_172)) || (x_182)) ||
        (x_175)) || (x_335)) || (x_126)) || (x_273) ? (x_27) : ((x_285 ?
        (update (x_27, x_215, x_286)) : (x_27)))));
        Vector#(16, Bit#(6)) x_414 = ((((((((x_68) || (x_172)) || (x_182)) ||
        (x_175)) || (x_335)) || (x_126)) || (x_273) ? (x_28) : ((x_285 ?
        (update (x_28, x_215, x_287)) : (x_28)))));
        Vector#(16, Bit#(4)) x_415 = ((((((((x_68) || (x_172)) || (x_182)) ||
        (x_175)) || (x_335)) || (x_126)) || (x_273) ? (x_30) : ((x_285 ?
        (update (x_30, x_215, x_288)) : (x_30)))));
        Vector#(16, Bool) x_416 = ((((((((x_68) || (x_172)) || (x_182)) ||
        (x_175)) || (x_335)) || (x_126)) || (x_273) ? (x_31) : ((x_285 ?
        (update (x_31, x_215, x_289)) : (x_31)))));
        Vector#(16, Bool) x_417 = ((((((((x_68) || (x_172)) || (x_182)) ||
        (x_175)) || (x_335)) || (x_126)) || (x_273) ? (x_29) : ((x_285 ?
        (update (x_29, x_215, (Bool)'(True))) : ((x_283 ? (update (x_29,
        x_213, (Bool)'(False))) : (x_29)))))));
        Bit#(5) x_418 = ((((((((x_68) || (x_172)) || (x_182)) || (x_175)) ||
        (x_335)) || (x_126)) || (x_273) ? (x_32) : ((x_285 ? ((x_32) +
        ((Bit#(5))'(5'h1))) : (x_32)))));
        Bit#(32) x_419 = (((((x_68) || (x_172)) || (x_126)) || (x_273) ?
        (x_14) : (((x_76) == ((Bit#(8))'(8'h3)) ? ((x_14) ^
        ((Bit#(32))'(32'hcafeeace))) : (x_14)))));
        Bit#(32) x_420 = ((((((((x_68) || (x_172)) || (x_182)) || (x_175)) ||
        (x_335)) || (x_126)) || (x_273) ? (x_15) : (((x_195) && (x_284) ?
        (x_209) : (((x_201) && (x_284) ? ((Bit#(32))'(32'h0)) : (x_15)))))));
        
        Bit#(32) x_421 = ((x_18) + ((Bit#(32))'(32'h1)));
        Bool x_422 = ((x_421) == ((Bit#(32))'(32'h0)));
        Bit#(32) x_423 = ((x_422 ? ((x_19) + ((Bit#(32))'(32'h1))) :
        (x_19)));
        Bool x_424 = ((((((! (x_172)) && (! (x_182))) && (! (x_175))) && (!
        (x_335))) && (! (x_126))) && (! (x_273)));
        Bit#(32) x_425 = ((x_424 ? ((x_20) + ((Bit#(32))'(32'h1))) :
        (x_20)));
        Bool x_426 = ((x_424) && ((x_425) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_427 = ((x_426 ? ((x_21) + ((Bit#(32))'(32'h1))) :
        (x_21)));
        Bit#(32) x_428 = ((x_173 ? ((Bit#(32))'(32'h1)) :
        ((Bit#(32))'(32'h0))));
        pc <= x_366;
        mu <= x_376;
        regs <= x_369;
        if ((!(((((((x_68) || (x_172)) || (x_182)) || (x_175)) || (x_335)) || (x_126)) || (x_273))) && ((x_76) == ((Bit#(8))'(8'h12)))) mem.upd(x_150, x_147);
        if ((!(((((((x_68) || (x_172)) || (x_182)) || (x_175)) || (x_335)) || (x_126)) || (x_273))) && ((x_76) == ((Bit#(8))'(8'h17)))) mem.upd(x_155, x_137);
        if ((!(((((((x_68) || (x_172)) || (x_182)) || (x_175)) || (x_335)) || (x_126)) || (x_273))) && ((x_76) == ((Bit#(8))'(8'h1d)))) mem.upd(x_150, x_147);

        halted <= x_371;
        err <= x_372;
        error_code <= x_373;
        logic_acc <= x_419;
        cert_addr <= x_420;
        mstatus <= x_428;
        mcycle_lo <= x_421;
        mcycle_hi <= x_423;
        minstret_lo <= x_425;
        minstret_hi <= x_427;
        partition_ops <= x_401;
        mdl_ops <= x_402;
        info_gain <= x_403;
        mu_tensor <= x_412;
        ptTable <= x_398;
        pt_next_id <= x_399;
        morph_src_table <= x_413;
        morph_dst_table <= x_414;
        morph_coupling_desc_table <= x_415;
        morph_identity_table <= x_416;
        morph_valid_table <= x_417;
        morph_next_id <= x_418;
        certified <= x_377;
        wc_same_00 <= x_404;
        wc_diff_00 <= x_405;
        wc_same_01 <= x_406;
        wc_diff_01 <= x_407;
        wc_same_10 <= x_408;
        wc_diff_10 <= x_409;
        wc_same_11 <= x_410;
        wc_diff_11 <= x_411;
        Bit#(32) x_429 = ((Bit#(32))'(32'h0));
        lassert_phase <= (((x_134) && (x_133)) && (! (x_126)) ?
        ((Bit#(3))'(3'h1)) : ((Bit#(3))'(3'h0)));
        lassert_kind <= ((x_134) && (! (x_126)) ? (x_133) :
        ((Bool)'(False)));
        lassert_fbase <= (((x_134) && (x_133)) && (! (x_126)) ? (x_146) :
        (x_429));
        lassert_cbase <= (((x_134) && (x_133)) && (! (x_126)) ? (x_147) :
        (x_429));
        lassert_cptr <= (((x_134) && (x_133)) && (! (x_126)) ? (x_128) :
        (x_429));
        lassert_fptr <= x_429;
        lassert_flen <= x_429;
        lassert_clen <= x_429;
        lassert_nvars <= x_429;
        lassert_clause_sat <= (Bool)'(False);
        lassert_counter_clause_sat <= (Bool)'(False);
        
        lassert_counter_seen_fail <= (Bool)'(False);
        chsh_phase <= (x_337 ? ((Bit#(5))'(5'h1)) : ((Bit#(5))'(5'h0)));
        
        chsh_n00 <= x_346;
        chsh_n01 <= x_347;
        chsh_n10 <= x_348;
        chsh_n11 <= x_349;
        chsh_d00 <= x_354;
        chsh_d01 <= x_355;
        chsh_d10 <= x_356;
        chsh_d11 <= x_357;
        chsh_sign00 <= x_350;
        chsh_sign01 <= x_351;
        chsh_sign10 <= x_352;
        chsh_sign11 <= x_353;
        
    endrule
    
    rule lassert_fsm_header;
        let x_0 = (lassert_phase);
        when ((x_0) == ((Bit#(3))'(3'h1)), noAction);

        let x_2 = (lassert_fbase);
        Bit#(7) x_3 = ((x_2)[6:0]);
        Bit#(7) x_4 = (((x_2) + ((Bit#(32))'(32'h1)))[6:0]);
        Bit#(7) x_5 = (((x_2) + ((Bit#(32))'(32'h2)))[6:0]);
        Bit#(32) x_6 = (mem.sub(x_3));
        Bit#(32) x_7 = (mem.sub(x_4));
        Bit#(32) x_8 = (mem.sub(x_5));
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
        Bit#(32) x_17 = (mem.sub(x_16));
        Bit#(1) x_18 = ((x_17)[31:31]);
        Bool x_19 = ((x_17) == ((Bit#(32))'(32'h0)));
        Bool x_20 = (((x_18) == ((Bit#(1))'(1'h1))) && (! (x_19)));
        Bit#(32) x_21 = ((x_20 ? (((Bit#(32))'(32'h0)) - (x_17)) : (x_17)));
        
        Bit#(7) x_22 = (((x_7) + (x_21))[6:0]);
        Bit#(7) x_23 = ((((x_7) + (x_10)) + (x_21))[6:0]);
        Bit#(32) x_24 = (mem.sub(x_22));
        Bit#(32) x_25 = (mem.sub(x_23));
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
    
    rule chsh_lassert_fsm;
        let x_0 = (chsh_phase);
        when (! ((x_0) == ((Bit#(5))'(5'h0))), noAction);
        let x_1 = (chsh_n00);
        let x_2 = (chsh_n01);
        let x_3 = (chsh_n10);
        let x_4 = (chsh_n11);
        let x_5 = (chsh_d00);
        let x_6 = (chsh_d01);
        let x_7 = (chsh_d10);
        let x_8 = (chsh_d11);
        let x_9 = (chsh_sign00);
        let x_10 = (chsh_sign01);
        let x_11 = (chsh_sign10);
        let x_12 = (chsh_sign11);
        let x_13 = (chsh_n00sq);
        let x_14 = (chsh_n01sq);
        let x_15 = (chsh_n10sq);
        let x_16 = (chsh_n11sq);
        let x_17 = (chsh_d00sq);
        let x_18 = (chsh_d01sq);
        let x_19 = (chsh_d10sq);
        let x_20 = (chsh_d11sq);
        let x_21 = (chsh_A_pos);
        let x_22 = (chsh_A_neg_a);
        let x_23 = (chsh_A_neg_b);
        let x_24 = (chsh_B_pos);
        let x_25 = (chsh_B_neg_a);
        let x_26 = (chsh_B_neg_b);
        let x_27 = (chsh_d00d01);
        let x_28 = (chsh_n10n11);
        let x_29 = (chsh_d10d11);
        let x_30 = (chsh_n00n01);
        let x_31 = (chsh_abs_C1);
        let x_32 = (chsh_abs_C2);
        let x_33 = (chsh_C_sq);
        let x_34 = (chsh_A_times_B);
        let x_35 = (chsh_check_result);
        Bit#(384) x_36 = (zeroExtend(x_1));
        Bit#(384) x_37 = (zeroExtend(x_2));
        Bit#(384) x_38 = (zeroExtend(x_3));
        Bit#(384) x_39 = (zeroExtend(x_4));
        Bit#(384) x_40 = (zeroExtend(x_5));
        Bit#(384) x_41 = (zeroExtend(x_6));
        Bit#(384) x_42 = (zeroExtend(x_7));
        Bit#(384) x_43 = (zeroExtend(x_8));
        Bit#(384) x_44 = (zeroExtend(x_13));
        Bit#(384) x_45 = (zeroExtend(x_14));
        Bit#(384) x_46 = (zeroExtend(x_15));
        Bit#(384) x_47 = (zeroExtend(x_16));
        Bit#(384) x_48 = (zeroExtend(x_17));
        Bit#(384) x_49 = (zeroExtend(x_18));
        Bit#(384) x_50 = (zeroExtend(x_19));
        Bit#(384) x_51 = (zeroExtend(x_20));
        Bit#(384) x_52 = (zeroExtend(x_27));
        Bit#(384) x_53 = (zeroExtend(x_28));
        Bit#(384) x_54 = (zeroExtend(x_29));
        Bit#(384) x_55 = (zeroExtend(x_30));
        Bool x_56 = (! ((x_9) == (x_10)));
        Bool x_57 = (! ((x_11) == (x_12)));
        Bool x_58 = ((x_56) == (x_57));
        Bit#(256) x_59 = ((x_31) + (x_32));
        Bool x_60 = (! ((x_31) < (x_32)));
        Bit#(256) x_61 = ((x_60 ? ((x_31) - (x_32)) : ((x_32) - (x_31))));
        
        Bit#(256) x_62 = ((x_58 ? (x_59) : (x_61)));
        Bit#(384) x_63 = (zeroExtend(x_62));
        Bit#(256) x_64 = ((x_22) + (x_23));
        Bool x_65 = (! ((x_21) < (x_64)));
        Bit#(256) x_66 = ((x_65 ? ((x_21) - (x_64)) : ((x_64) - (x_21))));
        
        Bit#(384) x_67 = (zeroExtend(x_66));
        Bit#(256) x_68 = ((x_25) + (x_26));
        Bool x_69 = (! ((x_24) < (x_68)));
        Bit#(256) x_70 = ((x_69 ? ((x_24) - (x_68)) : ((x_68) - (x_24))));
        
        Bit#(384) x_71 = (zeroExtend(x_70));
        Bool x_72 = ((x_0) == ((Bit#(5))'(5'h1)));
        Bool x_73 = ((x_0) == ((Bit#(5))'(5'h2)));
        Bool x_74 = ((x_0) == ((Bit#(5))'(5'h3)));
        Bool x_75 = ((x_0) == ((Bit#(5))'(5'h4)));
        Bool x_76 = ((x_0) == ((Bit#(5))'(5'h5)));
        Bool x_77 = ((x_0) == ((Bit#(5))'(5'h6)));
        Bool x_78 = ((x_0) == ((Bit#(5))'(5'h7)));
        Bool x_79 = ((x_0) == ((Bit#(5))'(5'h8)));
        Bool x_80 = ((x_0) == ((Bit#(5))'(5'h9)));
        Bool x_81 = ((x_0) == ((Bit#(5))'(5'ha)));
        Bool x_82 = ((x_0) == ((Bit#(5))'(5'hb)));
        Bool x_83 = ((x_0) == ((Bit#(5))'(5'hc)));
        Bool x_84 = ((x_0) == ((Bit#(5))'(5'hd)));
        Bool x_85 = ((x_0) == ((Bit#(5))'(5'he)));
        Bool x_86 = ((x_0) == ((Bit#(5))'(5'hf)));
        Bool x_87 = ((x_0) == ((Bit#(5))'(5'h10)));
        Bool x_88 = ((x_0) == ((Bit#(5))'(5'h11)));
        Bool x_89 = ((x_0) == ((Bit#(5))'(5'h12)));
        Bool x_90 = ((x_0) == ((Bit#(5))'(5'h13)));
        Bool x_91 = ((x_0) == ((Bit#(5))'(5'h14)));
        Bool x_92 = ((x_0) == ((Bit#(5))'(5'h15)));
        Bool x_93 = ((x_0) == ((Bit#(5))'(5'h16)));
        Bool x_94 = ((x_0) == ((Bit#(5))'(5'h17)));
        Bit#(384) x_95 = ((x_72 ? (x_36) : ((x_73 ? (x_37) : ((x_74 ? (x_38)
        : ((x_75 ? (x_39) : ((x_76 ? (x_40) : ((x_77 ? (x_41) : ((x_78 ?
        (x_42) : ((x_79 ? (x_43) : ((x_80 ? (x_44) : ((x_81 ? (x_48) : ((x_82
        ? (x_50) : ((x_83 ? (x_45) : ((x_84 ? (x_49) : ((x_85 ? (x_51) :
        ((x_86 ? (x_40) : ((x_87 ? (x_38) : ((x_88 ? (x_42) : ((x_89 ? (x_36)
        : ((x_90 ? (x_52) : ((x_91 ? (x_54) : ((x_92 ? (x_63) : ((x_93 ?
        (x_67) :
        ((Bit#(384))'(384'h0))))))))))))))))))))))))))))))))))))))))))))));
        
        Bit#(384) x_96 = ((x_72 ? (x_36) : ((x_73 ? (x_37) : ((x_74 ? (x_38)
        : ((x_75 ? (x_39) : ((x_76 ? (x_40) : ((x_77 ? (x_41) : ((x_78 ?
        (x_42) : ((x_79 ? (x_43) : ((x_80 ? (x_46) : ((x_81 ? (x_46) : ((x_82
        ? (x_44) : ((x_83 ? (x_47) : ((x_84 ? (x_47) : ((x_85 ? (x_45) :
        ((x_86 ? (x_41) : ((x_87 ? (x_39) : ((x_88 ? (x_43) : ((x_89 ? (x_37)
        : ((x_90 ? (x_53) : ((x_91 ? (x_55) : ((x_92 ? (x_63) : ((x_93 ?
        (x_71) :
        ((Bit#(384))'(384'h0))))))))))))))))))))))))))))))))))))))))))))));
        
        Bit#(768) x_97 = (multiply_unsigned ((zeroExtend(x_95)),
        (zeroExtend(x_96))));
        Bit#(128) x_98 = ((x_97)[127:0]);
        Bit#(256) x_99 = ((x_97)[255:0]);
        Bit#(384) x_100 = ((x_97)[383:0]);
        Bool x_101 = ((((! ((x_1) == ((Bit#(64))'(64'h0)))) && (! ((x_2) ==
        ((Bit#(64))'(64'h0))))) && (! ((x_3) == ((Bit#(64))'(64'h0))))) && (!
        ((x_4) == ((Bit#(64))'(64'h0)))));
        Bool x_102 = (! ((x_34) < (x_33)));
        Bool x_103 = ((((x_101) && (x_65)) && (x_69)) && (x_102));
        chsh_n00sq <= (x_72 ? (x_98) : (x_13));
        chsh_n01sq <= (x_73 ? (x_98) : (x_14));
        chsh_n10sq <= (x_74 ? (x_98) : (x_15));
        chsh_n11sq <= (x_75 ? (x_98) : (x_16));
        chsh_d00sq <= (x_76 ? (x_98) : (x_17));
        chsh_d01sq <= (x_77 ? (x_98) : (x_18));
        chsh_d10sq <= (x_78 ? (x_98) : (x_19));
        chsh_d11sq <= (x_79 ? (x_98) : (x_20));
        chsh_A_pos <= (x_80 ? (x_99) : (x_21));
        chsh_A_neg_a <= (x_81 ? (x_99) : (x_22));
        chsh_A_neg_b <= (x_82 ? (x_99) : (x_23));
        chsh_B_pos <= (x_83 ? (x_99) : (x_24));
        chsh_B_neg_a <= (x_84 ? (x_99) : (x_25));
        chsh_B_neg_b <= (x_85 ? (x_99) : (x_26));
        chsh_d00d01 <= (x_86 ? (x_98) : (x_27));
        chsh_n10n11 <= (x_87 ? (x_98) : (x_28));
        chsh_d10d11 <= (x_88 ? (x_98) : (x_29));
        chsh_n00n01 <= (x_89 ? (x_98) : (x_30));
        chsh_abs_C1 <= (x_90 ? (x_99) : (x_31));
        chsh_abs_C2 <= (x_91 ? (x_99) : (x_32));
        chsh_C_sq <= (x_92 ? (x_100) : (x_33));
        chsh_A_times_B <= (x_93 ? (x_100) : (x_34));
        chsh_check_result <= (x_94 ? (x_103) : (x_35));
        let x_104 = (pc);
        let x_105 = (err);
        let x_106 = (error_code);
        let x_107 = (trap_vector);
        Bool x_108 = ((x_94) && (! (x_103)));
        pc <= (x_108 ? (x_107) : (x_104));
        err <= (x_108 ? ((Bool)'(True)) : (x_105));
        error_code <= (x_108 ? ((Bit#(32))'(32'hc43471a1)) : (x_106));
        
        chsh_phase <= (x_94 ? ((Bit#(5))'(5'h0)) : ((x_0) +
        ((Bit#(5))'(5'h1))));
        
    endrule
    
    
    method Action loadInstr (Struct1 x_0);
        Bit#(7) x_2 = ((x_0).addr);
        Bit#(128) x_3 = ((x_0).data);
        imem.upd(x_2, x_3);        
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

        Bit#(6) x_24 = ((x_13 ? ((x_9)[5:0]) : (x_2)));
        Bit#(32) x_25 = ((x_14 ? (x_9) : (x_3)));
        if (x_22) imem.upd(x_19, x_20);

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
        return lassert_fbuf.sub(x_0);
    endmethod
    
    method ActionValue#(Bit#(32)) getLassertCbufWord (Bit#(6) x_0);
        return lassert_cbuf.sub(x_0);
    endmethod
    
endmodule

