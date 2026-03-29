import Vector::*;
import Vector::*;
import BuildVector::*;
import RegFile::*;
import RegFileZero::*;
import FIFO::*;
import FIFOF::*;
import MulDiv::*;
import SpecialFIFOs::*;
typedef struct { Bit#(16) addr; Bit#(32) data;  } Struct1 deriving(Eq, Bits);
typedef struct { Bit#(32) addr; Bit#(32) data;  } Struct2 deriving(Eq, Bits);

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
    
endinterface

module mkModule1 (Module1);
    Reg#(Bit#(32)) pc <- mkReg(unpack(0));
    Reg#(Bit#(32)) mu <- mkReg(unpack(0));Reg#(Bool) err <- mkReg(False);
    Reg#(Bool) halted <- mkReg(False);
    Reg#(Vector#(32, Bit#(32))) regs <- mkReg(unpack(0));
    RegFile#(Bit#(16), Bit#(32)) mem <- mkRegFileFullZero();
    RegFile#(Bit#(16), Bit#(32)) imem <- mkRegFileFullZero();
    Reg#(Bit#(32)) partition_ops <- mkReg(unpack(0));
    Reg#(Bit#(32)) mdl_ops <- mkReg(unpack(0));
    Reg#(Bit#(32)) info_gain <- mkReg(unpack(0));
    Reg#(Bit#(32)) error_code <- mkReg(unpack(0));
    Reg#(Bit#(32)) logic_acc <- mkReg(unpack(0));
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
    Reg#(Bit#(32)) lassert_fptr <- mkReg(unpack(0));
    Reg#(Bit#(32)) lassert_cptr <- mkReg(unpack(0));
    RegFile#(Bit#(8), Bit#(32)) lassert_fbuf <- mkRegFileFullZero();
    RegFile#(Bit#(9), Bit#(32)) lassert_cbuf <- mkRegFileFullZero();
    Reg#(Bit#(16)) bus_load_instr_addr <- mkReg(unpack(0));
    Reg#(Bit#(32)) bus_load_instr_data <- mkReg(unpack(0));
    Reg#(Bool) bus_load_instr_kick <- mkReg(False);
    Reg#(Vector#(16, Bit#(32))) mu_tensor <- mkReg(unpack(0));
    Reg#(Vector#(64, Bit#(32))) ptTable <- mkReg(unpack(0));
    Reg#(Bit#(7)) pt_next_id <- mkReg(7'h1);
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
        let x_2 = (pc);
        let x_3 = (mu);
        let x_4 = (regs);

        let x_7 = (partition_ops);
        let x_8 = (mdl_ops);
        let x_9 = (info_gain);
        let x_10 = (error_code);
        let x_11 = (logic_acc);
        let x_12 = (active_module);
        let x_13 = (mstatus);
        let x_14 = (mcycle_lo);
        let x_15 = (mcycle_hi);
        let x_16 = (minstret_lo);
        let x_17 = (minstret_hi);
        let x_18 = (trap_vector);
        let x_19 = (mu_tensor);
        let x_20 = (ptTable);
        let x_21 = (pt_next_id);
        let x_22 = (certified);
        let x_23 = (wc_same_00);
        let x_24 = (wc_diff_00);
        let x_25 = (wc_same_01);
        let x_26 = (wc_diff_01);
        let x_27 = (wc_same_10);
        let x_28 = (wc_diff_10);
        let x_29 = (wc_same_11);
        let x_30 = (wc_diff_11);
        Bit#(32) x_31 = ((x_19)[(Bit#(4))'(4'h0)]);
        Bit#(32) x_32 = ((x_19)[(Bit#(4))'(4'h1)]);
        Bit#(32) x_33 = ((x_19)[(Bit#(4))'(4'h2)]);
        Bit#(32) x_34 = ((x_19)[(Bit#(4))'(4'h3)]);
        Bit#(32) x_35 = ((x_19)[(Bit#(4))'(4'h4)]);
        Bit#(32) x_36 = ((x_19)[(Bit#(4))'(4'h5)]);
        Bit#(32) x_37 = ((x_19)[(Bit#(4))'(4'h6)]);
        Bit#(32) x_38 = ((x_19)[(Bit#(4))'(4'h7)]);
        Bit#(32) x_39 = ((x_19)[(Bit#(4))'(4'h8)]);
        Bit#(32) x_40 = ((x_19)[(Bit#(4))'(4'h9)]);
        Bit#(32) x_41 = ((x_19)[(Bit#(4))'(4'ha)]);
        Bit#(32) x_42 = ((x_19)[(Bit#(4))'(4'hb)]);
        Bit#(32) x_43 = ((x_19)[(Bit#(4))'(4'hc)]);
        Bit#(32) x_44 = ((x_19)[(Bit#(4))'(4'hd)]);
        Bit#(32) x_45 = ((x_19)[(Bit#(4))'(4'he)]);
        Bit#(32) x_46 = ((x_19)[(Bit#(4))'(4'hf)]);
        Bit#(32) x_47 = ((((((((((((((((x_31) + (x_32)) + (x_33)) + (x_34)) +
        (x_35)) + (x_36)) + (x_37)) + (x_38)) + (x_39)) + (x_40)) + (x_41)) +
        (x_42)) + (x_43)) + (x_44)) + (x_45)) + (x_46));
        Bool x_48 = ((x_3) < (x_47));
        Bit#(16) x_49 = ((x_2)[15:0]);
        Bit#(32) x_50 = (imem.sub(x_49));
        Bit#(8) x_51 = ((x_50)[31:24]);
        Bit#(8) x_52 = ((x_50)[23:16]);
        Bit#(8) x_53 = ((x_50)[15:8]);
        Bit#(8) x_54 = ((x_50)[7:0]);
        Bit#(32) x_55 = (zeroExtend(x_54));
        Bit#(32) x_56 = ((x_3) + (x_55));
        Bit#(32) x_57 = ((x_2) + ((Bit#(32))'(32'h1)));
        Bit#(5) x_58 = ((x_52)[4:0]);
        Bit#(5) x_59 = ((x_53)[4:0]);
        Bit#(4) x_60 = ((x_53)[7:4]);
        Bit#(4) x_61 = ((x_53)[3:0]);
        Bit#(5) x_62 = (zeroExtend(x_60));
        Bit#(5) x_63 = (zeroExtend(x_61));
        Bit#(32) x_64 = ((x_4)[x_62]);
        Bit#(32) x_65 = ((x_4)[x_63]);
        Bit#(32) x_66 = ((x_4)[x_58]);
        Bit#(32) x_67 = ((x_4)[x_59]);
        Bit#(32) x_68 = (zeroExtend(x_53));
        Bit#(16) x_69 = ((x_67)[15:0]);
        Bit#(16) x_70 = ((x_66)[15:0]);
        Bit#(16) x_71 = (zeroExtend(x_53));
        Bit#(32) x_72 = (mem.sub(x_69));
        Bit#(32) x_73 = (mem.sub(x_71));
        Bit#(32) x_74 = ((x_4)[(Bit#(5))'(5'h1f)]);
        Bit#(16) x_75 = ((x_74)[15:0]);
        Bit#(32) x_76 = ((x_74) + ((Bit#(32))'(32'h1)));
        Bit#(32) x_77 = ((x_74) - ((Bit#(32))'(32'h1)));
        Bit#(16) x_78 = ((x_77)[15:0]);
        Bit#(32) x_79 = ((x_20)[x_12]);
        Bool x_80 = ((zeroExtend(x_69)) < (x_79));
        Bool x_81 = ((zeroExtend(x_70)) < (x_79));
        Bool x_82 = ((zeroExtend(x_75)) < (x_79));
        Bool x_83 = ((zeroExtend(x_78)) < (x_79));
        Bool x_84 = (((x_51) == ((Bit#(8))'(8'h11))) || ((x_51) ==
        ((Bit#(8))'(8'h1c))));
        Bool x_85 = (((x_51) == ((Bit#(8))'(8'h12))) || ((x_51) ==
        ((Bit#(8))'(8'h1d))));
        Bool x_86 = ((x_51) == ((Bit#(8))'(8'h17)));
        Bool x_87 = ((x_51) == ((Bit#(8))'(8'h18)));
        Bool x_88 = ((x_84) && (! (x_80)));
        Bool x_89 = ((x_85) && (! (x_81)));
        Bool x_90 = ((x_86) && (! (x_82)));
        Bool x_91 = ((x_87) && (! (x_83)));
        Bool x_92 = ((((x_88) || (x_89)) || (x_90)) || (x_91));
        Bool x_93 = ((x_11) == ((Bit#(32))'(32'hcafeeace)));
        Bool x_94 = ((((x_51) == ((Bit#(8))'(8'hf))) || ((x_51) ==
        ((Bit#(8))'(8'h6)))) || ((x_51) == ((Bit#(8))'(8'h9))));
        Bool x_95 = ((x_94) && (! (x_93)));
        Bool x_96 = (! ((x_21) < ((Bit#(7))'(7'h40))));
        Bool x_97 = (! (x_96));
        Bool x_98 = (! (((Bit#(7))'(7'h40)) < ((x_21) +
        ((Bit#(7))'(7'h2)))));
        Bool x_99 = (((x_51) == ((Bit#(8))'(8'h0))) && (! (x_97)));
        Bool x_100 = (((x_51) == ((Bit#(8))'(8'h1))) && (! (x_98)));
        Bool x_101 = (((x_51) == ((Bit#(8))'(8'h2))) && (! (x_97)));
        Bool x_102 = (((x_99) || (x_100)) || (x_101));
        Bit#(6) x_103 = ((x_53)[5:0]);
        Bit#(32) x_104 = ((x_20)[x_103]);
        Bit#(32) x_105 = (zeroExtend(x_53));
        Bit#(16) x_106 = ({(x_52),(x_53)});
        Bit#(32) x_107 = (zeroExtend(x_106));
        Bit#(32) x_108 = ((x_83 ? (mem.sub(x_78)) : ((Bit#(32))'(32'h0))));
        
        Bit#(32) x_109 = ((x_64) + (x_65));
        Bit#(32) x_110 = ((x_64) - (x_65));
        Bit#(32) x_111 = ((x_64) & (x_65));
        Bit#(32) x_112 = ((x_64) | (x_65));
        Bit#(32) x_113 = ((x_64) << (x_65));
        Bit#(32) x_114 = ((x_64) >> (x_65));
        Bit#(32) x_115 = (multiply_unsigned ((x_64), (x_65)));
        Bit#(32) x_116 = ((Bit#(32))'(32'h8));
        Bit#(32) x_117 = ((x_68) << (x_116));
        Bit#(32) x_118 = ((x_66) ^ (x_67));
        Bool x_119 = (! ((x_66) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_120 = (x_67);
        Bit#(32) x_121 = ((Bit#(32))'(32'h55555555));
        Bit#(32) x_122 = ((x_120) & (x_121));
        Bit#(32) x_123 = (((x_120) >> ((Bit#(6))'(6'h1))) & (x_121));
        Bit#(32) x_124 = ((x_122) + (x_123));
        Bit#(32) x_125 = ((Bit#(32))'(32'h33333333));
        Bit#(32) x_126 = ((x_124) & (x_125));
        Bit#(32) x_127 = (((x_124) >> ((Bit#(6))'(6'h2))) & (x_125));
        Bit#(32) x_128 = ((x_126) + (x_127));
        Bit#(32) x_129 = ((Bit#(32))'(32'hf0f0f0f));
        Bit#(32) x_130 = ((x_128) & (x_129));
        Bit#(32) x_131 = (((x_128) >> ((Bit#(6))'(6'h4))) & (x_129));
        Bit#(32) x_132 = ((x_130) + (x_131));
        Bit#(32) x_133 = ((Bit#(32))'(32'hff00ff));
        Bit#(32) x_134 = ((x_132) & (x_133));
        Bit#(32) x_135 = (((x_132) >> ((Bit#(6))'(6'h8))) & (x_133));
        Bit#(32) x_136 = ((x_134) + (x_135));
        Bit#(32) x_137 = ((Bit#(32))'(32'hffff));
        Bit#(32) x_138 = ((x_136) & (x_137));
        Bit#(32) x_139 = (((x_136) >> ((Bit#(6))'(6'h10))) & (x_137));
        
        Bit#(32) x_140 = ((x_138) + (x_139));
        Bool x_141 = (((Bit#(8))'(8'h3)) < (x_53));
        Bool x_142 = (((Bit#(8))'(8'h1)) < (x_52));
        Bool x_143 = ((x_142) && ((x_47) == ((Bit#(32))'(32'h0))));
        Bool x_144 = (x_143);
        Bit#(2) x_145 = ((x_52)[1:0]);
        Bit#(2) x_146 = ((x_53)[1:0]);
        Bool x_147 = (((x_146) == ((Bit#(2))'(2'h0))) || ((x_146) ==
        ((Bit#(2))'(2'h3))));
        Bool x_148 = ((x_145) == ((Bit#(2))'(2'h0)));
        Bool x_149 = ((x_145) == ((Bit#(2))'(2'h1)));
        Bool x_150 = ((x_145) == ((Bit#(2))'(2'h2)));
        Bool x_151 = ((x_145) == ((Bit#(2))'(2'h3)));
        Bit#(32) x_152 = (zeroExtend(x_53));
        Bool x_153 = (((x_51) == ((Bit#(8))'(8'h6))) || ((x_51) ==
        ((Bit#(8))'(8'he))));
        Bool x_154 = ((x_153) && ((x_55) < (x_152)));
        Bool x_155 = ((((((((x_51) == ((Bit#(8))'(8'h9))) && (! (x_144))) &&
        (! (x_48))) && (! (x_92))) && (! (x_102))) && (! (x_95))) && (!
        (x_154)));
        Bit#(4) x_156 = ((x_52)[3:0]);
        Bit#(32) x_157 = ((x_19)[x_156]);
        Bit#(32) x_158 = ((x_157) + (x_55));
        Bit#(32) x_159 = ((((((x_48) || (x_92)) || (x_102)) || (x_95)) ||
        (x_154) ? (x_18) : (((x_51) == ((Bit#(8))'(8'hff)) ? (x_2) : (((x_51)
        == ((Bit#(8))'(8'h15)) ? (x_107) : (((x_51) == ((Bit#(8))'(8'h17)) ?
        (x_107) : (((x_51) == ((Bit#(8))'(8'h18)) ? (x_108) : ((((x_51) ==
        ((Bit#(8))'(8'h16))) && (x_119) ? (x_105) : (x_57)))))))))))));
        
        Vector#(32, Bit#(32)) x_160 = (update (update (x_4, x_58, x_67),
        x_59, x_66));
        Vector#(32, Bit#(32)) x_161 = ((((((x_48) || (x_92)) || (x_102)) ||
        (x_95)) || (x_154) ? (x_4) : (((x_51) == ((Bit#(8))'(8'h8)) ? (update
        (x_4, x_58, x_68)) : (((x_51) == ((Bit#(8))'(8'h13)) ? (update (x_4,
        x_58, x_109)) : (((x_51) == ((Bit#(8))'(8'h14)) ? (update (x_4, x_58,
        x_110)) : (((x_51) == ((Bit#(8))'(8'h7)) ? (update (x_4, x_58, x_67))
        : (((x_51) == ((Bit#(8))'(8'h11)) ? (update (x_4, x_58, x_72)) :
        (((x_51) == ((Bit#(8))'(8'ha)) ? (update (x_4, x_58, x_73)) :
        (((x_51) == ((Bit#(8))'(8'hb)) ? (update (x_4, x_58, x_118)) :
        (((x_51) == ((Bit#(8))'(8'hc)) ? (x_160) : (((x_51) ==
        ((Bit#(8))'(8'hd)) ? (update (x_4, x_58, x_140)) : (((x_51) ==
        ((Bit#(8))'(8'h17)) ? (update (x_4, (Bit#(5))'(5'h1f), x_76)) :
        (((x_51) == ((Bit#(8))'(8'h18)) ? (update (x_4, (Bit#(5))'(5'h1f),
        x_77)) : (((x_51) == ((Bit#(8))'(8'h6)) ? (update (x_4, x_58, x_104))
        : (((x_51) == ((Bit#(8))'(8'h1c)) ? (update (x_4, x_58, x_72)) :
        (((x_51) == ((Bit#(8))'(8'h1a)) ? (update (x_4, x_58,
        (Bit#(32))'(32'h0))) : (((x_51) == ((Bit#(8))'(8'h1f)) ? (update
        (x_4, x_58, x_111)) : (((x_51) == ((Bit#(8))'(8'h20)) ? (update (x_4,
        x_58, x_112)) : (((x_51) == ((Bit#(8))'(8'h21)) ? (update (x_4, x_58,
        x_113)) : (((x_51) == ((Bit#(8))'(8'h22)) ? (update (x_4, x_58,
        x_114)) : (((x_51) == ((Bit#(8))'(8'h23)) ? (update (x_4, x_58,
        x_115)) : (((x_51) == ((Bit#(8))'(8'h24)) ? (update (x_4, x_58,
        x_117)) : (((x_51) == ((Bit#(8))'(8'h26)) ? (update (x_4, x_58,
        x_157)) : (((((((x_51) == ((Bit#(8))'(8'h27))) || ((x_51) ==
        ((Bit#(8))'(8'h28)))) || ((x_51) == ((Bit#(8))'(8'h29)))) || ((x_51)
        == ((Bit#(8))'(8'h2c)))) || ((x_51) == ((Bit#(8))'(8'h2d))) ? (update
        (x_4, x_58, (Bit#(32))'(32'h0))) :
        (x_4)))))))))))))))))))))))))))))))))))))))))))))));

        Bool x_163 = (((((x_92) || (x_102)) || (x_95)) || (x_154)) || ((x_51)
        == ((Bit#(8))'(8'hff))));
        Bool x_164 = (((((x_92) || (x_102)) || (x_95)) || (x_154)) ||
        (((x_51) == ((Bit#(8))'(8'h9))) && (x_144)));
        Bit#(32) x_165 = ((x_48 ? ((Bit#(32))'(32'hb1a4c81)) : ((x_92 ?
        ((Bit#(32))'(32'hbadc0de)) : ((x_102 ? ((Bit#(32))'(32'hbadf001d)) :
        ((x_154 ? ((Bit#(32))'(32'hc43471a1)) : ((x_95 ?
        ((Bit#(32))'(32'hc43471a1)) : ((((x_51) == ((Bit#(8))'(8'h9))) &&
        (x_144) ? ((Bit#(32))'(32'hbadc45c)) : (x_10)))))))))))));
        Bit#(32) x_166 = (((((x_48) || (x_102)) || (x_95)) || (x_154) ? (x_3)
        : (((x_51) == ((Bit#(8))'(8'h10)) ? ((x_3) +
        ((Bit#(32))'(32'hf4240))) : ((((x_51) == ((Bit#(8))'(8'h9))) &&
        (x_142) ? ((x_56) + ((Bit#(32))'(32'h100))) : (((x_51) ==
        ((Bit#(8))'(8'h1e)) ? (((x_3) + (x_55)) + ((Bit#(32))'(32'h1))) :
        (((x_51) == ((Bit#(8))'(8'h2b)) ? (((x_3) + (x_55)) +
        ((Bit#(32))'(32'h1))) : (((((((x_51) == ((Bit#(8))'(8'he))) ||
        ((x_51) == ((Bit#(8))'(8'hf)))) || ((x_51) == ((Bit#(8))'(8'h3)))) ||
        ((x_51) == ((Bit#(8))'(8'h4)))) || ((x_51) == ((Bit#(8))'(8'h1a))) ?
        ((x_56) + ((Bit#(32))'(32'h1))) : (x_56)))))))))))));
        Bool x_167 = ((((((x_48) || (x_92)) || (x_102)) || (x_95)) || (x_154)
        ? (x_22) : (((x_51) == ((Bit#(8))'(8'h1e)) ? ((Bool)'(True)) :
        (x_22)))));
        Bit#(6) x_168 = ((x_21)[5:0]);
        Bit#(32) x_169 = (zeroExtend(x_52));
        Vector#(64, Bit#(32)) x_170 = (update (x_20, x_168, x_169));
        Bit#(7) x_171 = ((x_21) + ((Bit#(7))'(7'h1)));
        Bit#(6) x_172 = ((x_52)[5:0]);
        Bit#(32) x_173 = ((x_20)[x_172]);
        Bit#(32) x_174 = ((x_173) >> ((Bit#(5))'(5'h1)));
        Bit#(32) x_175 = ((x_173) - (x_174));
        Bit#(6) x_176 = ((x_21)[5:0]);
        Bit#(6) x_177 = (((x_21) + ((Bit#(7))'(7'h1)))[5:0]);
        
        Vector#(64, Bit#(32)) x_178 = (update (update (update (x_20, x_172,
        (Bit#(32))'(32'h0)), x_176, x_174), x_177, x_175));
        Bit#(7) x_179 = ((x_21) + ((Bit#(7))'(7'h2)));
        Bit#(6) x_180 = ((x_52)[5:0]);
        Bit#(6) x_181 = ((x_53)[5:0]);
        Bit#(32) x_182 = ((x_20)[x_180]);
        Bit#(32) x_183 = ((x_20)[x_181]);
        Bit#(32) x_184 = ((x_182) + (x_183));
        Bit#(6) x_185 = ((x_21)[5:0]);
        Vector#(64, Bit#(32)) x_186 = (update (update (update (x_20, x_180,
        (Bit#(32))'(32'h0)), x_181, (Bit#(32))'(32'h0)), x_185, x_184));
        
        Bit#(7) x_187 = ((x_21) + ((Bit#(7))'(7'h1)));
        Vector#(64, Bit#(32)) x_188 = (((x_48) || (x_102) ? (x_20) : (((x_51)
        == ((Bit#(8))'(8'h0)) ? (x_170) : (((x_51) == ((Bit#(8))'(8'h1)) ?
        (x_178) : (((x_51) == ((Bit#(8))'(8'h2)) ? (x_186) : (x_20)))))))));
        
        Bit#(7) x_189 = (((x_48) || (x_102) ? (x_21) : (((x_51) ==
        ((Bit#(8))'(8'h0)) ? (x_171) : (((x_51) == ((Bit#(8))'(8'h1)) ?
        (x_179) : (((x_51) == ((Bit#(8))'(8'h2)) ? (x_187) : (x_21)))))))));
        
        Bool x_190 = ((((x_51) == ((Bit#(8))'(8'h0))) || ((x_51) ==
        ((Bit#(8))'(8'h1)))) || ((x_51) == ((Bit#(8))'(8'h2))));
        Bit#(32) x_191 = (((x_190) && (! (x_48)) ? ((x_7) +
        ((Bit#(32))'(32'h1))) : (x_7)));
        Bit#(32) x_192 = ((((x_51) == ((Bit#(8))'(8'h5))) && (! (x_48)) ?
        ((x_8) + ((Bit#(32))'(32'h1))) : (x_8)));
        Bit#(32) x_193 = (((((((x_153) && (! (x_48))) && (! (x_92))) && (!
        (x_102))) && (! (x_95))) && (! (x_154)) ? ((x_9) + (x_152)) :
        (x_9)));
        Bit#(32) x_194 = ((((x_155) && (x_148)) && (x_147) ? ((x_23) +
        ((Bit#(32))'(32'h1))) : (x_23)));
        Bit#(32) x_195 = ((((x_155) && (x_148)) && (! (x_147)) ? ((x_24) +
        ((Bit#(32))'(32'h1))) : (x_24)));
        Bit#(32) x_196 = ((((x_155) && (x_149)) && (x_147) ? ((x_25) +
        ((Bit#(32))'(32'h1))) : (x_25)));
        Bit#(32) x_197 = ((((x_155) && (x_149)) && (! (x_147)) ? ((x_26) +
        ((Bit#(32))'(32'h1))) : (x_26)));
        Bit#(32) x_198 = ((((x_155) && (x_150)) && (x_147) ? ((x_27) +
        ((Bit#(32))'(32'h1))) : (x_27)));
        Bit#(32) x_199 = ((((x_155) && (x_150)) && (! (x_147)) ? ((x_28) +
        ((Bit#(32))'(32'h1))) : (x_28)));
        Bit#(32) x_200 = ((((x_155) && (x_151)) && (x_147) ? ((x_29) +
        ((Bit#(32))'(32'h1))) : (x_29)));
        Bit#(32) x_201 = ((((x_155) && (x_151)) && (! (x_147)) ? ((x_30) +
        ((Bit#(32))'(32'h1))) : (x_30)));
        Vector#(16, Bit#(32)) x_202 = (((((x_51) == ((Bit#(8))'(8'hf))) && (!
        (x_48))) && (! (x_95)) ? (update (x_19, x_156, x_158)) : ((((x_51) ==
        ((Bit#(8))'(8'h25))) && (! (x_48)) ? (update (x_19, x_156, x_67)) :
        (x_19)))));
        Bit#(32) x_203 = (((x_48) || (x_92) ? (x_11) : (((x_51) ==
        ((Bit#(8))'(8'h3)) ? ((x_11) ^ ((Bit#(32))'(32'hcafeeace))) :
        (((x_51) == ((Bit#(8))'(8'h10)) ? ((x_11) + ((Bit#(32))'(32'h1))) :
        (x_11)))))));
        Bit#(32) x_204 = ((x_14) + ((Bit#(32))'(32'h1)));
        Bool x_205 = ((x_204) == ((Bit#(32))'(32'h0)));
        Bit#(32) x_206 = ((x_205 ? ((x_15) + ((Bit#(32))'(32'h1))) :
        (x_15)));
        Bool x_207 = ((((! (x_92)) && (! (x_102))) && (! (x_95))) && (!
        (x_154)));
        Bit#(32) x_208 = ((x_207 ? ((x_16) + ((Bit#(32))'(32'h1))) :
        (x_16)));
        Bool x_209 = ((x_207) && ((x_208) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_210 = ((x_209 ? ((x_17) + ((Bit#(32))'(32'h1))) :
        (x_17)));
        Bit#(32) x_211 = ((x_93 ? ((Bit#(32))'(32'h1)) :
        ((Bit#(32))'(32'h0))));
        pc <= x_159;
        mu <= x_166;
        regs <= x_161;
        if ((!(((((x_48) || (x_92)) || (x_102)) || (x_95)) || (x_154))) && ((x_51) == ((Bit#(8))'(8'h12)))) mem.upd(x_70, x_67);
        if ((!(((((x_48) || (x_92)) || (x_102)) || (x_95)) || (x_154))) && ((x_51) == ((Bit#(8))'(8'h17)))) mem.upd(x_75, x_57);
        if ((!(((((x_48) || (x_92)) || (x_102)) || (x_95)) || (x_154))) && ((x_51) == ((Bit#(8))'(8'h1d)))) mem.upd(x_70, x_67);

        halted <= x_163;
        err <= x_164;
        error_code <= x_165;
        logic_acc <= x_203;
        mstatus <= x_211;
        mcycle_lo <= x_204;
        mcycle_hi <= x_206;
        minstret_lo <= x_208;
        minstret_hi <= x_210;
        partition_ops <= x_191;
        mdl_ops <= x_192;
        info_gain <= x_193;
        mu_tensor <= x_202;
        ptTable <= x_188;
        pt_next_id <= x_189;
        certified <= x_167;
        wc_same_00 <= x_194;
        wc_diff_00 <= x_195;
        wc_same_01 <= x_196;
        wc_diff_01 <= x_197;
        wc_same_10 <= x_198;
        wc_diff_10 <= x_199;
        wc_same_11 <= x_200;
        wc_diff_11 <= x_201;
        
    endrule
    
    
    method Action loadInstr (Struct1 x_0);
        Bit#(16) x_2 = ((x_0).addr);
        Bit#(32) x_3 = ((x_0).data);
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
        let x_15 = (mu_tensor);
        let x_16 = (pt_next_id);
        let x_17 = (ptTable);
        Bit#(32) x_18 = (((((x_15)[(Bit#(4))'(4'h0)]) +
        ((x_15)[(Bit#(4))'(4'h1)])) + ((x_15)[(Bit#(4))'(4'h2)])) +
        ((x_15)[(Bit#(4))'(4'h3)]));
        Bit#(32) x_19 = (((((x_15)[(Bit#(4))'(4'h4)]) +
        ((x_15)[(Bit#(4))'(4'h5)])) + ((x_15)[(Bit#(4))'(4'h6)])) +
        ((x_15)[(Bit#(4))'(4'h7)]));
        Bit#(32) x_20 = (((((x_15)[(Bit#(4))'(4'h8)]) +
        ((x_15)[(Bit#(4))'(4'h9)])) + ((x_15)[(Bit#(4))'(4'ha)])) +
        ((x_15)[(Bit#(4))'(4'hb)]));
        Bit#(32) x_21 = (((((x_15)[(Bit#(4))'(4'hc)]) +
        ((x_15)[(Bit#(4))'(4'hd)])) + ((x_15)[(Bit#(4))'(4'he)])) +
        ((x_15)[(Bit#(4))'(4'hf)]));
        Bit#(32) x_22 = ((((x_18) + (x_19)) + (x_20)) + (x_21));
        Bool x_23 = ((x_2) < (x_22));
        Bit#(32) x_24 = (zeroExtend(x_16));
        Bit#(32) x_25 = ((x_17)[(Bit#(6))'(6'h0)]);
        Bit#(32) x_26 = (((x_0) == ((Bit#(32))'(32'h0)) ? (x_1) : (((x_0) ==
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
        (x_14) : (((x_0) == ((Bit#(32))'(32'h44)) ? (x_18) : (((x_0) ==
        ((Bit#(32))'(32'h48)) ? (x_19) : (((x_0) == ((Bit#(32))'(32'h4c)) ?
        (x_20) : (((x_0) == ((Bit#(32))'(32'h50)) ? (x_21) : (((x_0) ==
        ((Bit#(32))'(32'h54)) ? ((x_23 ? ((Bit#(32))'(32'h1)) :
        ((Bit#(32))'(32'h0)))) : (((x_0) == ((Bit#(32))'(32'h58)) ? (x_24) :
        (((x_0) == ((Bit#(32))'(32'h5c)) ? (x_25) :
        ((Bit#(32))'(32'h0))))))))))))))))))))))))))))))))))))))))))));
        return x_26;
    endmethod
    
    method ActionValue#(Bool) apbReadErr (Bit#(32) x_0);
        Bool x_1 = ((((((((((((((((((((((x_0) == ((Bit#(32))'(32'h0))) ||
        ((x_0) == ((Bit#(32))'(32'h4)))) || ((x_0) == ((Bit#(32))'(32'h8))))
        || ((x_0) == ((Bit#(32))'(32'hc)))) || ((x_0) ==
        ((Bit#(32))'(32'h10)))) || ((x_0) == ((Bit#(32))'(32'h14)))) ||
        ((x_0) == ((Bit#(32))'(32'h18)))) || ((x_0) ==
        ((Bit#(32))'(32'h1c)))) || ((x_0) == ((Bit#(32))'(32'h20)))) ||
        ((x_0) == ((Bit#(32))'(32'h24)))) || ((x_0) ==
        ((Bit#(32))'(32'h28)))) || ((x_0) == ((Bit#(32))'(32'h2c)))) ||
        ((x_0) == ((Bit#(32))'(32'h30)))) || ((x_0) ==
        ((Bit#(32))'(32'h34)))) || ((x_0) == ((Bit#(32))'(32'h44)))) ||
        ((x_0) == ((Bit#(32))'(32'h48)))) || ((x_0) ==
        ((Bit#(32))'(32'h4c)))) || ((x_0) == ((Bit#(32))'(32'h50)))) ||
        ((x_0) == ((Bit#(32))'(32'h54)))) || ((x_0) ==
        ((Bit#(32))'(32'h58)))) || ((x_0) == ((Bit#(32))'(32'h5c))));
        return ! (x_1);
    endmethod
    
    method ActionValue#(Bool) apbWrite (Struct2 x_0);
        let x_2 = (active_module);
        let x_3 = (trap_vector);
        let x_4 = (bus_load_instr_addr);
        let x_5 = (bus_load_instr_data);
        let x_6 = (bus_load_instr_kick);
        Bit#(32) x_7 = ((x_0).addr);
        Bit#(32) x_8 = ((x_0).data);
        Bool x_9 = ((x_7) == ((Bit#(32))'(32'h80)));
        Bool x_10 = ((x_7) == ((Bit#(32))'(32'h84)));
        Bool x_11 = ((x_7) == ((Bit#(32))'(32'h88)));
        Bool x_12 = ((x_7) == ((Bit#(32))'(32'h98)));
        Bool x_13 = ((x_7) == ((Bit#(32))'(32'h9c)));
        Bool x_14 = (((((x_9) || (x_10)) || (x_11)) || (x_12)) || (x_13));
        
        Bit#(16) x_15 = ((x_8)[15:0]);
        Bit#(32) x_16 = ((x_8)[31:0]);
        Bool x_17 = (! ((x_8) == ((Bit#(32))'(32'h0))));
        Bit#(16) x_18 = ((x_9 ? (x_15) : (x_4)));
        Bit#(32) x_19 = ((x_10 ? (x_16) : (x_5)));
        Bool x_20 = ((x_11 ? (x_17) : (x_6)));
        Bool x_21 = ((x_11) && (x_17));

        Bit#(6) x_23 = ((x_12 ? ((x_8)[5:0]) : (x_2)));
        Bit#(32) x_24 = ((x_13 ? (x_8) : (x_3)));
        if (x_21) imem.upd(x_18, x_19);

        bus_load_instr_addr <= x_18;
        bus_load_instr_data <= x_19;
        bus_load_instr_kick <= x_20;
        active_module <= x_23;
        trap_vector <= x_24;
        return ! (x_14);
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
    
endmodule

