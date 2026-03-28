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
typedef struct { Bool valid; Bool error; Bit#(32) value;  } Struct2 deriving(Eq, Bits);
typedef struct { Bit#(32) addr; Bit#(32) data;  } Struct3 deriving(Eq, Bits);

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
    method ActionValue#(Bool) getLogicReqValid ();
    method ActionValue#(Bit#(8)) getLogicReqOpcode ();
    method ActionValue#(Bit#(32)) getLogicReqPayload ();
    method Action setLogicResp (Struct2 x_0);
    method ActionValue#(Bit#(32)) getMuTensor0 ();
    method ActionValue#(Bit#(32)) getMuTensor1 ();
    method ActionValue#(Bit#(32)) getMuTensor2 ();
    method ActionValue#(Bit#(32)) getMuTensor3 ();
    method Action setActiveModule (Bit#(6) x_0);
    method Action setTrapVector (Bit#(32) x_0);
    method ActionValue#(Bit#(32)) apbReadData (Bit#(32) x_0);
    method ActionValue#(Bool) apbReadErr (Bit#(32) x_0);
    method ActionValue#(Bool) apbWrite (Struct3 x_0);
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
    Reg#(Bool) logic_req_valid <- mkReg(False);
    Reg#(Bit#(8)) logic_req_opcode <- mkReg(unpack(0));
    Reg#(Bit#(32)) logic_req_payload <- mkReg(unpack(0));
    Reg#(Bool) logic_resp_valid <- mkReg(False);
    Reg#(Bool) logic_resp_error <- mkReg(False);
    Reg#(Bit#(32)) logic_resp_value <- mkReg(unpack(0));
    Reg#(Bool) logic_stall <- mkReg(False);
    Reg#(Bit#(16)) bus_load_instr_addr <- mkReg(unpack(0));
    Reg#(Bit#(32)) bus_load_instr_data <- mkReg(unpack(0));
    Reg#(Bool) bus_load_instr_kick <- mkReg(False);
    Reg#(Vector#(16, Bit#(32))) mu_tensor <- mkReg(unpack(0));
    Reg#(Vector#(64, Bit#(32))) ptTable <- mkReg(unpack(0));
    Reg#(Bit#(7)) pt_next_id <- mkReg(7'h1);
    Reg#(Bool) certified <- mkReg(False);
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
        let x_2 = (logic_stall);
        let x_3 = (pc);
        let x_4 = (mu);
        let x_5 = (regs);

        let x_8 = (partition_ops);
        let x_9 = (mdl_ops);
        let x_10 = (info_gain);
        let x_11 = (error_code);
        let x_12 = (logic_acc);
        let x_13 = (active_module);
        let x_14 = (mstatus);
        let x_15 = (mcycle_lo);
        let x_16 = (mcycle_hi);
        let x_17 = (minstret_lo);
        let x_18 = (minstret_hi);
        let x_19 = (trap_vector);
        let x_20 = (logic_req_valid);
        let x_21 = (logic_req_opcode);
        let x_22 = (logic_req_payload);
        let x_23 = (logic_resp_valid);
        let x_24 = (logic_resp_error);
        let x_25 = (logic_resp_value);
        let x_26 = (mu_tensor);
        let x_27 = (ptTable);
        let x_28 = (pt_next_id);
        let x_29 = (certified);
        let x_30 = (wc_same_00);
        let x_31 = (wc_diff_00);
        let x_32 = (wc_same_01);
        let x_33 = (wc_diff_01);
        let x_34 = (wc_same_10);
        let x_35 = (wc_diff_10);
        let x_36 = (wc_same_11);
        let x_37 = (wc_diff_11);
        Bit#(32) x_38 = ((x_26)[(Bit#(4))'(4'h0)]);
        Bit#(32) x_39 = ((x_26)[(Bit#(4))'(4'h1)]);
        Bit#(32) x_40 = ((x_26)[(Bit#(4))'(4'h2)]);
        Bit#(32) x_41 = ((x_26)[(Bit#(4))'(4'h3)]);
        Bit#(32) x_42 = ((x_26)[(Bit#(4))'(4'h4)]);
        Bit#(32) x_43 = ((x_26)[(Bit#(4))'(4'h5)]);
        Bit#(32) x_44 = ((x_26)[(Bit#(4))'(4'h6)]);
        Bit#(32) x_45 = ((x_26)[(Bit#(4))'(4'h7)]);
        Bit#(32) x_46 = ((x_26)[(Bit#(4))'(4'h8)]);
        Bit#(32) x_47 = ((x_26)[(Bit#(4))'(4'h9)]);
        Bit#(32) x_48 = ((x_26)[(Bit#(4))'(4'ha)]);
        Bit#(32) x_49 = ((x_26)[(Bit#(4))'(4'hb)]);
        Bit#(32) x_50 = ((x_26)[(Bit#(4))'(4'hc)]);
        Bit#(32) x_51 = ((x_26)[(Bit#(4))'(4'hd)]);
        Bit#(32) x_52 = ((x_26)[(Bit#(4))'(4'he)]);
        Bit#(32) x_53 = ((x_26)[(Bit#(4))'(4'hf)]);
        Bit#(32) x_54 = ((((((((((((((((x_38) + (x_39)) + (x_40)) + (x_41)) +
        (x_42)) + (x_43)) + (x_44)) + (x_45)) + (x_46)) + (x_47)) + (x_48)) +
        (x_49)) + (x_50)) + (x_51)) + (x_52)) + (x_53));
        Bool x_55 = ((x_4) < (x_54));
        Bit#(16) x_56 = ((x_3)[15:0]);
        Bit#(32) x_57 = (imem.sub(x_56));
        Bit#(8) x_58 = ((x_57)[31:24]);
        Bit#(8) x_59 = ((x_57)[23:16]);
        Bit#(8) x_60 = ((x_57)[15:8]);
        Bit#(8) x_61 = ((x_57)[7:0]);
        Bit#(32) x_62 = (zeroExtend(x_61));
        Bit#(32) x_63 = ((x_4) + (x_62));
        Bit#(32) x_64 = ((x_3) + ((Bit#(32))'(32'h1)));
        Bit#(5) x_65 = ((x_59)[4:0]);
        Bit#(5) x_66 = ((x_60)[4:0]);
        Bit#(4) x_67 = ((x_60)[7:4]);
        Bit#(4) x_68 = ((x_60)[3:0]);
        Bit#(5) x_69 = (zeroExtend(x_67));
        Bit#(5) x_70 = (zeroExtend(x_68));
        Bit#(32) x_71 = ((x_5)[x_69]);
        Bit#(32) x_72 = ((x_5)[x_70]);
        Bit#(32) x_73 = ((x_5)[x_65]);
        Bit#(32) x_74 = ((x_5)[x_66]);
        Bit#(32) x_75 = (zeroExtend(x_60));
        Bit#(16) x_76 = ((x_74)[15:0]);
        Bit#(16) x_77 = ((x_73)[15:0]);
        Bit#(16) x_78 = (zeroExtend(x_60));
        Bit#(32) x_79 = (mem.sub(x_76));
        Bit#(32) x_80 = (mem.sub(x_78));
        Bit#(32) x_81 = ((x_5)[(Bit#(5))'(5'h1f)]);
        Bit#(16) x_82 = ((x_81)[15:0]);
        Bit#(32) x_83 = ((x_81) + ((Bit#(32))'(32'h1)));
        Bit#(32) x_84 = ((x_81) - ((Bit#(32))'(32'h1)));
        Bit#(16) x_85 = ((x_84)[15:0]);
        Bit#(32) x_86 = ((x_27)[x_13]);
        Bool x_87 = ((zeroExtend(x_76)) < (x_86));
        Bool x_88 = ((zeroExtend(x_77)) < (x_86));
        Bool x_89 = ((zeroExtend(x_82)) < (x_86));
        Bool x_90 = ((zeroExtend(x_85)) < (x_86));
        Bool x_91 = (((x_58) == ((Bit#(8))'(8'h11))) || ((x_58) ==
        ((Bit#(8))'(8'h1c))));
        Bool x_92 = (((x_58) == ((Bit#(8))'(8'h12))) || ((x_58) ==
        ((Bit#(8))'(8'h1d))));
        Bool x_93 = ((x_58) == ((Bit#(8))'(8'h17)));
        Bool x_94 = ((x_58) == ((Bit#(8))'(8'h18)));
        Bool x_95 = ((x_91) && (! (x_87)));
        Bool x_96 = ((x_92) && (! (x_88)));
        Bool x_97 = ((x_93) && (! (x_89)));
        Bool x_98 = ((x_94) && (! (x_90)));
        Bool x_99 = ((((x_95) || (x_96)) || (x_97)) || (x_98));
        Bool x_100 = ((x_12) == ((Bit#(32))'(32'hcafeeace)));
        Bool x_101 = ((((x_58) == ((Bit#(8))'(8'hf))) || ((x_58) ==
        ((Bit#(8))'(8'h6)))) || ((x_58) == ((Bit#(8))'(8'h9))));
        Bool x_102 = ((x_101) && (! (x_100)));
        Bool x_103 = (! ((x_28) < ((Bit#(7))'(7'h40))));
        Bool x_104 = (! (x_103));
        Bool x_105 = (! (((Bit#(7))'(7'h40)) < ((x_28) +
        ((Bit#(7))'(7'h2)))));
        Bool x_106 = (((x_58) == ((Bit#(8))'(8'h0))) && (! (x_104)));
        Bool x_107 = (((x_58) == ((Bit#(8))'(8'h1))) && (! (x_105)));
        Bool x_108 = (((x_58) == ((Bit#(8))'(8'h2))) && (! (x_104)));
        Bool x_109 = (((x_106) || (x_107)) || (x_108));
        Bit#(6) x_110 = ((x_60)[5:0]);
        Bit#(32) x_111 = ((x_27)[x_110]);
        Bit#(32) x_112 = (zeroExtend(x_60));
        Bit#(16) x_113 = ({(x_59),(x_60)});
        Bit#(32) x_114 = (zeroExtend(x_113));
        Bit#(32) x_115 = ((x_90 ? (mem.sub(x_85)) : ((Bit#(32))'(32'h0))));
        
        Bit#(32) x_116 = ((x_71) + (x_72));
        Bit#(32) x_117 = ((x_71) - (x_72));
        Bit#(32) x_118 = ((x_71) & (x_72));
        Bit#(32) x_119 = ((x_71) | (x_72));
        Bit#(32) x_120 = ((x_71) << (x_72));
        Bit#(32) x_121 = ((x_71) >> (x_72));
        Bit#(32) x_122 = (multiply_unsigned ((x_71), (x_72)));
        Bit#(32) x_123 = ((Bit#(32))'(32'h8));
        Bit#(32) x_124 = ((x_75) << (x_123));
        Bit#(32) x_125 = ((x_73) ^ (x_74));
        Bool x_126 = (! ((x_73) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_127 = (x_74);
        Bit#(32) x_128 = ((Bit#(32))'(32'h55555555));
        Bit#(32) x_129 = ((x_127) & (x_128));
        Bit#(32) x_130 = (((x_127) >> ((Bit#(6))'(6'h1))) & (x_128));
        Bit#(32) x_131 = ((x_129) + (x_130));
        Bit#(32) x_132 = ((Bit#(32))'(32'h33333333));
        Bit#(32) x_133 = ((x_131) & (x_132));
        Bit#(32) x_134 = (((x_131) >> ((Bit#(6))'(6'h2))) & (x_132));
        Bit#(32) x_135 = ((x_133) + (x_134));
        Bit#(32) x_136 = ((Bit#(32))'(32'hf0f0f0f));
        Bit#(32) x_137 = ((x_135) & (x_136));
        Bit#(32) x_138 = (((x_135) >> ((Bit#(6))'(6'h4))) & (x_136));
        Bit#(32) x_139 = ((x_137) + (x_138));
        Bit#(32) x_140 = ((Bit#(32))'(32'hff00ff));
        Bit#(32) x_141 = ((x_139) & (x_140));
        Bit#(32) x_142 = (((x_139) >> ((Bit#(6))'(6'h8))) & (x_140));
        Bit#(32) x_143 = ((x_141) + (x_142));
        Bit#(32) x_144 = ((Bit#(32))'(32'hffff));
        Bit#(32) x_145 = ((x_143) & (x_144));
        Bit#(32) x_146 = (((x_143) >> ((Bit#(6))'(6'h10))) & (x_144));
        
        Bit#(32) x_147 = ((x_145) + (x_146));
        Bool x_148 = (((Bit#(8))'(8'h3)) < (x_60));
        Bool x_149 = (((Bit#(8))'(8'h1)) < (x_59));
        Bool x_150 = ((x_149) && ((x_54) == ((Bit#(32))'(32'h0))));
        Bool x_151 = (x_150);
        Bit#(2) x_152 = ((x_59)[1:0]);
        Bit#(2) x_153 = ((x_60)[1:0]);
        Bool x_154 = (((x_153) == ((Bit#(2))'(2'h0))) || ((x_153) ==
        ((Bit#(2))'(2'h3))));
        Bool x_155 = ((x_152) == ((Bit#(2))'(2'h0)));
        Bool x_156 = ((x_152) == ((Bit#(2))'(2'h1)));
        Bool x_157 = ((x_152) == ((Bit#(2))'(2'h2)));
        Bool x_158 = ((x_152) == ((Bit#(2))'(2'h3)));
        Bool x_159 = (((x_58) == ((Bit#(8))'(8'h3))) || ((x_58) ==
        ((Bit#(8))'(8'h4))));
        Bit#(16) x_160 = ({(x_59),(x_60)});
        Bit#(32) x_161 = (zeroExtend(x_160));
        Bool x_162 = ((x_20) && (! (x_23)));
        Bool x_163 = ((x_20) && (x_23));
        Bool x_164 = ((x_159) && (! (x_20)));
        Bit#(32) x_165 = (zeroExtend(x_60));
        Bool x_166 = (((x_58) == ((Bit#(8))'(8'h6))) || ((x_58) ==
        ((Bit#(8))'(8'he))));
        Bool x_167 = ((x_166) && ((x_62) < (x_165)));
        Bool x_168 = ((((((((x_58) == ((Bit#(8))'(8'h9))) && (! (x_151))) &&
        (! (x_55))) && (! (x_99))) && (! (x_109))) && (! (x_102))) && (!
        (x_167)));
        Bit#(4) x_169 = ((x_59)[3:0]);
        Bit#(32) x_170 = ((x_26)[x_169]);
        Bit#(32) x_171 = ((x_170) + (x_62));
        Bit#(32) x_172 = ((((((x_55) || (x_99)) || (x_109)) || (x_102)) ||
        (x_167) ? (x_19) : ((x_162 ? (x_3) : (((x_58) == ((Bit#(8))'(8'hff))
        ? (x_3) : (((x_58) == ((Bit#(8))'(8'h15)) ? (x_114) : (((x_58) ==
        ((Bit#(8))'(8'h17)) ? (x_114) : (((x_58) == ((Bit#(8))'(8'h18)) ?
        (x_115) : ((((x_58) == ((Bit#(8))'(8'h16))) && (x_126) ? (x_112) :
        (x_64)))))))))))))));
        Vector#(32, Bit#(32)) x_173 = (update (update (x_5, x_65, x_74),
        x_66, x_73));
        Vector#(32, Bit#(32)) x_174 = ((((((x_55) || (x_99)) || (x_109)) ||
        (x_102)) || (x_167) ? (x_5) : (((x_58) == ((Bit#(8))'(8'h8)) ?
        (update (x_5, x_65, x_75)) : (((x_58) == ((Bit#(8))'(8'h13)) ?
        (update (x_5, x_65, x_116)) : (((x_58) == ((Bit#(8))'(8'h14)) ?
        (update (x_5, x_65, x_117)) : (((x_58) == ((Bit#(8))'(8'h7)) ?
        (update (x_5, x_65, x_74)) : (((x_58) == ((Bit#(8))'(8'h11)) ?
        (update (x_5, x_65, x_79)) : (((x_58) == ((Bit#(8))'(8'ha)) ? (update
        (x_5, x_65, x_80)) : (((x_58) == ((Bit#(8))'(8'hb)) ? (update (x_5,
        x_65, x_125)) : (((x_58) == ((Bit#(8))'(8'hc)) ? (x_173) : (((x_58)
        == ((Bit#(8))'(8'hd)) ? (update (x_5, x_65, x_147)) : (((x_58) ==
        ((Bit#(8))'(8'h17)) ? (update (x_5, (Bit#(5))'(5'h1f), x_83)) :
        (((x_58) == ((Bit#(8))'(8'h18)) ? (update (x_5, (Bit#(5))'(5'h1f),
        x_84)) : (((x_58) == ((Bit#(8))'(8'h6)) ? (update (x_5, x_65, x_111))
        : (((x_58) == ((Bit#(8))'(8'h1c)) ? (update (x_5, x_65, x_79)) :
        (((x_58) == ((Bit#(8))'(8'h1a)) ? (update (x_5, x_65,
        (Bit#(32))'(32'h0))) : (((x_58) == ((Bit#(8))'(8'h1f)) ? (update
        (x_5, x_65, x_118)) : (((x_58) == ((Bit#(8))'(8'h20)) ? (update (x_5,
        x_65, x_119)) : (((x_58) == ((Bit#(8))'(8'h21)) ? (update (x_5, x_65,
        x_120)) : (((x_58) == ((Bit#(8))'(8'h22)) ? (update (x_5, x_65,
        x_121)) : (((x_58) == ((Bit#(8))'(8'h23)) ? (update (x_5, x_65,
        x_122)) : (((x_58) == ((Bit#(8))'(8'h24)) ? (update (x_5, x_65,
        x_124)) : (((x_58) == ((Bit#(8))'(8'h26)) ? (update (x_5, x_65,
        x_170)) : (((((((x_58) == ((Bit#(8))'(8'h27))) || ((x_58) ==
        ((Bit#(8))'(8'h28)))) || ((x_58) == ((Bit#(8))'(8'h29)))) || ((x_58)
        == ((Bit#(8))'(8'h2c)))) || ((x_58) == ((Bit#(8))'(8'h2d))) ? (update
        (x_5, x_65, (Bit#(32))'(32'h0))) :
        (x_5)))))))))))))))))))))))))))))))))))))))))))))));

        Bool x_176 = (((((x_99) || (x_109)) || (x_102)) || (x_167)) ||
        ((x_58) == ((Bit#(8))'(8'hff))));
        Bool x_177 = ((x_163) && (x_24));
        Bool x_178 = ((((((x_99) || (x_109)) || (x_102)) || (x_167)) ||
        (((x_58) == ((Bit#(8))'(8'h9))) && (x_151))) || (x_177));
        Bit#(32) x_179 = ((x_55 ? ((Bit#(32))'(32'hb1a4c81)) : ((x_99 ?
        ((Bit#(32))'(32'hbadc0de)) : ((x_109 ? ((Bit#(32))'(32'hbadf001d)) :
        ((x_167 ? ((Bit#(32))'(32'hc43471a1)) : (((x_102) || (x_177) ?
        ((Bit#(32))'(32'hc43471a1)) : ((((x_58) == ((Bit#(8))'(8'h9))) &&
        (x_151) ? ((Bit#(32))'(32'hbadc45c)) : (x_11)))))))))))));
        Bit#(32) x_180 = (((((x_55) || (x_109)) || (x_102)) || (x_167) ?
        (x_4) : ((x_162 ? (x_4) : (((x_58) == ((Bit#(8))'(8'h10)) ? ((x_4) +
        ((Bit#(32))'(32'hf4240))) : ((((x_58) == ((Bit#(8))'(8'h9))) &&
        (x_149) ? ((x_63) + ((Bit#(32))'(32'h100))) : (((x_58) ==
        ((Bit#(8))'(8'h1e)) ? (((x_4) + (x_62)) + ((Bit#(32))'(32'h1))) :
        (((x_58) == ((Bit#(8))'(8'h2b)) ? (((x_4) + (x_62)) +
        ((Bit#(32))'(32'h1))) : (((((((x_58) == ((Bit#(8))'(8'he))) ||
        ((x_58) == ((Bit#(8))'(8'hf)))) || ((x_58) == ((Bit#(8))'(8'h3)))) ||
        ((x_58) == ((Bit#(8))'(8'h4)))) || ((x_58) == ((Bit#(8))'(8'h1a))) ?
        ((x_63) + ((Bit#(32))'(32'h1))) : (x_63)))))))))))))));
        Bool x_181 = ((((((x_55) || (x_99)) || (x_109)) || (x_102)) ||
        (x_167) ? (x_29) : (((x_58) == ((Bit#(8))'(8'h1e)) ? ((Bool)'(True))
        : (x_29)))));
        Bit#(6) x_182 = ((x_28)[5:0]);
        Bit#(32) x_183 = (zeroExtend(x_59));
        Vector#(64, Bit#(32)) x_184 = (update (x_27, x_182, x_183));
        Bit#(7) x_185 = ((x_28) + ((Bit#(7))'(7'h1)));
        Bit#(6) x_186 = ((x_59)[5:0]);
        Bit#(32) x_187 = ((x_27)[x_186]);
        Bit#(32) x_188 = ((x_187) >> ((Bit#(5))'(5'h1)));
        Bit#(32) x_189 = ((x_187) - (x_188));
        Bit#(6) x_190 = ((x_28)[5:0]);
        Bit#(6) x_191 = (((x_28) + ((Bit#(7))'(7'h1)))[5:0]);
        
        Vector#(64, Bit#(32)) x_192 = (update (update (update (x_27, x_186,
        (Bit#(32))'(32'h0)), x_190, x_188), x_191, x_189));
        Bit#(7) x_193 = ((x_28) + ((Bit#(7))'(7'h2)));
        Bit#(6) x_194 = ((x_59)[5:0]);
        Bit#(6) x_195 = ((x_60)[5:0]);
        Bit#(32) x_196 = ((x_27)[x_194]);
        Bit#(32) x_197 = ((x_27)[x_195]);
        Bit#(32) x_198 = ((x_196) + (x_197));
        Bit#(6) x_199 = ((x_28)[5:0]);
        Vector#(64, Bit#(32)) x_200 = (update (update (update (x_27, x_194,
        (Bit#(32))'(32'h0)), x_195, (Bit#(32))'(32'h0)), x_199, x_198));
        
        Bit#(7) x_201 = ((x_28) + ((Bit#(7))'(7'h1)));
        Vector#(64, Bit#(32)) x_202 = (((x_55) || (x_109) ? (x_27) : (((x_58)
        == ((Bit#(8))'(8'h0)) ? (x_184) : (((x_58) == ((Bit#(8))'(8'h1)) ?
        (x_192) : (((x_58) == ((Bit#(8))'(8'h2)) ? (x_200) : (x_27)))))))));
        
        Bit#(7) x_203 = (((x_55) || (x_109) ? (x_28) : (((x_58) ==
        ((Bit#(8))'(8'h0)) ? (x_185) : (((x_58) == ((Bit#(8))'(8'h1)) ?
        (x_193) : (((x_58) == ((Bit#(8))'(8'h2)) ? (x_201) : (x_28)))))))));
        
        Bool x_204 = ((((x_58) == ((Bit#(8))'(8'h0))) || ((x_58) ==
        ((Bit#(8))'(8'h1)))) || ((x_58) == ((Bit#(8))'(8'h2))));
        Bit#(32) x_205 = (((x_204) && (! (x_55)) ? ((x_8) +
        ((Bit#(32))'(32'h1))) : (x_8)));
        Bit#(32) x_206 = ((((x_58) == ((Bit#(8))'(8'h5))) && (! (x_55)) ?
        ((x_9) + ((Bit#(32))'(32'h1))) : (x_9)));
        Bit#(32) x_207 = (((((((x_166) && (! (x_55))) && (! (x_99))) && (!
        (x_109))) && (! (x_102))) && (! (x_167)) ? ((x_10) + (x_165)) :
        (x_10)));
        Bit#(32) x_208 = ((((x_168) && (x_155)) && (x_154) ? ((x_30) +
        ((Bit#(32))'(32'h1))) : (x_30)));
        Bit#(32) x_209 = ((((x_168) && (x_155)) && (! (x_154)) ? ((x_31) +
        ((Bit#(32))'(32'h1))) : (x_31)));
        Bit#(32) x_210 = ((((x_168) && (x_156)) && (x_154) ? ((x_32) +
        ((Bit#(32))'(32'h1))) : (x_32)));
        Bit#(32) x_211 = ((((x_168) && (x_156)) && (! (x_154)) ? ((x_33) +
        ((Bit#(32))'(32'h1))) : (x_33)));
        Bit#(32) x_212 = ((((x_168) && (x_157)) && (x_154) ? ((x_34) +
        ((Bit#(32))'(32'h1))) : (x_34)));
        Bit#(32) x_213 = ((((x_168) && (x_157)) && (! (x_154)) ? ((x_35) +
        ((Bit#(32))'(32'h1))) : (x_35)));
        Bit#(32) x_214 = ((((x_168) && (x_158)) && (x_154) ? ((x_36) +
        ((Bit#(32))'(32'h1))) : (x_36)));
        Bit#(32) x_215 = ((((x_168) && (x_158)) && (! (x_154)) ? ((x_37) +
        ((Bit#(32))'(32'h1))) : (x_37)));
        Vector#(16, Bit#(32)) x_216 = (((((x_58) == ((Bit#(8))'(8'hf))) && (!
        (x_55))) && (! (x_102)) ? (update (x_26, x_169, x_171)) : ((((x_58)
        == ((Bit#(8))'(8'h25))) && (! (x_55)) ? (update (x_26, x_169, x_74))
        : (x_26)))));
        Bit#(32) x_217 = (((x_55) || (x_99) ? (x_12) : ((x_163 ? ((x_12) +
        (x_25)) : (((x_58) == ((Bit#(8))'(8'h3)) ? ((x_12) ^
        ((Bit#(32))'(32'hcafeeace))) : (((x_58) == ((Bit#(8))'(8'h10)) ?
        ((x_12) + ((Bit#(32))'(32'h1))) : (x_12)))))))));
        Bool x_218 = ((x_55 ? ((Bool)'(False)) : ((x_163 ? ((Bool)'(False)) :
        ((x_164 ? ((Bool)'(True)) : (x_2)))))));
        Bool x_219 = ((x_55 ? ((Bool)'(False)) : ((x_163 ? ((Bool)'(False)) :
        ((x_164 ? ((Bool)'(True)) : (x_20)))))));
        Bit#(8) x_220 = ((x_164 ? (x_58) : (x_21)));
        Bit#(32) x_221 = ((x_164 ? (x_161) : (x_22)));
        Bool x_222 = ((x_55 ? ((Bool)'(False)) : ((x_163 ? ((Bool)'(False)) :
        (x_23)))));
        Bit#(32) x_223 = ((x_15) + ((Bit#(32))'(32'h1)));
        Bool x_224 = ((x_223) == ((Bit#(32))'(32'h0)));
        Bit#(32) x_225 = ((x_224 ? ((x_16) + ((Bit#(32))'(32'h1))) :
        (x_16)));
        Bool x_226 = (((((! (x_162)) && (! (x_99))) && (! (x_109))) && (!
        (x_102))) && (! (x_167)));
        Bit#(32) x_227 = ((x_226 ? ((x_17) + ((Bit#(32))'(32'h1))) :
        (x_17)));
        Bool x_228 = ((x_226) && ((x_227) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_229 = ((x_228 ? ((x_18) + ((Bit#(32))'(32'h1))) :
        (x_18)));
        Bit#(32) x_230 = ((x_100 ? ((Bit#(32))'(32'h1)) :
        ((Bit#(32))'(32'h0))));
        pc <= x_172;
        mu <= x_180;
        regs <= x_174;
        if ((!(((((x_55) || (x_99)) || (x_109)) || (x_102)) || (x_167))) && ((x_58) == ((Bit#(8))'(8'h12)))) mem.upd(x_77, x_74);
        if ((!(((((x_55) || (x_99)) || (x_109)) || (x_102)) || (x_167))) && ((x_58) == ((Bit#(8))'(8'h17)))) mem.upd(x_82, x_64);
        if ((!(((((x_55) || (x_99)) || (x_109)) || (x_102)) || (x_167))) && ((x_58) == ((Bit#(8))'(8'h1d)))) mem.upd(x_77, x_74);

        halted <= x_176;
        err <= x_178;
        error_code <= x_179;
        logic_acc <= x_217;
        mstatus <= x_230;
        mcycle_lo <= x_223;
        mcycle_hi <= x_225;
        minstret_lo <= x_227;
        minstret_hi <= x_229;
        logic_req_valid <= x_219;
        logic_req_opcode <= x_220;
        logic_req_payload <= x_221;
        logic_resp_valid <= x_222;
        logic_stall <= x_218;
        partition_ops <= x_205;
        mdl_ops <= x_206;
        info_gain <= x_207;
        mu_tensor <= x_216;
        ptTable <= x_202;
        pt_next_id <= x_203;
        certified <= x_181;
        wc_same_00 <= x_208;
        wc_diff_00 <= x_209;
        wc_same_01 <= x_210;
        wc_diff_01 <= x_211;
        wc_same_10 <= x_212;
        wc_diff_10 <= x_213;
        wc_same_11 <= x_214;
        wc_diff_11 <= x_215;
        
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
    
    method ActionValue#(Bool) getLogicReqValid ();
        let x_1 = (logic_req_valid);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(8)) getLogicReqOpcode ();
        let x_1 = (logic_req_opcode);
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getLogicReqPayload ();
        let x_1 = (logic_req_payload);
        return x_1;
    endmethod
    
    method Action setLogicResp (Struct2 x_0);
        Bool x_1 = ((x_0).valid);
        Bool x_2 = ((x_0).error);
        Bit#(32) x_3 = ((x_0).value);
        logic_resp_valid <= x_1;
        logic_resp_error <= x_2;
        logic_resp_value <= x_3;
        
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
        let x_15 = (logic_req_valid);
        let x_16 = (logic_req_opcode);
        let x_17 = (logic_req_payload);
        let x_18 = (mu_tensor);
        let x_19 = (pt_next_id);
        let x_20 = (ptTable);
        Bit#(32) x_21 = (((((x_18)[(Bit#(4))'(4'h0)]) +
        ((x_18)[(Bit#(4))'(4'h1)])) + ((x_18)[(Bit#(4))'(4'h2)])) +
        ((x_18)[(Bit#(4))'(4'h3)]));
        Bit#(32) x_22 = (((((x_18)[(Bit#(4))'(4'h4)]) +
        ((x_18)[(Bit#(4))'(4'h5)])) + ((x_18)[(Bit#(4))'(4'h6)])) +
        ((x_18)[(Bit#(4))'(4'h7)]));
        Bit#(32) x_23 = (((((x_18)[(Bit#(4))'(4'h8)]) +
        ((x_18)[(Bit#(4))'(4'h9)])) + ((x_18)[(Bit#(4))'(4'ha)])) +
        ((x_18)[(Bit#(4))'(4'hb)]));
        Bit#(32) x_24 = (((((x_18)[(Bit#(4))'(4'hc)]) +
        ((x_18)[(Bit#(4))'(4'hd)])) + ((x_18)[(Bit#(4))'(4'he)])) +
        ((x_18)[(Bit#(4))'(4'hf)]));
        Bit#(32) x_25 = ((((x_21) + (x_22)) + (x_23)) + (x_24));
        Bool x_26 = ((x_2) < (x_25));
        Bit#(32) x_27 = (zeroExtend(x_19));
        Bit#(32) x_28 = ((x_20)[(Bit#(6))'(6'h0)]);
        Bit#(32) x_29 = (zeroExtend(x_16));
        Bit#(32) x_30 = (((x_0) == ((Bit#(32))'(32'h0)) ? (x_1) : (((x_0) ==
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
        (x_14) : (((x_0) == ((Bit#(32))'(32'h38)) ? ((x_15 ?
        ((Bit#(32))'(32'h1)) : ((Bit#(32))'(32'h0)))) : (((x_0) ==
        ((Bit#(32))'(32'h3c)) ? (x_29) : (((x_0) == ((Bit#(32))'(32'h40)) ?
        (x_17) : (((x_0) == ((Bit#(32))'(32'h44)) ? (x_21) : (((x_0) ==
        ((Bit#(32))'(32'h48)) ? (x_22) : (((x_0) == ((Bit#(32))'(32'h4c)) ?
        (x_23) : (((x_0) == ((Bit#(32))'(32'h50)) ? (x_24) : (((x_0) ==
        ((Bit#(32))'(32'h54)) ? ((x_26 ? ((Bit#(32))'(32'h1)) :
        ((Bit#(32))'(32'h0)))) : (((x_0) == ((Bit#(32))'(32'h58)) ? (x_27) :
        (((x_0) == ((Bit#(32))'(32'h5c)) ? (x_28) :
        ((Bit#(32))'(32'h0))))))))))))))))))))))))))))))))))))))))))))))))));
        
        return x_30;
    endmethod
    
    method ActionValue#(Bool) apbReadErr (Bit#(32) x_0);
        Bool x_1 = (((((((((((((((((((((((((x_0) == ((Bit#(32))'(32'h0))) ||
        ((x_0) == ((Bit#(32))'(32'h4)))) || ((x_0) == ((Bit#(32))'(32'h8))))
        || ((x_0) == ((Bit#(32))'(32'hc)))) || ((x_0) ==
        ((Bit#(32))'(32'h10)))) || ((x_0) == ((Bit#(32))'(32'h14)))) ||
        ((x_0) == ((Bit#(32))'(32'h18)))) || ((x_0) ==
        ((Bit#(32))'(32'h1c)))) || ((x_0) == ((Bit#(32))'(32'h20)))) ||
        ((x_0) == ((Bit#(32))'(32'h24)))) || ((x_0) ==
        ((Bit#(32))'(32'h28)))) || ((x_0) == ((Bit#(32))'(32'h2c)))) ||
        ((x_0) == ((Bit#(32))'(32'h30)))) || ((x_0) ==
        ((Bit#(32))'(32'h34)))) || ((x_0) == ((Bit#(32))'(32'h38)))) ||
        ((x_0) == ((Bit#(32))'(32'h3c)))) || ((x_0) ==
        ((Bit#(32))'(32'h40)))) || ((x_0) == ((Bit#(32))'(32'h44)))) ||
        ((x_0) == ((Bit#(32))'(32'h48)))) || ((x_0) ==
        ((Bit#(32))'(32'h4c)))) || ((x_0) == ((Bit#(32))'(32'h50)))) ||
        ((x_0) == ((Bit#(32))'(32'h54)))) || ((x_0) ==
        ((Bit#(32))'(32'h58)))) || ((x_0) == ((Bit#(32))'(32'h5c))));
        return ! (x_1);
    endmethod
    
    method ActionValue#(Bool) apbWrite (Struct3 x_0);
        let x_2 = (logic_resp_valid);
        let x_3 = (logic_resp_error);
        let x_4 = (logic_resp_value);
        let x_5 = (active_module);
        let x_6 = (trap_vector);
        let x_7 = (bus_load_instr_addr);
        let x_8 = (bus_load_instr_data);
        let x_9 = (bus_load_instr_kick);
        Bit#(32) x_10 = ((x_0).addr);
        Bit#(32) x_11 = ((x_0).data);
        Bool x_12 = ((x_10) == ((Bit#(32))'(32'h80)));
        Bool x_13 = ((x_10) == ((Bit#(32))'(32'h84)));
        Bool x_14 = ((x_10) == ((Bit#(32))'(32'h88)));
        Bool x_15 = ((x_10) == ((Bit#(32))'(32'h8c)));
        Bool x_16 = ((x_10) == ((Bit#(32))'(32'h90)));
        Bool x_17 = ((x_10) == ((Bit#(32))'(32'h94)));
        Bool x_18 = ((x_10) == ((Bit#(32))'(32'h98)));
        Bool x_19 = ((x_10) == ((Bit#(32))'(32'h9c)));
        Bool x_20 = ((((((((x_12) || (x_13)) || (x_14)) || (x_15)) || (x_16))
        || (x_17)) || (x_18)) || (x_19));
        Bit#(16) x_21 = ((x_11)[15:0]);
        Bit#(32) x_22 = ((x_11)[31:0]);
        Bool x_23 = (! ((x_11) == ((Bit#(32))'(32'h0))));
        Bit#(16) x_24 = ((x_12 ? (x_21) : (x_7)));
        Bit#(32) x_25 = ((x_13 ? (x_22) : (x_8)));
        Bool x_26 = ((x_14 ? (x_23) : (x_9)));
        Bool x_27 = ((x_14) && (x_23));

        Bool x_29 = ((x_15 ? (x_23) : (x_2)));
        Bool x_30 = ((x_16 ? (x_23) : (x_3)));
        Bit#(32) x_31 = ((x_17 ? (x_11) : (x_4)));
        Bit#(6) x_32 = ((x_18 ? ((x_11)[5:0]) : (x_5)));
        Bit#(32) x_33 = ((x_19 ? (x_11) : (x_6)));
        if (x_27) imem.upd(x_24, x_25);

        bus_load_instr_addr <= x_24;
        bus_load_instr_data <= x_25;
        bus_load_instr_kick <= x_26;
        logic_resp_valid <= x_29;
        logic_resp_error <= x_30;
        logic_resp_value <= x_31;
        active_module <= x_32;
        trap_vector <= x_33;
        return ! (x_20);
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

