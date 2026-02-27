import Vector::*;
import FIFO::*;
import FIFOF::*;
import BRAM::*;
import GetPut::*;
typedef struct { Bit#(8) addr; Bit#(32) data;  } Struct1 deriving(Eq, Bits);
typedef struct { Bool valid; Bool error; Bit#(32) value;  } Struct2 deriving(Eq, Bits);

interface Module1;
    method Action loadInstr (Struct1 x_0);
    method ActionValue#(Bit#(32)) getPC ();
    method ActionValue#(Bit#(32)) getMu ();
    method ActionValue#(Bool) getErr ();
    method ActionValue#(Bool) getHalted ();
    method ActionValue#(Bit#(32)) getPartitionOps ();
    method ActionValue#(Bit#(32)) getMdlOps ();
    method ActionValue#(Bit#(32)) getInfoGain ();
    method ActionValue#(Bit#(32)) getErrorCode ();
    method ActionValue#(Bit#(32)) getLogicAcc ();
    method ActionValue#(Bool) getLogicReqValid ();
    method ActionValue#(Bit#(8)) getLogicReqOpcode ();
    method ActionValue#(Bit#(32)) getLogicReqPayload ();
    method Action setLogicResp (Struct2 x_0);
    method ActionValue#(Bit#(32)) getMuTensor0 ();
    method ActionValue#(Bit#(32)) getMuTensor1 ();
    method ActionValue#(Bit#(32)) getMuTensor2 ();
    method ActionValue#(Bit#(32)) getMuTensor3 ();
    method ActionValue#(Bool) getBianchiAlarm ();
    method ActionValue#(Bit#(32)) getPtNextId ();
    method ActionValue#(Bit#(32)) getPtSize (Bit#(6) x_0);
    
endinterface

module mkModule1 (Module1);
    Reg#(Bit#(32)) pc <- mkReg(unpack(0));
    Reg#(Bit#(32)) mu <- mkReg(unpack(0));Reg#(Bool) err <- mkReg(False);
    Reg#(Bool) halted <- mkReg(False);
    Reg#(Vector#(32, Bit#(32))) regs <- mkReg(unpack(0));
    Reg#(Vector#(256, Bit#(32))) mem <- mkReg(unpack(0));
    Reg#(Vector#(256, Bit#(32))) imem <- mkReg(unpack(0));
    Reg#(Bit#(32)) partition_ops <- mkReg(unpack(0));
    Reg#(Bit#(32)) mdl_ops <- mkReg(unpack(0));
    Reg#(Bit#(32)) info_gain <- mkReg(unpack(0));
    Reg#(Bit#(32)) error_code <- mkReg(unpack(0));
    Reg#(Bit#(32)) logic_acc <- mkReg(unpack(0));
    Reg#(Bool) logic_req_valid <- mkReg(False);
    Reg#(Bit#(8)) logic_req_opcode <- mkReg(unpack(0));
    Reg#(Bit#(32)) logic_req_payload <- mkReg(unpack(0));
    Reg#(Bool) logic_resp_valid <- mkReg(False);
    Reg#(Bool) logic_resp_error <- mkReg(False);
    Reg#(Bit#(32)) logic_resp_value <- mkReg(unpack(0));
    Reg#(Vector#(16, Bit#(32))) mu_tensor <- mkReg(unpack(0));
    Reg#(Vector#(64, Bit#(32))) pt_sizes <- mkReg(unpack(0));
    Reg#(Bit#(32)) pt_next_id <- mkReg(32'h1);
    
    rule step;
        let x_0 = (halted);
        when (! (x_0), noAction);
        let x_1 = (err);
        when (! (x_1), noAction);
        let x_2 = (pc);
        let x_3 = (mu);
        let x_4 = (regs);
        let x_5 = (mem);
        let x_6 = (imem);
        let x_7 = (partition_ops);
        let x_8 = (mdl_ops);
        let x_9 = (info_gain);
        let x_10 = (error_code);
        let x_11 = (logic_acc);
        let x_12 = (logic_req_valid);
        let x_13 = (logic_req_opcode);
        let x_14 = (logic_req_payload);
        let x_15 = (logic_resp_valid);
        let x_16 = (logic_resp_error);
        let x_17 = (logic_resp_value);
        let x_18 = (mu_tensor);
        let x_19 = (pt_sizes);
        let x_20 = (pt_next_id);
        Bit#(32) x_21 = ((x_18)[(Bit#(4))'(4'h0)]);
        Bit#(32) x_22 = ((x_18)[(Bit#(4))'(4'h1)]);
        Bit#(32) x_23 = ((x_18)[(Bit#(4))'(4'h2)]);
        Bit#(32) x_24 = ((x_18)[(Bit#(4))'(4'h3)]);
        Bit#(32) x_25 = ((x_18)[(Bit#(4))'(4'h4)]);
        Bit#(32) x_26 = ((x_18)[(Bit#(4))'(4'h5)]);
        Bit#(32) x_27 = ((x_18)[(Bit#(4))'(4'h6)]);
        Bit#(32) x_28 = ((x_18)[(Bit#(4))'(4'h7)]);
        Bit#(32) x_29 = ((x_18)[(Bit#(4))'(4'h8)]);
        Bit#(32) x_30 = ((x_18)[(Bit#(4))'(4'h9)]);
        Bit#(32) x_31 = ((x_18)[(Bit#(4))'(4'ha)]);
        Bit#(32) x_32 = ((x_18)[(Bit#(4))'(4'hb)]);
        Bit#(32) x_33 = ((x_18)[(Bit#(4))'(4'hc)]);
        Bit#(32) x_34 = ((x_18)[(Bit#(4))'(4'hd)]);
        Bit#(32) x_35 = ((x_18)[(Bit#(4))'(4'he)]);
        Bit#(32) x_36 = ((x_18)[(Bit#(4))'(4'hf)]);
        Bit#(32) x_37 = ((((((((((((((((x_21) + (x_22)) + (x_23)) + (x_24)) +
        (x_25)) + (x_26)) + (x_27)) + (x_28)) + (x_29)) + (x_30)) + (x_31)) +
        (x_32)) + (x_33)) + (x_34)) + (x_35)) + (x_36));
        Bool x_38 = ((x_3) < (x_37));
        Bit#(8) x_39 = ((x_2)[7:0]);
        Bit#(32) x_40 = ((x_6)[x_39]);
        Bit#(8) x_41 = ((x_40)[31:24]);
        Bit#(8) x_42 = ((x_40)[23:16]);
        Bit#(8) x_43 = ((x_40)[15:8]);
        Bit#(8) x_44 = ((x_40)[7:0]);
        Bit#(32) x_45 = (zeroExtend(x_44));
        Bit#(32) x_46 = ((x_3) + (x_45));
        Bit#(32) x_47 = ((x_2) + ((Bit#(32))'(32'h1)));
        Bit#(5) x_48 = ((x_42)[4:0]);
        Bit#(5) x_49 = ((x_43)[4:0]);
        Bit#(4) x_50 = ((x_43)[7:4]);
        Bit#(4) x_51 = ((x_43)[3:0]);
        Bit#(5) x_52 = (zeroExtend(x_50));
        Bit#(5) x_53 = (zeroExtend(x_51));
        Bit#(32) x_54 = ((x_4)[x_52]);
        Bit#(32) x_55 = ((x_4)[x_53]);
        Bit#(32) x_56 = ((x_4)[x_48]);
        Bit#(32) x_57 = ((x_4)[x_49]);
        Bit#(32) x_58 = (zeroExtend(x_43));
        Bit#(8) x_59 = ((x_43)[7:0]);
        Bit#(8) x_60 = ((x_42)[7:0]);
        Bit#(32) x_61 = ((x_5)[x_59]);
        Bit#(6) x_62 = ((x_43)[5:0]);
        Bit#(32) x_63 = ((x_19)[x_62]);
        Bit#(32) x_64 = (zeroExtend(x_43));
        Bit#(16) x_65 = ({(x_42),(x_43)});
        Bit#(32) x_66 = (zeroExtend(x_65));
        Bit#(32) x_67 = ((x_4)[(Bit#(5))'(5'h1f)]);
        Bit#(8) x_68 = ((x_67)[7:0]);
        Bit#(32) x_69 = ((x_67) + ((Bit#(32))'(32'h1)));
        Bit#(32) x_70 = ((x_67) - ((Bit#(32))'(32'h1)));
        Bit#(8) x_71 = ((x_70)[7:0]);
        Bit#(32) x_72 = ((x_5)[x_71]);
        Bit#(32) x_73 = ((x_54) + (x_55));
        Bit#(32) x_74 = ((x_54) - (x_55));
        Bit#(32) x_75 = ((x_56) ^ (x_57));
        Bool x_76 = (! ((x_56) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_77 = (x_57);
        Bit#(32) x_78 = ((Bit#(32))'(32'h55555555));
        Bit#(32) x_79 = ((x_77) & (x_78));
        Bit#(32) x_80 = (((x_77) >> ((Bit#(5))'(5'h1))) & (x_78));
        Bit#(32) x_81 = ((x_79) + (x_80));
        Bit#(32) x_82 = ((Bit#(32))'(32'h33333333));
        Bit#(32) x_83 = ((x_81) & (x_82));
        Bit#(32) x_84 = (((x_81) >> ((Bit#(5))'(5'h2))) & (x_82));
        Bit#(32) x_85 = ((x_83) + (x_84));
        Bit#(32) x_86 = ((Bit#(32))'(32'hf0f0f0f));
        Bit#(32) x_87 = ((x_85) & (x_86));
        Bit#(32) x_88 = (((x_85) >> ((Bit#(5))'(5'h4))) & (x_86));
        Bit#(32) x_89 = ((x_87) + (x_88));
        Bit#(32) x_90 = ((Bit#(32))'(32'hff00ff));
        Bit#(32) x_91 = ((x_89) & (x_90));
        Bit#(32) x_92 = (((x_89) >> ((Bit#(5))'(5'h8))) & (x_90));
        Bit#(32) x_93 = ((x_91) + (x_92));
        Bit#(32) x_94 = ((Bit#(32))'(32'hffff));
        Bit#(32) x_95 = (((x_93) + ((x_93) >> ((Bit#(5))'(5'h10)))) &
        (x_94));
        Bool x_96 = (((Bit#(8))'(8'h3)) < (x_43));
        Bool x_97 = (((Bit#(8))'(8'h1)) < (x_42));
        Bool x_98 = ((x_97) && ((x_37) == ((Bit#(32))'(32'h0))));
        Bool x_99 = ((x_96) || (x_98));
        Bool x_100 = (((x_41) == ((Bit#(8))'(8'h3))) || ((x_41) ==
        ((Bit#(8))'(8'h4))));
        Bit#(16) x_101 = ({(x_42),(x_43)});
        Bit#(32) x_102 = (zeroExtend(x_101));
        Bool x_103 = ((x_12) && (! (x_15)));
        Bool x_104 = ((x_12) && (x_15));
        Bool x_105 = ((x_100) && (! (x_12)));
        Bit#(4) x_106 = ((x_42)[3:0]);
        Bit#(32) x_107 = ((x_18)[x_106]);
        Bit#(32) x_108 = ((x_107) + (x_45));
        Bit#(32) x_109 = (((x_38) || (x_103) ? (x_2) : (((x_41) ==
        ((Bit#(8))'(8'hff)) ? (x_2) : (((x_41) == ((Bit#(8))'(8'h15)) ?
        (x_66) : (((x_41) == ((Bit#(8))'(8'h17)) ? (x_66) : (((x_41) ==
        ((Bit#(8))'(8'h18)) ? (x_72) : ((((x_41) == ((Bit#(8))'(8'h16))) &&
        (x_76) ? (x_64) : (x_47)))))))))))));
        Vector#(32, Bit#(32)) x_110 = (update (update (x_4, x_48, x_57),
        x_49, x_56));
        Vector#(32, Bit#(32)) x_111 = ((x_38 ? (x_4) : (((x_41) ==
        ((Bit#(8))'(8'h8)) ? (update (x_4, x_48, x_58)) : (((x_41) ==
        ((Bit#(8))'(8'h13)) ? (update (x_4, x_48, x_73)) : (((x_41) ==
        ((Bit#(8))'(8'h14)) ? (update (x_4, x_48, x_74)) : (((x_41) ==
        ((Bit#(8))'(8'h7)) ? (update (x_4, x_48, x_57)) : (((x_41) ==
        ((Bit#(8))'(8'h11)) ? (update (x_4, x_48, x_61)) : (((x_41) ==
        ((Bit#(8))'(8'ha)) ? (update (x_4, x_48, x_61)) : (((x_41) ==
        ((Bit#(8))'(8'hb)) ? (update (x_4, x_48, x_75)) : (((x_41) ==
        ((Bit#(8))'(8'hc)) ? (x_110) : (((x_41) == ((Bit#(8))'(8'hd)) ?
        (update (x_4, x_48, x_95)) : (((x_41) == ((Bit#(8))'(8'h17)) ?
        (update (x_4, (Bit#(5))'(5'h1f), x_69)) : (((x_41) ==
        ((Bit#(8))'(8'h18)) ? (update (x_4, (Bit#(5))'(5'h1f), x_70)) :
        (((x_41) == ((Bit#(8))'(8'h6)) ? (update (x_4, x_48, x_63)) :
        (x_4)))))))))))))))))))))))))));
        Vector#(256, Bit#(32)) x_112 = ((x_38 ? (x_5) : (((x_41) ==
        ((Bit#(8))'(8'h12)) ? (update (x_5, x_60, x_57)) : (((x_41) ==
        ((Bit#(8))'(8'h17)) ? (update (x_5, x_68, x_47)) : (x_5)))))));
        Bool x_113 = ((x_38) || ((x_41) == ((Bit#(8))'(8'hff))));
        Bool x_114 = ((x_104) && (x_16));
        Bool x_115 = ((((x_41) == ((Bit#(8))'(8'h9))) && (x_99)) || (x_114));
        
        Bit#(32) x_116 = ((x_38 ? ((Bit#(32))'(32'hb1a4c81)) : ((x_114 ?
        ((Bit#(32))'(32'hc43471a1)) : ((((x_41) == ((Bit#(8))'(8'h9))) &&
        (x_99) ? ((Bit#(32))'(32'hbadc45c)) : (x_10)))))));
        Bit#(32) x_117 = ((x_38 ? (x_3) : ((x_103 ? (x_3) : (((x_41) ==
        ((Bit#(8))'(8'h10)) ? ((x_3) + ((Bit#(32))'(32'hf4240))) : ((((x_41)
        == ((Bit#(8))'(8'h9))) && (x_97) ? ((x_46) + ((Bit#(32))'(32'h100)))
        : (x_46)))))))));
        Bit#(6) x_118 = ((x_20)[5:0]);
        Bit#(32) x_119 = (zeroExtend(x_42));
        Vector#(64, Bit#(32)) x_120 = (update (x_19, x_118, x_119));
        Bit#(32) x_121 = ((x_20) + ((Bit#(32))'(32'h1)));
        Bit#(6) x_122 = ((x_42)[5:0]);
        Bit#(32) x_123 = ((x_19)[x_122]);
        Bit#(32) x_124 = ((x_123) >> ((Bit#(5))'(5'h1)));
        Bit#(32) x_125 = ((x_123) - (x_124));
        Bit#(6) x_126 = ((x_20)[5:0]);
        Bit#(6) x_127 = (((x_20) + ((Bit#(32))'(32'h1)))[5:0]);
        
        Vector#(64, Bit#(32)) x_128 = (update (update (update (x_19, x_122,
        (Bit#(32))'(32'h0)), x_126, x_124), x_127, x_125));
        Bit#(32) x_129 = ((x_20) + ((Bit#(32))'(32'h2)));
        Bit#(6) x_130 = ((x_42)[5:0]);
        Bit#(6) x_131 = ((x_43)[5:0]);
        Bit#(32) x_132 = ((x_19)[x_130]);
        Bit#(32) x_133 = ((x_19)[x_131]);
        Bit#(32) x_134 = ((x_132) + (x_133));
        Bit#(6) x_135 = ((x_20)[5:0]);
        Vector#(64, Bit#(32)) x_136 = (update (update (update (x_19, x_130,
        (Bit#(32))'(32'h0)), x_131, (Bit#(32))'(32'h0)), x_135, x_134));
        
        Bit#(32) x_137 = ((x_20) + ((Bit#(32))'(32'h1)));
        
        Vector#(64, Bit#(32)) x_138 = ((x_38 ? (x_19) : (((x_41) ==
        ((Bit#(8))'(8'h0)) ? (x_120) : (((x_41) == ((Bit#(8))'(8'h1)) ?
        (x_128) : (((x_41) == ((Bit#(8))'(8'h2)) ? (x_136) : (x_19)))))))));
        
        Bit#(32) x_139 = ((x_38 ? (x_20) : (((x_41) == ((Bit#(8))'(8'h0)) ?
        (x_121) : (((x_41) == ((Bit#(8))'(8'h1)) ? (x_129) : (((x_41) ==
        ((Bit#(8))'(8'h2)) ? (x_137) : (x_20)))))))));
        Bool x_140 = ((((x_41) == ((Bit#(8))'(8'h0))) || ((x_41) ==
        ((Bit#(8))'(8'h1)))) || ((x_41) == ((Bit#(8))'(8'h2))));
        Bit#(32) x_141 = (((x_140) && (! (x_38)) ? ((x_7) +
        ((Bit#(32))'(32'h1))) : (x_7)));
        Bit#(32) x_142 = ((((x_41) == ((Bit#(8))'(8'h5))) && (! (x_38)) ?
        ((x_8) + ((Bit#(32))'(32'h1))) : (x_8)));
        Bit#(32) x_143 = (zeroExtend(x_43));
        Bool x_144 = (((x_41) == ((Bit#(8))'(8'h6))) || ((x_41) ==
        ((Bit#(8))'(8'he))));
        Bit#(32) x_145 = (((x_144) && (! (x_38)) ? ((x_9) + (x_143)) :
        (x_9)));
        Vector#(16, Bit#(32)) x_146 = ((((x_41) == ((Bit#(8))'(8'hf))) && (!
        (x_38)) ? (update (x_18, x_106, x_108)) : (x_18)));
        Bit#(32) x_147 = ((x_38 ? (x_11) : ((x_104 ? ((x_11) + (x_17)) :
        (((x_41) == ((Bit#(8))'(8'h10)) ? ((x_11) + ((Bit#(32))'(32'h1))) :
        (x_11)))))));
        Bool x_148 = ((x_38 ? (x_12) : ((x_104 ? ((Bool)'(False)) : ((x_105 ?
        ((Bool)'(True)) : (x_12)))))));
        Bit#(8) x_149 = ((x_105 ? (x_41) : (x_13)));
        Bit#(32) x_150 = ((x_105 ? (x_102) : (x_14)));
        Bool x_151 = ((x_38 ? (x_15) : ((x_104 ? ((Bool)'(False)) :
        (x_15)))));
        pc <= x_109;
        mu <= x_117;
        regs <= x_111;
        mem <= x_112;
        halted <= x_113;
        err <= x_115;
        error_code <= x_116;
        logic_acc <= x_147;
        logic_req_valid <= x_148;
        logic_req_opcode <= x_149;
        logic_req_payload <= x_150;
        logic_resp_valid <= x_151;
        partition_ops <= x_141;
        mdl_ops <= x_142;
        info_gain <= x_145;
        mu_tensor <= x_146;
        pt_sizes <= x_138;
        pt_next_id <= x_139;
        
    endrule
    
    
    method Action loadInstr (Struct1 x_0);
        let x_1 = (imem);
        Bit#(8) x_2 = ((x_0).addr);
        Bit#(32) x_3 = ((x_0).data);
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
        return x_1;
    endmethod
    
    method ActionValue#(Bit#(32)) getPtSize (Bit#(6) x_0);
        let x_1 = (pt_sizes);
        return (x_1)[x_0];
    endmethod
    
endmodule



