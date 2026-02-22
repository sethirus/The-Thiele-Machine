typedef struct { Bit#(8) addr; Bit#(32) data;  } Struct1 deriving(Eq, Bits);

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
    method ActionValue#(Bit#(32)) getMuTensor0 ();
    method ActionValue#(Bit#(32)) getMuTensor1 ();
    method ActionValue#(Bit#(32)) getMuTensor2 ();
    method ActionValue#(Bit#(32)) getMuTensor3 ();
    method ActionValue#(Bool) getBianchiAlarm ();
    
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
    Reg#(Vector#(16, Bit#(32))) mu_tensor <- mkReg(unpack(0));
    
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
        let x_11 = (mu_tensor);
        Bit#(32) x_12 = ((x_11)[(Bit#(4))'(4'h0)]);
        Bit#(32) x_13 = ((x_11)[(Bit#(4))'(4'h1)]);
        Bit#(32) x_14 = ((x_11)[(Bit#(4))'(4'h2)]);
        Bit#(32) x_15 = ((x_11)[(Bit#(4))'(4'h3)]);
        Bit#(32) x_16 = ((x_11)[(Bit#(4))'(4'h4)]);
        Bit#(32) x_17 = ((x_11)[(Bit#(4))'(4'h5)]);
        Bit#(32) x_18 = ((x_11)[(Bit#(4))'(4'h6)]);
        Bit#(32) x_19 = ((x_11)[(Bit#(4))'(4'h7)]);
        Bit#(32) x_20 = ((x_11)[(Bit#(4))'(4'h8)]);
        Bit#(32) x_21 = ((x_11)[(Bit#(4))'(4'h9)]);
        Bit#(32) x_22 = ((x_11)[(Bit#(4))'(4'ha)]);
        Bit#(32) x_23 = ((x_11)[(Bit#(4))'(4'hb)]);
        Bit#(32) x_24 = ((x_11)[(Bit#(4))'(4'hc)]);
        Bit#(32) x_25 = ((x_11)[(Bit#(4))'(4'hd)]);
        Bit#(32) x_26 = ((x_11)[(Bit#(4))'(4'he)]);
        Bit#(32) x_27 = ((x_11)[(Bit#(4))'(4'hf)]);
        Bit#(32) x_28 = ((((((((((((((((x_12) + (x_13)) + (x_14)) + (x_15)) +
        (x_16)) + (x_17)) + (x_18)) + (x_19)) + (x_20)) + (x_21)) + (x_22)) +
        (x_23)) + (x_24)) + (x_25)) + (x_26)) + (x_27));
        Bool x_29 = ((x_3) < (x_28));
        Bit#(8) x_30 = ((x_2)[7:0]);
        Bit#(32) x_31 = ((x_6)[x_30]);
        Bit#(8) x_32 = ((x_31)[31:24]);
        Bit#(8) x_33 = ((x_31)[23:16]);
        Bit#(8) x_34 = ((x_31)[15:8]);
        Bit#(8) x_35 = ((x_31)[7:0]);
        Bit#(32) x_36 = (zeroExtend(x_35));
        Bit#(32) x_37 = ((x_3) + (x_36));
        Bit#(32) x_38 = ((x_2) + ((Bit#(32))'(32'h1)));
        Bit#(5) x_39 = ((x_33)[4:0]);
        Bit#(5) x_40 = ((x_34)[4:0]);
        Bit#(4) x_41 = ((x_34)[7:4]);
        Bit#(4) x_42 = ((x_34)[3:0]);
        Bit#(5) x_43 = (zeroExtend(x_41));
        Bit#(5) x_44 = (zeroExtend(x_42));
        Bit#(32) x_45 = ((x_4)[x_43]);
        Bit#(32) x_46 = ((x_4)[x_44]);
        Bit#(32) x_47 = ((x_4)[x_39]);
        Bit#(32) x_48 = ((x_4)[x_40]);
        Bit#(32) x_49 = (zeroExtend(x_34));
        Bit#(8) x_50 = ((x_34)[7:0]);
        Bit#(8) x_51 = ((x_33)[7:0]);
        Bit#(32) x_52 = ((x_5)[x_50]);
        Bit#(32) x_53 = (zeroExtend(x_34));
        Bit#(16) x_54 = ({(x_33),(x_34)});
        Bit#(32) x_55 = (zeroExtend(x_54));
        Bit#(32) x_56 = ((x_4)[(Bit#(5))'(5'h1f)]);
        Bit#(8) x_57 = ((x_56)[7:0]);
        Bit#(32) x_58 = ((x_56) + ((Bit#(32))'(32'h1)));
        Bit#(32) x_59 = ((x_56) - ((Bit#(32))'(32'h1)));
        Bit#(8) x_60 = ((x_59)[7:0]);
        Bit#(32) x_61 = ((x_5)[x_60]);
        Bit#(32) x_62 = ((x_45) + (x_46));
        Bit#(32) x_63 = ((x_45) - (x_46));
        Bit#(32) x_64 = ((x_47) ^ (x_48));
        Bool x_65 = (! ((x_47) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_66 = (x_48);
        Bit#(32) x_67 = ((Bit#(32))'(32'h55555555));
        Bit#(32) x_68 = ((x_66) & (x_67));
        Bit#(32) x_69 = (((x_66) >> ((Bit#(5))'(5'h1))) & (x_67));
        Bit#(32) x_70 = ((x_68) + (x_69));
        Bit#(32) x_71 = ((Bit#(32))'(32'h33333333));
        Bit#(32) x_72 = ((x_70) & (x_71));
        Bit#(32) x_73 = (((x_70) >> ((Bit#(5))'(5'h2))) & (x_71));
        Bit#(32) x_74 = ((x_72) + (x_73));
        Bit#(32) x_75 = ((Bit#(32))'(32'hf0f0f0f));
        Bit#(32) x_76 = ((x_74) & (x_75));
        Bit#(32) x_77 = (((x_74) >> ((Bit#(5))'(5'h4))) & (x_75));
        Bit#(32) x_78 = ((x_76) + (x_77));
        Bit#(32) x_79 = ((Bit#(32))'(32'hff00ff));
        Bit#(32) x_80 = ((x_78) & (x_79));
        Bit#(32) x_81 = (((x_78) >> ((Bit#(5))'(5'h8))) & (x_79));
        Bit#(32) x_82 = ((x_80) + (x_81));
        Bit#(32) x_83 = ((Bit#(32))'(32'hffff));
        Bit#(32) x_84 = (((x_82) + ((x_82) >> ((Bit#(5))'(5'h10)))) &
        (x_83));
        Bit#(8) x_85 = (x_33);
        Bit#(8) x_86 = (x_34);
        Bool x_87 = ((((Bit#(8))'(8'h1)) < (x_85)) || (((Bit#(8))'(8'h1)) <
        (x_86)));
        Bit#(4) x_88 = ((x_33)[3:0]);
        Bit#(32) x_89 = ((x_11)[x_88]);
        Bit#(32) x_90 = ((x_89) + (x_36));
        Bit#(32) x_91 = ((x_29 ? (x_2) : (((x_32) == ((Bit#(8))'(8'hff)) ?
        (x_2) : (((x_32) == ((Bit#(8))'(8'h15)) ? (x_55) : (((x_32) ==
        ((Bit#(8))'(8'h17)) ? (x_55) : (((x_32) == ((Bit#(8))'(8'h18)) ?
        (x_61) : ((((x_32) == ((Bit#(8))'(8'h16))) && (x_65) ? (x_53) :
        (x_38)))))))))))));
        Vector#(32, Bit#(32)) x_92 = (update (update (x_4, x_39, x_48), x_40,
        x_47));
        Vector#(32, Bit#(32)) x_93 = ((x_29 ? (x_4) : (((x_32) ==
        ((Bit#(8))'(8'h8)) ? (update (x_4, x_39, x_49)) : (((x_32) ==
        ((Bit#(8))'(8'h13)) ? (update (x_4, x_39, x_62)) : (((x_32) ==
        ((Bit#(8))'(8'h14)) ? (update (x_4, x_39, x_63)) : (((x_32) ==
        ((Bit#(8))'(8'h7)) ? (update (x_4, x_39, x_48)) : (((x_32) ==
        ((Bit#(8))'(8'h11)) ? (update (x_4, x_39, x_52)) : (((x_32) ==
        ((Bit#(8))'(8'ha)) ? (update (x_4, x_39, x_52)) : (((x_32) ==
        ((Bit#(8))'(8'hb)) ? (update (x_4, x_39, x_64)) : (((x_32) ==
        ((Bit#(8))'(8'hc)) ? (x_92) : (((x_32) == ((Bit#(8))'(8'hd)) ?
        (update (x_4, x_39, x_84)) : (((x_32) == ((Bit#(8))'(8'h17)) ?
        (update (x_4, (Bit#(5))'(5'h1f), x_58)) : (((x_32) ==
        ((Bit#(8))'(8'h18)) ? (update (x_4, (Bit#(5))'(5'h1f), x_59)) :
        (x_4)))))))))))))))))))))))));
        Vector#(256, Bit#(32)) x_94 = ((x_29 ? (x_5) : (((x_32) ==
        ((Bit#(8))'(8'h12)) ? (update (x_5, x_51, x_48)) : (((x_32) ==
        ((Bit#(8))'(8'h17)) ? (update (x_5, x_57, x_38)) : (x_5)))))));
        Bool x_95 = ((x_29) || ((x_32) == ((Bit#(8))'(8'hff))));
        Bool x_96 = (x_87);
        Bit#(32) x_97 = ((x_29 ? ((Bit#(32))'(32'hb1a4c81)) : ((x_87 ?
        ((Bit#(32))'(32'hbadc45c)) : (x_10)))));
        Bit#(32) x_98 = ((x_29 ? (x_3) : (x_37)));
        Bool x_99 = ((((x_32) == ((Bit#(8))'(8'h0))) || ((x_32) ==
        ((Bit#(8))'(8'h1)))) || ((x_32) == ((Bit#(8))'(8'h2))));
        Bit#(32) x_100 = (((x_99) && (! (x_29)) ? ((x_7) +
        ((Bit#(32))'(32'h1))) : (x_7)));
        Bit#(32) x_101 = ((((x_32) == ((Bit#(8))'(8'h5))) && (! (x_29)) ?
        ((x_8) + ((Bit#(32))'(32'h1))) : (x_8)));
        Bit#(32) x_102 = (zeroExtend(x_34));
        Bool x_103 = (((x_32) == ((Bit#(8))'(8'h6))) || ((x_32) ==
        ((Bit#(8))'(8'he))));
        Bit#(32) x_104 = (((x_103) && (! (x_29)) ? ((x_9) + (x_102)) :
        (x_9)));
        Vector#(16, Bit#(32)) x_105 = ((((x_32) == ((Bit#(8))'(8'hf))) && (!
        (x_29)) ? (update (x_11, x_88, x_90)) : (x_11)));
        pc <= x_91;
        mu <= x_98;
        regs <= x_93;
        mem <= x_94;
        halted <= x_95;
        err <= x_96;
        error_code <= x_97;
        partition_ops <= x_100;
        mdl_ops <= x_101;
        info_gain <= x_104;
        mu_tensor <= x_105;
        
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
    
endmodule

module mkThieleCPU (ThieleCPU);Module1 m1 <- mkModule1 ();
                               
endmodule
