import Vector::*;

typedef struct { Bit#(8) addr; Bit#(32) data;  } Struct1 deriving(Eq, Bits);

interface Module1; method Action loadInstr (Struct1 x_0);
                   
endinterface

module mkModule1 (Module1);
    Reg#(Bit#(32)) pc <- mkReg(unpack(0));
    Reg#(Bit#(32)) mu <- mkReg(unpack(0));Reg#(Bool) err <- mkReg(False);
    Reg#(Bool) halted <- mkReg(False);
    Reg#(Vector#(32, Bit#(32))) regs <- mkReg(unpack(0));
    Reg#(Vector#(256, Bit#(32))) mem <- mkReg(unpack(0));
    Reg#(Vector#(256, Bit#(32))) imem <- mkReg(unpack(0));
    
    rule step;
        let x_0 = (halted);
        when (! (x_0), noAction);
        let x_1 = (pc);
        let x_2 = (mu);
        let x_3 = (err);
        let x_4 = (regs);
        let x_5 = (mem);
        let x_6 = (imem);
        Bit#(8) x_7 = ((x_1)[7:0]);
        Bit#(32) x_8 = ((x_6)[x_7]);
        Bit#(8) x_9 = ((x_8)[31:24]);
        Bit#(8) x_10 = ((x_8)[23:16]);
        Bit#(8) x_11 = ((x_8)[15:8]);
        Bit#(8) x_12 = ((x_8)[7:0]);
        Bit#(32) x_13 = (zeroExtend(x_12));
        Bit#(32) x_14 = ((x_2) + (x_13));
        Bit#(32) x_15 = ((x_1) + ((Bit#(32))'(32'h1)));
        Bit#(5) x_16 = ((x_10)[4:0]);
        Bit#(5) x_17 = ((x_11)[4:0]);
        Bit#(4) x_18 = ((x_11)[7:4]);
        Bit#(4) x_19 = ((x_11)[3:0]);
        Bit#(5) x_20 = (zeroExtend(x_18));
        Bit#(5) x_21 = (zeroExtend(x_19));
        Bit#(32) x_22 = ((x_4)[x_20]);
        Bit#(32) x_23 = ((x_4)[x_21]);
        Bit#(32) x_24 = ((x_4)[x_16]);
        Bit#(32) x_25 = ((x_4)[x_17]);
        Bit#(32) x_26 = (zeroExtend(x_11));
        Bit#(8) x_27 = ((x_11)[7:0]);
        Bit#(8) x_28 = ((x_10)[7:0]);
        Bit#(32) x_29 = ((x_5)[x_27]);
        Bit#(32) x_30 = (zeroExtend(x_11));
        Bit#(16) x_31 = ({(x_10),(x_11)});
        Bit#(32) x_32 = (zeroExtend(x_31));
        Bit#(32) x_33 = ((x_4)[(Bit#(5))'(5'h1f)]);
        Bit#(8) x_34 = ((x_33)[7:0]);
        Bit#(32) x_35 = ((x_33) + ((Bit#(32))'(32'h1)));
        Bit#(32) x_36 = ((x_33) - ((Bit#(32))'(32'h1)));
        Bit#(8) x_37 = ((x_36)[7:0]);
        Bit#(32) x_38 = ((x_5)[x_37]);
        Bit#(32) x_39 = ((x_22) + (x_23));
        Bit#(32) x_40 = ((x_22) - (x_23));
        Bit#(32) x_41 = ((x_24) ^ (x_25));
        Bool x_42 = (! ((x_24) == ((Bit#(32))'(32'h0))));
        Bit#(32) x_43 = (x_25);
        Bit#(32) x_44 = ((Bit#(32))'(32'h55555555));
        Bit#(32) x_45 = ((x_43) & (x_44));
        Bit#(32) x_46 = (((x_43) >> ((Bit#(5))'(5'h1))) & (x_44));
        Bit#(32) x_47 = ((x_45) + (x_46));
        Bit#(32) x_48 = ((Bit#(32))'(32'h33333333));
        Bit#(32) x_49 = ((x_47) & (x_48));
        Bit#(32) x_50 = (((x_47) >> ((Bit#(5))'(5'h2))) & (x_48));
        Bit#(32) x_51 = ((x_49) + (x_50));
        Bit#(32) x_52 = ((Bit#(32))'(32'hf0f0f0f));
        Bit#(32) x_53 = ((x_51) & (x_52));
        Bit#(32) x_54 = (((x_51) >> ((Bit#(5))'(5'h4))) & (x_52));
        Bit#(32) x_55 = ((x_53) + (x_54));
        Bit#(32) x_56 = ((Bit#(32))'(32'hff00ff));
        Bit#(32) x_57 = ((x_55) & (x_56));
        Bit#(32) x_58 = (((x_55) >> ((Bit#(5))'(5'h8))) & (x_56));
        Bit#(32) x_59 = ((x_57) + (x_58));
        Bit#(32) x_60 = ((Bit#(32))'(32'hffff));
        Bit#(32) x_61 = (((x_59) + ((x_59) >> ((Bit#(5))'(5'h10)))) &
        (x_60));
        Bit#(8) x_62 = (x_10);
        Bit#(8) x_63 = (x_11);
        Bool x_64 = ((((Bit#(8))'(8'h1)) < (x_62)) || (((Bit#(8))'(8'h1)) <
        (x_63)));
        Bit#(32) x_65 = (((x_9) == ((Bit#(8))'(8'hff)) ? (x_1) : (((x_9) ==
        ((Bit#(8))'(8'h15)) ? (x_32) : (((x_9) == ((Bit#(8))'(8'h17)) ?
        (x_32) : (((x_9) == ((Bit#(8))'(8'h18)) ? (x_38) : ((((x_9) ==
        ((Bit#(8))'(8'h16))) && (x_42) ? (x_30) : (x_15)))))))))));
        
        Vector#(32, Bit#(32)) x_66 = (update (update (x_4, x_16, x_25), x_17,
        x_24));
        Vector#(32, Bit#(32)) x_67 = (((x_9) == ((Bit#(8))'(8'h8)) ? (update
        (x_4, x_16, x_26)) : (((x_9) == ((Bit#(8))'(8'h13)) ? (update (x_4,
        x_16, x_39)) : (((x_9) == ((Bit#(8))'(8'h14)) ? (update (x_4, x_16,
        x_40)) : (((x_9) == ((Bit#(8))'(8'h7)) ? (update (x_4, x_16, x_25)) :
        (((x_9) == ((Bit#(8))'(8'h11)) ? (update (x_4, x_16, x_29)) : (((x_9)
        == ((Bit#(8))'(8'ha)) ? (update (x_4, x_16, x_29)) : (((x_9) ==
        ((Bit#(8))'(8'hb)) ? (update (x_4, x_16, x_41)) : (((x_9) ==
        ((Bit#(8))'(8'hc)) ? (x_66) : (((x_9) == ((Bit#(8))'(8'hd)) ? (update
        (x_4, x_16, x_61)) : (((x_9) == ((Bit#(8))'(8'h17)) ? (update (x_4,
        (Bit#(5))'(5'h1f), x_35)) : (((x_9) == ((Bit#(8))'(8'h18)) ? (update
        (x_4, (Bit#(5))'(5'h1f), x_36)) : (x_4)))))))))))))))))))))));
        
        Vector#(256, Bit#(32)) x_68 = (((x_9) == ((Bit#(8))'(8'h12)) ?
        (update (x_5, x_28, x_25)) : (((x_9) == ((Bit#(8))'(8'h17)) ? (update
        (x_5, x_34, x_15)) : (x_5)))));
        Bool x_69 = ((x_9) == ((Bit#(8))'(8'hff)));
        Bool x_70 = ((x_3) || (x_64));
        pc <= x_65;
        mu <= x_14;
        regs <= x_67;
        mem <= x_68;
        halted <= x_69;
        err <= x_70;
        
    endrule
    
    
    method Action loadInstr (Struct1 x_0);
        let x_1 = (imem);
        Bit#(8) x_2 = ((x_0).addr);
        Bit#(32) x_3 = ((x_0).data);
        imem <= update (x_1, x_2, x_3);
        
    endmethod
    
endmodule

