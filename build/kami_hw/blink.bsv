
interface Module1; 
endinterface

module mkModule1 (Module1);
    Reg#(Bit#(32)) counter <- mkReg(unpack(0));
    
    rule increment;
        let x_0 = (counter);
        counter <= (x_0) + ((Bit#(32))'(32'h1));
        
    endrule
    
    // No methods in this module
endmodule

module mkBlink (Blink);Module1 m1 <- mkModule1 ();
                       
endmodule
