(** ThieleLoader: the serial program loader and status reporter, in Kami.

    The board feeds the serial receive line to [rxSample] once per clock
    cycle, drives the serial transmit pin from [getTx], and drives its
    lights from [getLeds]. The loader runs
    three machines.

    - Receiver. The pin is sampled through two registers. The line idles high. A low level starts a frame; the start
      bit is checked at its middle, then eight data bits, least significant
      first, are sampled at the middle of each bit time, then the stop bit.
      A frame whose stop bit is low is dropped.
    - Program. The first two bytes are the instruction count N, low byte
      first. Each instruction follows as sixteen bytes, least significant
      first; the completed word is written to instruction address i through
      the CPU's [loadInstr]. After the Nth word, or at once when N is zero,
      the loader calls the CPU's [start]. Instruction memory holds 128 words,
      so a program has at most 128 instructions.
    - Report. Once the start has reached the CPU and the CPU is halted or
      in error, the loader sends fifteen bytes and stops: 0xDE, a status byte
      (bit 0 halted, bit 1 error, bit 2 certified), the program counter, the
      mu ledger and the error code, each four bytes least significant first,
      and 0xAD.

    One bit lasts [ClksPerBit] clock cycles: 174 cycles of the 20 MHz CPU
    clock is within 0.3 percent of 115200 baud. *)

Require Import Kami.Kami.
Require Import Kami.Synthesize.
Require Import Kami.Ext.BSyntax.
From KamiHW Require Import ThieleTypes ThieleCPUCore.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section ThieleLoader.

  Definition ClksPerBit : nat := 174.
  (** Counter values at the middle and at the end of a bit time. *)
  Definition rx_half_last : word 8 := natToWord 8 (Nat.pred (Nat.div ClksPerBit 2)).
  Definition bit_last : word 8 := natToWord 8 (Nat.pred ClksPerBit).

  Definition loadInstrSig := MethodSig "loadInstr"(Struct LoadInstrPort) : Void.
  Definition startSig := MethodSig "start"() : Void.
  Definition getHaltedSig := MethodSig "getHalted"() : Bool.
  Definition getErrSig := MethodSig "getErr"() : Bool.
  Definition getCertifiedSig := MethodSig "getCertified"() : Bool.
  Definition getPCSig := MethodSig "getPC"() : Bit WordSz.
  Definition getMuSig := MethodSig "getMu"() : Bit WordSz.
  Definition getErrorCodeSig := MethodSig "getErrorCode"() : Bit WordSz.

  Definition thieleLoader :=
    MODULE {
      (* The pin passes through two registers before use: it changes with
         no relation to the clock. The line idles high. *)
      Register "rx_sync1" : Bool <- true
      with Register "rx_sync2" : Bool <- true

      (* Receiver: 0 idle, 1 start bit, 2 data bits, 3 stop bit. *)
      with Register "rx_state" : Bit 2 <- Default
      with Register "rx_clk" : Bit 8 <- Default
      with Register "rx_bit" : Bit 3 <- Default
      with Register "rx_shift" : Bit 8 <- Default

      (* Program: 0 count low, 1 count high, 2 instruction bytes, 3 complete. *)
      with Register "ld_phase" : Bit 2 <- Default
      with Register "ld_count_lo" : Bit 8 <- Default
      with Register "ld_count_hi" : Bit 8 <- Default
      with Register "ld_index" : Bit 8 <- Default
      with Register "ld_byte" : Bit 4 <- Default
      with Register "ld_accum" : Bit InstrSz <- Default

      (* Hand-off to the CPU: a request differs from its acknowledgement
         while a call is pending. *)
      with Register "load_req" : Bool <- false
      with Register "load_ack" : Bool <- false
      with Register "load_addr" : Bit MemAddrSz <- Default
      with Register "load_data" : Bit InstrSz <- Default
      with Register "start_req" : Bool <- false
      with Register "start_ack" : Bool <- false
      with Register "started" : Bool <- false

      (* Report. *)
      with Register "tx_active" : Bool <- false
      with Register "tx_done" : Bool <- false
      with Register "tx_bytes" : Bit 120 <- Default
      with Register "tx_shift" : Bit 8 <- Default
      with Register "tx_index" : Bit 4 <- Default
      with Register "tx_bit" : Bit 4 <- Default
      with Register "tx_clk" : Bit 8 <- Default

      (* The CPU's status as of the previous cycle, for the board's lights. *)
      with Register "seen_halted" : Bool <- false
      with Register "seen_err" : Bool <- false
      with Register "seen_bianchi" : Bool <- false

      with Method "rxSample" (pin : Bool) : Void :=
        Read sync1 : Bool <- "rx_sync1";
        Read b : Bool <- "rx_sync2";
        Write "rx_sync1" <- #pin;
        Write "rx_sync2" <- #sync1;
        Read st : Bit 2 <- "rx_state";
        Read clk : Bit 8 <- "rx_clk";
        Read bitn : Bit 3 <- "rx_bit";
        Read shift : Bit 8 <- "rx_shift";
        LET half_bit <- #clk == $$rx_half_last;
        LET full_bit <- #clk == $$bit_last;
        LET in_bit : Bit 1 <- IF #b then $$(WO~1) else $$(WO~0);
        LET shifted <- BinBit (Concat 1 7) #in_bit (UniBit (ConstExtract 1 7 0) #shift);
        (* A byte is complete at the middle of a high stop bit. *)
        LET byte_done <- (#st == $$(natToWord 2 3)) && #full_bit && #b;
        Write "rx_state" <-
          IF #st == $$(natToWord 2 0) then
            (IF #b then $$(natToWord 2 0) else $$(natToWord 2 1))
          else IF #st == $$(natToWord 2 1) then
            (IF #half_bit then (IF #b then $$(natToWord 2 0) else $$(natToWord 2 2))
             else $$(natToWord 2 1))
          else IF #st == $$(natToWord 2 2) then
            (IF #full_bit && (#bitn == $$(natToWord 3 7)) then $$(natToWord 2 3)
             else $$(natToWord 2 2))
          else
            (IF #full_bit then $$(natToWord 2 0) else $$(natToWord 2 3));
        Write "rx_clk" <-
          IF #st == $$(natToWord 2 0) then $$(natToWord 8 0)
          else IF (#st == $$(natToWord 2 1)) && #half_bit then $$(natToWord 8 0)
          else IF #full_bit then $$(natToWord 8 0)
          else #clk + $$(natToWord 8 1);
        Write "rx_bit" <-
          IF #st == $$(natToWord 2 2) then
            (IF #full_bit then #bitn + $$(natToWord 3 1) else #bitn)
          else $$(natToWord 3 0);
        Write "rx_shift" <-
          IF (#st == $$(natToWord 2 2)) && #full_bit then #shifted else #shift;

        Read phase : Bit 2 <- "ld_phase";
        Read count_lo : Bit 8 <- "ld_count_lo";
        Read count_hi : Bit 8 <- "ld_count_hi";
        Read index : Bit 8 <- "ld_index";
        Read bytei : Bit 4 <- "ld_byte";
        Read accum : Bit InstrSz <- "ld_accum";
        LET count : Bit 16 <- BinBit (Concat 8 8) #count_hi #count_lo;
        LET word <- BinBit (Concat 8 120) #shift (UniBit (ConstExtract 8 120 0) #accum);
        LET word_done <- #byte_done && (#phase == $$(natToWord 2 2))
                         && (#bytei == $$(natToWord 4 15));
        LET next_index <- #index + $$(natToWord 8 1);
        LET last_word <- #word_done
                         && (UniBit (ZeroExtendTrunc 8 16) #next_index == #count);
        LET empty_program <- #byte_done && (#phase == $$(natToWord 2 1))
                             && (BinBit (Concat 8 8) #shift #count_lo == $$(natToWord 16 0));
        LET take <- #byte_done;
        Write "ld_phase" <-
          IF !#take then #phase
          else IF #phase == $$(natToWord 2 0) then $$(natToWord 2 1)
          else IF #phase == $$(natToWord 2 1) then
            (IF #empty_program then $$(natToWord 2 3) else $$(natToWord 2 2))
          else IF #last_word then $$(natToWord 2 3)
          else #phase;
        Write "ld_count_lo" <-
          IF #take && (#phase == $$(natToWord 2 0)) then #shift else #count_lo;
        Write "ld_count_hi" <-
          IF #take && (#phase == $$(natToWord 2 1)) then #shift else #count_hi;
        Write "ld_index" <- IF #word_done then #next_index else #index;
        Write "ld_byte" <-
          IF #take && (#phase == $$(natToWord 2 2)) then
            (IF #word_done then $$(natToWord 4 0) else #bytei + $$(natToWord 4 1))
          else #bytei;
        Write "ld_accum" <-
          IF #take && (#phase == $$(natToWord 2 2)) then
            (IF #word_done then $$(natToWord InstrSz 0) else #word)
          else #accum;

        (* A completed word, and the start once the last word is out, are
           handed to the rules below by flipping a request bit; each rule
           flips its acknowledgement when it has made the call. *)
        Read load_req : Bool <- "load_req";
        Read start_req : Bool <- "start_req";
        Read load_addr : Bit MemAddrSz <- "load_addr";
        Read load_data : Bit InstrSz <- "load_data";
        Write "load_req" <- IF #word_done then !#load_req else #load_req;
        Write "load_addr" <-
          IF #word_done then UniBit (ConstExtract 0 MemAddrSz 1) #index else #load_addr;
        Write "load_data" <- IF #word_done then #word else #load_data;
        Write "start_req" <- IF #last_word || #empty_program then !#start_req else #start_req;
        Retv

      with Rule "load" :=
        Read load_req : Bool <- "load_req";
        Read load_ack : Bool <- "load_ack";
        Assert !(#load_req == #load_ack);
        Read addr : Bit MemAddrSz <- "load_addr";
        Read data : Bit InstrSz <- "load_data";
        Call loadInstrSig(STRUCT { "addr" ::= #addr ; "data" ::= #data });
        Write "load_ack" <- #load_req;
        Retv

      (* The start goes out only once every word has been written. *)
      with Rule "go" :=
        Read start_req : Bool <- "start_req";
        Read start_ack : Bool <- "start_ack";
        Read load_req : Bool <- "load_req";
        Read load_ack : Bool <- "load_ack";
        Assert !(#start_req == #start_ack) && (#load_req == #load_ack);
        Call startSig();
        Write "start_ack" <- #start_req;
        Write "started" <- $$true;
        Retv

      with Rule "report" :=
        Read started : Bool <- "started";
        Read active : Bool <- "tx_active";
        Read done : Bool <- "tx_done";
        Read bytes : Bit 120 <- "tx_bytes";
        Read shift : Bit 8 <- "tx_shift";
        Read index : Bit 4 <- "tx_index";
        Read bitn : Bit 4 <- "tx_bit";
        Read clk : Bit 8 <- "tx_clk";
        Call halted <- getHaltedSig();
        Call err <- getErrSig();
        Call certified <- getCertifiedSig();
        Call pc <- getPCSig();
        Call mu <- getMuSig();
        Call ec <- getErrorCodeSig();
        LET begin <- !#active && !#done && #started && (#halted || #err);
        LET status : Bit 8 <-
          BinBit (Concat 5 3) $$(natToWord 5 0)
            (BinBit (Concat 1 2) (IF #certified then $$(WO~1) else $$(WO~0))
              (BinBit (Concat 1 1) (IF #err then $$(WO~1) else $$(WO~0))
                                   (IF #halted then $$(WO~1) else $$(WO~0))));
        (* Fifteen bytes, the first in bits 7 to 0. *)
        LET frame : Bit 120 <-
          BinBit (Concat 8 112) $$(natToWord 8 173)
            (BinBit (Concat 32 80) #ec
              (BinBit (Concat 32 48) #mu
                (BinBit (Concat 32 16) #pc
                  (BinBit (Concat 8 8) #status $$(natToWord 8 222)))));
        LET full_bit <- #clk == $$bit_last;
        LET last_bit <- #bitn == $$(natToWord 4 9);
        LET last_byte <- #index == $$(natToWord 4 14);
        LET byte_end <- #active && #full_bit && #last_bit;
        Write "tx_active" <- IF #begin then $$true
                             else IF #byte_end && #last_byte then $$false
                             else #active;
        Write "tx_done" <- IF #byte_end && #last_byte then $$true else #done;
        Write "seen_halted" <- #halted;
        Write "seen_err" <- #err;
        Write "seen_bianchi" <- #ec == $$(natToWord WordSz 186272897);
        Write "tx_bytes" <-
          IF #begin then #frame
          else IF #byte_end then
            BinBit (Concat 8 112) $$(natToWord 8 0) (UniBit (ConstExtract 8 112 0) #bytes)
          else #bytes;
        Write "tx_index" <- IF #begin then $$(natToWord 4 0)
                            else IF #byte_end then #index + $$(natToWord 4 1)
                            else #index;
        Write "tx_bit" <- IF #begin then $$(natToWord 4 0)
                          else IF #active && #full_bit then
                            (IF #last_bit then $$(natToWord 4 0) else #bitn + $$(natToWord 4 1))
                          else #bitn;
        Write "tx_clk" <- IF #begin then $$(natToWord 8 0)
                          else IF #active then
                            (IF #full_bit then $$(natToWord 8 0) else #clk + $$(natToWord 8 1))
                          else #clk;
        (* The current byte moves into [tx_shift] at the end of its start
           bit; each data bit shifts it one place right. *)
        Write "tx_shift" <-
          IF #active && #full_bit && (#bitn == $$(natToWord 4 0)) then
            UniBit (ConstExtract 0 8 112) #bytes
          else IF #active && #full_bit then
            BinBit (Concat 1 7) $$(WO~0) (UniBit (ConstExtract 1 7 0) #shift)
          else #shift;
        Retv

      (* The line is high when idle and during the stop bit, low during the
         start bit, and carries [tx_shift]'s low bit during data bits. *)
      with Method "getTx" () : Bool :=
        Read active : Bool <- "tx_active";
        Read bitn : Bit 4 <- "tx_bit";
        Read shift : Bit 8 <- "tx_shift";
        Ret (IF !#active then $$true
             else IF #bitn == $$(natToWord 4 0) then $$false
             else IF #bitn == $$(natToWord 4 9) then $$true
             else (UniBit (ConstExtract 0 1 7) #shift == $$(WO~1)))

      (* Bit 0 halted, bit 1 error, bit 2 the conservation alarm (error code
         0x0B1A4C81), bit 3 loading. *)
      with Method "getLeds" () : Bit 4 :=
        Read phase : Bit 2 <- "ld_phase";
        Read h : Bool <- "seen_halted";
        Read e : Bool <- "seen_err";
        Read a : Bool <- "seen_bianchi";
        Ret (BinBit (Concat 1 3) (IF #phase == $$(natToWord 2 3) then $$(WO~0) else $$(WO~1))
              (BinBit (Concat 1 2) (IF #a then $$(WO~1) else $$(WO~0))
                (BinBit (Concat 1 1) (IF #e then $$(WO~1) else $$(WO~0))
                                     (IF #h then $$(WO~1) else $$(WO~0)))))
    }.

  Definition thieleLoaderS := getModuleS thieleLoader.
  Definition thieleLoaderB := ModulesSToBModules thieleLoaderS.

End ThieleLoader.
