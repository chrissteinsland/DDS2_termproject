//////////////////////////////////////////////////
// Title:   assertions_hdlc
// Author:  
// Date:    
//////////////////////////////////////////////////

/* The assertions_hdlc module is a test module containing the concurrent
   assertions. It is used by binding the signals of assertions_hdlc to the
   corresponding signals in the test_hdlc testbench. This is already done in
   bind_hdlc.sv 

   For this exercise you will write concurrent assertions for the Rx module:
   - Verify that Rx_FlagDetect is asserted two cycles after a flag is received
   - Verify that Rx_AbortSignal is asserted after receiving an abort flag
*/

module assertions_hdlc (
  output int   ErrCntAssertions,
  input  logic Clk,
  input  logic Rst,
  input  logic Rx,
  input  logic Rx_FlagDetect,
  input  logic Rx_ValidFrame,
  input  logic Rx_AbortDetect,
  input  logic Rx_AbortSignal,
  input  logic Rx_Overflow,
  input  logic Rx_WrBuff,
  input  logic Rx_FrameError,
  input  logic Rx_FCSen,
  input  logic Rx_Drop,
  input  logic Rx_Ready,
  input  logic Rx_EoF 

);

  initial begin
    ErrCntAssertions  =  0;
  end

  /*******************************************
   *  Verify correct Rx_FlagDetect behavior  *
   *******************************************/

  sequence Rx_flag;
 	!Rx ##1 Rx[*6] ##1 !Rx;	
  endsequence

  // Check if flag sequence is detected
  property RX_FlagDetect;
    @(posedge Clk) Rx_flag |-> ##2 Rx_FlagDetect;
  endproperty

  RX_FlagDetect_Assert : assert property (RX_FlagDetect) 
   else begin 
    $error("Flag sequence did not generate FlagDetect at time %0t", $time); 
    ErrCntAssertions++; 
  end

  /********************************************
   *  Verify correct Rx_AbortSignal behavior  *
   ********************************************/

  //If abort is detected during valid frame. then abort signal should go high
  property RX_AbortSignal;
 	@(posedge Clk) Rx_AbortDetect && Rx_ValidFrame |=> Rx_AbortSignal;  
  endproperty

  RX_AbortSignal_Assert : assert property (RX_AbortSignal) 
   else begin 
    $error("AbortSignal did not go high after AbortDetect during validframe at time %0t", $time); 
    ErrCntAssertions++; 
  end

  /*********************************************************
   *  Verify correct Rx status/control after receivin frame*
   *********************************************************/

  // Correct bits set in the RX status/control register after receiving frame. All bits (Overflow, abort and so on) should be correct

  property RX_SC_correct;
 	@(posedge Clk) disable iff(!Rst) $rose(Rx_EoF) |->
		if(Rx_AbortSignal)
			(!Rx_Overflow ##0 Rx_AbortSignal ##0 !Rx_FrameError ##0 Rx_Ready)
		else if(Rx_Overflow)
			(Rx_Overflow ##0 !Rx_AbortSignal ##0 !Rx_FrameError ##0 !Rx_Ready)
		else if(Rx_FrameError)
			(!Rx_Overflow ##0 !Rx_AbortSignal ##0 Rx_FrameError ##0 !Rx_Ready)
		else
			(!Rx_Overflow ##0 !Rx_AbortSignal ##0 !Rx_FrameError ##0 Rx_Ready);
  endproperty

  RX_SC_correct_Assert : assert property (RX_SC_correct) $display("RX status control register correct");
   else begin 
    $error("RX status control register is not correct at time %0t", $time); 
    ErrCntAssertions++; 
   end



endmodule
