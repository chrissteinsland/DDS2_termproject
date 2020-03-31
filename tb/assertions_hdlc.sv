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
  input	 logic TxEN,
  input  logic RxEN,
  input  logic Rx_EoF,
  input  logic Rx_FCSerr,
  input  logic Rx_Ready
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

  /********************************************
   *  Verify correct Idle_pattern behavior	  *
   ********************************************/
  //Idle pattern generation and checking (1111_1111 when not operating)

  property idle_pattern;
 	@(posedge Clk) Rx[*8] |-> (	!Rx_ValidFrame && !Rx_Ready && !Rx_AbortSignal && 
								!Rx_WrBuff && !Rx_Overflow && !Rx_FCSerr) ##1 $fell(Rx_EoF); 
  endproperty

  idle_pattern_assert: assert property (idle_pattern) 
   else begin 
    $error("Idle pattern not valid at time %0t", $time); 
    ErrCntAssertions++; 
   end

endmodule
