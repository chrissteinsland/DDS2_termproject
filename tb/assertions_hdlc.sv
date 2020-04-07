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
  input  logic WriteEnable,
  input  logic[7:0] Data_In,
  input  logic[2:0] Address,
  input  logic Rx,
  input  logic Rx_FlagDetect,
  input  logic Rx_ValidFrame,
  input  logic Rx_AbortDetect,
  input  logic Rx_AbortSignal,
  input  logic Rx_Overflow,
  input  logic Rx_WrBuff,
  input  logic RxEN,
  input  logic Rx_EoF,
  input  logic Rx_FCSerr,
  input  logic Rx_FrameError,
  input  logic Rx_FCSen,
  input  logic Rx_Drop,
  input  logic Rx_Ready,
	input  logic[7:0] Rx_DataBuffOut,
  input	 logic TxEN,
  input  logic Tx,
  input  logic[127:0][7:0] Tx_DataArray,
  input  logic[7:0] Tx_DataOutBuff,
  input  logic[7:0] Tx_FrameSize,
  input  logic Tx_AbortedTrans,
  input  logic Tx_ValidFrame
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
  sequence Rx_abort_seq;
    !Rx ##1 Rx[*7];	
  endsequence

  // Check 8
  property RX_abort_detected;
    @(posedge Clk) Rx_abort_seq |=> ##1 $rose(Rx_AbortDetect);  
  endproperty

  // Check 10
  //If abort is detected during valid frame. then abort signal should go high
  property RX_AbortSignal;
    @(posedge Clk) Rx_AbortDetect && Rx_ValidFrame |=> Rx_AbortSignal;  
  endproperty


  RX_Detect_Assert : assert property (RX_abort_detected) 
   else begin 
    $error("Rx_AbortDetect did not go high after abort sequence %0t", $time); 
    ErrCntAssertions++; 
  end


  RX_AbortSignal_Assert : assert property (RX_AbortSignal) 
    $display("Abort signal went high as expected"); 
   else begin 
    $error("AbortSignal did not go high after AbortDetect during validframe at time %0t", $time); 
    ErrCntAssertions++; 
  end

 /*********************************************************
   *  Verify correct Rx status/control after receivin frame*
   *********************************************************/

  // Assertion 3 - Correct bits set in the RX status/control register after receiving frame

  property RX_SC_correct;
    @(posedge Clk) disable iff(!Rst) $rose(Rx_EoF) |->
      if(Rx_AbortSignal)
        (!Rx_Overflow ##0 Rx_AbortSignal ##0 !Rx_FrameError ##1 !Rx_Ready)
      else if(Rx_Overflow)
        (Rx_Overflow ##0 !Rx_AbortSignal ##0 !Rx_FrameError ##0 Rx_Ready)
      else if(Rx_FrameError)
        (!Rx_Overflow ##0 !Rx_AbortSignal ##0 Rx_FrameError ##0 !Rx_Ready)
      else
        (!Rx_Overflow ##0 !Rx_AbortSignal ##0 !Rx_FrameError ##0 Rx_Ready);
  endproperty

  RX_SC_correct_Assert : assert property (RX_SC_correct) 
  	else begin 
    	$error("RX status control register is not correct at time %0t", $time); 
    	ErrCntAssertions++; 
		end	
 
  /******************************************************************
   *  Verify zero insertion and removal for transparent transmission*
   ******************************************************************/

  // Assertion 6 - zero insertion and removal for transparent transmission 
  sequence Tx_flag;
    !Tx ##1 Tx[*6] ##1 !Tx;	
  endsequence
		
  property zero_insertion;
    @(posedge Clk) disable iff(!Rst || !Tx_ValidFrame) Tx_flag ##[0:$] Tx[*5] |=> $fell(Tx);
  endproperty

  zero_insertion_Assert : assert property (zero_insertion) 
  	else begin 
    	$error("Zeroes not inserted correctly at time %0t", $time); 
    	ErrCntAssertions++; 
  	end

  /********************************************
   *  Verify correct Idle_pattern behavior    *
   ********************************************/
  //Assertion 7 - Idle pattern generation and checking (1111_1111 when not operating)
  property idle_pattern;
    @(posedge Clk) disable iff(!Rst)
      !Tx_ValidFrame && $past(!Tx_ValidFrame,8) |=> Tx;
  endproperty

  idle_pattern_assert: assert property (idle_pattern) 
   else begin 
    $error("Idle pattern not valid at time %0t", $time); 
    ErrCntAssertions++; 
   end


  /************************************************
   *  Verify that Tx_AbortedTrans works correctly	*
   ************************************************/

  // Assertion 9 - Correct bits set in the RX status/control register after receiving frame

  property Tx_AbortedTrans_correct;
    @(posedge Clk) disable iff(!Rst) 
			((Address == 0) && Data_In[2] && WriteEnable) |=> ##2 Tx_AbortedTrans;
  endproperty

  Tx_AbortedTrans_correct_Assert : assert property (Tx_AbortedTrans_correct) 
  	else begin 
   		$error("Tx_AbortedTrans not asserted correctly at time %0t", $time); 
    	ErrCntAssertions++; 
   end

  /************************************************
   *  Verify that Rx_EoF works correctly	*
   ************************************************/

  // Assertion 12 - Rx_EoF is generated when a whole RX frame has been received 

  property Rx_EoF_correct;
    @(posedge Clk) disable iff(!Rst) 
			$fell(Rx_ValidFrame) |=> Rx_EoF;
  endproperty

  Rx_EoF_correct_Assert : assert property (Rx_EoF_correct) 
  	else begin 
   		$error("Rx_EoF not correctly generated at time %0t", $time); 
    	ErrCntAssertions++; 
   end

  /***********************************************************************
   *  Rx_Ready should indicate byte(s) in Rx buffer is ready to be read *
   ***********************************************************************/

  // Assertion 15

  property Rx_Ready_buffer_can_be_read;
    @(posedge Clk) disable iff(!Rst) 
			Rx_Ready |-> !$isunknown(Rx_Data);
  endproperty

  Rx_Ready_buffer_can_be_read_Assert : assert property (Rx_Ready_buffer_can_be_read) 
  	else begin 
   		$error("Rx buffer contains unknown values, when Rx_Ready was high at time %0t", $time); 
    	ErrCntAssertions++; 
   end
endmodule
