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
  input  logic Rx_EoF ,
  input  logic Tx,
  input  logic[127:0][7:0] Tx_DataArray,
  input  logic[7:0] Tx_DataOutBuff,
  input  logic[7:0] Tx_FrameSize,
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

  RX_SC_correct_Assert : assert property (RX_SC_correct) $display("RX status control register correct");
   else begin 
    $error("RX status control register is not correct at time %0t", $time); 
    ErrCntAssertions++; 
   end

  /***********************************************************
   *  Verify correct TX output according to written TX buffer*
   ***********************************************************/
  // Assertion 4 - Correct TX output according to written TX buffer
  sequence Tx_flag;
 	!Tx ##1 Tx[*6] ##1 !Tx;	
  endsequence
 /* 
  function bit correct_tx(logic [127:0][7:0] Data, logic [7:0] Size);
    for(int i=0;i<Tx_FrameSize;i++) begin
      logic [7:0] Current_Byte;
      Current_Byte = Data[i];
      for(int j=0;j<8;j++) begin
        if(Tx != Current_Byte[j]) return 0; 
      end
    end
    return 1;
  endfunction;
*/
  property Tx_according_to_buffer;
    logic[127:0][7:0] Tx_DataArray_Saved;
    @(posedge Clk) disable iff(!Rst) ($rose(Tx_ValidFrame), Tx_DataArray_Saved = Tx_DataArray) |-> 
    //  TODO: Use a fucking for loop
      ##10
      Tx == Tx_DataArray_Saved[0][0] ##1
      Tx == Tx_DataArray_Saved[0][1] ##1
      Tx == Tx_DataArray_Saved[0][2] ##1
      Tx == Tx_DataArray_Saved[0][3] ##1
      Tx == Tx_DataArray_Saved[0][4] ##1
      Tx == Tx_DataArray_Saved[0][5] ##1
      Tx == Tx_DataArray_Saved[0][6] ##1
      Tx == Tx_DataArray_Saved[0][7] ##1
      Tx == Tx_DataArray_Saved[1][0] ##1
      Tx == Tx_DataArray_Saved[1][1] ##1
      Tx == Tx_DataArray_Saved[1][2] ##1
      Tx == Tx_DataArray_Saved[1][3] ##1
      Tx == Tx_DataArray_Saved[1][4] ##1
      Tx == Tx_DataArray_Saved[1][5] ##1
      Tx == Tx_DataArray_Saved[1][6] ##1
      Tx == Tx_DataArray_Saved[1][7] ##1
      Tx == Tx_DataArray_Saved[2][0] ##1
      Tx == Tx_DataArray_Saved[2][1] ##1
      Tx == Tx_DataArray_Saved[2][2] ##1
      Tx == Tx_DataArray_Saved[2][3] ##1
      Tx == Tx_DataArray_Saved[2][4] ##1
      Tx == Tx_DataArray_Saved[2][5] ##1
      Tx == Tx_DataArray_Saved[2][6] ##1
      Tx == Tx_DataArray_Saved[2][7]; 
  endproperty

  Tx_according_to_buffer_Assert : assert property (Tx_according_to_buffer) $display("Tx is correct according to Tx buffer");
    else begin 
      $display("Tx is not correct according to Tx buffer at time ½0t", $time); 
      ErrCntAssertions++; 
    end
endmodule
