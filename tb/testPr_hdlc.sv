//////////////////////////////////////////////////
// Title:   testPr_hdlc
// Author: 
// Date:  
//////////////////////////////////////////////////

/* testPr_hdlc contains the simulation and immediate assertion code of the
   testbench. 

   For this exercise you will write immediate assertions for the Rx module which
   should verify correct values in some of the Rx registers for:
   - Normal behavior
   - Buffer overflow 
   - Aborts

   HINT:
   - A ReadAddress() task is provided, and addresses are documentet in the 
     HDLC Module Design Description
*/

program testPr_hdlc(
  in_hdlc uin_hdlc
);
  
  int TbErrorCnt;
  enum int {TXSC, TXBuf, RXSC, RXBuf, RXLen} address; 
  /****************************************************************************
   *                                                                          *
   *                               Student code                               *
   *                                                                          *
   ****************************************************************************/

  // VerifyAbortReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer is zero after abort.
  task VerifyAbortReceive(logic [127:0][7:0] data, int Size);  
    // data is not being used in this case!
    logic [7:0] ReadData;
    logic [7:0] rx_status;
  
    //Check for RX Abort flag
    
     ReadAddress(RXSC, rx_status);
     assert(rx_status[3] != 0)
      else begin 
        TbErrorCnt++;
        $display("Error: Abort flag not set at time %0t!", $time);
      end
    
    //Check that RXBuf is zero

    for(int i = 0; i < Size; i++) begin
     ReadAddress(RXBuf, ReadData); 
     assert (ReadData == 0) 
      else begin
        TbErrorCnt++;
        $display("Error: data in RXBuf is not zero"); 
      end
    end
  endtask

  // VerifyNormalReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer contains correct data.
  task VerifyNormalReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;
    logic [7:0] rx_status;
    wait(uin_hdlc.Rx_Ready);

    // INSERT CODE HERE
    // Check RX status/control
    ReadAddress(RXSC, rx_status);
      assert(rx_status[0] && !rx_status[1] && !rx_status[2] && !rx_status[3])
        else begin
          TbErrorCnt++; 
          $display("Error: rx_status is not correct! %d", rx_status);
        end 

    //Check that Rx data is correct
    for(int i = 0; i < Size; i++) begin
      ReadAddress(RXBuf, ReadData);
      assert(ReadData == data[i])
        else begin
          TbErrorCnt++;
          $display("Error: Data in RXBuf is not equal to RX_data");
        end
    end
  endtask

  // VerifyOverflowReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer contains correct data.
  task VerifyOverflowReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;
    logic [7:0] rx_status;

    wait(uin_hdlc.Rx_Ready);

    // INSERT CODE HERE

    // Check RX status/control
    ReadAddress(RXSC, rx_status);
    assert(rx_status[4])
      else begin
        TbErrorCnt++; 
        $display("Error: rx_status is not correct! %d", rx_status);
      end 
    
	// VERIFICATION ON THE DATA IN RX DATA BUFFER NEEDS TO BE DONE

  endtask
  
  task VerifyDropReceive(logic [127:0][7:0] data, int Size);  
    // data is not being used in this case!
    logic [7:0] ReadData;
    logic [7:0] rx_status;
  
   
	//Check for RX Drop flag
     ReadAddress(RXSC, rx_status);
	 $display("rx_status = %d", rx_status);
     assert(rx_status[1] != 0)
      else begin 
        TbErrorCnt++;
        $display("Error: Drop flag not set at time %0t! (rx_status = %d)", $time, rx_status);
      end

    //Check that RXBuf is zero

    for(int i = 0; i < Size; i++) begin
     ReadAddress(RXBuf, ReadData); 
     assert (ReadData == 0) 
      else begin
        TbErrorCnt++;
        $display("Error: data in RXBuf is not zero, when testing for drop"); 
      end
    end
  endtask

   task VerifyFrameErrorReceive(logic [127:0][7:0] data, int Size);  
    // data is not being used in this case!
    logic [7:0] ReadData;
    logic [7:0] rx_status;
  
    //Check for RX FCSErr flag
    
     ReadAddress(RXSC, rx_status);
     assert(rx_status[2] != 0)
      else begin 
        TbErrorCnt++;
        $display("Error: FCSErr flag not set at time %0t!", $time);
      end
    
    //Check that RXBuf is zero

    for(int i = 0; i < Size; i++) begin
     ReadAddress(RXBuf, ReadData); 
     assert (ReadData == 0) 
      else begin
        TbErrorCnt++;
        $display("Error: data in RXBuf is not zeroi, when testing for frame error"); 
      end
    end
  endtask
 




  /****************************************************************************
   *                                                                          *
   *                             Simulation code                              *
   *                                                                          *
   ****************************************************************************/

  initial begin
    $display("*************************************************************");
    $display("%t - Starting Test Program", $time);
    $display("*************************************************************");

    Init();

    //Receive: Size, Abort, FCSerr, NonByteAligned, Overflow, Drop, SkipRead
    Receive( 10, 0, 0, 0, 0, 0, 0); //Normal
    Receive( 40, 1, 0, 0, 0, 0, 0); //Abort
    Receive(126, 0, 0, 0, 1, 0, 0); //Overflow
    Receive( 45, 0, 0, 0, 0, 0, 0); //Normal
    Receive(126, 0, 0, 0, 0, 0, 0); //Normal
    Receive(122, 1, 0, 0, 0, 0, 0); //Abort
    Receive(126, 0, 0, 0, 1, 0, 0); //Overflow
    Receive( 25, 0, 0, 0, 0, 0, 0); //Normal
    Receive( 47, 0, 0, 0, 0, 0, 0); //Normal
    Receive(126, 0, 1, 0, 0, 0, 0); //FCSerr
    Receive( 25, 0, 0, 0, 0, 1, 0); //Drop
    Receive( 83, 0, 1, 0, 0, 0, 0); //FCSerr
    Receive( 69, 0, 0, 0, 0, 1, 0); //Drop
    $display("*************************************************************");
    $display("%t - Finishing Test Program", $time);
    $display("*************************************************************");
    $stop;
  end

  final begin

    $display("*********************************");
    $display("*                               *");
    $display("* \tAssertion Errors: %0d\t  *", TbErrorCnt + uin_hdlc.ErrCntAssertions);
    $display("*                               *");
    $display("*********************************");

  end

  task Init();
    uin_hdlc.Clk         =   1'b0;
    uin_hdlc.Rst         =   1'b0;
    uin_hdlc.Address     = 3'b000;
    uin_hdlc.WriteEnable =   1'b0;
    uin_hdlc.ReadEnable  =   1'b0;
    uin_hdlc.DataIn      =     '0;
    uin_hdlc.TxEN        =   1'b1;
    uin_hdlc.Rx          =   1'b1;
    uin_hdlc.RxEN        =   1'b1;

    TbErrorCnt = 0;

    #1000ns;
    uin_hdlc.Rst         =   1'b1;
  endtask

  task WriteAddress(input logic [2:0] Address ,input logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address     = Address;
    uin_hdlc.WriteEnable = 1'b1;
    uin_hdlc.DataIn      = Data;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.WriteEnable = 1'b0;
  endtask

  task ReadAddress(input logic [2:0] Address ,output logic [7:0] Data);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Address    = Address;
    uin_hdlc.ReadEnable = 1'b1;
    #100ns;
    Data                = uin_hdlc.DataOut;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.ReadEnable = 1'b0;
  endtask

  task InsertFlagOrAbort(int flag);
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b0;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;
    @(posedge uin_hdlc.Clk);
    if(flag)
      uin_hdlc.Rx = 1'b0;
    else
      uin_hdlc.Rx = 1'b1;
  endtask

  task MakeRxStimulus(logic [127:0][7:0] Data, int Size);
    logic [4:0] PrevData;
    PrevData = '0;
    for (int i = 0; i < Size; i++) begin
      for (int j = 0; j < 8; j++) begin
        if(&PrevData) begin
          @(posedge uin_hdlc.Clk);
          uin_hdlc.Rx = 1'b0;
          PrevData = PrevData >> 1;
          PrevData[4] = 1'b0;
        end

        @(posedge uin_hdlc.Clk);
        uin_hdlc.Rx = Data[i][j];

        PrevData = PrevData >> 1;
        PrevData[4] = Data[i][j];
      end
    end
  endtask

  task Receive(int Size, int Abort, int FCSerr, int NonByteAligned, int Overflow, int Drop, int SkipRead);
    logic [127:0][7:0] ReceiveData;
    logic       [15:0] FCSBytes;
    logic   [2:0][7:0] OverflowData;
    string msg;
    if(Abort)
      msg = "- Abort";
    else if(FCSerr)
      msg = "- FCS error";
    else if(NonByteAligned)
      msg = "- Non-byte aligned";
    else if(Overflow)
      msg = "- Overflow";
    else if(Drop)
      msg = "- Drop";
    else if(SkipRead)
      msg = "- Skip read";
    else
      msg = "- Normal";
    $display("*************************************************************");
    $display("%t - Starting task Receive %s", $time, msg);
    $display("*************************************************************");

    for (int i = 0; i < Size; i++) begin
      ReceiveData[i] = $urandom;
    end
    ReceiveData[Size]   = '0;
    ReceiveData[Size+1] = '0;

    //Calculate FCS bits;
    GenerateFCSBytes(ReceiveData, Size, FCSBytes);
    ReceiveData[Size]   = FCSBytes[7:0];
    ReceiveData[Size+1] = FCSBytes[15:8];

    //Enable FCS
    if(!Overflow && !NonByteAligned)
      WriteAddress(RXSC, 8'h20);
    else
      WriteAddress(RXSC, 8'h00);

    //Generate stimulus
    InsertFlagOrAbort(1);
    
    MakeRxStimulus(ReceiveData, Size + 2);


    if(FCSerr) begin
     /*     Proposed pseudocode for testing FCS
        Generate some random bytes
        Randomize placement in data
        Replace the good bytes with bad bytes
     */
    end

    if(Drop) begin
      logic [7:0] rx_status;
      logic [7:0] dropmask;
      ReadAddress(RXSC, rx_status);
	  $display("rx_status is: %d", rx_status);
      dropmask = (8'b00000010 | rx_status);
      //$display("Dropmask is: %d", dropmask);
	  WriteAddress(RXSC, 2);
    end	

    if(Overflow) begin
      OverflowData[0] = 8'h44;
      OverflowData[1] = 8'hBB;
      OverflowData[2] = 8'hCC;
      MakeRxStimulus(OverflowData, 3);
    end

    if(Abort) begin
      InsertFlagOrAbort(0);
    end else begin
      InsertFlagOrAbort(1);
    end

    @(posedge uin_hdlc.Clk);
    uin_hdlc.Rx = 1'b1;

    repeat(8)
      @(posedge uin_hdlc.Clk);

    if(Abort)
      VerifyAbortReceive(ReceiveData, Size);
    else if(Overflow)
      VerifyOverflowReceive(ReceiveData, Size);
     else if(Drop)
      VerifyDropReceive(ReceiveData, Size);
   /* else if(FCSerr)
      VerifyFrameErrorReceive(ReceiveData, Size);*/
	else if(!SkipRead)
      VerifyNormalReceive(ReceiveData, Size);

    #5000ns;
  endtask

  task GenerateFCSBytes(logic [127:0][7:0] data, int size, output logic[15:0] FCSBytes);
    logic [23:0] CheckReg;
    CheckReg[15:8]  = data[1];
    CheckReg[7:0]   = data[0];
    for(int i = 2; i < size+2; i++) begin
      CheckReg[23:16] = data[i];
      for(int j = 0; j < 8; j++) begin
        if(CheckReg[0]) begin
          CheckReg[0]    = CheckReg[0] ^ 1;
          CheckReg[1]    = CheckReg[1] ^ 1;
          CheckReg[13:2] = CheckReg[13:2];
          CheckReg[14]   = CheckReg[14] ^ 1;
          CheckReg[15]   = CheckReg[15];
          CheckReg[16]   = CheckReg[16] ^1;
        end
        CheckReg = CheckReg >> 1;
      end
    end
    FCSBytes = CheckReg;
  endtask

endprogram
