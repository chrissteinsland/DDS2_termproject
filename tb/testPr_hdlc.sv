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
  // Check to see if data is equal in rx buffer
  task RxCheckDataEqual(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;
    for(int i = 0; i < Size; i++) begin
      ReadAddress(RXBuf, ReadData);
      assert(ReadData == data[i])
        else begin
          TbErrorCnt++;
          $display("Error: Data in RXBuf is not equal to RX_data");
        end
    end
  endtask;

  // Test RX buffer for normal operation
  task TestRxBuffer(int Size, int Mismatch);
    logic [127:0][7:0] ReceiveData;
    logic       [15:0] FCSBytes;

    string msg;
    if(Mismatch)
      msg = "- Mismatch";
    else
      msg = "- Normal";
    $display("*************************************************************");
    $display("%t - Starting task TestRxBuffer %s", $time, msg);
    $display("*************************************************************");

    // Generate random data
    for (int i = 0; i < Size; i++) begin
      ReceiveData[i] = $urandom;
    end

    // FCS bytes
    ReceiveData[Size]   = '0;
    ReceiveData[Size+1] = '0;

    //Calculate FCS bits;
    GenerateFCSBytes(ReceiveData, Size, FCSBytes);
    ReceiveData[Size]   = FCSBytes[7:0];
    ReceiveData[Size+1] = FCSBytes[15:8];

    //Enable FCS
    WriteAddress(RXSC, 8'h20);

    //Generate stimulus, load into module
    InsertFlagOrAbort(1);
    MakeRxStimulus(ReceiveData, Size + 2);
    InsertFlagOrAbort(1);

    // Create a mismatch case
    if (Mismatch) begin
        ReceiveData[2]++;
    end

    // Verify
    VerifyNormalReceive(ReceiveData, Size);
    
  endtask

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
    RxCheckDataEqual(data, Size);
    
  endtask

  // VerifyOverflowReceive should verify correct value in the Rx status/control
  // register, and that the Rx data buffer contains correct data.
  task VerifyOverflowReceive(logic [127:0][7:0] data, int Size);
    logic [7:0] ReadData;
    logic [7:0] rx_status;

    wait(uin_hdlc.Rx_Ready);

    // Check RX status/control
    ReadAddress(RXSC, rx_status);
    assert(rx_status[4] == 0)
      else begin
        TbErrorCnt++; 
        $display("Error: RX overflow!");
      end 
    
    // VERIFICATION ON THE DATA IN RX DATA BUFFER NEEDS TO BE DONE
    RxCheckDataEqual(data, Size);

  endtask
  
  task VerifyDropReceive(logic [127:0][7:0] data, int Size);  
    logic [7:0] ReadData;
    logic [7:0] rx_status;
   

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

   task VerifyFrameErrorReceive(logic [127:0][7:0] data, int Size);  
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
        $display("Error: data in RXBuf is not zero"); 
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
    Transmit(13,0);                 //Normal
    Transmit(25,1);                 //Abort
    Transmit(69,0);                 //Normal
    Transmit(128,0);                //Normal
    Transmit(3,0);                  //Normal
    Transmit(18,0);                 //Normal
    TestRxBuffer(34, 0);            //Normal
    TestRxBuffer(76, 1);            //Mismatch
    TestRxBuffer(103, 1);           //Mismatch
    TestRxBuffer(126, 0);           //Normal
    TestRxBuffer(4, 1);             //Mismatch
    $display("*************************************************************");
    $display("%t - Finishing Test Program", $time);
    $display("*************************************************************");
    #10ms;
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

    if(FCSerr) begin	//Here we "corrupt" the data to force a FCS error
      for (int i=10;i<15;i++) begin
        ReceiveData[i] = $urandom;
      end
    end

    MakeRxStimulus(ReceiveData, Size + 2);

    if(Drop) begin
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
    else if(FCSerr)
      VerifyFrameErrorReceive(ReceiveData, Size);
		else if(!SkipRead)
      VerifyNormalReceive(ReceiveData, Size);

    #5000ns;
  endtask

  task Verify_DataOutBuff(logic [127:0][7:0] Data, int Size);
  	@(posedge uin_hdlc.Tx_FCSDone);
    for(int i=0;i<Size;i++) begin
			assert (uin_hdlc.Tx_Data == Data[i]) 
	  	else begin
	    	$display("Data in Output buffer is not the same as what is being written to the controller at time %0t", $time);
	    	$display("DataOutBuffer is %h, while it should be %h", uin_hdlc.Tx_Data, Data[i]);
        TbErrorCnt++;
      end
    	@(posedge uin_hdlc.Tx_RdBuff); 
		end
  endtask

  task Transmit(int Size, int Abort);
    string msg;
    logic [127:0][7:0] messages;
    if(Abort)
      msg = "- Abort";
    else
      msg = "- Normal";
    $display("*************************************************************");
    $display("%t - Starting task Transmit %s", $time, msg);
    $display("*************************************************************");

    for(int i=0; i<Size; i++) begin
      messages[i] = $urandom;
      //$display("Sent to buffer: %h", messages[i]);
      WriteAddress(TXBuf, messages[i]);
    end

    #1000ns;

    if(Abort) begin 
      WriteAddress(TXSC, 2);
			#1000ns;
      WriteAddress(TXSC, 4);
		end
    else begin
      WriteAddress(TXSC, 2);
        Verify_DataOutBuff(messages, Size);
    end
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
