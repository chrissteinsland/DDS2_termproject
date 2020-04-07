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


	covergroup hdlc_cg @(posedge uin_hdlc.Clk);
			Rx_Overflow: coverpoint uin_hdlc.Rx_Overflow {
				bins No_Rx_Overflow = {0};
				bins Rx_Overflow = {1};
			}
			Rx_Drop: coverpoint uin_hdlc.Rx_Drop {
				bins No_Rx_Drop = {0};
				bins Rx_Drop = {1};
			}
			Rx_AbortDetect: coverpoint uin_hdlc.Rx_AbortDetect {
				bins No_Rx_AbortDetect = {0};
				bins Rx_AbortDetect = {1};
			}
			Rx_FlagDetect: coverpoint uin_hdlc.Rx_FlagDetect {
				bins No_Rx_FlagDetect = {0};
				bins Rx_FlagDetect = {1};
			}
			Rx_FrameError: coverpoint uin_hdlc.Rx_FrameError {
				bins No_Rx_FrameError = {0};
				bins Rx_FrameError = {1};
			}
			Rx_FCSerr: coverpoint uin_hdlc.Rx_FCSerr {
				bins No_Rx_FCSerr = {0};
				bins Rx_FCSerr = {1};
			}
			Rx_EoF: coverpoint uin_hdlc.Rx_EoF {
				bins No_Rx_EoF = {0};
				bins Rx_EoF = {1};
			}

			Tx_ValidFrame: coverpoint uin_hdlc.Tx_ValidFrame {
				bins No_Tx_ValidFrame = {0};
				bins Tx_ValidFrame = {1};
			}
			Tx_Done: coverpoint uin_hdlc.Tx_Done {
				bins No_Tx_Done = {0};
				bins Tx_Done = {1};
			}
			Tx_Full: coverpoint uin_hdlc.Tx_Full {
				bins No_Tx_Full = {0};
				bins Tx_Full = {1};
			}
			Tx_AbortedTrans: coverpoint uin_hdlc.Tx_AbortedTrans {
				bins No_Tx_AbortedTrans = {0};
				bins Tx_AbortedTrans = {1};
			}
			Tx_zero_insertions: coverpoint uin_hdlc.Tx_Data {
				bins No_Tx_zero_insertions = default;
				bins Tx_zero_insertions = {'h3f, 'h7f, 'hff, 'h7e, 'hfc, 'hfe}; 
			}
	endgroup
	hdlc_cg hdlc_cg_inst;
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
          //TbErrorCnt++;
          $display("Data in RXBuf is not equal to RX_data");
        end
    end
  endtask;


  // Check that the frame size is equal to received frames
  task RxCheckFrameSize(int Size);
    logic [7:0] rx_frame_size;
    ReadAddress(RXLen, rx_frame_size);

    assert(rx_frame_size == Size)
    else begin
        //TbErrorCnt++;
        $display("Frame size reg (%0d) is not equal to recieved frames (%0d)", rx_frame_size, Size);
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

    // Check overflow
    assert(rx_status[4])
            $display("RX overflow as expected!");
         else begin
            $display("Error: No overflow during overflow test");
            TbErrorCnt++; 
          end
    
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
		hdlc_cg_inst = new();
    
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
    Transmit(8,0);                  //Normal
    Transmit(25,1);                 //Abort
    Transmit(69,0);                 //Normal
    Transmit(11,0);                 //Normal
    Transmit(44,0);                 //Normal
    Transmit(120,0);                //Normal
    TestRxBuffer(34, 0);            //Normal
    TestRxBuffer(76, 1);            //Mismatch
    TestRxBuffer(103, 1);           //Mismatch
    TestRxBuffer(126, 0);           //Normal
    TestRxBuffer(4, 1);             //Mismatch
		Verify_Transmit_Receive(70);		//Normal
		Overflow_Tx_Buffer();						//Full Buffer	
		Overflow_Tx_Buffer();						//Full Buffer
		Overflow_Tx_Buffer();						//Full Buffer
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

    // Check Framsize is equal to number of bytes received
    RxCheckFrameSize(Size);

    #5000ns;
  endtask

  task Verify_DataOutBuff(logic [127:0][7:0] Data, int Size);
		@(posedge uin_hdlc.Tx_RdBuff);
    for(int i=0;i<Size;i++) begin
  	if(i) @(negedge uin_hdlc.Tx_RdBuff);
			assert (uin_hdlc.Tx_DataOutBuff == Data[i]) 
	  	else begin
	    	$display("Data in Output buffer is not the same as what is being written to the controller at time %0t", $time);
	    	$display("DataOutBuffer is %h, while it should be %h", uin_hdlc.Tx_DataOutBuff, Data[i]);
        TbErrorCnt++;
      end
			if(i == Size-1) begin
				assert (uin_hdlc.Tx_Done == 1)
				else begin
	    		$display("Tx_Done did not go high after buffer has been read at time %0t", $time);
        	TbErrorCnt++;
				end
			end
		end
  endtask

	task Verify_FCS(logic[127:0][7:0] messages, int Size);
		logic[1:0][7:0] FCSByte;
		logic[15:0] FCSBytes;
 		GenerateFCSBytes(messages, Size, FCSBytes);
		FCSByte[0] = FCSBytes[7:0];
		FCSByte[1] = FCSBytes[15:8];
		@(uin_hdlc.Tx_Data);
		for(int i=0;i<2;i++) begin
			@(uin_hdlc.Tx_Data);
			if(!$isunknown(FCSBytes)) begin
			assert (uin_hdlc.Tx_Data == FCSByte[i]) $display("FCS correct at time %0t", $time);
				else begin
	    		$display("FCS not correct at time %0t", $time);
	    		$display("Data in buffer was %h, expected %h", uin_hdlc.Tx_Data, FCSByte[i]);
        	TbErrorCnt++;
				end
			end
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
      WriteAddress(TXBuf, messages[i]);
    end
    
    #1000ns;
		WriteAddress(TXSC, 2);
    if(Abort) begin 
			#1000ns;
      WriteAddress(TXSC, 4);
		end
    else begin
			Verify_DataOutBuff(messages, Size);
			Verify_FCS(messages, Size);
		end
    #5000ns;
 endtask
	
	task Overflow_Tx_Buffer();
		logic[127:0][7:0] messages;
    $display("*************************************************************");
    $display("%t - Starting task Overflowing Tx Buffer", $time, );
    $display("*************************************************************");

    for(int i=0; i<128; i++) begin
      messages[i] = $urandom;
			WriteAddress(TXBuf, messages[i]);
			if(i>125) begin
				assert(uin_hdlc.Tx_Full == 1) 
      	else begin 
      		TbErrorCnt++;
        	$display("Tx_Full not correctly asserted at time %t", $time);
				end
			end
    end
		#1000ns;
		WriteAddress(TXSC, 2);
		@(posedge uin_hdlc.Tx_Done);
	endtask

	task Verify_Transmit_Receive(int Size);
    logic [127:0][7:0] messages;
		int counter;
    $display("*************************************************************");
    $display("%t - Starting task Transmit to Receive", $time);
    $display("*************************************************************");

    for(int i=0; i<Size; i++) begin
      messages[i] = $urandom;
      WriteAddress(TXBuf, messages[i]);
    end

		#1000ns;
		WriteAddress(TXSC, 2);
		@(posedge uin_hdlc.Tx_ValidFrame);
		while(uin_hdlc.Tx_ValidFrame == 1 || uin_hdlc.Rx_Ready == 0) begin
			@(posedge uin_hdlc.Clk) uin_hdlc.Rx = uin_hdlc.Tx;
			if(uin_hdlc.Rx_WrBuff && counter < Size) begin
				assert(uin_hdlc.Rx_Data == messages[counter]) 
      	else begin 
      		TbErrorCnt++;
        	$display("Received byte not what was transmitted! Expected %h, received %h at time %0t", messages[counter], uin_hdlc.Rx_Data, $time);
				end
				counter++;
			end
		end
		uin_hdlc.Rx = 0;
		#6000ns;
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
