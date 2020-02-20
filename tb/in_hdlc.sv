//////////////////////////////////////////////////
// Title:   in_hdlc
// Author:  Karianne Krokan Kragseth
// Date:    20.10.2017
//////////////////////////////////////////////////

interface in_hdlc ();
  //Tb
  int ErrCntAssertions;

  //Clock and reset
  logic Clk;
  logic Rst;

  // Address
  logic [2:0] Address;
  logic       WriteEnable;
  logic       ReadEnable;
  logic [7:0] DataIn;
  logic [7:0] DataOut;

  // TX
  logic Tx;
  logic TxEN;


  // TX internal
  logic              Tx_ValidFrame;   
  logic              Tx_AbortedTrans;
  logic              Tx_WriteFCS;     
  logic              Tx_InitZero;     
  logic              Tx_StartFCS;     
  logic              Tx_RdBuff;       
  logic              Tx_NewByte;      
  logic              Tx_FCSDone;      
  logic [7:0]        Tx_Data;         
  logic              Tx_Done;         
  logic              Tx_Full;         
  logic              Tx_DataAvail;    
  logic [7:0]        Tx_FrameSize;    
  logic [127:0][7:0] Tx_DataArray;    
  logic [7:0]        Tx_DataOutBuff;  
  logic              Tx_WrBuff;       
  logic              Tx_Enable;       
  logic [7:0]        Tx_DataInBuff;   
  logic              Tx_AbortFrame;   

  // RX
  logic Rx;
  logic RxEN;

  // Rx internal
  logic       Rx_ValidFrame;
  logic [7:0] Rx_Data;
  logic       Rx_AbortSignal;
  logic       Rx_Ready;
  logic       Rx_WrBuff;
  logic       Rx_EoF;
  logic [7:0] Rx_FrameSize;
  logic       Rx_Overflow;
  logic       Rx_FCSerr;
  logic       Rx_FCSen;
  logic [7:0] Rx_DataBuffOut;
  logic       Rx_RdBuff;
  logic       Rx_NewByte;
  logic       Rx_StartZeroDetect;
  logic       Rx_FlagDetect;
  logic       Rx_AbortDetect;
  logic       Rx_FrameError;
  logic       Rx_Drop;
  logic       Rx_StartFCS;
  logic       Rx_StopFCS;
  logic       RxD;
  logic       ZeroDetect;

endinterface
