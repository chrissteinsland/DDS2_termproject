//////////////////////////////////////////////////
// Title:   bind_hdlc
// Author:  Karianne Krokan Kragseth
// Date:    20.10.2017
//////////////////////////////////////////////////

module bind_hdlc ();
  bind test_hdlc assertions_hdlc u_assertion_bind(
    .ErrCntAssertions (uin_hdlc.ErrCntAssertions),
    .Clk              (uin_hdlc.Clk),
    .Rst              (uin_hdlc.Rst),
    .WriteEnable      (uin_hdlc.WriteEnable),
    .Data_In          (uin_hdlc.DataIn),
    .Address          (uin_hdlc.Address),
    .Rx               (uin_hdlc.Rx),
    .Rx_FlagDetect    (uin_hdlc.Rx_FlagDetect),
    .Rx_ValidFrame    (uin_hdlc.Rx_ValidFrame),
    .Rx_AbortDetect   (uin_hdlc.Rx_AbortDetect),
    .Rx_AbortSignal   (uin_hdlc.Rx_AbortSignal),
    .Rx_Overflow      (uin_hdlc.Rx_Overflow),
    .Rx_WrBuff        (uin_hdlc.Rx_WrBuff), 
    .RxEN	      (uin_hdlc.RxEN),
    .TxEN             (uin_hdlc.TxEN),
    .Rx_EoF           (uin_hdlc.Rx_EoF),
    .Rx_Ready         (uin_hdlc.Rx_Ready),
    .Rx_Drop          (uin_hdlc.Rx_Drop),
    .Rx_FCSen         (uin_hdlc.Rx_FCSen),
    .Rx_FrameError    (uin_hdlc.Rx_FrameError),
    .Rx_DataBuffOut   (uin_hdlc.Rx_DataBuffOut),
    .Tx               (uin_hdlc.Tx),
    .Tx_DataOutBuff   (uin_hdlc.Tx_DataOutBuff),
    .Tx_DataArray     (uin_hdlc.Tx_DataArray),
    .Tx_FrameSize     (uin_hdlc.Tx_FrameSize),
    .Tx_AbortedTrans	(uin_hdlc.Tx_AbortedTrans),
    .Tx_ValidFrame    (uin_hdlc.Tx_ValidFrame)

);

endmodule
