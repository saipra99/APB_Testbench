// Code your testbench here
// or browse Examples


`define A_WIDTH 8
`define D_WIDTH 8

//*****************Assertions******************
module APB_assert(
  input logic p_clk,
    input logic p_rstn,
    input logic p_enable,
    input logic p_sel,
    input logic  p_write,
    input logic [`A_WIDTH-1:0] p_addr,
    input logic [`D_WIDTH-1:0] wr_data,
    input logic [`D_WIDTH-1:0] rd_data,
    input logic p_ready,
    input logic [1:0] state);
  
   parameter IDLE_PHASE=0,
             SETUP_PHASE=1,
             W_PHASE=2,
             R_PHASE=3;
  
  let setup=(state==SETUP_PHASE);
  
  //#1) Check if wr_data and RESET VAL when in  IDLE phase.
  
     property check_rstn_state;
       @(posedge p_clk)
       (!(p_rstn) |-> (rd_data=='h12));
     endproperty
  
  //#2) Check if state is W_PHASE when p_write high.
  
     property check_state_w;
       disable iff(!p_rstn||p_enable||!p_write)
         @(posedge p_clk)
       ((p_sel && p_write)|=>(state==W_PHASE));
     endproperty
  
  //#3) Check if R_PHASE when p_write is not high.
  
    property check_state_r ;
      disable iff(!p_rstn||p_enable||p_write)
      @(posedge p_clk)
      ((p_sel && !p_write)|=> (state==R_PHASE));
    endproperty
  

  
  
  //4) Check whether after access phase if sel is high it goes back to SETUP phase.
      sequence rd_wr_phase;
        (state==R_PHASE||state==W_PHASE) ##1 p_sel;
      endsequence
      
      
      property check_back_setup;
        disable iff(!p_rstn)
        @(posedge p_clk)
        (rd_wr_phase|-> (state==SETUP_PHASE));
      endproperty
  
      
  
  //#5) Check if p_ready is zero in IDLE PHASE and data is RESET VAL
          
         property check_rd_data;
           disable iff(!p_rstn)
           @(posedge p_clk)
           ((state==IDLE_PHASE && p_rstn)|-> (p_ready==0) && !$isunknown(rd_data));
         endproperty
          
  
  //#6) Check if sel not high after setup phase it goes back to IDLE phase.
          property back_idle; 
            disable iff(!p_rstn)
            @(posedge p_clk)
            ((setup && !p_sel)|-> (state==IDLE_PHASE));
          endproperty
  
  
  
  ERR_CHECK_RST_VAL: assert property (check_rstn_state)
    $display("Successful RESET");
    else
     $error("ERROR CHECK");
    
  ERR_CHECK_WRITE: assert property (check_state_w)
      $display("WRITE SUCCESSFUL");
    
  ERR_CHECK_READ: assert property (check_state_r)
    $display("READ SUCCESSFUL");
    
  ERR_CHECK_SETUP_HIGH_AGAIN: assert property (check_back_setup)
    $display("SETUP HIGH AGAIN");
    
  ERR_CHECK_IDLE_PHASE: assert property (back_idle)
    $display("Back IDLE Phase");
    
  ERR_CHECK_READ_CONTENTS: assert property (check_rd_data)
    $display("Ready success");

  
endmodule

//*************************TESTBENCH************************

module tb();
  
  logic p_clk;
  logic p_rstn;
  logic p_enable;
  logic p_sel;
  logic p_write;
  logic [`A_WIDTH-1:0] p_addr;
  logic [`D_WIDTH-1:0] wr_data;
  logic [`D_WIDTH-1:0] rd_data;
  logic p_ready;
  
  bind APB_slave:DUT APB_assert inst1(.*);
  
  APB_slave#(.A_WIDTH(8),.D_WIDTH(8)) DUT( 
    .p_clk(p_clk),
    .p_rstn(p_rstn),
    .p_sel(p_sel),
    .p_write(p_write),
    .p_addr(p_addr),
    .wr_data(wr_data),
    .rd_data(rd_data),
    .p_ready(p_ready),
    .p_enable(p_enable));
  
  
  initial forever #10 p_clk=!p_clk;
  
  initial
    begin
      
      $monitor("[%0t] rst: %0d sel:%0d enable:%0d write:%0d addr:%0h ready:%0d",$stime,p_rstn,p_sel,p_enable,p_write,p_addr,p_ready);
      
      p_clk=1;
      p_rstn=0; p_sel=0; p_enable=0; p_write=0; p_addr=0; 
      
      #20;
      p_rstn=1; p_sel=1; p_enable=0; p_write=1; p_addr='h45; 
      #40;
      p_enable=1;
      #20;
      p_sel=0;
      #20;
      p_rstn=1; p_sel=1; p_enable=0; p_write=0; p_addr='h65;
      #40;
      p_enable=1;
      #20
      p_rstn=1; p_sel=1; p_enable=0; p_write=1; p_addr= 'h55;
      #40;
      p_enable=1;
      #20;
      p_rstn=1; p_sel=1; p_enable=0; p_write=0; p_addr='h76; 
      
      #60;
      $finish;
      
    end
  
      
initial
  begin
  $dumpfile("dump.vcd");
  $dumpvars(1);
  end
  
  
endmodule
    
