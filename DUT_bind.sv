// Code your testbench here
// or browse Examples
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
    input logic p_slverr,
    input logic [1:0] state);
  
   parameter IDLE_PHASE=0,
             SETUP_PHASE=1,
             W_PHASE=2,
             R_PHASE=3;
  
  parameter RESET_VAL='h12 ;
  
  let setup=(state==SETUP_PHASE);
  
  //#1) Check if wr_data and in IDLE phase data is RESET VAL
  
     property check_rstn_state;
       @(posedge p_clk)
       (!p_rstn |=> (rd_data=='h12));
     endproperty
  
  //#2) Check if W_PHASE when p_write high
  
     property check_state_w;
       disable iff(!p_rstn||p_enable||!p_write)
       
       @(posedge p_clk)
       ((p_sel && $rose(p_write))|=>(state==W_PHASE));
     endproperty
  
  //#3) Check if R_PHASE when p_write not high
  
    property check_state_r;
      disable iff(!p_rstn||p_enable||p_write||p_slverr)
      @(posedge p_clk)
      ((p_sel && !p_write)|=> (state==R_PHASE));
    endproperty
  

  
  
  //4) Check if sel is high after access phase it goes back to SETUP
      sequence rd_wr_phase;
        (state==R_PHASE||state==W_PHASE) ##1 p_sel;
      endsequence
      
      
      property check_back_setup;
        disable iff(!p_rstn)
        @(posedge p_clk)
        (rd_wr_phase|-> (state==SETUP_PHASE));
      endproperty
  
      
  
  //#5) Check if rd_data is zero in IDLE PHASE
          
         property check_rd_data;
           disable iff(!p_rstn)
           @(posedge p_clk)
           ((state==IDLE_PHASE && p_rstn)|-> (p_ready==0) && !$isunknown(rd_data));
         endproperty
          
  
  //#6) Check if sel not high after rd/wr phase it goes back to IDLE
  
    sequence back;
     ##1 (state==R_PHASE || state==W_PHASE);
    endsequence
  
     property back_idle; 
       disable iff(!p_rstn||!p_enable)
         @(posedge p_clk)
       (back ##1 !p_sel ##1 (state==IDLE_PHASE));
     endproperty
  
  //#7) Check if slave error is high rd_data has RESET_VAL;
  
      sequence phase;
        ##1 (state==R_PHASE||state==W_PHASE) && !p_write;
      endsequence
      
        property check_slverr;
          disable iff(!p_rstn||!p_slverr)
          @(posedge p_clk)
          ( phase|-> ##1 (rd_data==RESET_VAL));
        endproperty
   
   
  //#8) Check whether control,addr bus values are stable if PREADY is not high.
  
         property stable_sig;
           disable iff(!p_rstn||state==SETUP_PHASE)
           @(posedge p_clk)
           (!p_ready |-> ($stable(addr) && $stable(p_sel) && $stable(p_write) && $stable(p_enable)));
         endproperty
  
  /* property stable_sig;
           disable iff(!p_rstn)
      @(state==R_PHASE||W_PHASE)
           !p_ready |-> ($stable(addr) && $stable(p_sel) && $stable(p_write) && $stable(p_enable));         //Can also be written like this
         endproperty                                                                                         
  */
     
 
  
  COVERAGE_RSTN: cover property(check_rstn_state);
  COVERGAE_WR  : cover property(check_state_w);
  COVERGAE_R   : cover property(check_state_r);
  
  
  
  ERR_CHECK_RST_VAL: assert property (check_rstn_state)
    $display("Successful RESET");
    else
     $error("ERROR CHECK");
    
  ERR_CHECK_WRITE: assert property (check_state_w)
      $display("WRITE SUCCESSFUL");
    
  ERR_CHECK_READ: assert property (check_state_r)
    $display("READ SUCCESSFUL");
    
  ERR_CHECK_IDLE_PHASE: assert property (back_idle)
    $display("Back IDLE Phase");
    
  ERR_CHECK_SETUP_HIGH_AGAIN: assert property (check_back_setup)
    $display("SETUP HIGH AGAIN");
    
  ERR_CHECK_READ_CONTENTS: assert property (check_rd_data)
    $display("Ready success");
    
  ERR_CHECK_SLVERR: assert property (check_slverr)
      $display("Checked for error transfers");
  
  ERR_CHECK_STABLE_SIG: assert property(stable_sig)
    $display("Checked if signals are stable");
  
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
  logic p_slverr;
  
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
    .p_enable(p_enable),
    .p_slverr(p_slverr));
  

  
  initial forever #10 p_clk<= ~p_clk;
  
  initial
    begin
      
      $monitor("[%0t] rst: %0d sel:%0d enable:%0d write:%0d addr:%0h rd_data: %0h slv_err: %0d ",$stime,p_rstn,p_sel,p_enable,p_write,p_addr,rd_data,p_slverr);
      p_clk<=1;
      
      @(posedge p_clk);
      
      p_rstn<=0; p_sel<=0; p_enable<=0; p_write<=0; p_addr<=0; 
      
      @(posedge p_clk);
      
      p_rstn<=1; p_sel<=1; p_enable<=0; p_write<=1; p_addr<='h45; p_slverr<=0; p_ready<=0;
      
      repeat(2) @(posedge p_clk);
      
      p_enable=1; p_ready<=1;
      
      @(posedge p_clk);
      
      p_sel=0; p_ready<=0;
      
     @(posedge p_clk);
      
      p_rstn<=1; p_sel<=1; p_enable<=0; p_write<=0; p_addr<='h65; p_slverr<=0;
      
      repeat(2) @(posedge p_clk);
      
      p_enable<=1; p_ready<=1;
      
      @(posedge p_clk);
      
      p_rstn<=1; p_sel<=1; p_enable<=0; p_write<=1; p_addr<='h55; p_slverr<=0; p_ready<=0;
      
      repeat(2) @(posedge p_clk);
      
      p_enable<=1; p_ready<=0;
      
      repeat(3) @(posedge clk);                 //Checked for p_ready being low in access phase
      
      p_ready<=1;
      
      @(posedge p_clk);
      
      p_rstn<=1; p_sel<=1; p_enable<=0; p_write<=0; p_addr<='h76; p_slverr<=0; p_ready<=0;
      
      repeat(2) @(posedge p_clk);
      
      p_enable<=1; p_ready<=1;
      
      @(posedge p_clk);
      
      p_rstn<=1; p_sel<=1; p_enable<=0; p_write<=0; p_addr<='h94; p_slverr<=1;
      
      repeat(4) @(posedge p_clk);
      
      $finish;
      
    end
  
  /*initial
    begin
      #320 $display("%0.2f% %",cg.get_inst_coverage());
     $finish;
    end*/
 
      
initial
  begin
  $dumpfile("dump.vcd");
  $dumpvars(1);
  end
  
  
endmodule
    
