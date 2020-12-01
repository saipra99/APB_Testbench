module APB_slave#(A_WIDTH=8, D_WIDTH=8, DEPTH=16,RESET_VAL='h12)
  ( input logic p_clk,
    input logic p_rstn,
    input logic p_enable,
    input logic p_sel,
    input logic  p_write,
    input logic [A_WIDTH-1:0] p_addr,
    input logic [D_WIDTH-1:0] wr_data,
    output logic [D_WIDTH-1:0] rd_data,
   output logic p_ready);
  
  
  parameter IDLE_PHASE=0,
            SETUP_PHASE=1,
            W_PHASE=2,
            R_PHASE=3;
  
  logic [1:0] state;
  logic [D_WIDTH-1:0] apb_mem[DEPTH];
  
  always @(posedge p_clk)
    begin
      if(!p_rstn)
        begin
          rd_data=RESET_VAL;
          ERR_RD_DATA: assert(rd_data=='h12)
          else
            $display("Failed");
          state<=IDLE_PHASE;
          p_ready<=0;
        end
      else
        begin
        case(state)
          
          IDLE_PHASE:
             begin
               rd_data<=0;
               p_ready<=0;
               if(p_rstn)
               state<=SETUP_PHASE;
             end
          
          
          SETUP_PHASE:
            begin
              if(p_sel && p_rstn)
                begin
                  if(p_write)
                    state<=W_PHASE;
                  else
                    state<=R_PHASE;
                end
              else
                state<=IDLE_PHASE;
            end
          
          W_PHASE:
            begin
              if(p_sel && p_enable && p_rstn)
                begin
                  apb_mem[p_addr]<=wr_data;
                end
              
               state<=SETUP_PHASE;
            end
          
          R_PHASE:
            begin
              if(p_sel && p_enable && p_rstn)
                begin
                  rd_data<=apb_mem[p_addr];
                end
              state<=SETUP_PHASE;
            end
        endcase
        end
    end
endmodule  

// Code your testbench here
// or browse Examples
// Code your testbench here
// or browse Examples
