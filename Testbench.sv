// Code your testbench here
// or browse Examples
import uvm_pkg::*;
`include "uvm_macros.svh"

class Packet extends uvm_sequence_item;
  
  function new(string name="Packet");
    super.new(name);
  endfunction
  
  rand bit [15:0] p_addr;
  rand bit p_write;
  rand bit [31:0] p_wdata;
  bit [31:0] p_rdata;
       bit p_ready;
  
  `uvm_object_utils_begin(Packet)
    `uvm_field_int(p_addr,UVM_ALL_ON)
    `uvm_field_int(p_wdata, UVM_ALL_ON)
    `uvm_field_int(p_rdata,UVM_ALL_ON)
    `uvm_field_int(p_write,UVM_ALL_ON)
  `uvm_object_utils_end
  
  function string convert2str() ;
    return $sformatf("addr =0x%0h write =%0d wdata= 0x%0h rdata =0x%0h", p_addr,p_write, p_wdata,p_rdata);
  endfunction
  
endclass

//***********************SEQUENCE***************************

class base_sequence extends uvm_sequence #(Packet);
  `uvm_object_utils(base_sequence)
  
  function new(string name="base_sequence");
    super.new(name);
  endfunction
  
  rand int num;
  
  constraint num_sequences{soft num inside{[7:15]};}
  
  task body();
    
    for(int i=0;i<num;i=i+1)
      begin
        Packet apb_pkt=Packet::type_id::create("apb_pkt");
        
        start_item(apb_pkt);
        
        void'(apb_pkt.randomize());
        
        finish_item(apb_pkt);
        
      end
    `uvm_info(get_type_name(),$sformatf("Done generating %0d items",num),UVM_LOW)
    
  endtask
endclass

//******************CONFIG************************

class apb_config extends uvm_object;
  
  `uvm_object_utils(apb_config)
  
  function new(string name="apb_config");
    super.new(name);
  endfunction
  
  virtual apb_if apb_vif;
  bit p_valid_val;
endclass


//*********************DRIVER************************

class driver extends uvm_driver #(Packet);  //REQ,RSP
  
  `uvm_component_utils(driver)
  
  function new(string name,uvm_component parent);
    super.new(name,parent);
  endfunction
  
  apb_config m_cfg;
  
  virtual apb_if m_vif;
  
 // uvm_analysis_port#(Packet) m_analy_port;
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    //m_vif=m_cfg.apb_vif;
    if(! uvm_config_db #(virtual apb_if)::get(this,"", "apb_if", m_vif))
      `uvm_fatal(get_type_name(),"Couldn't get vif")
  endfunction
  
  //Packet m_pkt;  One can also  use this handle
  
  virtual task reset_phase(uvm_phase phase);
    super.reset_phase(phase);        // IDLE-Phase
    phase.raise_objection(this);
    m_vif.paddr=0;
    m_vif.psel=0;
    m_vif.penable=0;
    m_vif.pready=0;
    m_vif.pwdata=0;
    m_vif.pwrite=0;
    phase.drop_objection(this);
  endtask
   
  
  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    forever
      begin
        seq_item_port.get_next_item(req);
        
        drive_item(req);
        
        seq_item_port.item_done();

      end
  endtask
  
  
  virtual task drive_item(REQ req); // REQ type=uvm_sequence item
    
   m_vif.paddr=req.p_addr;
   m_vif.pwrite=req.p_write;
   m_vif.pwdata=req.p_wdata;
   m_vif.psel=1;
   m_vif.penable=0;
    
    @(m_vif.cb);  //Set-UP phase
    m_vif.penable=1;
    
    do
      @(m_vif.cb);
    while(!m_vif.cb.pready); //Should continue with same addr,data,en,sel
    
    if(!m_vif.pwrite)
      req.p_rdata=m_vif.cb.prdata;
  endtask
endclass

    
    
//*******************MONITOR************************

class monitor extends uvm_monitor;
  
  `uvm_component_utils(monitor)
  
  function new(string name,uvm_component parent);
    super.new(name,parent);
  endfunction
  
  uvm_analysis_port #(Packet) mon_analy_port;
  
  apb_config m_cfg;
  virtual apb_if m_vif;
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    //m_vif=m_cfg.apb_vif;
    
    if(!uvm_config_db#(virtual apb_if)::get(this,"", "apb_if",m_vif))
      `uvm_fatal(get_type_name(),"Couldn't get vif handle")
    mon_analy_port=new("mon_analy_port",this);
  endfunction
  
  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    forever
      begin
        @(m_vif.cb);
        if(m_vif.cb.pready && m_vif.penable && m_vif.psel && m_vif.presetn)
          begin
            Packet apb_pkt=Packet::type_id::create("apb_pkt");
            apb_pkt.p_addr=m_vif.paddr;
            apb_pkt.p_write=m_vif.pwrite;
            
            
                if(apb_pkt.p_write)
                  apb_pkt.p_wdata=m_vif.pwdata;
                else
                  apb_pkt.p_rdata=m_vif.prdata;
            /*else
              begin
                apb_pkt.p_wdata=m_vif.pwdata;
                apb_pkt.p_rdata=m_vif.prdata;
              end*/
            
            mon_analy_port.write(apb_pkt);
          end
      end
  endtask
endclass


//***********************AGENT*************************
    
class apb_agent extends uvm_agent;
  
  `uvm_component_utils(apb_agent)
  
  function new(string name,uvm_component parent);
    super.new(name,parent);
  endfunction
  
  driver drv;
  monitor mon;
  uvm_sequencer #(Packet) seqr;
  apb_config m_cfg;
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    
    /*if(!uvm_config_db#(apb_config)::get(this,"*","m_cfg",m_cfg))
      `uvm_fatal(get_type_name(),"Couldn't get the config object");*/
    
    if(get_is_active())
      begin
        seqr=uvm_sequencer#(Packet)::type_id::create("sqr",this);
        drv = driver::type_id::create("drv",this);
      end
    
    mon=monitor::type_id::create("mon",this);
    
    //drv.m_cfg=m_cfg;
    //mon.m_cfg=m_cfg;
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    if(get_is_active)
    drv.seq_item_port.connect(seqr.seq_item_export);
  endfunction
endclass



//***************SCOREBOARD*****************************

class scoreboard extends uvm_scoreboard;
  `uvm_component_utils(scoreboard)
  
  function new(string name,uvm_component parent);
    super.new(name,parent);
  endfunction
  
  uvm_analysis_imp#(Packet, scoreboard) sbd_analy_imp;
  
   function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    sbd_analy_imp=new("sbd_analy_imp",this);
  endfunction
  
  Packet m_apb_pkt[$]; //An unbounded queue
  
  virtual function void write(Packet pkt);
    
    `uvm_info(get_type_name(),$sformatf("Got packet %s ",pkt.convert2str()),UVM_LOW)
      m_apb_pkt.push_back(pkt);
  endfunction
endclass


//*********************ENVIRONMENT****************
  
class apb_environment extends uvm_env;
  `uvm_component_utils(apb_environment)
  
  apb_agent apb_agnt;
  scoreboard sbd;
  
  function new(string name,uvm_component parent);
    super.new(name,parent);
  endfunction
  
  
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    
    apb_agnt = apb_agent::type_id::create("apb_agnt",this);
    sbd =scoreboard::type_id::create("sbd",this);
  endfunction
  
  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    
    apb_agnt.mon.mon_analy_port.connect(sbd.sbd_analy_imp);
  endfunction
endclass

//*************INTERFACE************************

interface apb_if(input p_clk);
  
  logic [15:0] paddr;
  logic [31:0] pwdata;
  logic [31:0] prdata;
  logic psel;
  logic pready;
  logic penable;
  logic presetn;
  logic pwrite;
  logic pslverr;
  
  clocking cb @(posedge p_clk);
    input pready;
    input pslverr;
    input prdata;
    output paddr,psel,penable,pwdata,pwrite;
  endclocking
endinterface


//**********************TEST***********************

class apb_test extends uvm_test;
  
  `uvm_component_utils(apb_test)
  
  function new(string name,uvm_component parent);
    super.new(name,parent);
  endfunction
  
  apb_environment env;
  apb_config m_cfg;
  base_sequence m_apb_seq;
  
  virtual apb_if apb_vif;
  
  virtual function void build_phase(uvm_phase phase);
    
    uvm_factory factory = uvm_factory::get();
    super.build_phase(phase);
    
    env=apb_environment::type_id::create("env",this);
    
    if(!uvm_config_db#(virtual apb_if)::get(this,"","apb_if",apb_vif))
      `uvm_fatal(get_type_name(),"Couldn't get vif handle from configuration object")
      
    uvm_config_db#(virtual apb_if)::set(this,"env.apb_agnt.*","apb_if",apb_vif);
      
     /* m_cfg=apb_config::type_id::create("m_cfg");
      m_cfg.apb_vif=apb_vif;
    
    uvm_config_db#(apb_config)::set(this,"*apb_agnt*","m_cfg",m_cfg);*/
   
    m_apb_seq=base_sequence::type_id::create("m_apb_seq");
    
  endfunction
  
  
   function void end_of_elaboration_phase(uvm_phase phase);
     super.end_of_elaboration_phase(phase);
     this.print();
     //factory.print();
     
     `uvm_info(get_type_name(),"End of elaboration phase debug",UVM_LOW)
   endfunction
  
     
     
  virtual task reset_phase(uvm_phase phase);
    super.reset_phase(phase);
    phase.raise_objection(this);
    
    apb_vif.presetn=0;
    repeat(5) @(apb_vif.cb);
    apb_vif.presetn=1;
    phase.drop_objection(this);
  endtask
  
  virtual task main_phase(uvm_phase phase);
    super.main_phase(phase);
    
    
    phase.raise_objection(this);
    
    void'(m_apb_seq.randomize() with {num==15;});
    
    m_apb_seq.start(env.apb_agnt.seqr);
    
    phase.drop_objection(this);
  endtask
  
    
endclass


//****************TESTBENCH_TOP**************************

module top;
  
  bit clk;
  
  always #10 clk=~clk;
  
  apb_if m_apb_if(clk);
  
  initial
    begin
  uvm_config_db#(virtual apb_if)::set(null,"uvm_test_top", "apb_if", m_apb_if);
      run_test("apb_test");
    end
  
  assign m_apb_if.pslverr=0;  // Not used
  
  initial
  begin
    m_apb_if.pready<=0;
    forever 
      begin
        repeat($urandom_range(1,4)) @(posedge clk);
        m_apb_if.pready<=~m_apb_if.pready;
      end
  end
  
 
  initial 
    begin
    m_apb_if.prdata <= 0;
    forever begin
      repeat ($urandom_range(2,6)) @ (posedge clk);
      m_apb_if.prdata <= $random;
    end
  end
  
endmodule
