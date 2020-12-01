# APB_Testbench

1)  AHB-APB bridge that could send transaction from high speed connect AXI/AHB to low speed APB bus. I have tried to model a simple DUT to check whether all my transactions are successfully sent, but and haven't implemented any checker for the correctness of data transfer.(Using UVM Methodology).

2) To increase the observability of design  I have also added SVA assertions using bind construct to my APB slave that checks for appropiate control signal being toggled.
 (Aim of each assertions is commented).

