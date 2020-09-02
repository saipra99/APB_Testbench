# APB_Testbench

1) Verification of AHB-APB bridge that could send transaction from high speed connect AXI/AHB to low speed APB bus. I have tried to check whether all my transactions are successfully sent, but and haven't implemented any checker for the correctness of data transfer.(Using UVM Methodology

2) To increase the observability of design I have also added SVA concurrent assertions with the help of bind construct that checks for appropiate control signal being toggled.
 (Aim of each assertions is commented).

