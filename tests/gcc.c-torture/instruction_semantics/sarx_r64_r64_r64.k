// Autogenerated using stratification.
requires "x86-configuration.k"

module SARX-R64-R64-R64
  imports X86-CONFIGURATION

  rule <k>
    execinstr (sarx R1:R64, R2:R64, R3:R64,  .Operands) => execinstr (sarxq R1:R64, R2:R64, R3:R64,  .Operands)
  ...</k>
      
endmodule

