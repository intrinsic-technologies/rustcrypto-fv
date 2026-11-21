import K256.Proofs.Common.Lift.Footprint
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.M8R8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Adc.Generated.R8M8.Triple
import X86Proofs.Instructions.Adc.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.M8R8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.R8M8.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.M8R8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.R8M8.Triple
import X86Proofs.Instructions.And.Generated.RM.Triple
import X86Proofs.Instructions.Cmov.Generated.RM.Triple
import X86Proofs.Instructions.Cmov.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.M8R8.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm32.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm8.Triple
import X86Proofs.Instructions.Cmp.Generated.MR.Triple
import X86Proofs.Instructions.Cmp.Generated.R8M8.Triple
import X86Proofs.Instructions.Cmp.Generated.RM.Triple
import X86Proofs.Instructions.Nop.Triple
import X86Proofs.Instructions.NopMem.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.M8R8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.R8M8.Triple
import X86Proofs.Instructions.Or.Generated.RM.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.M8R8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.R8M8.Triple
import X86Proofs.Instructions.Sbb.Generated.RM.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Setcc.Generated.R8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8R8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.R8M8.Triple
import X86Proofs.Instructions.Sub.Generated.RM.Triple
import X86Proofs.Instructions.Test.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Test.Generated.M8R8.Triple
import X86Proofs.Instructions.Test.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.M8R8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.R8M8.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
namespace K256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG

theorem nopEffect_footprint (p : BitVec 64) (len : Nat) :
    EffectFootprint p (fun _ => nopEffect p len) ([]) []
      [.rip] :=
  ⟨.ofLocal nopEffect_local, by lift_reads [nopEffect], by lift_closed, by lift_params,
    by lift_components [nopEffect, Effect.components]⟩

theorem cmovR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (cc : BitVec 4) :
    EffectFootprint p (atFlags (condHolds cc) (cmovR32R32Effect p len dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) (condFlags cc)
      [.reg dst, .rip] :=
  ⟨LocalWith.atFlags (condHolds_congr cc) fun _ => cmovR32R32Effect_local, by lift_reads [cmovR32R32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, cmovR32R32Effect_components]⟩

theorem cmovR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (cc : BitVec 4) :
    EffectFootprint p (atFlags (condHolds cc) (cmovR64R64Effect p len dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) (condFlags cc)
      [.reg dst, .rip] :=
  ⟨LocalWith.atFlags (condHolds_congr cc) fun _ => cmovR64R64Effect_local, by lift_reads [cmovR64R64Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, cmovR64R64Effect_components]⟩

theorem setccR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cc : BitVec 4) :
    EffectFootprint p (atFlags (condHolds cc) (setccR8Effect p len dst)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) (condFlags cc)
      [.reg dst, .rip] :=
  ⟨LocalWith.atFlags (condHolds_congr cc) fun _ => setccR8Effect_local, by lift_reads [setccR8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, setccR8Effect_components]⟩

theorem subR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (subR32M32Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR32M32Effect_local, by lift_reads [subR32M32Effect], by lift_closed, by lift_params,
    by lift_components [subR32M32Effect_components]⟩

theorem subR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (subR64M64Effect p dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR64M64Effect_local, by lift_reads [subR64M64Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [subR64M64Effect_components]⟩

theorem cmpM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (cmpM8Imm8Effect p len am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpM8Imm8Effect_local, by lift_reads [cmpM8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpM8Imm8Effect_components]⟩

theorem testM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (testM8Imm8Effect p len am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal testM8Imm8Effect_local, by lift_reads [testM8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [testM8Imm8Effect_components]⟩

theorem cmpMImm8Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (cmpMImm8Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpMImm8Effect_local, by lift_reads [cmpMImm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpMImm8Effect_components]⟩

end K256.Proofs.Lift
