import K256.Proofs.Common.Lift.Footprint
import X86Proofs.Instructions.Cmp.Generated.MImm32.Triple
import X86Proofs.Instructions.Dec.Generated.M.Triple
import X86Proofs.Instructions.Dec.Generated.M8.Triple
import X86Proofs.Instructions.Inc.Generated.M.Triple
import X86Proofs.Instructions.Inc.Generated.M8.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple
import X86Proofs.Instructions.Mov.Generated.MImm32C7.Triple
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Mov.Generated.R8M8.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Neg.Generated.M.Triple
import X86Proofs.Instructions.Neg.Generated.M8.Triple
import X86Proofs.Instructions.Not.Generated.M.Triple
import X86Proofs.Instructions.Not.Generated.M8.Triple
import X86Proofs.Instructions.Rol.Generated.M.Triple
import X86Proofs.Instructions.Rol.Generated.M8.Triple
import X86Proofs.Instructions.Rol.Generated.M8Cl.Triple
import X86Proofs.Instructions.Rol.Generated.MCl.Triple
import X86Proofs.Instructions.Ror.Generated.M.Triple
import X86Proofs.Instructions.Ror.Generated.M8.Triple
import X86Proofs.Instructions.Ror.Generated.M8Cl.Triple
import X86Proofs.Instructions.Ror.Generated.MCl.Triple
import X86Proofs.Instructions.Sal.Generated.M.Triple
import X86Proofs.Instructions.Sal.Generated.M8.Triple
import X86Proofs.Instructions.Sal.Generated.M8Cl.Triple
import X86Proofs.Instructions.Sal.Generated.MCl.Triple
import X86Proofs.Instructions.Sar.Generated.M.Triple
import X86Proofs.Instructions.Sar.Generated.M8.Triple
import X86Proofs.Instructions.Sar.Generated.M8Cl.Triple
import X86Proofs.Instructions.Sar.Generated.MCl.Triple
import X86Proofs.Instructions.Shl.Generated.M.Triple
import X86Proofs.Instructions.Shl.Generated.M8.Triple
import X86Proofs.Instructions.Shl.Generated.M8Cl.Triple
import X86Proofs.Instructions.Shl.Generated.MCl.Triple
import X86Proofs.Instructions.Shr.Generated.M.Triple
import X86Proofs.Instructions.Shr.Generated.M8.Triple
import X86Proofs.Instructions.Shr.Generated.M8Cl.Triple
import X86Proofs.Instructions.Shr.Generated.MCl.Triple
import X86Proofs.Instructions.Test.Generated.MImm32.Triple
namespace K256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG

theorem movR32M32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movR32M32Effect p dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR32M32Effect_local, by lift_reads [movR32M32Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [movR32M32Effect_components]⟩

theorem movR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movR64M64Effect p dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR64M64Effect_local, by lift_reads [movR64M64Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [movR64M64Effect_components]⟩

theorem movR32M32LowEffect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movR32M32LowEffect p dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR32M32LowEffect_local, by lift_reads [movR32M32LowEffect], by lift_closed, by lift_params,
    by lift_components [movR32M32LowEffect_components]⟩

theorem movM16Imm16Effect_footprint (p : BitVec 64) (am : AddrMode) (imm : BitVec 16) :
    EffectFootprint p (movM16Imm16Effect p am imm) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM16Imm16Effect_local, by lift_reads [movM16Imm16Effect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM16Imm16Effect_components]⟩

theorem movM32R32Effect_footprint (p : BitVec 64) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movM32R32Effect p src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM32R32Effect_local, by lift_reads [movM32R32Effect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM32R32Effect_components]⟩

theorem movM64Imm32Effect_footprint (p : BitVec 64) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (movM64Imm32Effect p am imm) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM64Imm32Effect_local, by lift_reads [movM64Imm32Effect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM64Imm32Effect_components]⟩

theorem movM64R64Effect_footprint (p : BitVec 64) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movM64R64Effect p src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM64R64Effect_local, by lift_reads [movM64R64Effect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM64R64Effect_components]⟩

theorem movM8Imm8Effect_footprint (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (movM8Imm8Effect p am imm) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM8Imm8Effect_local, by lift_reads [movM8Imm8Effect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM8Imm8Effect_components]⟩

theorem movM16R16Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movM16R16Effect p len src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM16R16Effect_local, by lift_reads [movM16R16Effect, storeEffect], by lift_closed, by lift_params,
    by lift_components [movM16R16Effect, storeEffect_components]⟩

theorem movM32R32LowEffect_footprint (p : BitVec 64) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movM32R32LowEffect p src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM32R32LowEffect_local, by lift_reads [movM32R32LowEffect, storeEffect], by lift_closed, by lift_params,
    by lift_components [movM32R32LowEffect, storeEffect_components]⟩

theorem movM8R8Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movM8R8Effect p len src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM8R8Effect_local, by lift_reads [movM8R8Effect, storeEffect], by lift_closed, by lift_params,
    by lift_components [movM8R8Effect, storeEffect_components]⟩

theorem movM32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (movM32Imm32Effect p len am imm) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM32Imm32Effect_local, by lift_reads [movM32Imm32Effect, storeEffect], by lift_closed, by lift_params,
    by lift_components [movM32Imm32Effect, storeEffect_components]⟩

theorem leaR64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (leaR64Effect p dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal leaR64Effect_local, by lift_reads [leaR64Effect, leaLen], by lift_closed, by lift_params,
    by lift_components [leaR64Effect_components]⟩

theorem leaR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (leaR32Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal leaR32Effect_local, by lift_reads [leaR32Effect, leaSpec], by lift_closed, by lift_params,
    by lift_components [leaR32Effect_components]⟩

end K256.Proofs.Lift
