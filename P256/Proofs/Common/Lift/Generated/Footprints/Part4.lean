import P256.Proofs.Common.Lift.Footprint
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

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG

theorem nopEffect_footprint (p : BitVec 64) (len : Nat) :
    EffectFootprint p (fun _ => nopEffect p len) ([]) []
      [.rip] :=
  ⟨.ofLocal nopEffect_local, by lift_reads [nopEffect], by lift_closed, by lift_params,
    by lift_components [nopEffect, Effect.components]⟩

theorem cmovR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (cc : BitVec 4) :
    EffectFootprint p (atFlags (condHolds cc) (cmovR16R16Effect p len dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) (condFlags cc)
      [.reg dst, .rip] :=
  ⟨LocalWith.atFlags (condHolds_congr cc) fun _ => cmovR16R16Effect_local, by lift_reads [cmovR16R16Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, cmovR16R16Effect_components]⟩

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

theorem cmovR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (cc : BitVec 4) :
    EffectFootprint p (atFlags (condHolds cc) (cmovR32M32Effect p len dst am)) (([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) (condFlags cc)
      [.reg dst, .rip] :=
  ⟨LocalWith.atFlags (condHolds_congr cc) fun _ => cmovR32M32Effect_local, by lift_reads [cmovR32M32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, cmovR32M32Effect_components]⟩

theorem cmovR64M64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (cc : BitVec 4) :
    EffectFootprint p (atFlags (condHolds cc) (cmovR64M64Effect p len dst am)) (([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) (condFlags cc)
      [.reg dst, .rip] :=
  ⟨LocalWith.atFlags (condHolds_congr cc) fun _ => cmovR64M64Effect_local, by lift_reads [cmovR64M64Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, cmovR64M64Effect_components]⟩

theorem setccR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cc : BitVec 4) :
    EffectFootprint p (atFlags (condHolds cc) (setccR8Effect p len dst)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) (condFlags cc)
      [.reg dst, .rip] :=
  ⟨LocalWith.atFlags (condHolds_congr cc) fun _ => setccR8Effect_local, by lift_reads [setccR8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, setccR8Effect_components]⟩

theorem setccM8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (cc : BitVec 4) :
    EffectFootprint p (atFlags (condHolds cc) (setccM8Effect p len am)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) (condFlags cc)
      [.rip] :=
  ⟨LocalWith.atFlags (condHolds_congr cc) fun _ => setccM8Effect_local, by lift_reads [setccM8Effect, atFlags, storeEffect], by lift_closed, by lift_params,
    by lift_components [atFlags, setccM8Effect, storeEffect_components]⟩

theorem addR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (addR32M32Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR32M32Effect_local, by lift_reads [addR32M32Effect], by lift_closed, by lift_params,
    by lift_components [addR32M32Effect_components]⟩

theorem addR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (addR64M64Effect p dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR64M64Effect_local, by lift_reads [addR64M64Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [addR64M64Effect_components]⟩

theorem addR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (addR8M8Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR8M8Effect_local, by lift_reads [addR8M8Effect], by lift_closed, by lift_params,
    by lift_components [addR8M8Effect_components]⟩

theorem orR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (orR32M32Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR32M32Effect_local, by lift_reads [orR32M32Effect], by lift_closed, by lift_params,
    by lift_components [orR32M32Effect_components]⟩

theorem orR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (orR64M64Effect p dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR64M64Effect_local, by lift_reads [orR64M64Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [orR64M64Effect_components]⟩

theorem orR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (orR8M8Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR8M8Effect_local, by lift_reads [orR8M8Effect], by lift_closed, by lift_params,
    by lift_components [orR8M8Effect_components]⟩

theorem adcR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR32M32Effect p len dst am)) (([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR32M32Effect_local, by lift_reads [adcR32M32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR32M32Effect_components]⟩

theorem adcR32M32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR32M32Effect p len dst am)) f := by
  lift_fresh [adcR32M32Effect, atFlags]

theorem adcR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR64M64Effect p dst am)) (([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR64M64Effect_local, by lift_reads [adcR64M64Effect, atFlags, movLoadLen], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR64M64Effect_components]⟩

theorem adcR64M64Effect_fresh (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR64M64Effect p dst am)) f := by
  lift_fresh [adcR64M64Effect, atFlags, movLoadLen]

theorem adcR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR8M8Effect p len dst am)) (([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR8M8Effect_local, by lift_reads [adcR8M8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR8M8Effect_components]⟩

theorem adcR8M8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR8M8Effect p len dst am)) f := by
  lift_fresh [adcR8M8Effect, atFlags]

theorem sbbR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR32M32Effect p len dst am)) (([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR32M32Effect_local, by lift_reads [sbbR32M32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR32M32Effect_components]⟩

theorem sbbR32M32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR32M32Effect p len dst am)) f := by
  lift_fresh [sbbR32M32Effect, atFlags]

theorem sbbR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR64M64Effect p dst am)) (([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR64M64Effect_local, by lift_reads [sbbR64M64Effect, atFlags, movLoadLen], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR64M64Effect_components]⟩

theorem sbbR64M64Effect_fresh (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR64M64Effect p dst am)) f := by
  lift_fresh [sbbR64M64Effect, atFlags, movLoadLen]

theorem sbbR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR8M8Effect p len dst am)) (([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR8M8Effect_local, by lift_reads [sbbR8M8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR8M8Effect_components]⟩

theorem sbbR8M8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR8M8Effect p len dst am)) f := by
  lift_fresh [sbbR8M8Effect, atFlags]

theorem andR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (andR32M32Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR32M32Effect_local, by lift_reads [andR32M32Effect], by lift_closed, by lift_params,
    by lift_components [andR32M32Effect_components]⟩

theorem andR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (andR64M64Effect p dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR64M64Effect_local, by lift_reads [andR64M64Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [andR64M64Effect_components]⟩

theorem andR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (andR8M8Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR8M8Effect_local, by lift_reads [andR8M8Effect], by lift_closed, by lift_params,
    by lift_components [andR8M8Effect_components]⟩

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

theorem subR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (subR8M8Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR8M8Effect_local, by lift_reads [subR8M8Effect], by lift_closed, by lift_params,
    by lift_components [subR8M8Effect_components]⟩

theorem xorR32M32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (xorR32M32Effect p dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR32M32Effect_local, by lift_reads [xorR32M32Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [xorR32M32Effect_components]⟩

theorem xorR32M32LowEffect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (xorR32M32LowEffect p dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR32M32LowEffect_local, by lift_reads [xorR32M32LowEffect], by lift_closed, by lift_params,
    by lift_components [xorR32M32LowEffect_components]⟩

theorem xorR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (xorR64M64Effect p dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR64M64Effect_local, by lift_reads [xorR64M64Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [xorR64M64Effect_components]⟩

theorem xorR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (xorR8M8Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR8M8Effect_local, by lift_reads [xorR8M8Effect], by lift_closed, by lift_params,
    by lift_components [xorR8M8Effect_components]⟩

theorem cmpR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (cmpR32M32Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR32M32Effect_local, by lift_reads [cmpR32M32Effect], by lift_closed, by lift_params,
    by lift_components [cmpR32M32Effect_components]⟩

theorem cmpR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (cmpR64M64Effect p dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR64M64Effect_local, by lift_reads [cmpR64M64Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [cmpR64M64Effect_components]⟩

theorem cmpR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (cmpR8M8Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR8M8Effect_local, by lift_reads [cmpR8M8Effect], by lift_closed, by lift_params,
    by lift_components [cmpR8M8Effect_components]⟩

theorem addMREffect32_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (addMREffect p len 32 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal addMREffect_local32, by lift_reads [addMREffect], by lift_closed, by lift_params,
    by lift_components [addMREffect_components]⟩

theorem addMREffect64_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (addMREffect p len 64 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal addMREffect_local64, by lift_reads [addMREffect], by lift_closed, by lift_params,
    by lift_components [addMREffect_components]⟩

theorem addMREffect8_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (addMREffect p len 8 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal addMREffect_local8, by lift_reads [addMREffect], by lift_closed, by lift_params,
    by lift_components [addMREffect_components]⟩

theorem orMREffect32_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (orMREffect p len 32 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal orMREffect_local32, by lift_reads [orMREffect], by lift_closed, by lift_params,
    by lift_components [orMREffect_components]⟩

theorem orMREffect64_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (orMREffect p len 64 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal orMREffect_local64, by lift_reads [orMREffect], by lift_closed, by lift_params,
    by lift_components [orMREffect_components]⟩

theorem orMREffect8_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (orMREffect p len 8 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal orMREffect_local8, by lift_reads [orMREffect], by lift_closed, by lift_params,
    by lift_components [orMREffect_components]⟩

theorem adcMREffect32_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (adcMREffect p len 32 src am)) (([.gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcMREffect_local32, by lift_reads [adcMREffect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcMREffect_components]⟩

theorem adcMREffect32_fresh (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcMREffect p len 32 src am)) f := by
  lift_fresh [adcMREffect, atFlags]

theorem adcMREffect64_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (adcMREffect p len 64 src am)) (([.gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcMREffect_local64, by lift_reads [adcMREffect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcMREffect_components]⟩

theorem adcMREffect64_fresh (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcMREffect p len 64 src am)) f := by
  lift_fresh [adcMREffect, atFlags]

theorem adcMREffect8_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (adcMREffect p len 8 src am)) (([.gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcMREffect_local8, by lift_reads [adcMREffect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcMREffect_components]⟩

theorem adcMREffect8_fresh (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcMREffect p len 8 src am)) f := by
  lift_fresh [adcMREffect, atFlags]

theorem sbbMREffect32_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbMREffect p len 32 src am)) (([.gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbMREffect_local32, by lift_reads [sbbMREffect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbMREffect_components]⟩

theorem sbbMREffect32_fresh (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbMREffect p len 32 src am)) f := by
  lift_fresh [sbbMREffect, atFlags]

theorem sbbMREffect64_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbMREffect p len 64 src am)) (([.gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbMREffect_local64, by lift_reads [sbbMREffect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbMREffect_components]⟩

theorem sbbMREffect64_fresh (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbMREffect p len 64 src am)) f := by
  lift_fresh [sbbMREffect, atFlags]

theorem sbbMREffect8_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbMREffect p len 8 src am)) (([.gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbMREffect_local8, by lift_reads [sbbMREffect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbMREffect_components]⟩

theorem sbbMREffect8_fresh (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbMREffect p len 8 src am)) f := by
  lift_fresh [sbbMREffect, atFlags]

theorem andMREffect32_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (andMREffect p len 32 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal andMREffect_local32, by lift_reads [andMREffect], by lift_closed, by lift_params,
    by lift_components [andMREffect_components]⟩

theorem andMREffect64_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (andMREffect p len 64 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal andMREffect_local64, by lift_reads [andMREffect], by lift_closed, by lift_params,
    by lift_components [andMREffect_components]⟩

theorem andMREffect8_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (andMREffect p len 8 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal andMREffect_local8, by lift_reads [andMREffect], by lift_closed, by lift_params,
    by lift_components [andMREffect_components]⟩

theorem subMREffect32_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (subMREffect p len 32 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal subMREffect_local32, by lift_reads [subMREffect], by lift_closed, by lift_params,
    by lift_components [subMREffect_components]⟩

theorem subMREffect64_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (subMREffect p len 64 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal subMREffect_local64, by lift_reads [subMREffect], by lift_closed, by lift_params,
    by lift_components [subMREffect_components]⟩

theorem subMREffect8_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (subMREffect p len 8 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal subMREffect_local8, by lift_reads [subMREffect], by lift_closed, by lift_params,
    by lift_components [subMREffect_components]⟩

theorem xorMREffect32_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (xorMREffect p len 32 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal xorMREffect_local32, by lift_reads [xorMREffect], by lift_closed, by lift_params,
    by lift_components [xorMREffect_components]⟩

theorem xorMREffect64_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (xorMREffect p len 64 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal xorMREffect_local64, by lift_reads [xorMREffect], by lift_closed, by lift_params,
    by lift_components [xorMREffect_components]⟩

theorem xorMREffect8_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (xorMREffect p len 8 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal xorMREffect_local8, by lift_reads [xorMREffect], by lift_closed, by lift_params,
    by lift_components [xorMREffect_components]⟩

theorem cmpMREffect32_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (cmpMREffect p len 32 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpMREffect_local, by lift_reads [cmpMREffect], by lift_closed, by lift_params,
    by lift_components [cmpMREffect_components]⟩

theorem cmpMREffect64_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (cmpMREffect p len 64 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpMREffect_local, by lift_reads [cmpMREffect], by lift_closed, by lift_params,
    by lift_components [cmpMREffect_components]⟩

theorem cmpMREffect8_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (cmpMREffect p len 8 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpMREffect_local, by lift_reads [cmpMREffect], by lift_closed, by lift_params,
    by lift_components [cmpMREffect_components]⟩

theorem testMREffect32_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (testMREffect p len 32 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal testMREffect_local, by lift_reads [testMREffect], by lift_closed, by lift_params,
    by lift_components [testMREffect_components]⟩

theorem testMREffect64_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (testMREffect p len 64 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal testMREffect_local, by lift_reads [testMREffect], by lift_closed, by lift_params,
    by lift_components [testMREffect_components]⟩

theorem testMREffect8_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (testMREffect p len 8 src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal testMREffect_local, by lift_reads [testMREffect], by lift_closed, by lift_params,
    by lift_components [testMREffect_components]⟩

theorem addM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (addM8Imm8Effect p len am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal addM8Imm8Effect_local, by lift_reads [addM8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [addM8Imm8Effect_components]⟩

theorem orM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (orM8Imm8Effect p len am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal orM8Imm8Effect_local, by lift_reads [orM8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [orM8Imm8Effect_components]⟩

theorem adcM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (adcM8Imm8Effect p len am imm)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcM8Imm8Effect_local, by lift_reads [adcM8Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcM8Imm8Effect_components]⟩

theorem adcM8Imm8Effect_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcM8Imm8Effect p len am imm)) f := by
  lift_fresh [adcM8Imm8Effect, atFlags]

theorem sbbM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbM8Imm8Effect p len am imm)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbM8Imm8Effect_local, by lift_reads [sbbM8Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbM8Imm8Effect_components]⟩

theorem sbbM8Imm8Effect_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbM8Imm8Effect p len am imm)) f := by
  lift_fresh [sbbM8Imm8Effect, atFlags]

theorem andM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (andM8Imm8Effect p len am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal andM8Imm8Effect_local, by lift_reads [andM8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [andM8Imm8Effect_components]⟩

theorem subM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (subM8Imm8Effect p len am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal subM8Imm8Effect_local, by lift_reads [subM8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [subM8Imm8Effect_components]⟩

theorem xorM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (xorM8Imm8Effect p len am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal xorM8Imm8Effect_local, by lift_reads [xorM8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [xorM8Imm8Effect_components]⟩

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

theorem addMImm8Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (addMImm8Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal addMImm8Effect_local32, by lift_reads [addMImm8Effect], by lift_closed, by lift_params,
    by lift_components [addMImm8Effect_components]⟩

theorem addMImm8Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (addMImm8Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal addMImm8Effect_local64, by lift_reads [addMImm8Effect], by lift_closed, by lift_params,
    by lift_components [addMImm8Effect_components]⟩

theorem orMImm8Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (orMImm8Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal orMImm8Effect_local32, by lift_reads [orMImm8Effect], by lift_closed, by lift_params,
    by lift_components [orMImm8Effect_components]⟩

theorem orMImm8Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (orMImm8Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal orMImm8Effect_local64, by lift_reads [orMImm8Effect], by lift_closed, by lift_params,
    by lift_components [orMImm8Effect_components]⟩

theorem adcMImm8Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (adcMImm8Effect p len 32 am imm)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcMImm8Effect_local32, by lift_reads [adcMImm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcMImm8Effect_components]⟩

theorem adcMImm8Effect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcMImm8Effect p len 32 am imm)) f := by
  lift_fresh [adcMImm8Effect, atFlags]

theorem adcMImm8Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (adcMImm8Effect p len 64 am imm)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcMImm8Effect_local64, by lift_reads [adcMImm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcMImm8Effect_components]⟩

theorem adcMImm8Effect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcMImm8Effect p len 64 am imm)) f := by
  lift_fresh [adcMImm8Effect, atFlags]

theorem sbbMImm8Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbMImm8Effect p len 32 am imm)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbMImm8Effect_local32, by lift_reads [sbbMImm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbMImm8Effect_components]⟩

theorem sbbMImm8Effect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbMImm8Effect p len 32 am imm)) f := by
  lift_fresh [sbbMImm8Effect, atFlags]

theorem sbbMImm8Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbMImm8Effect p len 64 am imm)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbMImm8Effect_local64, by lift_reads [sbbMImm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbMImm8Effect_components]⟩

theorem sbbMImm8Effect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbMImm8Effect p len 64 am imm)) f := by
  lift_fresh [sbbMImm8Effect, atFlags]

theorem andMImm8Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (andMImm8Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal andMImm8Effect_local32, by lift_reads [andMImm8Effect], by lift_closed, by lift_params,
    by lift_components [andMImm8Effect_components]⟩

theorem andMImm8Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (andMImm8Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal andMImm8Effect_local64, by lift_reads [andMImm8Effect], by lift_closed, by lift_params,
    by lift_components [andMImm8Effect_components]⟩

theorem subMImm8Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (subMImm8Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal subMImm8Effect_local32, by lift_reads [subMImm8Effect], by lift_closed, by lift_params,
    by lift_components [subMImm8Effect_components]⟩

theorem subMImm8Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (subMImm8Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal subMImm8Effect_local64, by lift_reads [subMImm8Effect], by lift_closed, by lift_params,
    by lift_components [subMImm8Effect_components]⟩

theorem xorMImm8Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (xorMImm8Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal xorMImm8Effect_local32, by lift_reads [xorMImm8Effect], by lift_closed, by lift_params,
    by lift_components [xorMImm8Effect_components]⟩

theorem xorMImm8Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (xorMImm8Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal xorMImm8Effect_local64, by lift_reads [xorMImm8Effect], by lift_closed, by lift_params,
    by lift_components [xorMImm8Effect_components]⟩

theorem cmpMImm8Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (cmpMImm8Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpMImm8Effect_local, by lift_reads [cmpMImm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpMImm8Effect_components]⟩

theorem cmpMImm8Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (cmpMImm8Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpMImm8Effect_local, by lift_reads [cmpMImm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpMImm8Effect_components]⟩

theorem addMImm32Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (addMImm32Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal addMImm32Effect_local32, by lift_reads [addMImm32Effect], by lift_closed, by lift_params,
    by lift_components [addMImm32Effect_components]⟩

theorem addMImm32Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (addMImm32Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal addMImm32Effect_local64, by lift_reads [addMImm32Effect], by lift_closed, by lift_params,
    by lift_components [addMImm32Effect_components]⟩

theorem orMImm32Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (orMImm32Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal orMImm32Effect_local32, by lift_reads [orMImm32Effect], by lift_closed, by lift_params,
    by lift_components [orMImm32Effect_components]⟩

theorem orMImm32Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (orMImm32Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal orMImm32Effect_local64, by lift_reads [orMImm32Effect], by lift_closed, by lift_params,
    by lift_components [orMImm32Effect_components]⟩

theorem adcMImm32Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (adcMImm32Effect p len 32 am imm)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcMImm32Effect_local32, by lift_reads [adcMImm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcMImm32Effect_components]⟩

theorem adcMImm32Effect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcMImm32Effect p len 32 am imm)) f := by
  lift_fresh [adcMImm32Effect, atFlags]

theorem adcMImm32Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (adcMImm32Effect p len 64 am imm)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcMImm32Effect_local64, by lift_reads [adcMImm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcMImm32Effect_components]⟩

theorem adcMImm32Effect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcMImm32Effect p len 64 am imm)) f := by
  lift_fresh [adcMImm32Effect, atFlags]

theorem sbbMImm32Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbMImm32Effect p len 32 am imm)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbMImm32Effect_local32, by lift_reads [sbbMImm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbMImm32Effect_components]⟩

theorem sbbMImm32Effect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbMImm32Effect p len 32 am imm)) f := by
  lift_fresh [sbbMImm32Effect, atFlags]

theorem sbbMImm32Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbMImm32Effect p len 64 am imm)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbMImm32Effect_local64, by lift_reads [sbbMImm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbMImm32Effect_components]⟩

theorem sbbMImm32Effect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbMImm32Effect p len 64 am imm)) f := by
  lift_fresh [sbbMImm32Effect, atFlags]

theorem andMImm32Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (andMImm32Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal andMImm32Effect_local32, by lift_reads [andMImm32Effect], by lift_closed, by lift_params,
    by lift_components [andMImm32Effect_components]⟩

theorem andMImm32Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (andMImm32Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal andMImm32Effect_local64, by lift_reads [andMImm32Effect], by lift_closed, by lift_params,
    by lift_components [andMImm32Effect_components]⟩

theorem subMImm32Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (subMImm32Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal subMImm32Effect_local32, by lift_reads [subMImm32Effect], by lift_closed, by lift_params,
    by lift_components [subMImm32Effect_components]⟩

theorem subMImm32Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (subMImm32Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal subMImm32Effect_local64, by lift_reads [subMImm32Effect], by lift_closed, by lift_params,
    by lift_components [subMImm32Effect_components]⟩

theorem xorMImm32Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (xorMImm32Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal xorMImm32Effect_local32, by lift_reads [xorMImm32Effect], by lift_closed, by lift_params,
    by lift_components [xorMImm32Effect_components]⟩

theorem xorMImm32Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (xorMImm32Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal xorMImm32Effect_local64, by lift_reads [xorMImm32Effect], by lift_closed, by lift_params,
    by lift_components [xorMImm32Effect_components]⟩

theorem cmpMImm32Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (cmpMImm32Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpMImm32Effect_local, by lift_reads [cmpMImm32Effect], by lift_closed, by lift_params,
    by lift_components [cmpMImm32Effect_components]⟩

end P256.Proofs.Lift
