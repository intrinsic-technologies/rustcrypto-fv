import K256.Proofs.Common.Lift.Footprint
import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Sec1.LIR.Generated.Footprints
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.R8M8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Cmp.Generated.MR.Triple
import X86Proofs.Instructions.Imul.Generated.RRImm32.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Or.Generated.R8M8.Triple
import X86Proofs.Instructions.Sar.Generated.Cl.Triple
import X86Proofs.Instructions.Sar.Generated.R.Triple
import X86Proofs.Instructions.Sar.Generated.R8.Triple
import X86Proofs.Instructions.Sar.Generated.R8Cl.Triple
import X86Proofs.Instructions.Sbb.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.R8.Triple

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

open K256.Proofs.Sec1.LIR

theorem sbbR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR64R64Effect p dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR64R64Effect_local, by lift_reads [sbbR64R64Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR64R64Effect_components]⟩

theorem sbbR64R64Effect_fresh (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR64R64Effect p dst src)) f := by
  lift_fresh [sbbR64R64Effect, atFlags]

theorem xorR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (xorR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR8R8Effect_local, by lift_reads [xorR8R8Effect], by lift_closed, by lift_params,
    by lift_components [xorR8R8Effect_components]⟩

theorem notR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (notR32Effect p len dst) ([.gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal notR32Effect_local, by lift_reads [notR32Effect], by lift_closed, by lift_params,
    by lift_components [notR32Effect_components]⟩

theorem sarR64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (sarR64Effect p len dst c) f := by
  lift_fresh [sarR64Effect, sarFlags]

theorem sarR64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (sarR64ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR64ClEffect_local, by lift_reads [sarR64ClEffect, sarR64Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR64ClEffect_components]⟩

theorem sarR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (sarR8Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR8Effect_local, by lift_reads [sarR8Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR8Effect_components]⟩

theorem sarR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (sarR8Effect p len dst c) f := by
  lift_fresh [sarR8Effect, sarFlags]

theorem sarR8ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (sarR8ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR8ClEffect_local, by lift_reads [sarR8ClEffect, sarR8Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR8ClEffect_components]⟩

theorem imulR64R64Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (imulR64R64Imm32Effect p len dst src imm) ([.gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR64R64Imm32Effect_local, by lift_reads [imulR64R64Imm32Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR64R64Imm32Effect_components]⟩

theorem addR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (addR8M8Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR8M8Effect_local, by lift_reads [addR8M8Effect], by lift_closed, by lift_params,
    by lift_components [addR8M8Effect_components]⟩

theorem orR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (orR8M8Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR8M8Effect_local, by lift_reads [orR8M8Effect], by lift_closed, by lift_params,
    by lift_components [orR8M8Effect_components]⟩

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

theorem addM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (addM8Imm8Effect p len am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal addM8Imm8Effect_local, by lift_reads [addM8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [addM8Imm8Effect_components]⟩

end K256.Proofs.Generate.LIR
