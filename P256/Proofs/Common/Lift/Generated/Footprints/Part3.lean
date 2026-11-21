import P256.Proofs.Common.Lift.Footprint
import X86Proofs.Instructions.Bsf.Generated.RM.Triple
import X86Proofs.Instructions.Bsf.Generated.RR.Triple
import X86Proofs.Instructions.Bsr.Generated.RM.Triple
import X86Proofs.Instructions.Bsr.Generated.RR.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Imul.Generated.M.Triple
import X86Proofs.Instructions.Imul.Generated.M8.Triple
import X86Proofs.Instructions.Imul.Generated.R.Triple
import X86Proofs.Instructions.Imul.Generated.R8.Triple
import X86Proofs.Instructions.Imul.Generated.RM.Triple
import X86Proofs.Instructions.Imul.Generated.RMImm32.Triple
import X86Proofs.Instructions.Imul.Generated.RMImm8.Triple
import X86Proofs.Instructions.Imul.Generated.RR.Triple
import X86Proofs.Instructions.Imul.Generated.RRImm32.Triple
import X86Proofs.Instructions.Imul.Generated.RRImm8.Triple
import X86Proofs.Instructions.Mov.Generated.R16Imm16.Triple
import X86Proofs.Instructions.Mov.Generated.R8.Triple
import X86Proofs.Instructions.Mov.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Mov.Generated.R8Imm8C6.Triple
import X86Proofs.Instructions.Mov.Generated.R8Rev.Triple
import X86Proofs.Instructions.Mov.Generated.RImmC7.Triple
import X86Proofs.Instructions.Mov.Generated.RR16.Triple
import X86Proofs.Instructions.Mov.Generated.RRRev.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Movsx.Generated.RM16.Triple
import X86Proofs.Instructions.Movsx.Generated.RM8.Triple
import X86Proofs.Instructions.Movsx.Generated.RR16.Triple
import X86Proofs.Instructions.Movsx.Generated.RR8.Triple
import X86Proofs.Instructions.Movsxd.Generated.RM32.Triple
import X86Proofs.Instructions.Movsxd.Generated.RR32.Triple
import X86Proofs.Instructions.Movzx.Generated.RM16.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Movzx.Generated.RR16.Triple
import X86Proofs.Instructions.Movzx.Generated.RR8.Triple
import X86Proofs.Instructions.Mul.Generated.M.Triple
import X86Proofs.Instructions.Mul.Generated.M8.Triple
import X86Proofs.Instructions.Mul.Generated.R.Triple
import X86Proofs.Instructions.Mul.Generated.R8.Triple
import X86Proofs.Instructions.Rol.Generated.R8Cl.Triple
import X86Proofs.Instructions.Ror.Generated.R8Cl.Triple
import X86Proofs.Instructions.Sal.Generated.R8.Triple
import X86Proofs.Instructions.Sal.Generated.R8Cl.Triple
import X86Proofs.Instructions.Sar.Generated.R8.Triple
import X86Proofs.Instructions.Sar.Generated.R8Cl.Triple
import X86Proofs.Instructions.Shl.Generated.R8Cl.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shld.Generated.RRCl.Triple
import X86Proofs.Instructions.Shld.Generated.RRImm8.Triple
import X86Proofs.Instructions.Shr.Generated.R8.Triple
import X86Proofs.Instructions.Shr.Generated.R8Cl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.RRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.RRImm8.Triple
import X86Proofs.Instructions.Xchg.Generated.Acc.Triple
import X86Proofs.Instructions.Xchg.Generated.R8.Triple
import X86Proofs.Instructions.Xchg.Generated.RR.Triple

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG

theorem salR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (salR8Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal salR8Effect_local, by lift_reads [salR8Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salR8Effect_components]⟩

theorem salR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (salR8Effect p len dst c) f := by
  lift_fresh [salR8Effect, shlFlags]

theorem shrR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shrR8Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR8Effect_local, by lift_reads [shrR8Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR8Effect_components]⟩

theorem shrR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrR8Effect p len dst c) f := by
  lift_fresh [shrR8Effect, shrFlags]

theorem sarR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (sarR8Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR8Effect_local, by lift_reads [sarR8Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR8Effect_components]⟩

theorem sarR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (sarR8Effect p len dst c) f := by
  lift_fresh [sarR8Effect, sarFlags]

theorem rolR8ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (rolR8ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR8ClEffect_local, by lift_reads [rolR8ClEffect, rolR8Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR8ClEffect_components]⟩

theorem rorR8ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (rorR8ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rorR8ClEffect_local, by lift_reads [rorR8ClEffect, rorR8Effect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorR8ClEffect_components]⟩

theorem shlR8ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shlR8ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR8ClEffect_local, by lift_reads [shlR8ClEffect, shlR8Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR8ClEffect_components]⟩

theorem salR8ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (salR8ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal salR8ClEffect_local, by lift_reads [salR8ClEffect, salR8Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salR8ClEffect_components]⟩

theorem shrR8ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shrR8ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR8ClEffect_local, by lift_reads [shrR8ClEffect, shrR8Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR8ClEffect_components]⟩

theorem sarR8ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (sarR8ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR8ClEffect_local, by lift_reads [sarR8ClEffect, sarR8Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR8ClEffect_components]⟩

theorem shldR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shldR16R16Effect p len dst src c) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shldR16R16Effect_local, by lift_reads [shldR16R16Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldR16R16Effect_components]⟩

theorem shldR16R16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shldR16R16Effect p len dst src c) f := by
  lift_fresh [shldR16R16Effect, shldFlags]

theorem shldR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shldR32R32Effect p len dst src c) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shldR32R32Effect_local, by lift_reads [shldR32R32Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldR32R32Effect_components]⟩

theorem shldR32R32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shldR32R32Effect p len dst src c) f := by
  lift_fresh [shldR32R32Effect, shldFlags]

theorem shldR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shldR64R64Effect p len dst src c) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shldR64R64Effect_local, by lift_reads [shldR64R64Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldR64R64Effect_components]⟩

theorem shldR64R64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shldR64R64Effect p len dst src c) f := by
  lift_fresh [shldR64R64Effect, shldFlags]

theorem shldR32R32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (shldR32R32ClEffect p len dst src) ([.gpr dst, .gpr src, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shldR32R32ClEffect_local, by lift_reads [shldR32R32ClEffect, shldR32R32Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldR32R32ClEffect_components]⟩

theorem shldR64R64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (shldR64R64ClEffect p len dst src) ([.gpr dst, .gpr src, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shldR64R64ClEffect_local, by lift_reads [shldR64R64ClEffect, shldR64R64Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldR64R64ClEffect_components]⟩

theorem shldM32R32Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shldM32R32Effect p len am src c) (([.gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shldM32R32Effect_local, by lift_reads [shldM32R32Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldM32R32Effect_components]⟩

theorem shldM32R32Effect_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shldM32R32Effect p len am src c) f := by
  lift_fresh [shldM32R32Effect, shldFlags]

theorem shldM64R64Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shldM64R64Effect p len am src c) (([.gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shldM64R64Effect_local, by lift_reads [shldM64R64Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldM64R64Effect_components]⟩

theorem shldM64R64Effect_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shldM64R64Effect p len am src c) f := by
  lift_fresh [shldM64R64Effect, shldFlags]

theorem shldM32R32ClEffect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) :
    EffectFootprint p (shldM32R32ClEffect p len am src) (([.gpr src, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shldM32R32ClEffect_local, by lift_reads [shldM32R32ClEffect, shldM32R32Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldM32R32ClEffect_components]⟩

theorem shldM64R64ClEffect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) :
    EffectFootprint p (shldM64R64ClEffect p len am src) (([.gpr src, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shldM64R64ClEffect_local, by lift_reads [shldM64R64ClEffect, shldM64R64Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldM64R64ClEffect_components]⟩

theorem shrdR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shrdR16R16Effect p len dst src c) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrdR16R16Effect_local, by lift_reads [shrdR16R16Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdR16R16Effect_components]⟩

theorem shrdR16R16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrdR16R16Effect p len dst src c) f := by
  lift_fresh [shrdR16R16Effect, shrdFlags]

theorem shrdR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shrdR32R32Effect p len dst src c) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrdR32R32Effect_local, by lift_reads [shrdR32R32Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdR32R32Effect_components]⟩

theorem shrdR32R32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrdR32R32Effect p len dst src c) f := by
  lift_fresh [shrdR32R32Effect, shrdFlags]

theorem shrdR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shrdR64R64Effect p len dst src c) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrdR64R64Effect_local, by lift_reads [shrdR64R64Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdR64R64Effect_components]⟩

theorem shrdR64R64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrdR64R64Effect p len dst src c) f := by
  lift_fresh [shrdR64R64Effect, shrdFlags]

theorem shrdR32R32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (shrdR32R32ClEffect p len dst src) ([.gpr dst, .gpr src, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrdR32R32ClEffect_local, by lift_reads [shrdR32R32ClEffect, shrdR32R32Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdR32R32ClEffect_components]⟩

theorem shrdR64R64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (shrdR64R64ClEffect p len dst src) ([.gpr dst, .gpr src, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrdR64R64ClEffect_local, by lift_reads [shrdR64R64ClEffect, shrdR64R64Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdR64R64ClEffect_components]⟩

theorem shrdM32R32Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shrdM32R32Effect p len am src c) (([.gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shrdM32R32Effect_local, by lift_reads [shrdM32R32Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdM32R32Effect_components]⟩

theorem shrdM32R32Effect_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrdM32R32Effect p len am src c) f := by
  lift_fresh [shrdM32R32Effect, shrdFlags]

theorem shrdM64R64Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shrdM64R64Effect p len am src c) (([.gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shrdM64R64Effect_local, by lift_reads [shrdM64R64Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdM64R64Effect_components]⟩

theorem shrdM64R64Effect_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrdM64R64Effect p len am src c) f := by
  lift_fresh [shrdM64R64Effect, shrdFlags]

theorem shrdM32R32ClEffect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) :
    EffectFootprint p (shrdM32R32ClEffect p len am src) (([.gpr src, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shrdM32R32ClEffect_local, by lift_reads [shrdM32R32ClEffect, shrdM32R32Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdM32R32ClEffect_components]⟩

theorem shrdM64R64ClEffect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) :
    EffectFootprint p (shrdM64R64ClEffect p len am src) (([.gpr src, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shrdM64R64ClEffect_local, by lift_reads [shrdM64R64ClEffect, shrdM64R64Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdM64R64ClEffect_components]⟩

theorem imulR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (imulR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR16R16Effect_local, by lift_reads [imulR16R16Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR16R16Effect_components]⟩

theorem imulR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (imulR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR32R32Effect_local, by lift_reads [imulR32R32Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR32R32Effect_components]⟩

theorem imulR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (imulR64R64Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR64R64Effect_local, by lift_reads [imulR64R64Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR64R64Effect_components]⟩

theorem imulR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (imulR32M32Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR32M32Effect_local, by lift_reads [imulR32M32Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR32M32Effect_components]⟩

theorem imulR64M64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (imulR64M64Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR64M64Effect_local, by lift_reads [imulR64M64Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR64M64Effect_components]⟩

theorem imulR16R16Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (imulR16R16Imm8Effect p len dst src imm) ([.gpr src, .gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR16R16Imm8Effect_local, by lift_reads [imulR16R16Imm8Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR16R16Imm8Effect_components]⟩

theorem imulR32R32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (imulR32R32Imm8Effect p len dst src imm) ([.gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR32R32Imm8Effect_local, by lift_reads [imulR32R32Imm8Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR32R32Imm8Effect_components]⟩

theorem imulR64R64Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (imulR64R64Imm8Effect p len dst src imm) ([.gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR64R64Imm8Effect_local, by lift_reads [imulR64R64Imm8Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR64R64Imm8Effect_components]⟩

theorem imulR32M32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (imulR32M32Imm8Effect p len dst am imm) (addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR32M32Imm8Effect_local, by lift_reads [imulR32M32Imm8Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR32M32Imm8Effect_components]⟩

theorem imulR64M64Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (imulR64M64Imm8Effect p len dst am imm) (addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR64M64Imm8Effect_local, by lift_reads [imulR64M64Imm8Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR64M64Imm8Effect_components]⟩

theorem imulR16R16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (imulR16R16Imm16Effect p len dst src imm) ([.gpr src, .gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR16R16Imm16Effect_local, by lift_reads [imulR16R16Imm16Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR16R16Imm16Effect_components]⟩

theorem imulR32R32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (imulR32R32Imm32Effect p len dst src imm) ([.gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR32R32Imm32Effect_local, by lift_reads [imulR32R32Imm32Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR32R32Imm32Effect_components]⟩

theorem imulR64R64Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (imulR64R64Imm32Effect p len dst src imm) ([.gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR64R64Imm32Effect_local, by lift_reads [imulR64R64Imm32Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR64R64Imm32Effect_components]⟩

theorem imulR32M32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (imulR32M32Imm32Effect p len dst am imm) (addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR32M32Imm32Effect_local, by lift_reads [imulR32M32Imm32Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR32M32Imm32Effect_components]⟩

theorem imulR64M64Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (imulR64M64Imm32Effect p len dst am imm) (addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR64M64Imm32Effect_local, by lift_reads [imulR64M64Imm32Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR64M64Imm32Effect_components]⟩

theorem mulR16Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) :
    EffectFootprint p (mulR16Effect p len src) ([.gpr src, .gpr 0, .gpr 2]) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal mulR16Effect_local, by lift_reads [mulR16Effect, mulFlags], by lift_closed, by lift_params,
    by lift_components [mulR16Effect_components]⟩

theorem mulR32Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) :
    EffectFootprint p (mulR32Effect p len src) ([.gpr src, .gpr 0]) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal mulR32Effect_local, by lift_reads [mulR32Effect, mulFlags], by lift_closed, by lift_params,
    by lift_components [mulR32Effect_components]⟩

theorem mulR64Effect_footprint (p : BitVec 64) (src : BitVec 5) :
    EffectFootprint p (mulR64Effect p src) ([.gpr src, .gpr 0]) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal mulR64Effect_local, by lift_reads [mulR64Effect, mulFlags], by lift_closed, by lift_params,
    by lift_components [mulR64Effect_components]⟩

theorem imulR16Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) :
    EffectFootprint p (imulR16Effect p len src) ([.gpr src, .gpr 0, .gpr 2]) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal imulR16Effect_local, by lift_reads [imulR16Effect, imulWideFlags], by lift_closed, by lift_params,
    by lift_components [imulR16Effect_components]⟩

theorem imulR32Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) :
    EffectFootprint p (imulR32Effect p len src) ([.gpr src, .gpr 0]) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal imulR32Effect_local, by lift_reads [imulR32Effect, imulWideFlags], by lift_closed, by lift_params,
    by lift_components [imulR32Effect_components]⟩

theorem imulR64Effect_footprint (p : BitVec 64) (src : BitVec 5) :
    EffectFootprint p (imulR64Effect p src) ([.gpr src, .gpr 0]) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal imulR64Effect_local, by lift_reads [imulR64Effect, imulWideFlags], by lift_closed, by lift_params,
    by lift_components [imulR64Effect_components]⟩

theorem mulR8Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) :
    EffectFootprint p (mulR8Effect p len src) ([.gpr src, .gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal mulR8Effect_local, by lift_reads [mulR8Effect, mulFlags], by lift_closed, by lift_params,
    by lift_components [mulR8Effect_components]⟩

theorem imulR8Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) :
    EffectFootprint p (imulR8Effect p len src) ([.gpr src, .gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal imulR8Effect_local, by lift_reads [imulR8Effect, imulWideFlags], by lift_closed, by lift_params,
    by lift_components [imulR8Effect_components]⟩

theorem mulM32Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (mulM32Effect p len am) (([.gpr 0] : List Reg) ++ addrRegs am) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal mulM32Effect_local, by lift_reads [mulM32Effect, mulFlags], by lift_closed, by lift_params,
    by lift_components [mulM32Effect_components]⟩

theorem mulM64Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (mulM64Effect p len am) (([.gpr 0] : List Reg) ++ addrRegs am) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal mulM64Effect_local, by lift_reads [mulM64Effect, mulFlags], by lift_closed, by lift_params,
    by lift_components [mulM64Effect_components]⟩

theorem imulM32Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (imulM32Effect p len am) (([.gpr 0] : List Reg) ++ addrRegs am) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal imulM32Effect_local, by lift_reads [imulM32Effect, imulWideFlags], by lift_closed, by lift_params,
    by lift_components [imulM32Effect_components]⟩

theorem imulM64Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (imulM64Effect p len am) (([.gpr 0] : List Reg) ++ addrRegs am) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal imulM64Effect_local, by lift_reads [imulM64Effect, imulWideFlags], by lift_closed, by lift_params,
    by lift_components [imulM64Effect_components]⟩

theorem mulM8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (mulM8Effect p len am) (([.gpr 0] : List Reg) ++ addrRegs am) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal mulM8Effect_local, by lift_reads [mulM8Effect, mulFlags], by lift_closed, by lift_params,
    by lift_components [mulM8Effect_components]⟩

theorem imulM8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (imulM8Effect p len am) (([.gpr 0] : List Reg) ++ addrRegs am) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal imulM8Effect_local, by lift_reads [imulM8Effect, imulWideFlags], by lift_closed, by lift_params,
    by lift_components [imulM8Effect_components]⟩

theorem bswapR32Effect_footprint (p : BitVec 64) (len : Nat) (r : BitVec 5) :
    EffectFootprint p (bswapR32Effect p len r) ([.gpr r]) []
      [.reg r, .rip] :=
  ⟨.ofLocal bswapR32Effect_local, by lift_reads [bswapR32Effect], by lift_closed, by lift_params,
    by lift_components [bswapR32Effect_components]⟩

theorem bswapR64Effect_footprint (p : BitVec 64) (len : Nat) (r : BitVec 5) :
    EffectFootprint p (bswapR64Effect p len r) ([.gpr r]) []
      [.reg r, .rip] :=
  ⟨.ofLocal bswapR64Effect_local, by lift_reads [bswapR64Effect], by lift_closed, by lift_params,
    by lift_components [bswapR64Effect_components]⟩

theorem bsfR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (bsfR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsfR16R16Effect_local, by lift_reads [bsfR16R16Effect], by lift_closed, by lift_params,
    by lift_components [bsfR16R16Effect_components]⟩

theorem bsfR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (bsfR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsfR32R32Effect_local, by lift_reads [bsfR32R32Effect], by lift_closed, by lift_params,
    by lift_components [bsfR32R32Effect_components]⟩

theorem bsfR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (bsfR64R64Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsfR64R64Effect_local, by lift_reads [bsfR64R64Effect], by lift_closed, by lift_params,
    by lift_components [bsfR64R64Effect_components]⟩

theorem bsfR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (bsfR32M32Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsfR32M32Effect_local, by lift_reads [bsfR32M32Effect], by lift_closed, by lift_params,
    by lift_components [bsfR32M32Effect_components]⟩

theorem bsfR64M64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (bsfR64M64Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsfR64M64Effect_local, by lift_reads [bsfR64M64Effect], by lift_closed, by lift_params,
    by lift_components [bsfR64M64Effect_components]⟩

theorem bsrR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (bsrR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsrR16R16Effect_local, by lift_reads [bsrR16R16Effect], by lift_closed, by lift_params,
    by lift_components [bsrR16R16Effect_components]⟩

theorem bsrR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (bsrR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsrR32R32Effect_local, by lift_reads [bsrR32R32Effect], by lift_closed, by lift_params,
    by lift_components [bsrR32R32Effect_components]⟩

theorem bsrR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (bsrR64R64Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsrR64R64Effect_local, by lift_reads [bsrR64R64Effect], by lift_closed, by lift_params,
    by lift_components [bsrR64R64Effect_components]⟩

theorem bsrR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (bsrR32M32Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsrR32M32Effect_local, by lift_reads [bsrR32M32Effect], by lift_closed, by lift_params,
    by lift_components [bsrR32M32Effect_components]⟩

theorem bsrR64M64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (bsrR64M64Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsrR64M64Effect_local, by lift_reads [bsrR64M64Effect], by lift_closed, by lift_params,
    by lift_components [bsrR64M64Effect_components]⟩

theorem movzxR32R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movzxR32R8Effect p len dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movzxR32R8Effect_local, by lift_reads [movzxR32R8Effect], by lift_closed, by lift_params,
    by lift_components [movzxR32R8Effect_components]⟩

theorem movzxR32M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movzxR32M8Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movzxR32M8Effect_local, by lift_reads [movzxR32M8Effect], by lift_closed, by lift_params,
    by lift_components [movzxR32M8Effect_components]⟩

theorem movzxR32R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movzxR32R16Effect p len dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movzxR32R16Effect_local, by lift_reads [movzxR32R16Effect], by lift_closed, by lift_params,
    by lift_components [movzxR32R16Effect_components]⟩

theorem movzxR32M16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movzxR32M16Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movzxR32M16Effect_local, by lift_reads [movzxR32M16Effect], by lift_closed, by lift_params,
    by lift_components [movzxR32M16Effect_components]⟩

theorem movsxR32R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movsxR32R8Effect p len dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxR32R8Effect_local, by lift_reads [movsxR32R8Effect], by lift_closed, by lift_params,
    by lift_components [movsxR32R8Effect_components]⟩

theorem movsxR64R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movsxR64R8Effect p len dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxR64R8Effect_local, by lift_reads [movsxR64R8Effect], by lift_closed, by lift_params,
    by lift_components [movsxR64R8Effect_components]⟩

theorem movsxR32M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movsxR32M8Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxR32M8Effect_local, by lift_reads [movsxR32M8Effect], by lift_closed, by lift_params,
    by lift_components [movsxR32M8Effect_components]⟩

theorem movsxR64M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movsxR64M8Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxR64M8Effect_local, by lift_reads [movsxR64M8Effect], by lift_closed, by lift_params,
    by lift_components [movsxR64M8Effect_components]⟩

theorem movsxR32R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movsxR32R16Effect p len dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxR32R16Effect_local, by lift_reads [movsxR32R16Effect], by lift_closed, by lift_params,
    by lift_components [movsxR32R16Effect_components]⟩

theorem movsxR64R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movsxR64R16Effect p len dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxR64R16Effect_local, by lift_reads [movsxR64R16Effect], by lift_closed, by lift_params,
    by lift_components [movsxR64R16Effect_components]⟩

theorem movsxR32M16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movsxR32M16Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxR32M16Effect_local, by lift_reads [movsxR32M16Effect], by lift_closed, by lift_params,
    by lift_components [movsxR32M16Effect_components]⟩

theorem movsxR64M16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movsxR64M16Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxR64M16Effect_local, by lift_reads [movsxR64M16Effect], by lift_closed, by lift_params,
    by lift_components [movsxR64M16Effect_components]⟩

theorem movsxdR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movsxdR32R32Effect p len dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxdR32R32Effect_local, by lift_reads [movsxdR32R32Effect], by lift_closed, by lift_params,
    by lift_components [movsxdR32R32Effect_components]⟩

theorem movsxdR64R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movsxdR64R32Effect p len dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxdR64R32Effect_local, by lift_reads [movsxdR64R32Effect], by lift_closed, by lift_params,
    by lift_components [movsxdR64R32Effect_components]⟩

theorem movsxdR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movsxdR32M32Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxdR32M32Effect_local, by lift_reads [movsxdR32M32Effect], by lift_closed, by lift_params,
    by lift_components [movsxdR32M32Effect_components]⟩

theorem movsxdR64M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movsxdR64M32Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxdR64M32Effect_local, by lift_reads [movsxdR64M32Effect], by lift_closed, by lift_params,
    by lift_components [movsxdR64M32Effect_components]⟩

theorem movR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movR16R16Effect p len dst src) ([.gpr src, .gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR16R16Effect_local, by lift_reads [movR16R16Effect], by lift_closed, by lift_params,
    by lift_components [movR16R16Effect_components]⟩

theorem movR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movR32R32Effect p len dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR32R32Effect_local, by lift_reads [movR32R32Effect], by lift_closed, by lift_params,
    by lift_components [movR32R32Effect_components]⟩

theorem movR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movR64R64Effect p dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR64R64Effect_local, by lift_reads [movR64R64Effect], by lift_closed, by lift_params,
    by lift_components [movR64R64Effect_components]⟩

theorem movR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movR8R8Effect p len dst src) ([.gpr src, .gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR8R8Effect_local, by lift_reads [movR8R8Effect], by lift_closed, by lift_params,
    by lift_components [movR8R8Effect_components]⟩

theorem movR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (movR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR8Imm8Effect_local, by lift_reads [movR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [movR8Imm8Effect_components]⟩

theorem movR16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (movR16Imm16Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR16Imm16Effect_local, by lift_reads [movR16Imm16Effect], by lift_closed, by lift_params,
    by lift_components [movR16Imm16Effect_components]⟩

theorem movR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (movR32Imm32Effect p len dst imm) ([]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR32Imm32Effect_local, by lift_reads [movR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [movR32Imm32Effect_components]⟩

theorem movR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (movR64Imm32Effect p dst imm) ([]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR64Imm32Effect_local, by lift_reads [movR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [movR64Imm32Effect_components]⟩

theorem movR64Imm64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 64) :
    EffectFootprint p (movR64Imm64Effect p dst imm) ([]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR64Imm64Effect_local, by lift_reads [movR64Imm64Effect], by lift_closed, by lift_params,
    by lift_components [movR64Imm64Effect_components]⟩

theorem xchgR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (xchgR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg src, .reg dst, .rip] :=
  ⟨.ofLocal xchgR16R16Effect_local, by lift_reads [xchgR16R16Effect], by lift_closed, by lift_params,
    by lift_components [xchgR16R16Effect_components]⟩

theorem xchgR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (xchgR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg src, .reg dst, .rip] :=
  ⟨.ofLocal xchgR32R32Effect_local, by lift_reads [xchgR32R32Effect], by lift_closed, by lift_params,
    by lift_components [xchgR32R32Effect_components]⟩

theorem xchgR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (xchgR64R64Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg src, .reg dst, .rip] :=
  ⟨.ofLocal xchgR64R64Effect_local, by lift_reads [xchgR64R64Effect], by lift_closed, by lift_params,
    by lift_components [xchgR64R64Effect_components]⟩

theorem xchgR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (xchgR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg src, .reg dst, .rip] :=
  ⟨.ofLocal xchgR8R8Effect_local, by lift_reads [xchgR8R8Effect], by lift_closed, by lift_params,
    by lift_components [xchgR8R8Effect_components]⟩

theorem xchgR16AxEffect_footprint (p : BitVec 64) (len : Nat) (r : BitVec 5) :
    EffectFootprint p (xchgR16AxEffect p len r) ([.gpr r, .gpr 0]) []
      [.reg 0, .reg r, .rip] :=
  ⟨.ofLocal xchgR16AxEffect_local, by lift_reads [xchgR16AxEffect], by lift_closed, by lift_params,
    by lift_components [xchgR16AxEffect_components]⟩

theorem xchgR32EaxEffect_footprint (p : BitVec 64) (len : Nat) (r : BitVec 5) :
    EffectFootprint p (xchgR32EaxEffect p len r) ([.gpr r, .gpr 0]) []
      [.reg 0, .reg r, .rip] :=
  ⟨.ofLocal xchgR32EaxEffect_local, by lift_reads [xchgR32EaxEffect], by lift_closed, by lift_params,
    by lift_components [xchgR32EaxEffect_components]⟩

theorem xchgR64RaxEffect_footprint (p : BitVec 64) (len : Nat) (r : BitVec 5) :
    EffectFootprint p (xchgR64RaxEffect p len r) ([.gpr r, .gpr 0]) []
      [.reg 0, .reg r, .rip] :=
  ⟨.ofLocal xchgR64RaxEffect_local, by lift_reads [xchgR64RaxEffect], by lift_closed, by lift_params,
    by lift_components [xchgR64RaxEffect_components]⟩

end P256.Proofs.Lift
