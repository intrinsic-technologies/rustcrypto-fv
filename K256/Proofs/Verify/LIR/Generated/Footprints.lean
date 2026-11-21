import K256.Proofs.Common.Lift.Footprint
import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Sec1.LIR.Generated.Footprints
import K256.Proofs.Generate.LIR.Generated.Footprints
import K256.Proofs.Ecdh.LIR.Generated.Footprints
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.Add.Generated.R8.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Bsr.Generated.RM.Triple
import X86Proofs.Instructions.Bsr.Generated.RR.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Cmov.Generated.RM.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Imul.Generated.RRImm8.Triple
import X86Proofs.Instructions.Inc.Generated.M.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Movsx.Generated.RR8.Triple
import X86Proofs.Instructions.Or.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Push.Generated.Imm8.Triple
import X86Proofs.Instructions.Rol.Generated.Cl.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

open K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

theorem pushImm8Effect_footprint (p : BitVec 64) (len : Nat) (imm : BitVec 8) :
    EffectFootprint p (pushImm8Effect p len imm) ([.gpr 4]) []
      [.reg 4, .rip] :=
  ⟨.ofLocal pushImm8Effect_local, by lift_reads [pushImm8Effect, pushEffect], by lift_closed, by lift_params,
    by lift_components [pushImm8Effect_components]⟩

theorem cmpR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (cmpR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR16R16Effect_local, by lift_reads [cmpR16R16Effect], by lift_closed, by lift_params,
    by lift_components [cmpR16R16Effect_components]⟩

theorem addR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (addR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR8R8Effect_local, by lift_reads [addR8R8Effect], by lift_closed, by lift_params,
    by lift_components [addR8R8Effect_components]⟩

theorem orR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (orR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR8Imm8Effect_local, by lift_reads [orR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [orR8Imm8Effect_components]⟩

theorem addEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (addEaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal addEaxImm32Effect_local, by lift_reads [addEaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [addEaxImm32Effect_components]⟩

theorem rolR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rolR32Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR32Effect_local, by lift_reads [rolR32Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR32Effect_components]⟩

theorem rolR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rolR32Effect p len dst c) f := by
  lift_fresh [rolR32Effect, rolFlags]

theorem rolR32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (rolR32ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR32ClEffect_local, by lift_reads [rolR32ClEffect, rolR32Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR32ClEffect_components]⟩

theorem imulR64R64Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (imulR64R64Imm8Effect p len dst src imm) ([.gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR64R64Imm8Effect_local, by lift_reads [imulR64R64Imm8Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR64R64Imm8Effect_components]⟩

theorem bswapR32Effect_footprint (p : BitVec 64) (len : Nat) (r : BitVec 5) :
    EffectFootprint p (bswapR32Effect p len r) ([.gpr r]) []
      [.reg r, .rip] :=
  ⟨.ofLocal bswapR32Effect_local, by lift_reads [bswapR32Effect], by lift_closed, by lift_params,
    by lift_components [bswapR32Effect_components]⟩

theorem bsrR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (bsrR64R64Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsrR64R64Effect_local, by lift_reads [bsrR64R64Effect], by lift_closed, by lift_params,
    by lift_components [bsrR64R64Effect_components]⟩

theorem bsrR64M64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (bsrR64M64Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal bsrR64M64Effect_local, by lift_reads [bsrR64M64Effect], by lift_closed, by lift_params,
    by lift_components [bsrR64M64Effect_components]⟩

theorem movsxR64R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movsxR64R8Effect p len dst src) ([.gpr src]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxR64R8Effect_local, by lift_reads [movsxR64R8Effect], by lift_closed, by lift_params,
    by lift_components [movsxR64R8Effect_components]⟩

theorem cmovR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (cc : BitVec 4) :
    EffectFootprint p (atFlags (condHolds cc) (cmovR32M32Effect p len dst am)) (([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) (condFlags cc)
      [.reg dst, .rip] :=
  ⟨LocalWith.atFlags (condHolds_congr cc) fun _ => cmovR32M32Effect_local, by lift_reads [cmovR32M32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, cmovR32M32Effect_components]⟩

theorem addR32M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (addR32M32Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR32M32Effect_local, by lift_reads [addR32M32Effect], by lift_closed, by lift_params,
    by lift_components [addR32M32Effect_components]⟩

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

theorem xorM8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (xorM8Imm8Effect p len am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal xorM8Imm8Effect_local, by lift_reads [xorM8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [xorM8Imm8Effect_components]⟩

theorem incMEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (incMEffect p len 32 am) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal incMEffect_local32, by lift_reads [incMEffect, incSpec], by lift_closed, by lift_params,
    by lift_components [incMEffect_components]⟩

theorem incMEffect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (incMEffect p len 32 am) f := by
  lift_fresh [incMEffect, incSpec]

theorem incMEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (incMEffect p len 64 am) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal incMEffect_local64, by lift_reads [incMEffect, incSpec], by lift_closed, by lift_params,
    by lift_components [incMEffect_components]⟩

theorem incMEffect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (incMEffect p len 64 am) f := by
  lift_fresh [incMEffect, incSpec]

theorem incMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (incMEffect p len 8 am) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal incMEffect_local8, by lift_reads [incMEffect, incSpec], by lift_closed, by lift_params,
    by lift_components [incMEffect_components]⟩

theorem incMEffect8_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (incMEffect p len 8 am) f := by
  lift_fresh [incMEffect, incSpec]

end K256.Proofs.Verify.LIR
