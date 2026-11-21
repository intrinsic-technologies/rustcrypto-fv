import AesGcm.Proofs.Copied.X86Proofs.Lift.Footprint
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

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG

theorem shldR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shldR64R64Effect p len dst src c) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shldR64R64Effect_local, by lift_reads [shldR64R64Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldR64R64Effect_components]⟩

theorem imulR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (imulR64R64Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR64R64Effect_local, by lift_reads [imulR64R64Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR64R64Effect_components]⟩

theorem imulR32R32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (imulR32R32Imm8Effect p len dst src imm) ([.gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR32R32Imm8Effect_local, by lift_reads [imulR32R32Imm8Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR32R32Imm8Effect_components]⟩

theorem imulR32R32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (imulR32R32Imm32Effect p len dst src imm) ([.gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal imulR32R32Imm32Effect_local, by lift_reads [imulR32R32Imm32Effect, imulFlags], by lift_closed, by lift_params,
    by lift_components [imulR32R32Imm32Effect_components]⟩

theorem mulR64Effect_footprint (p : BitVec 64) (src : BitVec 5) :
    EffectFootprint p (mulR64Effect p src) ([.gpr src, .gpr 0]) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal mulR64Effect_local, by lift_reads [mulR64Effect, mulFlags], by lift_closed, by lift_params,
    by lift_components [mulR64Effect_components]⟩

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

theorem movsxdR64M32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movsxdR64M32Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxdR64M32Effect_local, by lift_reads [movsxdR64M32Effect], by lift_closed, by lift_params,
    by lift_components [movsxdR64M32Effect_components]⟩

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

end X86Proofs.Lift
