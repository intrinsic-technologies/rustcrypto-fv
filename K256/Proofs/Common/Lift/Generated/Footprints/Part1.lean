import K256.Proofs.Common.Lift.Footprint
import X86Proofs.Instructions.Adc.Generated.Imm32.Triple
import X86Proofs.Instructions.Adc.Generated.Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.R8.Triple
import X86Proofs.Instructions.Adc.Generated.R8Rev.Triple
import X86Proofs.Instructions.Adc.Generated.RR.Triple
import X86Proofs.Instructions.Adc.Generated.Rev.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.R8.Triple
import X86Proofs.Instructions.Add.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.R8Rev.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Rev.Triple
import X86Proofs.Instructions.And.Generated.Imm32.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.R8.Triple
import X86Proofs.Instructions.And.Generated.R8Rev.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.Rev.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm32.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.R8.Triple
import X86Proofs.Instructions.Cmp.Generated.R8Rev.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Rev.Triple
import X86Proofs.Instructions.Jmp.Generated.M.Triple
import X86Proofs.Instructions.Jmp.Generated.R.Triple
import X86Proofs.Instructions.Movs.Generated.Rep.Triple
import X86Proofs.Instructions.Or.Generated.Imm32.Triple
import X86Proofs.Instructions.Or.Generated.Imm8.Triple
import X86Proofs.Instructions.Or.Generated.R8.Triple
import X86Proofs.Instructions.Or.Generated.R8Rev.Triple
import X86Proofs.Instructions.Or.Generated.RR.Triple
import X86Proofs.Instructions.Or.Generated.Rev.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Sbb.Generated.Imm32.Triple
import X86Proofs.Instructions.Sbb.Generated.Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.R8.Triple
import X86Proofs.Instructions.Sbb.Generated.R8Rev.Triple
import X86Proofs.Instructions.Sbb.Generated.RR.Triple
import X86Proofs.Instructions.Sbb.Generated.Rev.Triple
import X86Proofs.Instructions.Stos.Generated.Rep.Triple
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.R8.Triple
import X86Proofs.Instructions.Sub.Generated.R8Rev.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Sub.Generated.Rev.Triple
import X86Proofs.Instructions.Test.Generated.Imm32.Triple
import X86Proofs.Instructions.Test.Generated.R8.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.Imm32.Triple
import X86Proofs.Instructions.Xor.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.R8.Triple
import X86Proofs.Instructions.Xor.Generated.R8Rev.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.Rev.Triple
import K256.Proofs.Common.Lift.Rep
namespace K256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG

theorem pushR64Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) :
    EffectFootprint p (pushR64Effect p len src) ([.gpr 4, .gpr src]) []
      [.reg 4, .rip] :=
  ⟨.ofLocal pushR64Effect_local, by lift_reads [pushR64Effect, pushEffect], by lift_closed, by lift_params,
    by lift_components [pushR64Effect_components]⟩

theorem popR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (popR64Effect p len dst) ([.gpr 4]) []
      [.reg dst, .reg 4, .rip] :=
  ⟨.ofLocal popR64Effect_local, by lift_reads [popR64Effect], by lift_closed, by lift_params,
    by lift_components [popR64Effect_components]⟩

theorem callEffect_footprint (p : BitVec 64) (target : BitVec 64) (ret : BitVec 64) :
    EffectFootprint p (callEffect (fun _ => target) ret) ([.gpr 4]) []
      [.reg 4, .rip] :=
  ⟨.ofLocal (by effect_local [callEffect, pushEffect, pushAddr, stackPtr]), by lift_reads [callEffect, pushEffect], by lift_closed, by lift_params,
    by lift_components [pushEffect_components]⟩

theorem retEffect_footprint (p : BitVec 64) :
    EffectFootprint p (retEffect) ([.gpr 4]) []
      [.reg 4, .rip] :=
  ⟨.ofLocal retEffect_local, by lift_reads [retEffect], by lift_closed, by lift_params,
    by lift_components [retEffect_components]⟩

theorem callMemEffect_footprint (p : BitVec 64) (am : AddrMode) :
    EffectFootprint p (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am))) (([.gpr 4] : List Reg) ++ addrRegs am) []
      [.reg 4, .rip] :=
  ⟨.ofLocal (by effect_local [callEffect, pushEffect, pushAddr, stackPtr, callMemPtr]), by lift_reads [callEffect, pushEffect, callMemPtr, callMemLen], by lift_closed, by lift_params,
    by lift_components [pushEffect_components]⟩

theorem jmpM64Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (jmpM64Effect p len am) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal (by effect_local [jmpM64Effect]), by lift_reads [jmpM64Effect], by lift_closed, by lift_params,
    by lift_components [jmpM64Effect_components]⟩

theorem repMovsbEffect_footprint (p : BitVec 64) :
    EffectFootprint p (repMovsbEffect p) ([.gpr 6, .gpr 7, .gpr 1, .df]) []
      [.reg 6, .reg 7, .reg 1, .rip] :=
  ⟨.ofLocal repMovsbEffect_local, repMovsbEffect_reads p, by lift_closed, by lift_params,
    by lift_components [repMovsbEffect_components]⟩

theorem repMovsqEffect_footprint (p : BitVec 64) :
    EffectFootprint p (repMovsqEffect p) ([.gpr 6, .gpr 7, .gpr 1, .df]) []
      [.reg 6, .reg 7, .reg 1, .rip] :=
  ⟨.ofLocal repMovsqEffect_local, repMovsqEffect_reads p, by lift_closed, by lift_params,
    by lift_components [repMovsqEffect_components]⟩

theorem xorR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (xorR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR16R16Effect_local, by lift_reads [xorR16R16Effect], by lift_closed, by lift_params,
    by lift_components [xorR16R16Effect_components]⟩

theorem xorR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (xorR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR32R32Effect_local, by lift_reads [xorR32R32Effect], by lift_closed, by lift_params,
    by lift_components [xorR32R32Effect_components]⟩

theorem xorR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (xorR64R64Effect p dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR64R64Effect_local, by lift_reads [xorR64R64Effect], by lift_closed, by lift_params,
    by lift_components [xorR64R64Effect_components]⟩

theorem andR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (andR64R64Effect p dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR64R64Effect_local, by lift_reads [andR64R64Effect], by lift_closed, by lift_params,
    by lift_components [andR64R64Effect_components]⟩

theorem addR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (addR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR32R32Effect_local, by lift_reads [addR32R32Effect], by lift_closed, by lift_params,
    by lift_components [addR32R32Effect_components]⟩

theorem addR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (addR64R64Effect p dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR64R64Effect_local, by lift_reads [addR64R64Effect], by lift_closed, by lift_params,
    by lift_components [addR64R64Effect_components]⟩

theorem subR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (subR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR32R32Effect_local, by lift_reads [subR32R32Effect], by lift_closed, by lift_params,
    by lift_components [subR32R32Effect_components]⟩

theorem subR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (subR64R64Effect p dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR64R64Effect_local, by lift_reads [subR64R64Effect], by lift_closed, by lift_params,
    by lift_components [subR64R64Effect_components]⟩

theorem cmpR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (cmpR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR32R32Effect_local, by lift_reads [cmpR32R32Effect], by lift_closed, by lift_params,
    by lift_components [cmpR32R32Effect_components]⟩

theorem cmpR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (cmpR64R64Effect p dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR64R64Effect_local, by lift_reads [cmpR64R64Effect], by lift_closed, by lift_params,
    by lift_components [cmpR64R64Effect_components]⟩

theorem testR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (testR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR32R32Effect_local, by lift_reads [testR32R32Effect], by lift_closed, by lift_params,
    by lift_components [testR32R32Effect_components]⟩

theorem testR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (testR64R64Effect p dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR64R64Effect_local, by lift_reads [testR64R64Effect], by lift_closed, by lift_params,
    by lift_components [testR64R64Effect_components]⟩

theorem sbbR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR32R32Effect_local, by lift_reads [sbbR32R32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR32R32Effect_components]⟩

theorem orR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (orR64R64Effect p dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR64R64Effect_local, by lift_reads [orR64R64Effect], by lift_closed, by lift_params,
    by lift_components [orR64R64Effect_components]⟩

theorem testR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (testR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR8R8Effect_local, by lift_reads [testR8R8Effect], by lift_closed, by lift_params,
    by lift_components [testR8R8Effect_components]⟩

theorem addR32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (addR32Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR32Imm8Effect_local, by lift_reads [addR32Imm8Effect], by lift_closed, by lift_params,
    by lift_components [addR32Imm8Effect_components]⟩

theorem addR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (addR64Imm8Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR64Imm8Effect_local, by lift_reads [addR64Imm8Effect], by lift_closed, by lift_params,
    by lift_components [addR64Imm8Effect_components]⟩

theorem orR32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (orR32Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR32Imm8Effect_local, by lift_reads [orR32Imm8Effect], by lift_closed, by lift_params,
    by lift_components [orR32Imm8Effect_components]⟩

theorem sbbR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR64Imm8Effect_local, by lift_reads [sbbR64Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR64Imm8Effect_components]⟩

theorem andR32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (andR32Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR32Imm8Effect_local, by lift_reads [andR32Imm8Effect], by lift_closed, by lift_params,
    by lift_components [andR32Imm8Effect_components]⟩

theorem andR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (andR64Imm8Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR64Imm8Effect_local, by lift_reads [andR64Imm8Effect], by lift_closed, by lift_params,
    by lift_components [andR64Imm8Effect_components]⟩

theorem subR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (subR64Imm8Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR64Imm8Effect_local, by lift_reads [subR64Imm8Effect], by lift_closed, by lift_params,
    by lift_components [subR64Imm8Effect_components]⟩

theorem xorR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (xorR64Imm8Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR64Imm8Effect_local, by lift_reads [xorR64Imm8Effect], by lift_closed, by lift_params,
    by lift_components [xorR64Imm8Effect_components]⟩

theorem cmpR32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (cmpR32Imm8Effect p len dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR32Imm8Effect_local, by lift_reads [cmpR32Imm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpR32Imm8Effect_components]⟩

theorem cmpR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (cmpR64Imm8Effect p dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR64Imm8Effect_local, by lift_reads [cmpR64Imm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpR64Imm8Effect_components]⟩

theorem addR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (addR64Imm32Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR64Imm32Effect_local, by lift_reads [addR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [addR64Imm32Effect_components]⟩

theorem andR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (andR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR32Imm32Effect_local, by lift_reads [andR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [andR32Imm32Effect_components]⟩

theorem subR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (subR64Imm32Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR64Imm32Effect_local, by lift_reads [subR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [subR64Imm32Effect_components]⟩

theorem cmpR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (cmpR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR32Imm32Effect_local, by lift_reads [cmpR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [cmpR32Imm32Effect_components]⟩

theorem cmpR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (cmpR64Imm32Effect p dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR64Imm32Effect_local, by lift_reads [cmpR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [cmpR64Imm32Effect_components]⟩

theorem testR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (testR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR32Imm32Effect_local, by lift_reads [testR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [testR32Imm32Effect_components]⟩

end K256.Proofs.Lift
