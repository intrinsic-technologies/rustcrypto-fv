import ChaCha20Poly1305.Proofs.Common.Lift.Footprint
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
import ChaCha20Poly1305.Proofs.Common.Lift.Rep

namespace ChaCha20Poly1305.Proofs.Lift
open X86Proofs

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG

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

theorem callRegEffect_footprint (p : BitVec 64) (r : BitVec 5) (ret : BitVec 64) :
    EffectFootprint p (callEffect (fun s => (Operand.reg r : Operand 64).read s) ret) ([.gpr 4, .gpr r]) []
      [.reg 4, .rip] :=
  ⟨.ofLocal (by effect_local [callEffect, pushEffect, pushAddr, stackPtr]), by lift_reads [callEffect, pushEffect], by lift_closed, by lift_params,
    by lift_components [pushEffect_components]⟩

theorem jmpR64Effect_footprint (p : BitVec 64) (r : BitVec 5) :
    EffectFootprint p (jmpR64Effect r) ([.gpr r]) []
      [.rip] :=
  ⟨.ofLocal (by effect_local [jmpR64Effect]), by lift_reads [jmpR64Effect], by lift_closed, by lift_params,
    by lift_components [jmpR64Effect_components]⟩

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

theorem repStosbEffect_footprint (p : BitVec 64) :
    EffectFootprint p (repStosbEffect p) ([.gpr 0, .gpr 7, .gpr 1, .df]) []
      [.reg 7, .reg 1, .rip] :=
  ⟨.ofLocal repStosbEffect_local, repStosbEffect_reads p, by lift_closed, by lift_params,
    by lift_components [repStosbEffect_components]⟩

theorem repStosqEffect_footprint (p : BitVec 64) :
    EffectFootprint p (repStosqEffect p) ([.gpr 0, .gpr 7, .gpr 1, .df]) []
      [.reg 7, .reg 1, .rip] :=
  ⟨.ofLocal repStosqEffect_local, repStosqEffect_reads p, by lift_closed, by lift_params,
    by lift_components [repStosqEffect_components]⟩

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

theorem andR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (andR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR16R16Effect_local, by lift_reads [andR16R16Effect], by lift_closed, by lift_params,
    by lift_components [andR16R16Effect_components]⟩

theorem andR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (andR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR32R32Effect_local, by lift_reads [andR32R32Effect], by lift_closed, by lift_params,
    by lift_components [andR32R32Effect_components]⟩

theorem andR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (andR64R64Effect p dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR64R64Effect_local, by lift_reads [andR64R64Effect], by lift_closed, by lift_params,
    by lift_components [andR64R64Effect_components]⟩

theorem addR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (addR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR16R16Effect_local, by lift_reads [addR16R16Effect], by lift_closed, by lift_params,
    by lift_components [addR16R16Effect_components]⟩

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

theorem subR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (subR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR16R16Effect_local, by lift_reads [subR16R16Effect], by lift_closed, by lift_params,
    by lift_components [subR16R16Effect_components]⟩

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

theorem cmpR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (cmpR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR16R16Effect_local, by lift_reads [cmpR16R16Effect], by lift_closed, by lift_params,
    by lift_components [cmpR16R16Effect_components]⟩

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

theorem testR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (testR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR16R16Effect_local, by lift_reads [testR16R16Effect], by lift_closed, by lift_params,
    by lift_components [testR16R16Effect_components]⟩

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

theorem adcR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR16R16Effect p len dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR16R16Effect_local, by lift_reads [adcR16R16Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR16R16Effect_components]⟩

theorem adcR16R16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR16R16Effect p len dst src)) f := by
  lift_fresh [adcR16R16Effect, atFlags]

theorem adcR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR32R32Effect p len dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR32R32Effect_local, by lift_reads [adcR32R32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR32R32Effect_components]⟩

theorem adcR32R32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR32R32Effect p len dst src)) f := by
  lift_fresh [adcR32R32Effect, atFlags]

theorem adcR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR64R64Effect p dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR64R64Effect_local, by lift_reads [adcR64R64Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR64R64Effect_components]⟩

theorem adcR64R64Effect_fresh (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR64R64Effect p dst src)) f := by
  lift_fresh [adcR64R64Effect, atFlags]

theorem sbbR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR16R16Effect p len dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR16R16Effect_local, by lift_reads [sbbR16R16Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR16R16Effect_components]⟩

theorem sbbR16R16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR16R16Effect p len dst src)) f := by
  lift_fresh [sbbR16R16Effect, atFlags]

theorem sbbR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR32R32Effect_local, by lift_reads [sbbR32R32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR32R32Effect_components]⟩

theorem sbbR32R32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src)) f := by
  lift_fresh [sbbR32R32Effect, atFlags]

theorem sbbR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR64R64Effect p dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR64R64Effect_local, by lift_reads [sbbR64R64Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR64R64Effect_components]⟩

theorem sbbR64R64Effect_fresh (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR64R64Effect p dst src)) f := by
  lift_fresh [sbbR64R64Effect, atFlags]

theorem orR16R16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (orR16R16Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR16R16Effect_local, by lift_reads [orR16R16Effect], by lift_closed, by lift_params,
    by lift_components [orR16R16Effect_components]⟩

theorem orR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (orR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR32R32Effect_local, by lift_reads [orR32R32Effect], by lift_closed, by lift_params,
    by lift_components [orR32R32Effect_components]⟩

theorem orR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (orR64R64Effect p dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR64R64Effect_local, by lift_reads [orR64R64Effect], by lift_closed, by lift_params,
    by lift_components [orR64R64Effect_components]⟩

theorem addR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (addR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR8R8Effect_local, by lift_reads [addR8R8Effect], by lift_closed, by lift_params,
    by lift_components [addR8R8Effect_components]⟩

theorem adcR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR8R8Effect p len dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR8R8Effect_local, by lift_reads [adcR8R8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR8R8Effect_components]⟩

theorem adcR8R8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR8R8Effect p len dst src)) f := by
  lift_fresh [adcR8R8Effect, atFlags]

theorem subR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (subR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR8R8Effect_local, by lift_reads [subR8R8Effect], by lift_closed, by lift_params,
    by lift_components [subR8R8Effect_components]⟩

theorem sbbR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR8R8Effect p len dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR8R8Effect_local, by lift_reads [sbbR8R8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR8R8Effect_components]⟩

theorem sbbR8R8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR8R8Effect p len dst src)) f := by
  lift_fresh [sbbR8R8Effect, atFlags]

theorem andR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (andR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR8R8Effect_local, by lift_reads [andR8R8Effect], by lift_closed, by lift_params,
    by lift_components [andR8R8Effect_components]⟩

theorem orR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (orR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR8R8Effect_local, by lift_reads [orR8R8Effect], by lift_closed, by lift_params,
    by lift_components [orR8R8Effect_components]⟩

theorem xorR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (xorR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR8R8Effect_local, by lift_reads [xorR8R8Effect], by lift_closed, by lift_params,
    by lift_components [xorR8R8Effect_components]⟩

theorem cmpR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (cmpR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR8R8Effect_local, by lift_reads [cmpR8R8Effect], by lift_closed, by lift_params,
    by lift_components [cmpR8R8Effect_components]⟩

theorem testR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (testR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR8R8Effect_local, by lift_reads [testR8R8Effect], by lift_closed, by lift_params,
    by lift_components [testR8R8Effect_components]⟩

theorem addR16Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (addR16Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR16Imm8Effect_local, by lift_reads [addR16Imm8Effect], by lift_closed, by lift_params,
    by lift_components [addR16Imm8Effect_components]⟩

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

theorem orR16Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (orR16Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR16Imm8Effect_local, by lift_reads [orR16Imm8Effect], by lift_closed, by lift_params,
    by lift_components [orR16Imm8Effect_components]⟩

theorem orR32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (orR32Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR32Imm8Effect_local, by lift_reads [orR32Imm8Effect], by lift_closed, by lift_params,
    by lift_components [orR32Imm8Effect_components]⟩

theorem orR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (orR64Imm8Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR64Imm8Effect_local, by lift_reads [orR64Imm8Effect], by lift_closed, by lift_params,
    by lift_components [orR64Imm8Effect_components]⟩

theorem adcR16Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR16Imm8Effect p len dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR16Imm8Effect_local, by lift_reads [adcR16Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR16Imm8Effect_components]⟩

theorem adcR16Imm8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR16Imm8Effect p len dst imm)) f := by
  lift_fresh [adcR16Imm8Effect, atFlags]

theorem adcR32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR32Imm8Effect p len dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR32Imm8Effect_local, by lift_reads [adcR32Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR32Imm8Effect_components]⟩

theorem adcR32Imm8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR32Imm8Effect p len dst imm)) f := by
  lift_fresh [adcR32Imm8Effect, atFlags]

theorem adcR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR64Imm8Effect_local, by lift_reads [adcR64Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR64Imm8Effect_components]⟩

theorem adcR64Imm8Effect_fresh (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm)) f := by
  lift_fresh [adcR64Imm8Effect, atFlags]

theorem sbbR16Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR16Imm8Effect p len dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR16Imm8Effect_local, by lift_reads [sbbR16Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR16Imm8Effect_components]⟩

theorem sbbR16Imm8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR16Imm8Effect p len dst imm)) f := by
  lift_fresh [sbbR16Imm8Effect, atFlags]

theorem sbbR32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR32Imm8Effect p len dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR32Imm8Effect_local, by lift_reads [sbbR32Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR32Imm8Effect_components]⟩

theorem sbbR32Imm8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR32Imm8Effect p len dst imm)) f := by
  lift_fresh [sbbR32Imm8Effect, atFlags]

theorem sbbR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR64Imm8Effect_local, by lift_reads [sbbR64Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR64Imm8Effect_components]⟩

theorem sbbR64Imm8Effect_fresh (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm)) f := by
  lift_fresh [sbbR64Imm8Effect, atFlags]

theorem andR16Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (andR16Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR16Imm8Effect_local, by lift_reads [andR16Imm8Effect], by lift_closed, by lift_params,
    by lift_components [andR16Imm8Effect_components]⟩

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

theorem subR16Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (subR16Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR16Imm8Effect_local, by lift_reads [subR16Imm8Effect], by lift_closed, by lift_params,
    by lift_components [subR16Imm8Effect_components]⟩

theorem subR32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (subR32Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR32Imm8Effect_local, by lift_reads [subR32Imm8Effect], by lift_closed, by lift_params,
    by lift_components [subR32Imm8Effect_components]⟩

theorem subR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (subR64Imm8Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR64Imm8Effect_local, by lift_reads [subR64Imm8Effect], by lift_closed, by lift_params,
    by lift_components [subR64Imm8Effect_components]⟩

theorem xorR16Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (xorR16Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR16Imm8Effect_local, by lift_reads [xorR16Imm8Effect], by lift_closed, by lift_params,
    by lift_components [xorR16Imm8Effect_components]⟩

theorem xorR32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (xorR32Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR32Imm8Effect_local, by lift_reads [xorR32Imm8Effect], by lift_closed, by lift_params,
    by lift_components [xorR32Imm8Effect_components]⟩

theorem xorR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (xorR64Imm8Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR64Imm8Effect_local, by lift_reads [xorR64Imm8Effect], by lift_closed, by lift_params,
    by lift_components [xorR64Imm8Effect_components]⟩

theorem cmpR16Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (cmpR16Imm8Effect p len dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR16Imm8Effect_local, by lift_reads [cmpR16Imm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpR16Imm8Effect_components]⟩

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

theorem addR16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (addR16Imm16Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR16Imm16Effect_local, by lift_reads [addR16Imm16Effect], by lift_closed, by lift_params,
    by lift_components [addR16Imm16Effect_components]⟩

theorem addR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (addR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR32Imm32Effect_local, by lift_reads [addR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [addR32Imm32Effect_components]⟩

theorem addR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (addR64Imm32Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR64Imm32Effect_local, by lift_reads [addR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [addR64Imm32Effect_components]⟩

theorem orR16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (orR16Imm16Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR16Imm16Effect_local, by lift_reads [orR16Imm16Effect], by lift_closed, by lift_params,
    by lift_components [orR16Imm16Effect_components]⟩

theorem orR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (orR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR32Imm32Effect_local, by lift_reads [orR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [orR32Imm32Effect_components]⟩

theorem orR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (orR64Imm32Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR64Imm32Effect_local, by lift_reads [orR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [orR64Imm32Effect_components]⟩

theorem adcR16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR16Imm16Effect p len dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR16Imm16Effect_local, by lift_reads [adcR16Imm16Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR16Imm16Effect_components]⟩

theorem adcR16Imm16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR16Imm16Effect p len dst imm)) f := by
  lift_fresh [adcR16Imm16Effect, atFlags]

theorem adcR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR32Imm32Effect p len dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR32Imm32Effect_local, by lift_reads [adcR32Imm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR32Imm32Effect_components]⟩

theorem adcR32Imm32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR32Imm32Effect p len dst imm)) f := by
  lift_fresh [adcR32Imm32Effect, atFlags]

theorem adcR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR64Imm32Effect p dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR64Imm32Effect_local, by lift_reads [adcR64Imm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR64Imm32Effect_components]⟩

theorem adcR64Imm32Effect_fresh (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR64Imm32Effect p dst imm)) f := by
  lift_fresh [adcR64Imm32Effect, atFlags]

theorem sbbR16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR16Imm16Effect p len dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR16Imm16Effect_local, by lift_reads [sbbR16Imm16Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR16Imm16Effect_components]⟩

theorem sbbR16Imm16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR16Imm16Effect p len dst imm)) f := by
  lift_fresh [sbbR16Imm16Effect, atFlags]

theorem sbbR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR32Imm32Effect p len dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR32Imm32Effect_local, by lift_reads [sbbR32Imm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR32Imm32Effect_components]⟩

theorem sbbR32Imm32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR32Imm32Effect p len dst imm)) f := by
  lift_fresh [sbbR32Imm32Effect, atFlags]

theorem sbbR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR64Imm32Effect p dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR64Imm32Effect_local, by lift_reads [sbbR64Imm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR64Imm32Effect_components]⟩

theorem sbbR64Imm32Effect_fresh (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR64Imm32Effect p dst imm)) f := by
  lift_fresh [sbbR64Imm32Effect, atFlags]

theorem andR16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (andR16Imm16Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR16Imm16Effect_local, by lift_reads [andR16Imm16Effect], by lift_closed, by lift_params,
    by lift_components [andR16Imm16Effect_components]⟩

theorem andR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (andR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR32Imm32Effect_local, by lift_reads [andR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [andR32Imm32Effect_components]⟩

theorem andR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (andR64Imm32Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR64Imm32Effect_local, by lift_reads [andR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [andR64Imm32Effect_components]⟩

theorem subR16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (subR16Imm16Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR16Imm16Effect_local, by lift_reads [subR16Imm16Effect], by lift_closed, by lift_params,
    by lift_components [subR16Imm16Effect_components]⟩

theorem subR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (subR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR32Imm32Effect_local, by lift_reads [subR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [subR32Imm32Effect_components]⟩

theorem subR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (subR64Imm32Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR64Imm32Effect_local, by lift_reads [subR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [subR64Imm32Effect_components]⟩

theorem xorR16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (xorR16Imm16Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR16Imm16Effect_local, by lift_reads [xorR16Imm16Effect], by lift_closed, by lift_params,
    by lift_components [xorR16Imm16Effect_components]⟩

theorem xorR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (xorR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR32Imm32Effect_local, by lift_reads [xorR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [xorR32Imm32Effect_components]⟩

theorem xorR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (xorR64Imm32Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR64Imm32Effect_local, by lift_reads [xorR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [xorR64Imm32Effect_components]⟩

theorem cmpR16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (cmpR16Imm16Effect p len dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR16Imm16Effect_local, by lift_reads [cmpR16Imm16Effect], by lift_closed, by lift_params,
    by lift_components [cmpR16Imm16Effect_components]⟩

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

theorem testR16Imm16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) :
    EffectFootprint p (testR16Imm16Effect p len dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR16Imm16Effect_local, by lift_reads [testR16Imm16Effect], by lift_closed, by lift_params,
    by lift_components [testR16Imm16Effect_components]⟩

theorem testR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (testR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR32Imm32Effect_local, by lift_reads [testR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [testR32Imm32Effect_components]⟩

theorem testR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (testR64Imm32Effect p dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR64Imm32Effect_local, by lift_reads [testR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [testR64Imm32Effect_components]⟩

theorem addR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (addR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR8Imm8Effect_local, by lift_reads [addR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [addR8Imm8Effect_components]⟩

end ChaCha20Poly1305.Proofs.Lift
