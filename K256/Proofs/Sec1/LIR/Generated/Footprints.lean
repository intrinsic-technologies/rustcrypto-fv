import K256.Proofs.Common.Lift.Footprint
import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Sec1.LIR.Rep
import X86Proofs.Instructions.Adc.Generated.Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.RM.Triple
import X86Proofs.Instructions.Adc.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.Imm32.Triple
import X86Proofs.Instructions.And.Generated.R8.Triple
import X86Proofs.Instructions.And.Generated.R8Imm8.Triple
import X86Proofs.Instructions.And.Generated.R8M8.Triple
import X86Proofs.Instructions.And.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm8.Triple
import X86Proofs.Instructions.Cmp.Generated.R8.Triple
import X86Proofs.Instructions.Cmp.Generated.RM.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Mov.Generated.R8.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Movsx.Generated.RM8.Triple
import X86Proofs.Instructions.Mul.Generated.M.Triple
import X86Proofs.Instructions.Not.Generated.R8.Triple
import X86Proofs.Instructions.Or.Generated.AccImm8.Triple
import X86Proofs.Instructions.Or.Generated.Imm8.Triple
import X86Proofs.Instructions.Or.Generated.R8.Triple
import X86Proofs.Instructions.Or.Generated.RM.Triple
import X86Proofs.Instructions.Or.Generated.RR.Triple
import X86Proofs.Instructions.Sbb.Generated.Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.RR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shl.Generated.Cl.Triple
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Instructions.Shl.Generated.R8.Triple
import X86Proofs.Instructions.Shl.Generated.R8Cl.Triple
import X86Proofs.Instructions.Shld.Generated.RRCl.Triple
import X86Proofs.Instructions.Shld.Generated.RRImm8.Triple
import X86Proofs.Instructions.Shr.Generated.Cl.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Shr.Generated.R8.Triple
import X86Proofs.Instructions.Shr.Generated.R8Cl.Triple
import X86Proofs.Instructions.Shrd.Generated.RRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.RRImm8.Triple
import X86Proofs.Instructions.Stos.Generated.Rep.Triple
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Sub.Generated.R8.Triple
import X86Proofs.Instructions.Test.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.R8M8.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

theorem callRegEffect_footprint (p : BitVec 64) (r : BitVec 5) (ret : BitVec 64) :
    EffectFootprint p (callEffect (fun s => (Operand.reg r : Operand 64).read s) ret) ([.gpr 4, .gpr r]) []
      [.reg 4, .rip] :=
  ⟨.ofLocal (by effect_local [callEffect, pushEffect, pushAddr, stackPtr]), by lift_reads [callEffect, pushEffect], by lift_closed, by lift_params,
    by lift_components [pushEffect_components]⟩

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

theorem andR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (andR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR32R32Effect_local, by lift_reads [andR32R32Effect], by lift_closed, by lift_params,
    by lift_components [andR32R32Effect_components]⟩

theorem adcR64R64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR64R64Effect p dst src)) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR64R64Effect_local, by lift_reads [adcR64R64Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR64R64Effect_components]⟩

theorem adcR64R64Effect_fresh (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR64R64Effect p dst src)) f := by
  lift_fresh [adcR64R64Effect, atFlags]

theorem sbbR32R32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src)) f := by
  lift_fresh [sbbR32R32Effect, atFlags]

theorem orR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (orR32R32Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR32R32Effect_local, by lift_reads [orR32R32Effect], by lift_closed, by lift_params,
    by lift_components [orR32R32Effect_components]⟩

theorem subR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (subR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR8R8Effect_local, by lift_reads [subR8R8Effect], by lift_closed, by lift_params,
    by lift_components [subR8R8Effect_components]⟩

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

theorem cmpR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (cmpR8R8Effect p len dst src) ([.gpr dst, .gpr src]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR8R8Effect_local, by lift_reads [cmpR8R8Effect], by lift_closed, by lift_params,
    by lift_components [cmpR8R8Effect_components]⟩

theorem orR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (orR64Imm8Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR64Imm8Effect_local, by lift_reads [orR64Imm8Effect], by lift_closed, by lift_params,
    by lift_components [orR64Imm8Effect_components]⟩

theorem adcR64Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR64Imm8Effect_local, by lift_reads [adcR64Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR64Imm8Effect_components]⟩

theorem adcR64Imm8Effect_fresh (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm)) f := by
  lift_fresh [adcR64Imm8Effect, atFlags]

theorem sbbR64Imm8Effect_fresh (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm)) f := by
  lift_fresh [sbbR64Imm8Effect, atFlags]

theorem xorR32Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (xorR32Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR32Imm8Effect_local, by lift_reads [xorR32Imm8Effect], by lift_closed, by lift_params,
    by lift_components [xorR32Imm8Effect_components]⟩

theorem cmpR16Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (cmpR16Imm8Effect p len dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR16Imm8Effect_local, by lift_reads [cmpR16Imm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpR16Imm8Effect_components]⟩

theorem addR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (addR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR32Imm32Effect_local, by lift_reads [addR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [addR32Imm32Effect_components]⟩

theorem andR64Imm32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (andR64Imm32Effect p dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR64Imm32Effect_local, by lift_reads [andR64Imm32Effect], by lift_closed, by lift_params,
    by lift_components [andR64Imm32Effect_components]⟩

theorem subR32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) :
    EffectFootprint p (subR32Imm32Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR32Imm32Effect_local, by lift_reads [subR32Imm32Effect], by lift_closed, by lift_params,
    by lift_components [subR32Imm32Effect_components]⟩

theorem addR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (addR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR8Imm8Effect_local, by lift_reads [addR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [addR8Imm8Effect_components]⟩


theorem sbbR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbR8Imm8Effect p len dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbR8Imm8Effect_local, by lift_reads [sbbR8Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbR8Imm8Effect_components]⟩

theorem sbbR8Imm8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbR8Imm8Effect p len dst imm)) f := by
  lift_fresh [sbbR8Imm8Effect, atFlags]

theorem andR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (andR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal andR8Imm8Effect_local, by lift_reads [andR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [andR8Imm8Effect_components]⟩

theorem xorR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (xorR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR8Imm8Effect_local, by lift_reads [xorR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [xorR8Imm8Effect_components]⟩

theorem testR8Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (testR8Imm8Effect p dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR8Imm8Effect_local, by lift_reads [testR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [testR8Imm8Effect_components]⟩

theorem orAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (orAlImm8Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal orAlImm8Effect_local, by lift_reads [orAlImm8Effect], by lift_closed, by lift_params,
    by lift_components [orAlImm8Effect_components]⟩

theorem incR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (incR32Effect p len dst) f := by
  lift_fresh [incR32Effect, incSpec]

theorem incR64Effect_fresh (p : BitVec 64) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (incR64Effect p dst) f := by
  lift_fresh [incR64Effect, incSpec]

theorem decR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (decR32Effect p len dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal decR32Effect_local, by lift_reads [decR32Effect, decSpec], by lift_closed, by lift_params,
    by lift_components [decR32Effect_components]⟩

theorem decR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (decR32Effect p len dst) f := by
  lift_fresh [decR32Effect, decSpec]

theorem notR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (notR8Effect p len dst) ([.gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal notR8Effect_local, by lift_reads [notR8Effect], by lift_closed, by lift_params,
    by lift_components [notR8Effect_components]⟩

theorem shlR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shlR32Effect p len dst c) f := by
  lift_fresh [shlR32Effect, shlFlags]

theorem shlR64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shlR64Effect p len dst c) f := by
  lift_fresh [shlR64Effect, shlFlags]

theorem shrR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrR32Effect p len dst c) f := by
  lift_fresh [shrR32Effect, shrFlags]

theorem shlR32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shlR32ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR32ClEffect_local, by lift_reads [shlR32ClEffect, shlR32Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR32ClEffect_components]⟩

theorem shrR32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shrR32ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR32ClEffect_local, by lift_reads [shrR32ClEffect, shrR32Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR32ClEffect_components]⟩

theorem shlR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shlR8Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR8Effect_local, by lift_reads [shlR8Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR8Effect_components]⟩

theorem shlR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shlR8Effect p len dst c) f := by
  lift_fresh [shlR8Effect, shlFlags]


theorem shrR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shrR8Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR8Effect_local, by lift_reads [shrR8Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR8Effect_components]⟩

theorem shrR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrR8Effect p len dst c) f := by
  lift_fresh [shrR8Effect, shrFlags]

theorem shlR8ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shlR8ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR8ClEffect_local, by lift_reads [shlR8ClEffect, shlR8Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR8ClEffect_components]⟩

theorem shrR8ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shrR8ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR8ClEffect_local, by lift_reads [shrR8ClEffect, shrR8Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR8ClEffect_components]⟩

theorem shldR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shldR64R64Effect p len dst src c) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shldR64R64Effect_local, by lift_reads [shldR64R64Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldR64R64Effect_components]⟩

theorem shldR64R64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shldR64R64Effect p len dst src c) f := by
  lift_fresh [shldR64R64Effect, shldFlags]

theorem shldR64R64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (shldR64R64ClEffect p len dst src) ([.gpr dst, .gpr src, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shldR64R64ClEffect_local, by lift_reads [shldR64R64ClEffect, shldR64R64Effect, shldFlags], by lift_closed, by lift_params,
    by lift_components [shldR64R64ClEffect_components]⟩

theorem shrdR64R64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) :
    EffectFootprint p (shrdR64R64Effect p len dst src c) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrdR64R64Effect_local, by lift_reads [shrdR64R64Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdR64R64Effect_components]⟩

theorem shrdR64R64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrdR64R64Effect p len dst src c) f := by
  lift_fresh [shrdR64R64Effect, shrdFlags]

theorem shrdR64R64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (shrdR64R64ClEffect p len dst src) ([.gpr dst, .gpr src, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrdR64R64ClEffect_local, by lift_reads [shrdR64R64ClEffect, shrdR64R64Effect, shrdFlags], by lift_closed, by lift_params,
    by lift_components [shrdR64R64ClEffect_components]⟩

theorem mulM64Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (mulM64Effect p len am) (([.gpr 0] : List Reg) ++ addrRegs am) []
      [.reg 0, .reg 2, .flags, .rip] :=
  ⟨.ofLocal mulM64Effect_local, by lift_reads [mulM64Effect, mulFlags], by lift_closed, by lift_params,
    by lift_components [mulM64Effect_components]⟩

theorem movsxR32M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movsxR32M8Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movsxR32M8Effect_local, by lift_reads [movsxR32M8Effect], by lift_closed, by lift_params,
    by lift_components [movsxR32M8Effect_components]⟩

theorem movR8R8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (movR8R8Effect p len dst src) ([.gpr src, .gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR8R8Effect_local, by lift_reads [movR8R8Effect], by lift_closed, by lift_params,
    by lift_components [movR8R8Effect_components]⟩

theorem setccM8Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (cc : BitVec 4) :
    EffectFootprint p (atFlags (condHolds cc) (setccM8Effect p len am)) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) (condFlags cc)
      [.rip] :=
  ⟨LocalWith.atFlags (condHolds_congr cc) fun _ => setccM8Effect_local, by lift_reads [setccM8Effect, atFlags, storeEffect], by lift_closed, by lift_params,
    by lift_components [atFlags, setccM8Effect, storeEffect_components]⟩

theorem addR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (addR64M64Effect p dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal addR64M64Effect_local, by lift_reads [addR64M64Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [addR64M64Effect_components]⟩

theorem orR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (orR64M64Effect p dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR64M64Effect_local, by lift_reads [orR64M64Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [orR64M64Effect_components]⟩

theorem adcR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR64M64Effect p dst am)) (([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR64M64Effect_local, by lift_reads [adcR64M64Effect, atFlags, movLoadLen], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR64M64Effect_components]⟩

theorem adcR64M64Effect_fresh (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR64M64Effect p dst am)) f := by
  lift_fresh [adcR64M64Effect, atFlags, movLoadLen]

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

theorem cmpMImm8Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (cmpMImm8Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpMImm8Effect_local, by lift_reads [cmpMImm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpMImm8Effect_components]⟩

theorem movM8Imm8RexEffect_footprint (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (movM8Imm8RexEffect p am imm) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM8Imm8RexEffect_local, by lift_reads [movM8Imm8RexEffect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM8Imm8RexEffect_components]⟩

end K256.Proofs.Sec1.LIR
