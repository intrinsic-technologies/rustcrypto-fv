import ChaCha20Poly1305.Proofs.Common.Lift.Footprint
import X86Proofs.Instructions.Adc.Generated.AccImm32.Triple
import X86Proofs.Instructions.Adc.Generated.AccImm8.Triple
import X86Proofs.Instructions.Adc.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.Add.Generated.AccImm8.Triple
import X86Proofs.Instructions.And.Generated.AccImm32.Triple
import X86Proofs.Instructions.And.Generated.AccImm8.Triple
import X86Proofs.Instructions.And.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.AccImm32.Triple
import X86Proofs.Instructions.Cmp.Generated.AccImm8.Triple
import X86Proofs.Instructions.Cmp.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Dec.Generated.R8.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Inc.Generated.R8.Triple
import X86Proofs.Instructions.Neg.Generated.R.Triple
import X86Proofs.Instructions.Neg.Generated.R8.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Not.Generated.R8.Triple
import X86Proofs.Instructions.Or.Generated.AccImm32.Triple
import X86Proofs.Instructions.Or.Generated.AccImm8.Triple
import X86Proofs.Instructions.Or.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Rol.Generated.Cl.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R8.Triple
import X86Proofs.Instructions.Ror.Generated.Cl.Triple
import X86Proofs.Instructions.Ror.Generated.R.Triple
import X86Proofs.Instructions.Ror.Generated.R8.Triple
import X86Proofs.Instructions.Sal.Generated.Cl.Triple
import X86Proofs.Instructions.Sal.Generated.R.Triple
import X86Proofs.Instructions.Sar.Generated.Cl.Triple
import X86Proofs.Instructions.Sar.Generated.R.Triple
import X86Proofs.Instructions.Sbb.Generated.AccImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.AccImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Shl.Generated.Cl.Triple
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Instructions.Shl.Generated.R8.Triple
import X86Proofs.Instructions.Shr.Generated.Cl.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Sub.Generated.AccImm32.Triple
import X86Proofs.Instructions.Sub.Generated.AccImm8.Triple
import X86Proofs.Instructions.Sub.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Test.Generated.AccImm32.Triple
import X86Proofs.Instructions.Test.Generated.AccImm8.Triple
import X86Proofs.Instructions.Test.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.AccImm32.Triple
import X86Proofs.Instructions.Xor.Generated.AccImm8.Triple
import X86Proofs.Instructions.Xor.Generated.R8Imm8.Triple

namespace ChaCha20Poly1305.Proofs.Lift
open X86Proofs

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG

theorem orR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (orR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal orR8Imm8Effect_local, by lift_reads [orR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [orR8Imm8Effect_components]⟩

theorem adcR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (adcR8Imm8Effect p len dst imm)) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg dst, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcR8Imm8Effect_local, by lift_reads [adcR8Imm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcR8Imm8Effect_components]⟩

theorem adcR8Imm8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcR8Imm8Effect p len dst imm)) f := by
  lift_fresh [adcR8Imm8Effect, atFlags]

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

theorem subR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (subR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal subR8Imm8Effect_local, by lift_reads [subR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [subR8Imm8Effect_components]⟩

theorem xorR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (xorR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal xorR8Imm8Effect_local, by lift_reads [xorR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [xorR8Imm8Effect_components]⟩

theorem cmpR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (cmpR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR8Imm8Effect_local, by lift_reads [cmpR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpR8Imm8Effect_components]⟩

theorem testR8Imm8Effect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (testR8Imm8Effect p dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR8Imm8Effect_local, by lift_reads [testR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [testR8Imm8Effect_components]⟩

theorem testR8Imm8LowEffect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (testR8Imm8LowEffect p dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR8Imm8LowEffect_local, by lift_reads [testR8Imm8LowEffect], by lift_closed, by lift_params,
    by lift_components [testR8Imm8LowEffect_components]⟩

theorem addAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (addAlImm8Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal addAlImm8Effect_local, by lift_reads [addAlImm8Effect], by lift_closed, by lift_params,
    by lift_components [addAlImm8Effect_components]⟩

theorem orAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (orAlImm8Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal orAlImm8Effect_local, by lift_reads [orAlImm8Effect], by lift_closed, by lift_params,
    by lift_components [orAlImm8Effect_components]⟩

theorem adcAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (adcAlImm8Effect p imm)) ([.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg 0, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcAlImm8Effect_local, by lift_reads [adcAlImm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcAlImm8Effect_components]⟩

theorem adcAlImm8Effect_fresh (p : BitVec 64) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcAlImm8Effect p imm)) f := by
  lift_fresh [adcAlImm8Effect, atFlags]

theorem sbbAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbAlImm8Effect p imm)) ([.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg 0, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbAlImm8Effect_local, by lift_reads [sbbAlImm8Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbAlImm8Effect_components]⟩

theorem sbbAlImm8Effect_fresh (p : BitVec 64) (imm : BitVec 8) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbAlImm8Effect p imm)) f := by
  lift_fresh [sbbAlImm8Effect, atFlags]

theorem andAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (andAlImm8Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal andAlImm8Effect_local, by lift_reads [andAlImm8Effect], by lift_closed, by lift_params,
    by lift_components [andAlImm8Effect_components]⟩

theorem subAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (subAlImm8Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal subAlImm8Effect_local, by lift_reads [subAlImm8Effect], by lift_closed, by lift_params,
    by lift_components [subAlImm8Effect_components]⟩

theorem xorAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (xorAlImm8Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal xorAlImm8Effect_local, by lift_reads [xorAlImm8Effect], by lift_closed, by lift_params,
    by lift_components [xorAlImm8Effect_components]⟩

theorem cmpAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (cmpAlImm8Effect p imm) ([.gpr 0]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpAlImm8Effect_local, by lift_reads [cmpAlImm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpAlImm8Effect_components]⟩

theorem testAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (testAlImm8Effect p imm) ([.gpr 0]) []
      [.flags, .rip] :=
  ⟨.ofLocal testAlImm8Effect_local, by lift_reads [testAlImm8Effect], by lift_closed, by lift_params,
    by lift_components [testAlImm8Effect_components]⟩

theorem addAxImm16Effect_footprint (p : BitVec 64) (imm : BitVec 16) :
    EffectFootprint p (addAxImm16Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal addAxImm16Effect_local, by lift_reads [addAxImm16Effect], by lift_closed, by lift_params,
    by lift_components [addAxImm16Effect_components]⟩

theorem addEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (addEaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal addEaxImm32Effect_local, by lift_reads [addEaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [addEaxImm32Effect_components]⟩

theorem addRaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (addRaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal addRaxImm32Effect_local, by lift_reads [addRaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [addRaxImm32Effect_components]⟩

theorem orAxImm16Effect_footprint (p : BitVec 64) (imm : BitVec 16) :
    EffectFootprint p (orAxImm16Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal orAxImm16Effect_local, by lift_reads [orAxImm16Effect], by lift_closed, by lift_params,
    by lift_components [orAxImm16Effect_components]⟩

theorem orEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (orEaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal orEaxImm32Effect_local, by lift_reads [orEaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [orEaxImm32Effect_components]⟩

theorem orRaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (orRaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal orRaxImm32Effect_local, by lift_reads [orRaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [orRaxImm32Effect_components]⟩

theorem adcAxImm16Effect_footprint (p : BitVec 64) (imm : BitVec 16) :
    EffectFootprint p (atFlags StatusFlags.CF (adcAxImm16Effect p imm)) ([.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg 0, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcAxImm16Effect_local, by lift_reads [adcAxImm16Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcAxImm16Effect_components]⟩

theorem adcAxImm16Effect_fresh (p : BitVec 64) (imm : BitVec 16) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcAxImm16Effect p imm)) f := by
  lift_fresh [adcAxImm16Effect, atFlags]

theorem adcEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (adcEaxImm32Effect p imm)) ([.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg 0, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcEaxImm32Effect_local, by lift_reads [adcEaxImm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcEaxImm32Effect_components]⟩

theorem adcEaxImm32Effect_fresh (p : BitVec 64) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcEaxImm32Effect p imm)) f := by
  lift_fresh [adcEaxImm32Effect, atFlags]

theorem adcRaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (adcRaxImm32Effect p imm)) ([.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg 0, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => adcRaxImm32Effect_local, by lift_reads [adcRaxImm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, adcRaxImm32Effect_components]⟩

theorem adcRaxImm32Effect_fresh (p : BitVec 64) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (adcRaxImm32Effect p imm)) f := by
  lift_fresh [adcRaxImm32Effect, atFlags]

theorem sbbAxImm16Effect_footprint (p : BitVec 64) (imm : BitVec 16) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbAxImm16Effect p imm)) ([.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg 0, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbAxImm16Effect_local, by lift_reads [sbbAxImm16Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbAxImm16Effect_components]⟩

theorem sbbAxImm16Effect_fresh (p : BitVec 64) (imm : BitVec 16) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbAxImm16Effect p imm)) f := by
  lift_fresh [sbbAxImm16Effect, atFlags]

theorem sbbEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbEaxImm32Effect p imm)) ([.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg 0, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbEaxImm32Effect_local, by lift_reads [sbbEaxImm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbEaxImm32Effect_components]⟩

theorem sbbEaxImm32Effect_fresh (p : BitVec 64) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbEaxImm32Effect p imm)) f := by
  lift_fresh [sbbEaxImm32Effect, atFlags]

theorem sbbRaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (atFlags StatusFlags.CF (sbbRaxImm32Effect p imm)) ([.gpr 0, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) [.CF]
      [.reg 0, .flags, .rip] :=
  ⟨LocalWith.atFlags carry_congr fun _ => sbbRaxImm32Effect_local, by lift_reads [sbbRaxImm32Effect, atFlags], by lift_closed, by lift_params,
    by lift_components [atFlags, sbbRaxImm32Effect_components]⟩

theorem sbbRaxImm32Effect_fresh (p : BitVec 64) (imm : BitVec 32) :
    ∀ f ∈ ([.CF, .PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [.CF] (atFlags StatusFlags.CF (sbbRaxImm32Effect p imm)) f := by
  lift_fresh [sbbRaxImm32Effect, atFlags]

theorem andAxImm16Effect_footprint (p : BitVec 64) (imm : BitVec 16) :
    EffectFootprint p (andAxImm16Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal andAxImm16Effect_local, by lift_reads [andAxImm16Effect], by lift_closed, by lift_params,
    by lift_components [andAxImm16Effect_components]⟩

theorem andEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (andEaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal andEaxImm32Effect_local, by lift_reads [andEaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [andEaxImm32Effect_components]⟩

theorem andRaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (andRaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal andRaxImm32Effect_local, by lift_reads [andRaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [andRaxImm32Effect_components]⟩

theorem subAxImm16Effect_footprint (p : BitVec 64) (imm : BitVec 16) :
    EffectFootprint p (subAxImm16Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal subAxImm16Effect_local, by lift_reads [subAxImm16Effect], by lift_closed, by lift_params,
    by lift_components [subAxImm16Effect_components]⟩

theorem subEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (subEaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal subEaxImm32Effect_local, by lift_reads [subEaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [subEaxImm32Effect_components]⟩

theorem subRaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (subRaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal subRaxImm32Effect_local, by lift_reads [subRaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [subRaxImm32Effect_components]⟩

theorem xorAxImm16Effect_footprint (p : BitVec 64) (imm : BitVec 16) :
    EffectFootprint p (xorAxImm16Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal xorAxImm16Effect_local, by lift_reads [xorAxImm16Effect], by lift_closed, by lift_params,
    by lift_components [xorAxImm16Effect_components]⟩

theorem xorEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (xorEaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal xorEaxImm32Effect_local, by lift_reads [xorEaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [xorEaxImm32Effect_components]⟩

theorem xorRaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (xorRaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal xorRaxImm32Effect_local, by lift_reads [xorRaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [xorRaxImm32Effect_components]⟩

theorem cmpAxImm16Effect_footprint (p : BitVec 64) (imm : BitVec 16) :
    EffectFootprint p (cmpAxImm16Effect p imm) ([.gpr 0]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpAxImm16Effect_local, by lift_reads [cmpAxImm16Effect], by lift_closed, by lift_params,
    by lift_components [cmpAxImm16Effect_components]⟩

theorem cmpEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (cmpEaxImm32Effect p imm) ([.gpr 0]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpEaxImm32Effect_local, by lift_reads [cmpEaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [cmpEaxImm32Effect_components]⟩

theorem cmpRaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (cmpRaxImm32Effect p imm) ([.gpr 0]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpRaxImm32Effect_local, by lift_reads [cmpRaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [cmpRaxImm32Effect_components]⟩

theorem testAxImm16Effect_footprint (p : BitVec 64) (imm : BitVec 16) :
    EffectFootprint p (testAxImm16Effect p imm) ([.gpr 0]) []
      [.flags, .rip] :=
  ⟨.ofLocal testAxImm16Effect_local, by lift_reads [testAxImm16Effect], by lift_closed, by lift_params,
    by lift_components [testAxImm16Effect_components]⟩

theorem testEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (testEaxImm32Effect p imm) ([.gpr 0]) []
      [.flags, .rip] :=
  ⟨.ofLocal testEaxImm32Effect_local, by lift_reads [testEaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [testEaxImm32Effect_components]⟩

theorem testRaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (testRaxImm32Effect p imm) ([.gpr 0]) []
      [.flags, .rip] :=
  ⟨.ofLocal testRaxImm32Effect_local, by lift_reads [testRaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [testRaxImm32Effect_components]⟩

theorem incR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (incR16Effect p len dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal incR16Effect_local, by lift_reads [incR16Effect, incSpec], by lift_closed, by lift_params,
    by lift_components [incR16Effect_components]⟩

theorem incR16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (incR16Effect p len dst) f := by
  lift_fresh [incR16Effect, incSpec]

theorem incR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (incR32Effect p len dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal incR32Effect_local, by lift_reads [incR32Effect, incSpec], by lift_closed, by lift_params,
    by lift_components [incR32Effect_components]⟩

theorem incR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (incR32Effect p len dst) f := by
  lift_fresh [incR32Effect, incSpec]

theorem incR64Effect_footprint (p : BitVec 64) (dst : BitVec 5) :
    EffectFootprint p (incR64Effect p dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal incR64Effect_local, by lift_reads [incR64Effect, incSpec], by lift_closed, by lift_params,
    by lift_components [incR64Effect_components]⟩

theorem incR64Effect_fresh (p : BitVec 64) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (incR64Effect p dst) f := by
  lift_fresh [incR64Effect, incSpec]

theorem decR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (decR16Effect p len dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal decR16Effect_local, by lift_reads [decR16Effect, decSpec], by lift_closed, by lift_params,
    by lift_components [decR16Effect_components]⟩

theorem decR16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (decR16Effect p len dst) f := by
  lift_fresh [decR16Effect, decSpec]

theorem decR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (decR32Effect p len dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal decR32Effect_local, by lift_reads [decR32Effect, decSpec], by lift_closed, by lift_params,
    by lift_components [decR32Effect_components]⟩

theorem decR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (decR32Effect p len dst) f := by
  lift_fresh [decR32Effect, decSpec]

theorem decR64Effect_footprint (p : BitVec 64) (dst : BitVec 5) :
    EffectFootprint p (decR64Effect p dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal decR64Effect_local, by lift_reads [decR64Effect, decSpec], by lift_closed, by lift_params,
    by lift_components [decR64Effect_components]⟩

theorem decR64Effect_fresh (p : BitVec 64) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (decR64Effect p dst) f := by
  lift_fresh [decR64Effect, decSpec]

theorem notR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (notR16Effect p len dst) ([.gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal notR16Effect_local, by lift_reads [notR16Effect], by lift_closed, by lift_params,
    by lift_components [notR16Effect_components]⟩

theorem notR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (notR32Effect p len dst) ([.gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal notR32Effect_local, by lift_reads [notR32Effect], by lift_closed, by lift_params,
    by lift_components [notR32Effect_components]⟩

theorem notR64Effect_footprint (p : BitVec 64) (dst : BitVec 5) :
    EffectFootprint p (notR64Effect p dst) ([.gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal notR64Effect_local, by lift_reads [notR64Effect], by lift_closed, by lift_params,
    by lift_components [notR64Effect_components]⟩

theorem negR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (negR16Effect p len dst) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal negR16Effect_local, by lift_reads [negR16Effect], by lift_closed, by lift_params,
    by lift_components [negR16Effect_components]⟩

theorem negR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (negR32Effect p len dst) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal negR32Effect_local, by lift_reads [negR32Effect], by lift_closed, by lift_params,
    by lift_components [negR32Effect_components]⟩

theorem negR64Effect_footprint (p : BitVec 64) (dst : BitVec 5) :
    EffectFootprint p (negR64Effect p dst) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal negR64Effect_local, by lift_reads [negR64Effect], by lift_closed, by lift_params,
    by lift_components [negR64Effect_components]⟩

theorem incR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (incR8Effect p len dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal incR8Effect_local, by lift_reads [incR8Effect, incSpec], by lift_closed, by lift_params,
    by lift_components [incR8Effect_components]⟩

theorem incR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (incR8Effect p len dst) f := by
  lift_fresh [incR8Effect, incSpec]

theorem decR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (decR8Effect p len dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal decR8Effect_local, by lift_reads [decR8Effect, decSpec], by lift_closed, by lift_params,
    by lift_components [decR8Effect_components]⟩

theorem decR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (decR8Effect p len dst) f := by
  lift_fresh [decR8Effect, decSpec]

theorem notR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (notR8Effect p len dst) ([.gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal notR8Effect_local, by lift_reads [notR8Effect], by lift_closed, by lift_params,
    by lift_components [notR8Effect_components]⟩

theorem negR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (negR8Effect p len dst) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal negR8Effect_local, by lift_reads [negR8Effect], by lift_closed, by lift_params,
    by lift_components [negR8Effect_components]⟩

theorem rolR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rolR16Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR16Effect_local, by lift_reads [rolR16Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR16Effect_components]⟩

theorem rolR16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rolR16Effect p len dst c) f := by
  lift_fresh [rolR16Effect, rolFlags]

theorem rolR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rolR32Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR32Effect_local, by lift_reads [rolR32Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR32Effect_components]⟩

theorem rolR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rolR32Effect p len dst c) f := by
  lift_fresh [rolR32Effect, rolFlags]

theorem rolR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rolR64Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR64Effect_local, by lift_reads [rolR64Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR64Effect_components]⟩

theorem rolR64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rolR64Effect p len dst c) f := by
  lift_fresh [rolR64Effect, rolFlags]

theorem rorR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rorR16Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rorR16Effect_local, by lift_reads [rorR16Effect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorR16Effect_components]⟩

theorem rorR16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rorR16Effect p len dst c) f := by
  lift_fresh [rorR16Effect, rorFlags]

theorem rorR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rorR32Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rorR32Effect_local, by lift_reads [rorR32Effect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorR32Effect_components]⟩

theorem rorR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rorR32Effect p len dst c) f := by
  lift_fresh [rorR32Effect, rorFlags]

theorem rorR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rorR64Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rorR64Effect_local, by lift_reads [rorR64Effect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorR64Effect_components]⟩

theorem rorR64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rorR64Effect p len dst c) f := by
  lift_fresh [rorR64Effect, rorFlags]

theorem shlR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shlR16Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR16Effect_local, by lift_reads [shlR16Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR16Effect_components]⟩

theorem shlR16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shlR16Effect p len dst c) f := by
  lift_fresh [shlR16Effect, shlFlags]

theorem shlR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shlR32Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR32Effect_local, by lift_reads [shlR32Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR32Effect_components]⟩

theorem shlR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shlR32Effect p len dst c) f := by
  lift_fresh [shlR32Effect, shlFlags]

theorem shlR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shlR64Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR64Effect_local, by lift_reads [shlR64Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR64Effect_components]⟩

theorem shlR64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shlR64Effect p len dst c) f := by
  lift_fresh [shlR64Effect, shlFlags]

theorem salR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (salR16Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal salR16Effect_local, by lift_reads [salR16Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salR16Effect_components]⟩

theorem salR16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (salR16Effect p len dst c) f := by
  lift_fresh [salR16Effect, shlFlags]

theorem salR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (salR32Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal salR32Effect_local, by lift_reads [salR32Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salR32Effect_components]⟩

theorem salR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (salR32Effect p len dst c) f := by
  lift_fresh [salR32Effect, shlFlags]

theorem salR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (salR64Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal salR64Effect_local, by lift_reads [salR64Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salR64Effect_components]⟩

theorem salR64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (salR64Effect p len dst c) f := by
  lift_fresh [salR64Effect, shlFlags]

theorem shrR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shrR16Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR16Effect_local, by lift_reads [shrR16Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR16Effect_components]⟩

theorem shrR16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrR16Effect p len dst c) f := by
  lift_fresh [shrR16Effect, shrFlags]

theorem shrR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shrR32Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR32Effect_local, by lift_reads [shrR32Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR32Effect_components]⟩

theorem shrR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrR32Effect p len dst c) f := by
  lift_fresh [shrR32Effect, shrFlags]

theorem shrR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shrR64Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR64Effect_local, by lift_reads [shrR64Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR64Effect_components]⟩

theorem shrR64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrR64Effect p len dst c) f := by
  lift_fresh [shrR64Effect, shrFlags]

theorem sarR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (sarR16Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR16Effect_local, by lift_reads [sarR16Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR16Effect_components]⟩

theorem sarR16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (sarR16Effect p len dst c) f := by
  lift_fresh [sarR16Effect, sarFlags]

theorem sarR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (sarR32Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR32Effect_local, by lift_reads [sarR32Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR32Effect_components]⟩

theorem sarR32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (sarR32Effect p len dst c) f := by
  lift_fresh [sarR32Effect, sarFlags]

theorem sarR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (sarR64Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR64Effect_local, by lift_reads [sarR64Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR64Effect_components]⟩

theorem sarR64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (sarR64Effect p len dst c) f := by
  lift_fresh [sarR64Effect, sarFlags]

theorem rolR16ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (rolR16ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR16ClEffect_local, by lift_reads [rolR16ClEffect, rolR16Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR16ClEffect_components]⟩

theorem rolR32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (rolR32ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR32ClEffect_local, by lift_reads [rolR32ClEffect, rolR32Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR32ClEffect_components]⟩

theorem rolR64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (rolR64ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR64ClEffect_local, by lift_reads [rolR64ClEffect, rolR64Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR64ClEffect_components]⟩

theorem rorR16ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (rorR16ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rorR16ClEffect_local, by lift_reads [rorR16ClEffect, rorR16Effect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorR16ClEffect_components]⟩

theorem rorR32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (rorR32ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rorR32ClEffect_local, by lift_reads [rorR32ClEffect, rorR32Effect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorR32ClEffect_components]⟩

theorem rorR64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (rorR64ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rorR64ClEffect_local, by lift_reads [rorR64ClEffect, rorR64Effect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorR64ClEffect_components]⟩

theorem shlR16ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shlR16ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR16ClEffect_local, by lift_reads [shlR16ClEffect, shlR16Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR16ClEffect_components]⟩

theorem shlR32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shlR32ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR32ClEffect_local, by lift_reads [shlR32ClEffect, shlR32Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR32ClEffect_components]⟩

theorem shlR64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shlR64ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR64ClEffect_local, by lift_reads [shlR64ClEffect, shlR64Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR64ClEffect_components]⟩

theorem salR16ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (salR16ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal salR16ClEffect_local, by lift_reads [salR16ClEffect, salR16Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salR16ClEffect_components]⟩

theorem salR32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (salR32ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal salR32ClEffect_local, by lift_reads [salR32ClEffect, salR32Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salR32ClEffect_components]⟩

theorem salR64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (salR64ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal salR64ClEffect_local, by lift_reads [salR64ClEffect, salR64Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salR64ClEffect_components]⟩

theorem shrR16ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shrR16ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR16ClEffect_local, by lift_reads [shrR16ClEffect, shrR16Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR16ClEffect_components]⟩

theorem shrR32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shrR32ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR32ClEffect_local, by lift_reads [shrR32ClEffect, shrR32Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR32ClEffect_components]⟩

theorem shrR64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shrR64ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR64ClEffect_local, by lift_reads [shrR64ClEffect, shrR64Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR64ClEffect_components]⟩

theorem sarR16ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (sarR16ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR16ClEffect_local, by lift_reads [sarR16ClEffect, sarR16Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR16ClEffect_components]⟩

theorem sarR32ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (sarR32ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR32ClEffect_local, by lift_reads [sarR32ClEffect, sarR32Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR32ClEffect_components]⟩

theorem sarR64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (sarR64ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR64ClEffect_local, by lift_reads [sarR64ClEffect, sarR64Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR64ClEffect_components]⟩

theorem rolR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rolR8Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR8Effect_local, by lift_reads [rolR8Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR8Effect_components]⟩

theorem rolR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rolR8Effect p len dst c) f := by
  lift_fresh [rolR8Effect, rolFlags]

theorem rorR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rorR8Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rorR8Effect_local, by lift_reads [rorR8Effect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorR8Effect_components]⟩

theorem rorR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rorR8Effect p len dst c) f := by
  lift_fresh [rorR8Effect, rorFlags]

theorem shlR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shlR8Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR8Effect_local, by lift_reads [shlR8Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR8Effect_components]⟩

theorem shlR8Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shlR8Effect p len dst c) f := by
  lift_fresh [shlR8Effect, shlFlags]

end ChaCha20Poly1305.Proofs.Lift
