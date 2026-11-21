import K256.Proofs.Common.Lift.Footprint
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
namespace K256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG

theorem cmpR8Imm8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (cmpR8Imm8Effect p len dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpR8Imm8Effect_local, by lift_reads [cmpR8Imm8Effect], by lift_closed, by lift_params,
    by lift_components [cmpR8Imm8Effect_components]⟩

theorem testR8Imm8LowEffect_footprint (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    EffectFootprint p (testR8Imm8LowEffect p dst imm) ([.gpr dst]) []
      [.flags, .rip] :=
  ⟨.ofLocal testR8Imm8LowEffect_local, by lift_reads [testR8Imm8LowEffect], by lift_closed, by lift_params,
    by lift_components [testR8Imm8LowEffect_components]⟩

theorem andAlImm8Effect_footprint (p : BitVec 64) (imm : BitVec 8) :
    EffectFootprint p (andAlImm8Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal andAlImm8Effect_local, by lift_reads [andAlImm8Effect], by lift_closed, by lift_params,
    by lift_components [andAlImm8Effect_components]⟩

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

theorem orEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (orEaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal orEaxImm32Effect_local, by lift_reads [orEaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [orEaxImm32Effect_components]⟩

theorem andEaxImm32Effect_footprint (p : BitVec 64) (imm : BitVec 32) :
    EffectFootprint p (andEaxImm32Effect p imm) ([.gpr 0]) []
      [.reg 0, .flags, .rip] :=
  ⟨.ofLocal andEaxImm32Effect_local, by lift_reads [andEaxImm32Effect], by lift_closed, by lift_params,
    by lift_components [andEaxImm32Effect_components]⟩

theorem incR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (incR32Effect p len dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal incR32Effect_local, by lift_reads [incR32Effect, incSpec], by lift_closed, by lift_params,
    by lift_components [incR32Effect_components]⟩

theorem incR64Effect_footprint (p : BitVec 64) (dst : BitVec 5) :
    EffectFootprint p (incR64Effect p dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal incR64Effect_local, by lift_reads [incR64Effect, incSpec], by lift_closed, by lift_params,
    by lift_components [incR64Effect_components]⟩

theorem decR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (decR16Effect p len dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal decR16Effect_local, by lift_reads [decR16Effect, decSpec], by lift_closed, by lift_params,
    by lift_components [decR16Effect_components]⟩

theorem decR16Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (decR16Effect p len dst) f := by
  lift_fresh [decR16Effect, decSpec]

theorem decR64Effect_footprint (p : BitVec 64) (dst : BitVec 5) :
    EffectFootprint p (decR64Effect p dst) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal decR64Effect_local, by lift_reads [decR64Effect, decSpec], by lift_closed, by lift_params,
    by lift_components [decR64Effect_components]⟩

theorem decR64Effect_fresh (p : BitVec 64) (dst : BitVec 5) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (decR64Effect p dst) f := by
  lift_fresh [decR64Effect, decSpec]

theorem notR64Effect_footprint (p : BitVec 64) (dst : BitVec 5) :
    EffectFootprint p (notR64Effect p dst) ([.gpr dst]) []
      [.reg dst, .rip] :=
  ⟨.ofLocal notR64Effect_local, by lift_reads [notR64Effect], by lift_closed, by lift_params,
    by lift_components [notR64Effect_components]⟩

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

theorem negR8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (negR8Effect p len dst) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal negR8Effect_local, by lift_reads [negR8Effect], by lift_closed, by lift_params,
    by lift_components [negR8Effect_components]⟩

theorem shlR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shlR32Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR32Effect_local, by lift_reads [shlR32Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR32Effect_components]⟩

theorem shlR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shlR64Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR64Effect_local, by lift_reads [shlR64Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR64Effect_components]⟩

theorem shrR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shrR32Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR32Effect_local, by lift_reads [shrR32Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR32Effect_components]⟩

theorem shrR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (shrR64Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR64Effect_local, by lift_reads [shrR64Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR64Effect_components]⟩

theorem shrR64Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrR64Effect p len dst c) f := by
  lift_fresh [shrR64Effect, shrFlags]

theorem sarR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (sarR64Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal sarR64Effect_local, by lift_reads [sarR64Effect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarR64Effect_components]⟩

theorem shlR64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shlR64ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shlR64ClEffect_local, by lift_reads [shlR64ClEffect, shlR64Effect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlR64ClEffect_components]⟩

theorem shrR64ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (shrR64ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal shrR64ClEffect_local, by lift_reads [shrR64ClEffect, shrR64Effect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrR64ClEffect_components]⟩

end K256.Proofs.Lift
