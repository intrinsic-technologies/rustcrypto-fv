import AesGcm.Proofs.Copied.X86Proofs.Lift.Footprint
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

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG

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

theorem negR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (negR32Effect p len dst) ([.gpr dst]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal negR32Effect_local, by lift_reads [negR32Effect], by lift_closed, by lift_params,
    by lift_components [negR32Effect_components]⟩

theorem rolR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rolR16Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR16Effect_local, by lift_reads [rolR16Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR16Effect_components]⟩

theorem rolR64Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rolR64Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rolR64Effect_local, by lift_reads [rolR64Effect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolR64Effect_components]⟩

theorem rorR16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) :
    EffectFootprint p (rorR16Effect p len dst c) ([.gpr dst, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rorR16Effect_local, by lift_reads [rorR16Effect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorR16Effect_components]⟩

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

theorem rorR16ClEffect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    EffectFootprint p (rorR16ClEffect p len dst) ([.gpr dst, .gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.reg dst, .flags, .rip] :=
  ⟨.ofLocal rorR16ClEffect_local, by lift_reads [rorR16ClEffect, rorR16Effect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorR16ClEffect_components]⟩

end X86Proofs.Lift
