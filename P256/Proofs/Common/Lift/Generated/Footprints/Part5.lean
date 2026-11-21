import P256.Proofs.Common.Lift.Footprint
import X86Proofs.Instructions.Cmp.Generated.MImm32.Triple
import X86Proofs.Instructions.Dec.Generated.M.Triple
import X86Proofs.Instructions.Dec.Generated.M8.Triple
import X86Proofs.Instructions.Inc.Generated.M.Triple
import X86Proofs.Instructions.Inc.Generated.M8.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple
import X86Proofs.Instructions.Mov.Generated.MImm32C7.Triple
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Mov.Generated.R8M8.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Neg.Generated.M.Triple
import X86Proofs.Instructions.Neg.Generated.M8.Triple
import X86Proofs.Instructions.Not.Generated.M.Triple
import X86Proofs.Instructions.Not.Generated.M8.Triple
import X86Proofs.Instructions.Rol.Generated.M.Triple
import X86Proofs.Instructions.Rol.Generated.M8.Triple
import X86Proofs.Instructions.Rol.Generated.M8Cl.Triple
import X86Proofs.Instructions.Rol.Generated.MCl.Triple
import X86Proofs.Instructions.Ror.Generated.M.Triple
import X86Proofs.Instructions.Ror.Generated.M8.Triple
import X86Proofs.Instructions.Ror.Generated.M8Cl.Triple
import X86Proofs.Instructions.Ror.Generated.MCl.Triple
import X86Proofs.Instructions.Sal.Generated.M.Triple
import X86Proofs.Instructions.Sal.Generated.M8.Triple
import X86Proofs.Instructions.Sal.Generated.M8Cl.Triple
import X86Proofs.Instructions.Sal.Generated.MCl.Triple
import X86Proofs.Instructions.Sar.Generated.M.Triple
import X86Proofs.Instructions.Sar.Generated.M8.Triple
import X86Proofs.Instructions.Sar.Generated.M8Cl.Triple
import X86Proofs.Instructions.Sar.Generated.MCl.Triple
import X86Proofs.Instructions.Shl.Generated.M.Triple
import X86Proofs.Instructions.Shl.Generated.M8.Triple
import X86Proofs.Instructions.Shl.Generated.M8Cl.Triple
import X86Proofs.Instructions.Shl.Generated.MCl.Triple
import X86Proofs.Instructions.Shr.Generated.M.Triple
import X86Proofs.Instructions.Shr.Generated.M8.Triple
import X86Proofs.Instructions.Shr.Generated.M8Cl.Triple
import X86Proofs.Instructions.Shr.Generated.MCl.Triple
import X86Proofs.Instructions.Test.Generated.MImm32.Triple

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG

theorem cmpMImm32Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (cmpMImm32Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal cmpMImm32Effect_local, by lift_reads [cmpMImm32Effect], by lift_closed, by lift_params,
    by lift_components [cmpMImm32Effect_components]⟩

theorem testMImm32Effect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (testMImm32Effect p len 32 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal testMImm32Effect_local, by lift_reads [testMImm32Effect], by lift_closed, by lift_params,
    by lift_components [testMImm32Effect_components]⟩

theorem testMImm32Effect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (testMImm32Effect p len 64 am imm) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal testMImm32Effect_local, by lift_reads [testMImm32Effect], by lift_closed, by lift_params,
    by lift_components [testMImm32Effect_components]⟩

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

theorem decMEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (decMEffect p len 32 am) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal decMEffect_local32, by lift_reads [decMEffect, decSpec], by lift_closed, by lift_params,
    by lift_components [decMEffect_components]⟩

theorem decMEffect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (decMEffect p len 32 am) f := by
  lift_fresh [decMEffect, decSpec]

theorem decMEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (decMEffect p len 64 am) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal decMEffect_local64, by lift_reads [decMEffect, decSpec], by lift_closed, by lift_params,
    by lift_components [decMEffect_components]⟩

theorem decMEffect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (decMEffect p len 64 am) f := by
  lift_fresh [decMEffect, decSpec]

theorem notMEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (notMEffect p len 32 am) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal notMEffect_local32, by lift_reads [notMEffect], by lift_closed, by lift_params,
    by lift_components [notMEffect_components]⟩

theorem notMEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (notMEffect p len 64 am) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal notMEffect_local64, by lift_reads [notMEffect], by lift_closed, by lift_params,
    by lift_components [notMEffect_components]⟩

theorem negMEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (negMEffect p len 32 am) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal negMEffect_local32, by lift_reads [negMEffect], by lift_closed, by lift_params,
    by lift_components [negMEffect_components]⟩

theorem negMEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (negMEffect p len 64 am) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal negMEffect_local64, by lift_reads [negMEffect], by lift_closed, by lift_params,
    by lift_components [negMEffect_components]⟩

theorem incMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (incMEffect p len 8 am) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal incMEffect_local8, by lift_reads [incMEffect, incSpec], by lift_closed, by lift_params,
    by lift_components [incMEffect_components]⟩

theorem incMEffect8_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (incMEffect p len 8 am) f := by
  lift_fresh [incMEffect, incSpec]

theorem decMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (decMEffect p len 8 am) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal decMEffect_local8, by lift_reads [decMEffect, decSpec], by lift_closed, by lift_params,
    by lift_components [decMEffect_components]⟩

theorem decMEffect8_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) :
    ∀ f ∈ ([.PF, .AF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (decMEffect p len 8 am) f := by
  lift_fresh [decMEffect, decSpec]

theorem notMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (notMEffect p len 8 am) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal notMEffect_local8, by lift_reads [notMEffect], by lift_closed, by lift_params,
    by lift_components [notMEffect_components]⟩

theorem negMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (negMEffect p len 8 am) (addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal negMEffect_local8, by lift_reads [negMEffect], by lift_closed, by lift_params,
    by lift_components [negMEffect_components]⟩

theorem rolMEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (rolMEffect p len 32 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rolMEffect_local32, by lift_reads [rolMEffect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolMEffect_components]⟩

theorem rolMEffect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rolMEffect p len 32 am c) f := by
  lift_fresh [rolMEffect, rolFlags]

theorem rolMEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (rolMEffect p len 64 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rolMEffect_local64, by lift_reads [rolMEffect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolMEffect_components]⟩

theorem rolMEffect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rolMEffect p len 64 am c) f := by
  lift_fresh [rolMEffect, rolFlags]

theorem rorMEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (rorMEffect p len 32 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rorMEffect_local32, by lift_reads [rorMEffect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorMEffect_components]⟩

theorem rorMEffect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rorMEffect p len 32 am c) f := by
  lift_fresh [rorMEffect, rorFlags]

theorem rorMEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (rorMEffect p len 64 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rorMEffect_local64, by lift_reads [rorMEffect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorMEffect_components]⟩

theorem rorMEffect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rorMEffect p len 64 am c) f := by
  lift_fresh [rorMEffect, rorFlags]

theorem shlMEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (shlMEffect p len 32 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shlMEffect_local32, by lift_reads [shlMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlMEffect_components]⟩

theorem shlMEffect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shlMEffect p len 32 am c) f := by
  lift_fresh [shlMEffect, shlFlags]

theorem shlMEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (shlMEffect p len 64 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shlMEffect_local64, by lift_reads [shlMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlMEffect_components]⟩

theorem shlMEffect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shlMEffect p len 64 am c) f := by
  lift_fresh [shlMEffect, shlFlags]

theorem salMEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (salMEffect p len 32 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal salMEffect_local32, by lift_reads [salMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salMEffect_components]⟩

theorem salMEffect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (salMEffect p len 32 am c) f := by
  lift_fresh [salMEffect, shlFlags]

theorem salMEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (salMEffect p len 64 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal salMEffect_local64, by lift_reads [salMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salMEffect_components]⟩

theorem salMEffect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (salMEffect p len 64 am c) f := by
  lift_fresh [salMEffect, shlFlags]

theorem shrMEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (shrMEffect p len 32 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shrMEffect_local32, by lift_reads [shrMEffect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrMEffect_components]⟩

theorem shrMEffect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrMEffect p len 32 am c) f := by
  lift_fresh [shrMEffect, shrFlags]

theorem shrMEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (shrMEffect p len 64 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shrMEffect_local64, by lift_reads [shrMEffect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrMEffect_components]⟩

theorem shrMEffect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrMEffect p len 64 am c) f := by
  lift_fresh [shrMEffect, shrFlags]

theorem sarMEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (sarMEffect p len 32 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal sarMEffect_local32, by lift_reads [sarMEffect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarMEffect_components]⟩

theorem sarMEffect32_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (sarMEffect p len 32 am c) f := by
  lift_fresh [sarMEffect, sarFlags]

theorem sarMEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (sarMEffect p len 64 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal sarMEffect_local64, by lift_reads [sarMEffect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarMEffect_components]⟩

theorem sarMEffect64_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (sarMEffect p len 64 am c) f := by
  lift_fresh [sarMEffect, sarFlags]

theorem rolMClEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (rolMClEffect p len 32 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rolMClEffect_local32, by lift_reads [rolMClEffect, rolMEffect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolMClEffect_components]⟩

theorem rolMClEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (rolMClEffect p len 64 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rolMClEffect_local64, by lift_reads [rolMClEffect, rolMEffect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolMClEffect_components]⟩

theorem rorMClEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (rorMClEffect p len 32 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rorMClEffect_local32, by lift_reads [rorMClEffect, rorMEffect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorMClEffect_components]⟩

theorem rorMClEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (rorMClEffect p len 64 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rorMClEffect_local64, by lift_reads [rorMClEffect, rorMEffect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorMClEffect_components]⟩

theorem shlMClEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (shlMClEffect p len 32 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shlMClEffect_local32, by lift_reads [shlMClEffect, shlMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlMClEffect_components]⟩

theorem shlMClEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (shlMClEffect p len 64 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shlMClEffect_local64, by lift_reads [shlMClEffect, shlMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlMClEffect_components]⟩

theorem salMClEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (salMClEffect p len 32 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal salMClEffect_local32, by lift_reads [salMClEffect, salMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salMClEffect_components]⟩

theorem salMClEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (salMClEffect p len 64 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal salMClEffect_local64, by lift_reads [salMClEffect, salMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salMClEffect_components]⟩

theorem shrMClEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (shrMClEffect p len 32 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shrMClEffect_local32, by lift_reads [shrMClEffect, shrMEffect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrMClEffect_components]⟩

theorem shrMClEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (shrMClEffect p len 64 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shrMClEffect_local64, by lift_reads [shrMClEffect, shrMEffect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrMClEffect_components]⟩

theorem sarMClEffect32_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (sarMClEffect p len 32 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal sarMClEffect_local32, by lift_reads [sarMClEffect, sarMEffect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarMClEffect_components]⟩

theorem sarMClEffect64_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (sarMClEffect p len 64 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal sarMClEffect_local64, by lift_reads [sarMClEffect, sarMEffect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarMClEffect_components]⟩

theorem rolMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (rolMEffect p len 8 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rolMEffect_local8, by lift_reads [rolMEffect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolMEffect_components]⟩

theorem rolMEffect8_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rolMEffect p len 8 am c) f := by
  lift_fresh [rolMEffect, rolFlags]

theorem rorMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (rorMEffect p len 8 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rorMEffect_local8, by lift_reads [rorMEffect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorMEffect_components]⟩

theorem rorMEffect8_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .OF] : List StatusFlag),
      FlagFresh [] (rorMEffect p len 8 am c) f := by
  lift_fresh [rorMEffect, rorFlags]

theorem shlMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (shlMEffect p len 8 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shlMEffect_local8, by lift_reads [shlMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlMEffect_components]⟩

theorem shlMEffect8_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shlMEffect p len 8 am c) f := by
  lift_fresh [shlMEffect, shlFlags]

theorem salMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (salMEffect p len 8 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal salMEffect_local8, by lift_reads [salMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salMEffect_components]⟩

theorem salMEffect8_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (salMEffect p len 8 am c) f := by
  lift_fresh [salMEffect, shlFlags]

theorem shrMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (shrMEffect p len 8 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shrMEffect_local8, by lift_reads [shrMEffect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrMEffect_components]⟩

theorem shrMEffect8_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (shrMEffect p len 8 am c) f := by
  lift_fresh [shrMEffect, shrFlags]

theorem sarMEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) :
    EffectFootprint p (sarMEffect p len 8 am c) (([.flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal sarMEffect_local8, by lift_reads [sarMEffect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarMEffect_components]⟩

theorem sarMEffect8_fresh (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (hc : c ≠ 0) :
    ∀ f ∈ ([.CF, .PF, .ZF, .SF, .OF] : List StatusFlag),
      FlagFresh [] (sarMEffect p len 8 am c) f := by
  lift_fresh [sarMEffect, sarFlags]

theorem rolMClEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (rolMClEffect p len 8 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rolMClEffect_local8, by lift_reads [rolMClEffect, rolMEffect, rolFlags], by lift_closed, by lift_params,
    by lift_components [rolMClEffect_components]⟩

theorem rorMClEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (rorMClEffect p len 8 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal rorMClEffect_local8, by lift_reads [rorMClEffect, rorMEffect, rorFlags], by lift_closed, by lift_params,
    by lift_components [rorMClEffect_components]⟩

theorem shlMClEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (shlMClEffect p len 8 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shlMClEffect_local8, by lift_reads [shlMClEffect, shlMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [shlMClEffect_components]⟩

theorem salMClEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (salMClEffect p len 8 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal salMClEffect_local8, by lift_reads [salMClEffect, salMEffect, shlFlags], by lift_closed, by lift_params,
    by lift_components [salMClEffect_components]⟩

theorem shrMClEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (shrMClEffect p len 8 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal shrMClEffect_local8, by lift_reads [shrMClEffect, shrMEffect, shrFlags], by lift_closed, by lift_params,
    by lift_components [shrMClEffect_components]⟩

theorem sarMClEffect8_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) :
    EffectFootprint p (sarMClEffect p len 8 am) (([.gpr 1, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF] : List Reg) ++ addrRegs am) []
      [.flags, .rip] :=
  ⟨.ofLocal sarMClEffect_local8, by lift_reads [sarMClEffect, sarMEffect, sarFlags], by lift_closed, by lift_params,
    by lift_components [sarMClEffect_components]⟩

theorem movR32M32Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movR32M32Effect p dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR32M32Effect_local, by lift_reads [movR32M32Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [movR32M32Effect_components]⟩

theorem movR64M64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movR64M64Effect p dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR64M64Effect_local, by lift_reads [movR64M64Effect, movLoadLen], by lift_closed, by lift_params,
    by lift_components [movR64M64Effect_components]⟩

theorem movR16M16Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movR16M16Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR16M16Effect_local, by lift_reads [movR16M16Effect], by lift_closed, by lift_params,
    by lift_components [movR16M16Effect_components]⟩

theorem movR32M32LowEffect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movR32M32LowEffect p dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR32M32LowEffect_local, by lift_reads [movR32M32LowEffect], by lift_closed, by lift_params,
    by lift_components [movR32M32LowEffect_components]⟩

theorem movR8M8Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movR8M8Effect p len dst am) (([.gpr dst] : List Reg) ++ addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal movR8M8Effect_local, by lift_reads [movR8M8Effect], by lift_closed, by lift_params,
    by lift_components [movR8M8Effect_components]⟩

theorem movM16Imm16Effect_footprint (p : BitVec 64) (am : AddrMode) (imm : BitVec 16) :
    EffectFootprint p (movM16Imm16Effect p am imm) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM16Imm16Effect_local, by lift_reads [movM16Imm16Effect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM16Imm16Effect_components]⟩

theorem movM32R32Effect_footprint (p : BitVec 64) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movM32R32Effect p src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM32R32Effect_local, by lift_reads [movM32R32Effect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM32R32Effect_components]⟩

theorem movM64Imm32Effect_footprint (p : BitVec 64) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (movM64Imm32Effect p am imm) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM64Imm32Effect_local, by lift_reads [movM64Imm32Effect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM64Imm32Effect_components]⟩

theorem movM64R64Effect_footprint (p : BitVec 64) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movM64R64Effect p src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM64R64Effect_local, by lift_reads [movM64R64Effect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM64R64Effect_components]⟩

theorem movM8Imm8Effect_footprint (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (movM8Imm8Effect p am imm) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM8Imm8Effect_local, by lift_reads [movM8Imm8Effect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM8Imm8Effect_components]⟩

theorem movM8Imm8RexEffect_footprint (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    EffectFootprint p (movM8Imm8RexEffect p am imm) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM8Imm8RexEffect_local, by lift_reads [movM8Imm8RexEffect, storeEffect, storeAddrAt], by lift_closed, by lift_params,
    by lift_components [movM8Imm8RexEffect_components]⟩

theorem movM16R16Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movM16R16Effect p len src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM16R16Effect_local, by lift_reads [movM16R16Effect, storeEffect], by lift_closed, by lift_params,
    by lift_components [movM16R16Effect, storeEffect_components]⟩

theorem movM32R32LowEffect_footprint (p : BitVec 64) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movM32R32LowEffect p src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM32R32LowEffect_local, by lift_reads [movM32R32LowEffect, storeEffect], by lift_closed, by lift_params,
    by lift_components [movM32R32LowEffect, storeEffect_components]⟩

theorem movM8R8Effect_footprint (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    EffectFootprint p (movM8R8Effect p len src am) (([.gpr src] : List Reg) ++ addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM8R8Effect_local, by lift_reads [movM8R8Effect, storeEffect], by lift_closed, by lift_params,
    by lift_components [movM8R8Effect, storeEffect_components]⟩

theorem movM32Imm32Effect_footprint (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) :
    EffectFootprint p (movM32Imm32Effect p len am imm) (addrRegs am) []
      [.rip] :=
  ⟨.ofLocal movM32Imm32Effect_local, by lift_reads [movM32Imm32Effect, storeEffect], by lift_closed, by lift_params,
    by lift_components [movM32Imm32Effect, storeEffect_components]⟩

theorem leaR64Effect_footprint (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (leaR64Effect p dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal leaR64Effect_local, by lift_reads [leaR64Effect, leaLen], by lift_closed, by lift_params,
    by lift_components [leaR64Effect_components]⟩

theorem leaR32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) :
    EffectFootprint p (leaR32Effect p len dst am) (addrRegs am) []
      [.reg dst, .rip] :=
  ⟨.ofLocal leaR32Effect_local, by lift_reads [leaR32Effect, leaSpec], by lift_closed, by lift_params,
    by lift_components [leaR32Effect_components]⟩

end P256.Proofs.Lift
