import P256.Proofs.Sec1Serialize.Tail.Selection.State
import P256.Proofs.Sec1Serialize.Tail.Selection.Memory
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize.Selection

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame
open Conversion (Stage)

theorem advance_index [bindings : Bindings] {s t : RamState}
    {boundary : ReturnBoundary} {bytes : Nat → UInt8} {infinity : Bool} {index : Nat}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (entry : Stored s t boundary bytes infinity index) (hi : index < 65) :
    ∃ u, LoopState s u boundary bytes infinity (index + 1) := by
  have hc1 : CodeIn (codeRange 0x1111c5 [0x48, 0xff, 0xc2]) t :=
    programText_slice (programLoaded_codeIn entry.stage.loaded) 0x111c5 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t1, hs1, hr1, he1⟩ := inc_r64_effect_step 0x1111c5 0x48 0xc2
    (by simp [RexWPrefix]) (by decide) (by decide) t entry.stage.ready hc1 entry.rip
  change (incR64Effect 0x1111c5 2 t).Holds t t1 at he1
  have stage1 := Conversion.Stage.step_registers pre entry.stage hs1 hr1 he1
    (by simp [Effect.components, incR64Effect, Write.component, Operand.component])
    (by simp) (inProgram_of_textOffset 0x111c8 (by decide))
  have hm1 : t1.external = t.external := he1.agrees.external (by simp [Component.Covers])
  have hn1 : t1.regValue .rdx = BitVec.ofNat 64 (index + 1) := by
    have hw : t1.regValue .rdx = t.regValue .rdx + 1 := he1.writes
    rw [hw, entry.counter, BitVec.ofNat_add]
    rfl
  have hc2 : CodeIn (codeRange 0x1111c8 [0x48, 0x83, 0xfa, 0x41]) t1 :=
    programText_slice (programLoaded_codeIn stage1.loaded) 0x111c8 _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨t2, hs2, hr2, he2⟩ := cmp_r64_imm8_effect_step 0x1111c8 0x48 0xfa 65
    (by simp [RexWPrefix]) (by decide) (by decide) t1 hr1 hc2 he1.rip
  change (cmpR64Imm8Effect 0x1111c8 2 65 t1).Holds t1 t2 at he2
  have stage2 := Conversion.Stage.step_registers pre stage1 hs2 hr2 he2
    (by simp [Effect.components, cmpR64Imm8Effect])
    (by simp) (inProgram_of_textOffset 0x111cc (by decide))
  have hm2 : t2.external = t.external :=
    (he2.agrees.external (by simp [Component.Covers])).trans hm1
  have hzero : (StatusFlags.ofRFLAGS t2.RFLAGS).ZF = decide (index + 1 = 65) := by
    have hz : (StatusFlags.ofRFLAGS t2.RFLAGS).ZF = (t1.regValue .rdx - 65 == 0) :=
      he2.flags.2.2.2.1
    rw [hz, hn1]
    change (BitVec.ofNat 64 (index + 1) - 65#64 == 0#64) = decide (index + 1 = 65)
    by_cases hidx : index + 1 = 65
    · rw [hidx]
      decide
    · have hne : BitVec.ofNat 64 (index + 1) - 65#64 ≠ 0#64 := by
        intro heq
        have hadd := congrArg (fun x : BitVec 64 => x + 65#64) heq
        rw [BitVec.sub_add_cancel, BitVec.zero_add] at hadd
        have hn := congrArg BitVec.toNat hadd
        simp only [BitVec.toNat_ofNat] at hn
        rw [Nat.mod_eq_of_lt (show index + 1 < 2^64 by omega)] at hn
        exact hidx hn
      simp [hne, hidx]
  have hc3 : CodeIn (codeRange 0x1111cc [0x75, 0xd2]) t2 :=
    programText_slice (programLoaded_codeIn stage2.loaded) 0x111cc _
      (by decide +kernel) (by decide +kernel)
  obtain ⟨u, hs3, hr3, he3⟩ := jcc_rel8_effect_step 0x1111cc 5 0xd2 t2 hr2 hc3
    ⟨he2.rip, by intro; decide⟩
  have next : (jccEffect 0x1111cc 2 5 ((0xd2 : BitVec 8).signExtend 64) t2).rip =
      if index + 1 < 65 then 0x1111a0 else 0x1111ce := by
    simp only [jccEffect, branchEffect, condHolds, hzero]
    by_cases hlt : index + 1 < 65
    · have hn : ¬ index + 1 = 65 := by omega
      simp [hlt, hn, branchTarget]
    · have heq : index + 1 = 65 := by omega
      simp [heq]
  have stage3 := Conversion.Stage.step_registers pre stage2 hs3 hr3 he3
    (by simp [jccEffect, branchEffect, Effect.components])
    (by simp [jccEffect]) (by
      rw [next]
      split
      · exact inProgram_of_textOffset 0x111a0 (by decide)
      · exact inProgram_of_textOffset 0x111ce (by decide))
  have hm3 : u.external = t.external :=
    (he3.agrees.external (by simp [jccEffect, Component.Covers])).trans hm2
  have he : AgreesExcept [.reg 2, .flags, .rip] t u :=
    ((he1.agrees.trans he2.agrees).trans he3.agrees).mono
      (by simp [jccEffect, Effect.components, incR64Effect, cmpR64Imm8Effect,
        branchEffect, Write.component, Operand.component])
  refine ⟨u, stage3, he3.rip.trans next, ?_, ?_, ?_, hm3 ▸ entry.source,
    hm3 ▸ entry.zeroSource, hm3 ▸ entry.selected⟩
  · exact (he.read (n := 8) (r := 0) (by simp)).trans entry.choice
  · exact (he3.agrees.read (n := 64) (r := 2) (by simp [jccEffect])).trans
      ((he2.agrees.read (n := 64) (r := 2) (by simp)).trans hn1)
  · exact (he.read (n := 64) (r := 5) (by simp)).trans entry.destination

end P256.Proofs.Sec1Serialize.Selection
