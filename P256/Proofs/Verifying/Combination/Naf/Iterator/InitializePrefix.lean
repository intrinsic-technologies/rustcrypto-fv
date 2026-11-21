import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

def initializePrefixBytes : List UInt8 :=
  [0x48,0x89,0xfb,0x48,0x85,0xd2,0x74,0x22,0x48,0x83,0xfa,0x07,0x77,0x45]

def initializePrefixEffect (s : RamState) : Effect :=
  { rip := 0x1182e7
    writes := [⟨(Operand.reg 3 : Operand 64), s.regValue .rdi⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem initialize_prefix [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x118294 ∧ s.regValue .rdx = 32)
      (codeRange 0x118294 initializePrefixBytes) (Effect.post initializePrefixEffect) := by
  intro s ready code pre
  obtain ⟨t1, run1, ready1, effect1⟩ :=
    (mov_r64_r64_effect_step 0x118294 0x48 0xfb (by simp [RexWPrefix]) rfl).advances ready
      (code.mono (by simpa [initializePrefixBytes] using codeRange_slice_subset 0x118294 initializePrefixBytes 0 3))
      pre.1 (boundary_ne_program hout (inProgram_of_textOffset 0x18297 (by decide)))
  change (movR64R64Effect 0x118294 3 7 s).Holds s t1 at effect1
  have code1 := effect1.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code
  have rdx1 : t1.regValue .rdx = 32 :=
    (effect1.agrees.read (n := 64) (r := 2) (by simp)).trans pre.2
  obtain ⟨t2, run2, ready2, effect2⟩ :=
    (test_r64_r64_effect_step 0x118297 0x48 0xd2 (by simp [RexWPrefix]) rfl).advances ready1
      (code1.mono (codeRange_slice_subset 0x118294 initializePrefixBytes 3 3))
      effect1.rip (boundary_ne_program hout (inProgram_of_textOffset 0x1829a (by decide)))
  change (testR64R64Effect 0x118297 2 2 t1).Holds t1 t2 at effect2
  have code2 := effect2.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code1
  have zf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).ZF = false := by
    have h := effect2.flags.2.2.2.1
    change _ = ((t1.regValue .rdx &&& t1.regValue .rdx) == 0#64) at h
    simpa [rdx1] using h
  have next2 : (jccEffect 0x11829a 2 4 ((0x22 : BitVec 8).signExtend 64) t2).rip = 0x11829c := by
    simp [jccEffect, branchEffect, condHolds, zf2]
  obtain ⟨t3, run3, ready3, effect3⟩ := (jcc_rel8_effect_step 0x11829a 4 0x22).advances ready2
    (code2.mono (codeRange_slice_subset 0x118294 initializePrefixBytes 6 2))
    ⟨effect2.rip, by intro _; decide +kernel⟩
    (by rw [next2]; exact boundary_ne_program hout (inProgram_of_textOffset 0x1829c (by decide)))
  have code3 := effect3.codeIn (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _) code2
  have rdx3 : t3.regValue .rdx = 32 :=
    (effect3.agrees.read (n := 64) (r := 2) (by simp [jccEffect])).trans
      ((effect2.agrees.read (n := 64) (r := 2) (by simp)).trans rdx1)
  obtain ⟨t4, run4, ready4, effect4⟩ :=
    (cmp_r64_imm8_effect_step 0x11829c 0x48 0xfa 7 (by simp [RexWPrefix]) rfl rfl).advances ready3
      (code3.mono (codeRange_slice_subset 0x118294 initializePrefixBytes 8 4))
      (effect3.rip.trans next2) (boundary_ne_program hout (inProgram_of_textOffset 0x182a0 (by decide)))
  change (cmpR64Imm8Effect 0x11829c 2 7 t3).Holds t3 t4 at effect4
  have code4 := effect4.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code3
  have cf4 : (StatusFlags.ofRFLAGS t4.RFLAGS).CF = false := by
    have h := effect4.flags.1
    change _ = (t3.regValue .rdx).ult ((7#8).signExtend 64) at h
    simpa [rdx3] using h
  have zf4 : (StatusFlags.ofRFLAGS t4.RFLAGS).ZF = false := by
    have h := effect4.flags.2.2.2.1
    change _ = ((t3.regValue .rdx - (7#8).signExtend 64) == 0#64) at h
    simpa [rdx3] using h
  have next4 : (jccEffect 0x1182a0 2 7 ((0x45 : BitVec 8).signExtend 64) t4).rip = 0x1182e7 := by
    simp [jccEffect, branchEffect, condHolds, cf4, zf4, branchTarget]
  obtain ⟨t5, run5, ready5, effect5⟩ := (jcc_rel8_effect_step 0x1182a0 7 0x45).advances ready4
    (code4.mono (codeRange_slice_subset 0x118294 initializePrefixBytes 12 2))
    ⟨effect4.rip, by intro _; decide +kernel⟩
    (by rw [next4]; exact boundary_ne_program hout (inProgram_of_textOffset 0x182e7 (by decide)))
  have code5 := effect5.codeIn (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _) code4
  refine ⟨5, t5, (((run1.trans run2).trans run3).trans run4).trans run5, ready5, code5,
    effect5.rip.trans next4, ?_, ?_, ?_⟩
  · change t5.regValue .rbx = s.regValue .rdi
    exact ((((effect2.agrees.trans effect3.agrees).trans effect4.agrees).trans effect5.agrees).read
      (n := 64) (r := 3) (by simp [jccEffect])).trans effect1.writes
  · trivial
  · exact ((((effect1.agrees.trans effect2.agrees).trans effect3.agrees).trans effect4.agrees).trans effect5.agrees).mono
      (by simp [initializePrefixEffect, jccEffect, branchEffect, movR64R64Effect, testR64R64Effect, cmpR64Imm8Effect, Effect.components])

end P256.Proofs.Verifying.Combination.Naf.Iterator
