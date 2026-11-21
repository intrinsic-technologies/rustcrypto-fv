import P256.Spec
import P256.Proofs.Program.Arena
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

theorem count_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x106808)
    (hcount : s.regValue .rsi = 2) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x106811 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (test_r64_r64_effect_step 0x106808 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x6808 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x680b (by decide)))
  have fu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := fu.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have he := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rsi &&& s.regValue .rsi) == 0) at he
    rw [hcount] at he
    exact he
  have hn : (jccEffect 0x10680b 6 4 ((0x4dd : BitVec 32).signExtend 64) u).rip = 0x106811 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x10680b 4 0x4dd).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0x680b _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x6811 (by decide)))
  refine ⟨t, hu.trans ht, rt, et.rip.trans hn, ?_⟩
  exact (fu.trans et.agrees).mono (by simp [jccEffect])

structure LoadArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x106811
  pointer : MemReadable s (s.regValue .rdi) 8
  length : MemReadable s (s.regValue .rdx) 8

def loadArgumentsBytes : List UInt8 :=
  [0x49,0x89,0xd7,0x49,0x89,0xfc,0x48,0x8b,0x07,0x48,0x8b,0x2a]

def loadArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10681d
    writes := [⟨(.reg 15 : Operand 64), s.regValue .rdx⟩,
      ⟨(.reg 12 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (s.regValue .rdi) 64⟩,
      ⟨(.reg 5 : Operand 64), memLoad s.external (s.regValue .rdx) 64⟩] }

theorem load_arguments [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadArgumentsPre (codeRange 0x106811 loadArgumentsBytes)
      (Effect.post loadArgumentsEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x106811 0x49 0xd7 (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x6814 (by decide))
  advance_then (mov_r64_r64_effect_step 0x106814 0x49 0xfc (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x106811 loadArgumentsBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x6817 (by decide))
  advance_then (mov_r64_m64_effect_step 0x106817 0x48 (by simp [RexWPrefix])
    0 (.base 7 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106811 loadArgumentsBytes 6 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      change MemReadable s (s.regValue .rdi + 0) 8
      exact (congrArg (fun a => MemReadable s a 8) (BitVec.add_zero (s.regValue .rdi))).mpr hP.pointer
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x681a (by decide))
  advance_then (mov_r64_m64_effect_step 0x10681a 0x48 (by simp [RexWPrefix])
    5 (.base 2 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106811 loadArgumentsBytes 9 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      change MemReadable s (s.regValue .rdx + 0) 8
      exact (congrArg (fun a => MemReadable s a 8) (BitVec.add_zero (s.regValue .rdx))).mpr hP.length
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x681d (by decide))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [loadArgumentsEffect]
  · x86_norm [loadArgumentsEffect, Operand.read_reg64, State.regValue, gprNumber, rexR, rexB, modrmReg, modrmRm]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · exact congrArg (fun a => (Operand.mem a : Operand 64).read s) (BitVec.add_zero (s.regValue .rdi)).symm
    · exact congrArg (fun a => (Operand.mem a : Operand 64).read s) (BitVec.add_zero (s.regValue .rdx)).symm
  · intro i
    cases i <;> x86_norm [loadArgumentsEffect]
  · x86_norm [loadArgumentsEffect, gprNumber, rexR, rexB, modrmRm, modrmReg]

theorem input_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x10681d)
    (hptr : s.regValue .rax ≠ 0) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x106826 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (test_r64_r64_effect_step 0x10681d 0x48 0xc0 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x681d _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x6820 (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have he := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((s.regValue .rax &&& s.regValue .rax) == 0) at he
    have hptr' : s.regValue .rax ≠ 0#64 := hptr
    have hz' : (s.regValue .rax == 0#64) = false := by
      exact beq_eq_false_iff_ne.mpr hptr'
    simp only [BitVec.and_self] at he
    exact he.trans hz'
  have hn : (jccEffect 0x106820 6 4 ((0x49d : BitVec 32).signExtend 64) a).rip = 0x106826 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨b, hb, rb, eb⟩ := (jcc_rel32_effect_step 0x106820 4 0x49d).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x6820 _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x6826 (by decide)))
  exact ⟨b, ha.trans hb, rb, eb.rip.trans hn,
    (fa.trans eb.agrees).mono (by simp [jccEffect])⟩

theorem length_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x106826)
    (hsize : s.regValue .rbp = 32) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x106830 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (cmp_r64_imm8_effect_step 0x106826 0x48 0xfd 32 (by simp [RexWPrefix]) rfl rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x6826 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x682a (by decide)))
  have fu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := fu.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = true := by
    have he := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rbp - 32) == 0) at he
    rw [hsize] at he
    exact he
  have hn : (jccEffect 0x10682a 6 5 ((0x4be : BitVec 32).signExtend 64) u).rip = 0x106830 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x10682a 5 0x4be).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0x682a _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x6830 (by decide)))
  refine ⟨t, hu.trans ht, rt, et.rip.trans hn, ?_⟩
  exact (fu.trans et.agrees).mono (by simp [jccEffect])

end P256.Proofs.EcdhWrapper
