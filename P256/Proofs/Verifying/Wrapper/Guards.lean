import P256.Proofs.Verifying.Wrapper.Arena
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

theorem count_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x103057)
    (hcount : s.regValue .rsi = 3) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x103060 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (test_r64_r64_effect_step 0x103057 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x3057 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x305a (by decide)))
  have fu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := fu.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have he := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rsi &&& s.regValue .rsi) == 0) at he
    rw [hcount] at he
    exact he
  have hn : (jccEffect 0x10305a 6 4 ((0x1d1 : BitVec 32).signExtend 64) u).rip = 0x103060 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x10305a 4 0x1d1).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0x305a _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x3060 (by decide)))
  refine ⟨t, hu.trans ht, rt, et.rip.trans hn, ?_⟩
  exact (fu.trans et.agrees).mono (by simp [jccEffect])

structure LoadArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x103060
  pointer : MemReadable s (s.regValue .rdi) 8
  length : MemReadable s (s.regValue .rdx) 8

def loadArgumentsBytes : List UInt8 :=
  [72, 137, 211, 73, 137, 254, 72, 139, 23, 72, 139, 3]

def loadArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10306c
    writes := [⟨(.reg 3 : Operand 64), s.regValue .rdx⟩,
      ⟨(.reg 14 : Operand 64), s.regValue .rdi⟩,
      ⟨(.reg 2 : Operand 64), memLoad s.external (s.regValue .rdi) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (s.regValue .rdx) 64⟩] }

theorem load_arguments [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadArgumentsPre (codeRange 0x103060 loadArgumentsBytes)
      (Effect.post loadArgumentsEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x103060 0x48 0xd3 (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x3063 (by decide))
  advance_then (mov_r64_r64_effect_step 0x103063 0x49 0xfe (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x103060 loadArgumentsBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x3066 (by decide))
  advance_then (mov_r64_m64_effect_step 0x103066 0x48 (by simp [RexWPrefix])
    2 (.base 7 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103060 loadArgumentsBytes 6 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      change MemReadable s (s.regValue .rdi + 0) 8
      exact (congrArg (fun a => MemReadable s a 8) (BitVec.add_zero (s.regValue .rdi))).mpr hP.pointer
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x3069 (by decide))
  advance_then (mov_r64_m64_effect_step 0x103069 0x48 (by simp [RexWPrefix])
    0 (.base 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103060 loadArgumentsBytes 9 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      change MemReadable s (s.regValue .rdx + 0) 8
      exact (congrArg (fun a => MemReadable s a 8) (BitVec.add_zero (s.regValue .rdx))).mpr hP.length
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x306c (by decide))
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
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x10306c)
    (hptr : s.regValue .rdx ≠ 0) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x103075 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (test_r64_r64_effect_step 0x10306c 0x48 0xd2 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x306c _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x306f (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have he := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((s.regValue .rdx &&& s.regValue .rdx) == 0) at he
    have hptr' : s.regValue .rdx ≠ 0#64 := hptr
    have hz' : (s.regValue .rdx == 0#64) = false := by
      exact beq_eq_false_iff_ne.mpr hptr'
    simp only [BitVec.and_self] at he
    exact he.trans hz'
  have hn : (jccEffect 0x10306f 6 4 ((0x1ab : BitVec 32).signExtend 64) a).rip = 0x103075 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨b, hb, rb, eb⟩ := (jcc_rel32_effect_step 0x10306f 4 0x1ab).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x306f _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x3075 (by decide)))
  exact ⟨b, ha.trans hb, rb, eb.rip.trans hn,
    (fa.trans eb.agrees).mono (by simp [jccEffect])⟩

theorem length_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x103075)
    (length : s.regValue .rax = 65) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x10307f ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (cmp_r64_imm8_effect_step 0x103075 0x48 0xf8 65 (by simp [RexWPrefix]) rfl rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x3075 _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x3079 (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have condition : condHolds 5 (StatusFlags.ofRFLAGS a.RFLAGS) = false := by
    have zf := ea.flag .ZF
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = (cmpSpec (s.regValue .rax) 65).ZF at zf
    rw [length, cmpSpec_ZF] at zf
    change Bool.not (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false
    rw [zf]
    rfl
  have next : (jccEffect 0x103079 6 5 ((0x1b2 : BitVec 32).signExtend 64) a).rip = 0x10307f := by
    simp only [jccEffect, condition]
    rfl
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x103079 5 0x1b2).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x3079 _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [next]; exact boundary_ne_program outside (inProgram_of_textOffset 0x307f (by decide)))
  exact ⟨t, ha.trans ht, rt, et.rip.trans next,
    (fa.trans et.agrees).mono (by simp [jccEffect])⟩

def saveArgumentsBytes : List UInt8 := [73, 137, 247, 73, 137, 204, 77, 137, 197]

def saveArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x103088
    writes := [⟨(.reg 15 : Operand 64), s.regValue .rsi⟩,
      ⟨(.reg 12 : Operand 64), s.regValue .rcx⟩,
      ⟨(.reg 13 : Operand 64), s.regValue .r8⟩] }

theorem save_arguments [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10307f)
      (codeRange 0x10307f saveArgumentsBytes) (Effect.post saveArgumentsEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x10307f 0x49 0xf7 (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x3082 (by decide))
  advance_then (mov_r64_r64_effect_step 0x103082 0x49 0xcc (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10307f saveArgumentsBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x3085 (by decide))
  advance_then (mov_r64_r64_effect_step 0x103085 0x4d 0xc5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10307f saveArgumentsBytes 6 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x3088 (by decide))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [saveArgumentsEffect]
  · x86_norm [saveArgumentsEffect, Operand.read_reg64, State.regValue, gprNumber,
      rexR, rexB, modrmRm, modrmReg]
    exact ⟨rfl,rfl,rfl⟩
  · intro i
    cases i <;> x86_norm [saveArgumentsEffect]
  · x86_norm [saveArgumentsEffect, gprNumber, rexR, rexB, modrmRm, modrmReg]

end P256.Proofs.Verifying.Wrapper
