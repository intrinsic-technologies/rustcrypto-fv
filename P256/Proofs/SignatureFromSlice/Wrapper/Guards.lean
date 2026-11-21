import P256.Proofs.SignatureFromSlice.Wrapper.Arena
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

theorem count_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x10225b)
    (hcount : s.regValue .rsi = 1) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x102264 ∧
      AgreesExcept [.flags, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (test_r64_r64_effect_step 0x10225b 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x225b _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x225e (by decide)))
  have fu : AgreesExcept [.flags, .rip] s u := eu.agrees
  have memu := fu.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS u.RFLAGS).ZF = false := by
    have he := eu.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS u.RFLAGS).ZF = ((s.regValue .rsi &&& s.regValue .rsi) == 0) at he
    rw [hcount] at he
    exact he
  have hn : (jccEffect 0x10225e 6 4 ((0xc4 : BitVec 32).signExtend 64) u).rip = 0x102264 := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨t, ht, rt, et⟩ := (jcc_rel32_effect_step 0x10225e 4 0xc4).advances ru
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq memu)
      0x225e _ (by decide) (by decide +kernel)) ⟨eu.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x2264 (by decide)))
  refine ⟨t, hu.trans ht, rt, et.rip.trans hn, ?_⟩
  exact (fu.trans et.agrees).mono (by simp [jccEffect])

structure LoadArgumentsPre (s : RamState) : Prop where
  rip : s.RIP = 0x102264
  pointer : MemReadable s (s.regValue .rdi) 8
  length : MemReadable s (s.regValue .rdx) 8

def loadArgumentsBytes : List UInt8 := [0x48,0x8b,0x37,0x48,0x8b,0x02]

def loadArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10226a
    writes := [⟨(.reg 6 : Operand 64), memLoad s.external (s.regValue .rdi) 64⟩,
      ⟨(.reg 0 : Operand 64), memLoad s.external (s.regValue .rdx) 64⟩] }

theorem load_arguments [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadArgumentsPre (codeRange 0x102264 loadArgumentsBytes)
      (Effect.post loadArgumentsEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x102264 0x48 (by simp [RexWPrefix])
    6 (.base 7 .none) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    change MemReadable s (s.regValue .rdi + 0#64) 8
    rw [BitVec.add_zero]
    exact hP.pointer
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x2267 (by decide))
  advance_then (mov_r64_m64_effect_step 0x102267 0x48 (by simp [RexWPrefix])
    0 (.base 2 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x102264 loadArgumentsBytes 3 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      change MemReadable s (s.regValue .rdx + 0) 8
      exact (congrArg (fun a => MemReadable s a 8) (BitVec.add_zero (s.regValue .rdx))).mpr hP.length
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x226a (by decide))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [loadArgumentsEffect]
  · x86_norm [loadArgumentsEffect, Operand.read_reg64, State.regValue, gprNumber, rexR, rexB, modrmReg, modrmRm]
    constructor
    · exact congrArg (fun a => (Operand.mem a : Operand 64).read s) (BitVec.add_zero (s.regValue .rdi)).symm
    · exact congrArg (fun a => (Operand.mem a : Operand 64).read s) (BitVec.add_zero (s.regValue .rdx)).symm
  · intro i
    cases i <;> x86_norm [loadArgumentsEffect]
  · x86_norm [loadArgumentsEffect, gprNumber, rexR, rexB, modrmRm, modrmReg]

theorem input_guard [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x10226a)
    (hptr : s.regValue .rsi ≠ 0) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ t.RIP = 0x102275 ∧
      t.regValue .rbx = s.regValue .rcx ∧ t.regValue .r14 = s.regValue .r8 ∧
      AgreesExcept [.reg 3, .reg 14, .flags, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (test_r64_r64_effect_step 0x10226a 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x226a _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x226d (by decide)))
  have fa : AgreesExcept [.flags, .rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have hz : (StatusFlags.ofRFLAGS a.RFLAGS).ZF = false := by
    have he := ea.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS a.RFLAGS).ZF = ((s.regValue .rsi &&& s.regValue .rsi) == 0) at he
    have hptr' : s.regValue .rsi ≠ 0#64 := hptr
    have hz' : (s.regValue .rsi == 0#64) = false := by
      exact beq_eq_false_iff_ne.mpr hptr'
    simp only [BitVec.and_self] at he
    exact he.trans hz'
  have hn : (jccEffect 0x10226d 2 4 ((0x3a : BitVec 8).signExtend 64) a).rip = 0x10226f := by
    simp [jccEffect, branchEffect, condHolds, hz]
  obtain ⟨b, hb, rb, eb⟩ := (jcc_rel8_effect_step 0x10226d 4 0x3a).advances ra
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq ma)
      0x226d _ (by decide) (by decide +kernel)) ⟨ea.rip, by intro; decide⟩
    (by rw [hn]; exact boundary_ne_program hout (inProgram_of_textOffset 0x226f (by decide)))
  have fb : AgreesExcept [.rip] a b := eb.agrees
  have mb := (fb.external (by simp [Component.Covers])).trans ma
  obtain ⟨c, hc, rc, ec⟩ := (mov_r64_r64_effect_step 0x10226f 0x4d 0xc6
    (by simp [RexWPrefix]) rfl).advances rb
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq mb) 0x226f _
      (by decide) (by decide +kernel)) (eb.rip.trans hn)
    (boundary_ne_program hout (inProgram_of_textOffset 0x2272 (by decide)))
  have fc : AgreesExcept [.reg 14,.rip] b c := ec.agrees
  have mc := (fc.external (by simp [Component.Covers])).trans mb
  obtain ⟨t, ht, rt, et⟩ := (mov_r64_r64_effect_step 0x102272 0x48 0xcb
    (by simp [RexWPrefix]) rfl).advances rc
    (programText_slice ((programLoaded_codeIn loaded).of_external_eq mc) 0x2272 _
      (by decide) (by decide +kernel)) ec.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0x2275 (by decide)))
  have ft : AgreesExcept [.reg 3,.rip] c t := et.agrees
  refine ⟨t, ((ha.trans hb).trans hc).trans ht, rt, et.rip, ?_, ?_, ?_⟩
  · exact et.writes.trans (((fa.trans fb).trans fc).read (n := 64) (r := 1) (by simp))
  · exact (ft.read (n := 64) (r := 14) (by simp)).trans
      (ec.writes.trans ((fa.trans fb).read (n := 64) (r := 8) (by simp)))
  · exact (((fa.trans fb).trans fc).trans ft).mono (by simp)

theorem call_arguments [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x102275) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x10227b ∧
      t.regValue .rdi = stackPtr s ∧ t.regValue .rdx = s.regValue .rax ∧
      AgreesExcept [.reg 7, .reg 2, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (mov_r64_r64_effect_step 0x102275 0x48 0xe7 (by simp [RexWPrefix]) rfl).advances
      ready (programText_slice (programLoaded_codeIn loaded) 0x2275 _
        (by decide) (by decide +kernel)) hip
      (boundary_ne_program hout (inProgram_of_textOffset 0x2278 (by decide)))
  have fu : AgreesExcept [.reg 7, .rip] s u := eu.agrees
  have mu := fu.external (by simp [Component.Covers])
  obtain ⟨t, ht, rt, et⟩ :=
    (mov_r64_r64_effect_step 0x102278 0x48 0xc2 (by simp [RexWPrefix]) rfl).advances
      ru (programText_slice ((programLoaded_codeIn loaded).of_external_eq mu) 0x2278 _
        (by decide) (by decide +kernel)) eu.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x227b (by decide)))
  have ft : AgreesExcept [.reg 2, .rip] u t := et.agrees
  refine ⟨t, hu.trans ht, rt, et.rip, ?_, ?_, ?_⟩
  · exact (ft.read (n := 64) (r := 7) (by simp)).trans eu.writes
  · exact et.writes.trans (fu.read (n := 64) (r := 0) (by simp))
  · exact (fu.trans ft).mono (by simp)

end P256.Proofs.SignatureFromSlice.Wrapper
