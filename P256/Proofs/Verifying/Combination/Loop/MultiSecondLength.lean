import P256.Proofs.Verifying.Combination.Loop.MultiLength
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

def secondLengthBytes : List UInt8 :=
  [0x48,0x69,0xf7,0x10,1,0,0,0x4c,1,0xce,0x4c,1,0xc6,0x48,0x81,0xc6,0x10,1,0,0,
    0x48,0x69,0xc9,0x10,1,0,0,0x31,0xff]

def secondLengthEffect (s : RamState) : Effect :=
  { rip := 0x10f100
    writes := [⟨(.reg 6 : Operand 64), BitVec.ofInt 64 ((s.regValue .rdi).toInt * 272) +
        s.regValue .r9 + s.regValue .r8 + 272⟩,
      ⟨(.reg 1 : Operand 64), BitVec.ofInt 64 ((s.regValue .rcx).toInt * 272)⟩,
      ⟨(.reg 7 : Operand 64), 0⟩]
    flags := some (xorFlags (0 : BitVec 32)) }

theorem secondLength_bytes : Extracted.textBytes.toListFrom 0xf0e3 29 = secondLengthBytes := by
  decide +kernel

theorem secondLength_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x10f0e3)
      (codeRange 0x10f0e3 secondLengthBytes) (Effect.post secondLengthEffect) := by
  advance_begin (imul_r64_r64_imm32_effect_step 0x10f0e3 0x48 (by simp [RexWPrefix]) 0xf7 rfl 272)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0xf0ea (by decide))
  advance_then (add_r64_r64_effect_step 0x10f0ea 0x4c 0xce (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f0e3 secondLengthBytes 7 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf0ed (by decide))⟩
  advance_then (add_r64_r64_effect_step 0x10f0ed 0x4c 0xc6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10f0e3 secondLengthBytes 10 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf0f0 (by decide))⟩
  advance_then (add_r64_imm32_effect_step 0x10f0f0 0x48 0xc6 272 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10f0e3 secondLengthBytes 13 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf0f7 (by decide))⟩
  advance_then (imul_r64_r64_imm32_effect_step 0x10f0f7 0x48 (by simp [RexWPrefix]) 0xc9 rfl 272)
  case sub => exact codeRange_slice_subset 0x10f0e3 secondLengthBytes 20 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf0fe (by decide))⟩
  advance_then (xor_r32_r32_effect_step 0x10f0fe 0xff rfl)
  case sub => exact codeRange_slice_subset 0x10f0e3 secondLengthBytes 27 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0xf100 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [secondLengthEffect, BitVec.xor_self, BitVec.setWidth_zero, show modrmRm (255 : UInt8) = 7 from rfl, show modrmReg (255 : UInt8) = 7 from rfl]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [secondLengthEffect, BitVec.xor_self, BitVec.setWidth_zero, show modrmRm (255 : UInt8) = 7 from rfl, show modrmReg (255 : UInt8) = 7 from rfl]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [secondLengthEffect, BitVec.xor_self, BitVec.setWidth_zero, show modrmRm (255 : UInt8) = 7 from rfl, show modrmReg (255 : UInt8) = 7 from rfl] <;> rfl
  · x86_norm [secondLengthEffect, BitVec.xor_self, BitVec.setWidth_zero, show modrmRm (255 : UInt8) = 7 from rfl, show modrmReg (255 : UInt8) = 7 from rfl]
    all_goals (repeat first | constructor | rfl)

theorem second_length_setup [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {tables digits : BitVec 64} (pre : MultiPre s boundary tables digits)
    (state : State s t) (rip : t.RIP = 0x10f0e3)
    (ptr : t.regValue .r8 = digits) (index : t.regValue .r9 = 0)
    (offset : t.regValue .rdi = 0) (count : t.regValue .rcx = 1) :
    ∃ fuel w, Advances boundary fuel t w ∧ State s w ∧ w.RIP = 0x10f100 ∧
      w.regValue .rsi = digits + 272 ∧ w.regValue .rcx = 272 ∧
      w.regValue .rdi = 0 ∧ AgreesExcept [.reg 6, .reg 1, .reg 7, .flags, .rip] t w := by
  obtain ⟨fuel, w, run, ready, _, effect⟩ := secondLength_correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf0e3 secondLengthBytes
      (by decide) secondLength_bytes) rip
  have frame : AgreesExcept [.reg 6, .reg 1, .reg 7, .flags, .rip] t w := effect.agrees
  refine ⟨fuel, w, run,
    state.after_registers ready frame (by simp [Component.Covers]) (by simp), effect.rip,
    ?_, ?_, effect.writes.2.2, frame⟩
  · have h := effect.writes.1
    change w.regValue .rsi = BitVec.ofInt 64 ((t.regValue .rdi).toInt * 272) +
      t.regValue .r9 + t.regValue .r8 + 272 at h
    rw [offset, index, ptr] at h
    change w.regValue .rsi = 0#64 + 0#64 + digits + 272 at h
    simpa only [BitVec.zero_add] using h
  · have h := effect.writes.2.1
    change w.regValue .rcx = BitVec.ofInt 64 ((t.regValue .rcx).toInt * 272) at h
    rw [count] at h
    exact h.trans (by decide +kernel)

end P256.Proofs.Verifying.Combination.Loop.Multi
