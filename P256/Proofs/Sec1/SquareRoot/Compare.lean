import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Field.Operations.Neg.Borrow.Or
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Program.ReadWrite.LoadFlags

set_option autoImplicit false

open P256.Proofs.Common.Field.FieldNeg.Instructions (orFlags or_r64_r64_effect_step)
open P256.Proofs.Program

namespace P256.Proofs.Sec1.SquareRoot

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ComparePre (s : RamState) : Prop where
  rip : s.RIP = 0x11450a
  readable : ∀ i ∈ ([48,56,64,72,192,200,208,216] : List (BitVec 64)),
    MemReadable s ((Operand.reg 4 : Operand 64).read s + i) 8

def compareLimb (s : RamState) (i : Nat) : BitVec 64 :=
  (Operand.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 (192+8*i)) : Operand 64).read s ^^^
    (Operand.mem ((Operand.reg 4 : Operand 64).read s + BitVec.ofNat 64 (48+8*i)) : Operand 64).read s

def compareWord (s : RamState) : BitVec 64 :=
  compareLimb s 3 ||| (compareLimb s 2 ||| (compareLimb s 0 ||| compareLimb s 1))

def compareEffect (s : RamState) : Effect :=
  { rip := 0x114549
    writes := [⟨(Operand.reg 0 : Operand 64), compareLimb s 0 ||| compareLimb s 1⟩,
      ⟨(Operand.reg 1 : Operand 64), compareLimb s 1⟩,
      ⟨(Operand.reg 2 : Operand 64), compareLimb s 2 ||| (compareLimb s 0 ||| compareLimb s 1)⟩,
      ⟨(Operand.reg 6 : Operand 64), compareWord s⟩,
      ⟨(Operand.reg 7 : Operand 64), 0⟩]
    flags := some (orFlags (compareWord s)) }

def compareBytes : List UInt8 :=
  [0x48,0x8b,0x84,0x24,0xc0,0,0,0,0x48,0x8b,0x8c,0x24,0xc8,0,0,0,
    0x48,0x8b,0x94,0x24,0xd0,0,0,0,0x48,0x33,0x4c,0x24,0x38,
    0x48,0x8b,0xb4,0x24,0xd8,0,0,0,0x48,0x33,0x44,0x24,0x30,
    0x48,0x09,0xc8,0x48,0x33,0x54,0x24,0x40,0x48,0x33,0x74,0x24,0x48,
    0x48,0x09,0xc2,0x31,0xff,0x48,0x09,0xd6]

theorem compare_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x11450a compareBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1450a compareBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem compare_square [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ComparePre (codeRange 0x11450a compareBytes) (Effect.post compareEffect) := by
  have er1 : gprNumber 0#1 0#1 (modrmRm 0xff) = 7#5 := by decide +kernel
  have er2 : gprNumber 0#1 0#1 (modrmReg 0xff) = 7#5 := by decide +kernel
  advance_begin (mov_r64_m64_effect_step 0x11450a 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip, h.readable 192 (by simp)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0x14512 (by decide))
  advance_then (mov_r64_m64_effect_step 0x114512 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 8 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 200 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1451a (by decide))
  advance_then (mov_r64_m64_effect_step 0x11451a 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 208)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 16 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 208 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14522 (by decide))
  advance_then (xor_r64_m64_effect_step 0x114522 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 24 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 56 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14527 (by decide))
  advance_then (mov_r64_m64_effect_step 0x114527 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 29 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 216 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1452f (by decide))
  advance_then (xor_r64_m64_effect_step 0x11452f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 37 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 48 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14534 (by decide))
  advance_then (or_r64_r64_effect_step 0x114534 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 42 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14537 (by decide))
  advance_then (xor_r64_m64_effect_step 0x114537 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 45 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 64 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1453c (by decide))
  advance_then (xor_r64_m64_effect_step 0x11453c 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 50 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 72 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14541 (by decide))
  advance_then (or_r64_r64_effect_step 0x114541 0x48 0xc2 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 55 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14544 (by decide))
  advance_then (xor_r32_r32_effect_step 0x114544 0xff rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 58 2
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14546 (by decide))
  advance_then (or_r64_r64_effect_step 0x114546 0x48 0xd6 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x11450a compareBytes 60 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x14549 (by decide))
  advance_finish [compareEffect, compareWord, compareLimb, er1, er2, BitVec.xor_self, BitVec.setWidth_zero]

end P256.Proofs.Sec1.SquareRoot
