import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Initialization

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x1044b1
  writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + 208) 8
  apart : RangeApart (stackPtr s + 208) 8 0x1044b1 31

def setupBytes : List UInt8 :=
  [0x49,0x89,0xf5,0x48,0x89,0xbc,0x24,0xd0,0,0,0,
    0x48,0x8d,0x6c,0x24,0x10,0xb9,0xc,0,0,0,
    0x48,0x89,0xef,0x48,0xc7,0xc6,0x90,0x24,0x20,0]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x1044d0
    writes := [⟨(Operand.reg 13 : Operand 64), s.regValue .rsi⟩,
      ⟨(Operand.mem (stackPtr s + 208) : Operand 64), s.regValue .rdi⟩,
      ⟨(Operand.reg 5 : Operand 64), stackPtr s + 16⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 7 : Operand 64), stackPtr s + 16⟩,
      ⟨(Operand.reg 6 : Operand 64), 0x202490⟩] }

set_option maxHeartbeats 800000 in
theorem setup_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupPre (codeRange 0x1044b1 setupBytes) (Effect.post setupEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x1044b1 0x49 0xf5
    (by simp [RexWPrefix]) rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x44b4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1044b4 0x48
    (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 208)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1044b1 setupBytes 3 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      intro i hi j hj he
      apply hP.apart i hi (3 + j) (by omega)
      change stackPtr s + 208 + BitVec.ofNat 64 i = _ at he
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.reduceAdd] using he
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x44bc (by decide))
  advance_then (lea_r64_effect_step 0x1044bc 0x48 (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1044b1 setupBytes 11 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x44c1 (by decide))⟩
  advance_then (mov_r32_imm32_effect_step 0x1044c1 0xb9 (by decide) 12)
  case sub => exact codeRange_slice_subset 0x1044b1 setupBytes 16 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x44c6 (by decide))⟩
  advance_then (mov_r64_r64_effect_step 0x1044c6 0x48 0xef (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x1044b1 setupBytes 21 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x44c9 (by decide))⟩
  advance_then (mov_r64_imm32_effect_step 0x1044c9 0x48 0xc6
    (by simp [RexWPrefix]) rfl rfl 0x202490)
  case sub => exact codeRange_slice_subset 0x1044b1 setupBytes 24 7
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x44d0 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [setupEffect]
    all_goals (repeat first | constructor | rfl)
  · x86_norm [setupEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [setupEffect]
  · x86_norm [setupEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Lookup.Initialization
