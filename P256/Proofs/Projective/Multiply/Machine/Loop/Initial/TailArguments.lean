import P256.Proofs.Projective.Multiply.Machine.Loop.Initial.Setup
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Projective.Multiply.Machine.Loop.Initial

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs

def tailArgumentsBytes : List UInt8 :=
  [0x49,0x83,0xc1,63,0x41,0xbf,64,0,0,0,0x4c,0x8d,0x6c,0x24,40,
    0x48,0x8d,0x84,0x24,0xe8,0,0,0]

def tailArgumentsEffect (s : RamState) : Effect :=
  { rip := 0x10332a
    writes := [⟨(Operand.reg 9 : Operand 64), s.regValue .r9 + 63⟩,
      ⟨(Operand.reg 15 : Operand 64), 64⟩,
      ⟨(Operand.reg 13 : Operand 64), stackPtr s + 40⟩,
      ⟨(Operand.reg 0 : Operand 64), stackPtr s + 232⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem tailArguments_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = 0x103313)
      (codeRange 0x103313 tailArgumentsBytes) (Effect.post tailArgumentsEffect) := by
  advance_begin (add_r64_imm8_effect_step 0x103313 0x49 0xc1 63 (by simp [RexWPrefix]) rfl rfl)
  case next => intro s h; exact boundary_ne_program hout (inProgram_of_textOffset 0x3317 (by decide))
  advance_then (mov_r32_imm32_rex_effect_step 0x103317 0x41 0xbf (by simp [RexNoWPrefix]) (by decide) 64)
  case sub => exact codeRange_slice_subset 0x103313 tailArgumentsBytes 4 6
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x331d (by decide))⟩
  advance_then (lea_r64_effect_step 0x10331d 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103313 tailArgumentsBytes 10 5
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x3322 (by decide))⟩
  advance_then (lea_r64_effect_step 0x103322 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 232)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x103313 tailArgumentsBytes 15 8
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program hout (inProgram_of_textOffset 0x332a (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [tailArgumentsEffect]
  · x86_norm [tailArgumentsEffect]
    all_goals (repeat first | constructor | rfl)
  · intro i; cases i <;> x86_norm [tailArgumentsEffect]
  · x86_norm [tailArgumentsEffect]
    all_goals (repeat first | constructor | rfl)

end P256.Proofs.Projective.Multiply.Machine.Loop.Initial
