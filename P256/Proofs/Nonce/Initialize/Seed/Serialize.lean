import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

structure SerializePre (s : RamState) : Prop where
  rip : s.RIP = 0x107b5c
  readable : ∀ i ∈ ([176, 296] : List (BitVec 64)), MemReadable s (stackPtr s + i) 8

def serializeBytes : List UInt8 :=
  [0x4c,0x8d,0xa4,0x24,0xc8,0x0,0x0,0x0,0x48,0x89,0xef,0x4c,0x8b,0xbc,0x24,0x28,0x1,0x0,0x0,0x4c,0x89,0xfe,0x4c,0x89,0xe2,0x48,0x8b,0x9c,0x24,0xb0,0x0,0x0,0x0,0x48,0x89,0xd9]

def serializeEffect (s : RamState) : Effect :=
  let sp := (Operand.reg 4 : Operand 64).read s
  { rip := 0x107b80
    writes := [
      ⟨(.reg 12 : Operand 64), sp + 200⟩,
      ⟨(.reg 7 : Operand 64), (Operand.reg 5 : Operand 64).read s⟩,
      ⟨(.reg 15 : Operand 64), (Operand.mem (sp + 296) : Operand 64).read s⟩,
      ⟨(.reg 6 : Operand 64), (Operand.mem (sp + 296) : Operand 64).read s⟩,
      ⟨(.reg 2 : Operand 64), sp + 200⟩,
      ⟨(.reg 3 : Operand 64), (Operand.mem (sp + 176) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (Operand.mem (sp + 176) : Operand 64).read s⟩] }

theorem serialize_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SerializePre (codeRange 0x107b5c serializeBytes)
      (Effect.post serializeEffect) := by
  advance_begin (lea_r64_effect_step 0x107b5c 0x4c (by simp [RexWPrefix]) 4
    (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl)
  case next => intro s hP; exact boundary_ne_program outside (inProgram_of_textOffset 0x7b64 (by decide))
  advance_then (mov_r64_r64_effect_step 0x107b64 0x48 0xef (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x107b5c serializeBytes 8 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7b67 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107b67 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107b5c serializeBytes 11 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 296 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7b6f (by decide))
  advance_then (mov_r64_r64_effect_step 0x107b6f 0x4c 0xfe (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x107b5c serializeBytes 19 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7b72 (by decide))
  advance_then (mov_r64_r64_effect_step 0x107b72 0x4c 0xe2 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x107b5c serializeBytes 22 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7b75 (by decide))
  advance_then (mov_r64_m64_effect_step 0x107b75 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107b5c serializeBytes 25 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 176 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7b7d (by decide))
  advance_then (mov_r64_r64_effect_step 0x107b7d 0x48 0xd9 (by simp [RexWPrefix]) (by decide))
  case sub => exact codeRange_slice_subset 0x107b5c serializeBytes 33 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7b80 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [serializeEffect]
  · x86_norm [serializeEffect]
    rfl
  · intro i; cases i <;> x86_norm [serializeEffect]
  · x86_norm [serializeEffect]

end P256.Proofs.Nonce.Initialize.Seed
