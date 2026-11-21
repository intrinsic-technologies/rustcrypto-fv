import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)

structure InitializePre (s : RamState) : Prop where
  rip : s.RIP = 0x107b85
  writable : ∀ i ∈ ([8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64)),
    MemWritable s (stackPtr s + i) 8
  codeApart : ∀ i ∈ ([8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (stackPtr s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def initializeBytes : List UInt8 :=
  [0x48, 0xc7, 0x44, 0x24, 0x20, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x18, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x10, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x8, 0x0, 0x0, 0x0, 0x0, 0x48, 0xb8, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x89, 0x44, 0x24, 0x40]

def initializeEffect (s : RamState) : Effect :=
  { rip := 0x107bc7
    writes := [
      ⟨(.reg 0 : Operand 64), 0x0101010101010101⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 8) : Operand 64), 0⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 16) : Operand 64), 0⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 24) : Operand 64), 0⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 32) : Operand 64), 0⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 40) : Operand 64), 0x0101010101010101⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 48) : Operand 64), 0x0101010101010101⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 56) : Operand 64), 0x0101010101010101⟩,
      ⟨(.mem ((Operand.reg 4 : Operand 64).read s + 64) : Operand 64), 0x0101010101010101⟩] }

set_option maxHeartbeats 800000 in
theorem initialize_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary InitializePre (codeRange 0x107b85 initializeBytes)
      (Effect.post initializeEffect) := by
  advance_begin (mov_m64_imm32_effect_step 0x107b85 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 32 (by simp), hP.codeApart 32 (by simp) 0x7b85 9 (by decide)⟩
  case next =>
    intro s hP
    exact boundary_ne_program outside (inProgram_of_textOffset 0x7b8e (by decide))
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.codeApart 32 (by simp) 0x7b85 66 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x107b8e 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x107b85 initializeBytes 9 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x7b8e 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x7b85 66 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7b97 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x107b97 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x107b85 initializeBytes 18 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x7b97 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x7b85 66 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7ba0 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x107ba0 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x107b85 initializeBytes 27 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x7ba0 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x7b85 66 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7ba9 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x107ba9 0x48 0xb8 (by simp [RexWPrefix]) (by decide) 0x0101010101010101)
  case sub => exact codeRange_slice_subset 0x107b85 initializeBytes 36 10
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bb3 (by decide))
  advance_then (mov_m64_r64_effect_step 0x107bb3 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107b85 initializeBytes 46 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x7bb3 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x7b85 66 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bb8 (by decide))
  advance_then (mov_m64_r64_effect_step 0x107bb8 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107b85 initializeBytes 51 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 (by simp) 0x7bb8 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp) 0x7b85 66 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bbd (by decide))
  advance_then (mov_m64_r64_effect_step 0x107bbd 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107b85 initializeBytes 56 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      exact hP.codeApart 56 (by simp) 0x7bbd 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp) 0x7b85 66 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bc2 (by decide))
  advance_then (mov_m64_r64_effect_step 0x107bc2 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x107b85 initializeBytes 61 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 (by simp)
    · x86_norm
      exact hP.codeApart 64 (by simp) 0x7bc2 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 64 (by simp) 0x7b85 66 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x7bc7 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [initializeEffect]
  · x86_norm [initializeEffect]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [initializeEffect]
  · x86_norm [initializeEffect]

end P256.Proofs.Nonce.Initialize.Seed
