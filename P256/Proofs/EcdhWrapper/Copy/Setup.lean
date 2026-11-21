import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)

structure SetupPre (s : RamState) : Prop where
  rip : s.RIP = 0x106830
  writable : ∀ off ∈ ([32,40] : List Nat),
    MemWritable s (stackPtr s + BitVec.ofNat 64 off) 8
  codeApart : ∀ off ∈ ([32,40] : List Nat), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (stackPtr s + BitVec.ofNat 64 off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def setupBytes : List UInt8 :=
  [0x49,0x89,0xf5,0x48,0x89,0x4c,0x24,0x20,0x4c,0x89,0x44,0x24,0x28]

def setupEffect (s : RamState) : Effect :=
  { rip := 0x10683d
    writes := [⟨(.reg 13 : Operand 64), s.regValue .rsi⟩,
      ⟨(.mem (stackPtr s+32) : Operand 64), s.regValue .rcx⟩,
      ⟨(.mem (stackPtr s+40) : Operand 64), s.regValue .r8⟩] }

set_option maxHeartbeats 800000 in
theorem setup_correct [Bindings] (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary SetupPre (codeRange 0x106830 setupBytes)
      (Effect.post setupEffect) := by
  advance_begin (mov_r64_r64_effect_step 0x106830 0x49 0xf5 (by simp [RexWPrefix]) rfl)
  case next =>
    intro s h
    exact boundary_ne_program outside (inProgram_of_textOffset 0x6833 (by decide))
  advance_then (mov_m64_r64_effect_step 0x106833 0x48 (by simp [RexWPrefix])
    1 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106830 setupBytes 3 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [stackPtr] using hP.writable 32 (by simp)
    · x86_norm [stackPtr]
      simpa [stackPtr, Extracted.textAddress] using hP.codeApart 32 (by simp) 0x6833 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [stackPtr, Extracted.textAddress] using hP.codeApart 32 (by simp) 0x6830 13 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6838 (by decide))
  advance_then (mov_m64_r64_effect_step 0x106838 0x4c (by simp [RexWPrefix])
    0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x106830 setupBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      simpa [stackPtr] using hP.writable 40 (by simp)
    · x86_norm [stackPtr]
      simpa [stackPtr, Extracted.textAddress] using hP.codeApart 40 (by simp) 0x6838 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      simpa [stackPtr, Extracted.textAddress] using hP.codeApart 40 (by simp) 0x6830 13 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x683d (by decide))
  apply AdvanceTriple.block_end
  intro s t _ h
  apply h.weaken
  · x86_norm [setupEffect]
  · x86_norm [setupEffect, stackPtr, Operand.read_reg64, State.regValue,
      Syntax.Reg.fin, gprIndex, gprNumber, rexR, rexB, modrmReg, modrmRm]
    exact ⟨rfl, rfl, rfl⟩
  · intro i
    cases i <;> x86_norm [setupEffect, stackPtr, Operand.read_reg64, State.regValue,
      Syntax.Reg.fin, gprIndex, gprNumber, rexR, rexB, modrmReg, modrmRm]
  · x86_norm [setupEffect, stackPtr, Operand.read_reg64, State.regValue,
      Syntax.Reg.fin, gprIndex, gprNumber, rexR, rexB, modrmReg, modrmRm]

end P256.Proofs.EcdhWrapper.Copy
