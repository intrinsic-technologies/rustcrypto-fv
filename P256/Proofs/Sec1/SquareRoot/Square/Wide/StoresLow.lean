import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Sec1.SquareRoot.Square.Wide.Common
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
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

open P256.Proofs.Common.Instructions.CrossPageStore (Pre Writable mov_m64_r64_effect_step_any)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.SquareRoot.Square.Wide

open P256.Proofs.Program P256.Spec.Program.Routines
open P256.Proofs.Common.Field

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure StoresLowPre (s : RamState) : Prop where
  rip : s.RIP = 0x11ccc2
  writable : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)), Writable s (((Operand.reg 7 : Operand 64).read s) + i) 8
  codeApart : ∀ i ∈ ([0, 8, 16, 24] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (((Operand.reg 7 : Operand 64).read s) + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def storesLowBytes : List UInt8 :=
  [0x48, 0x89, 0xf, 0x48, 0x89, 0x47, 0x8, 0x4c, 0x89, 0x6f, 0x10, 0x4c, 0x89, 0x5f, 0x18]

def storesLowEffect (s : RamState) : Effect :=
  { rip := 0x11ccd1
    writes := [
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 0) : Operand 64), ((Operand.reg 1 : Operand 64).read s)⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 8) : Operand 64), ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 16) : Operand 64), ((Operand.reg 13 : Operand 64).read s)⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 24) : Operand 64), ((Operand.reg 11 : Operand 64).read s)⟩]
    flags := some (⟨none, none, none, none, none, none⟩) }

set_option maxHeartbeats 1200000 in
theorem storesLow_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary StoresLowPre (codeRange 0x11ccc2 storesLowBytes)
      (Effect.post storesLowEffect) := by
  refine AdvanceTriple.block_first ?k (mov_m64_r64_effect_step_any 0x11ccc2 0x48 (by simp [RexWPrefix]) 1 (.base 7 .none) (by decide +kernel) rfl rfl) ?sub ?pre ?av ?next
  case sub => exact codeRange_slice_subset 0x11ccc2 storesLowBytes 0 3
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 0 (by simp), hP.codeApart 0 (by simp) 0x1ccc2 3 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.codeApart 0 (by simp) 0x1ccc2 15 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccc5 (by decide))
  case' k => x86_norm
  advance_then (mov_m64_r64_effect_step_any 0x11ccc5 0x48 (by simp [RexWPrefix]) 0 (.base 7 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11ccc2 storesLowBytes 3 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 8 (by simp)
    · x86_norm
      exact hP.codeApart 8 (by simp) 0x1ccc5 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 8 (by simp) 0x1ccc2 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccc9 (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11ccc9 0x4c (by simp [RexWPrefix]) 5 (.base 7 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11ccc2 storesLowBytes 7 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 16 (by simp)
    · x86_norm
      exact hP.codeApart 16 (by simp) 0x1ccc9 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 16 (by simp) 0x1ccc2 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cccd (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11cccd 0x4c (by simp [RexWPrefix]) 3 (.base 7 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11ccc2 storesLowBytes 11 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 24 (by simp)
    · x86_norm
      exact hP.codeApart 24 (by simp) 0x1cccd 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 24 (by simp) 0x1ccc2 15 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccd1 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [storesLowEffect]
  · x86_norm [storesLowEffect]
    repeat first | apply And.intro | rfl
  · intro i; cases i <;> x86_norm [storesLowEffect] <;> rfl
  · x86_norm [storesLowEffect]

end P256.Proofs.Sec1.SquareRoot.Square.Wide
