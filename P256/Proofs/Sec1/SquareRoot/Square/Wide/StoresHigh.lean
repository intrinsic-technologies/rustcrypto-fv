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

structure StoresHighPre (s : RamState) : Prop where
  rip : s.RIP = 0x11ccd1
  writable : ∀ i ∈ ([32, 40, 48, 56] : List (BitVec 64)), Writable s (((Operand.reg 7 : Operand 64).read s) + i) 8
  codeApart : ∀ i ∈ ([32, 40, 48, 56] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (((Operand.reg 7 : Operand 64).read s) + i) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def storesHighBytes : List UInt8 :=
  [0x4c, 0x89, 0x47, 0x20, 0x4c, 0x89, 0x77, 0x28, 0x48, 0x89, 0x5f, 0x30, 0x4c, 0x89, 0x7f, 0x38]

def storesHighEffect (s : RamState) : Effect :=
  { rip := 0x11cce1
    writes := [
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 32) : Operand 64), ((Operand.reg 8 : Operand 64).read s)⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 40) : Operand 64), ((Operand.reg 14 : Operand 64).read s)⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 48) : Operand 64), ((Operand.reg 3 : Operand 64).read s)⟩,
      ⟨(.mem (((Operand.reg 7 : Operand 64).read s) + 56) : Operand 64), ((Operand.reg 15 : Operand 64).read s)⟩]
    flags := some (⟨none, none, none, none, none, none⟩) }

set_option maxHeartbeats 1200000 in
theorem storesHigh_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary StoresHighPre (codeRange 0x11ccd1 storesHighBytes)
      (Effect.post storesHighEffect) := by
  refine AdvanceTriple.block_first ?k (mov_m64_r64_effect_step_any 0x11ccd1 0x4c (by simp [RexWPrefix]) 0 (.base 7 (.d8 32)) (by decide +kernel) rfl rfl) ?sub ?pre ?av ?next
  case sub => exact codeRange_slice_subset 0x11ccd1 storesHighBytes 0 4
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 32 (by simp), hP.codeApart 32 (by simp) 0x1ccd1 4 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm
    exact hP.codeApart 32 (by simp) 0x1ccd1 16 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccd5 (by decide))
  case' k => x86_norm
  advance_then (mov_m64_r64_effect_step_any 0x11ccd5 0x4c (by simp [RexWPrefix]) 6 (.base 7 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11ccd1 storesHighBytes 4 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 40 (by simp)
    · x86_norm
      exact hP.codeApart 40 (by simp) 0x1ccd5 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 40 (by simp) 0x1ccd1 16 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccd9 (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11ccd9 0x48 (by simp [RexWPrefix]) 3 (.base 7 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11ccd1 storesHighBytes 8 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 48 (by simp)
    · x86_norm
      exact hP.codeApart 48 (by simp) 0x1ccd9 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 48 (by simp) 0x1ccd1 16 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1ccdd (by decide))
  advance_then (mov_m64_r64_effect_step_any 0x11ccdd 0x4c (by simp [RexWPrefix]) 7 (.base 7 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x11ccd1 storesHighBytes 12 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 56 (by simp)
    · x86_norm
      exact hP.codeApart 56 (by simp) 0x1ccdd 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 56 (by simp) 0x1ccd1 16 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1cce1 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [storesHighEffect]
  · x86_norm [storesHighEffect]
    repeat first | apply And.intro | rfl
  · intro i; cases i <;> x86_norm [storesHighEffect] <;> rfl
  · x86_norm [storesHighEffect]

end P256.Proofs.Sec1.SquareRoot.Square.Wide
