import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.Compose
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Program.Code

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Select

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fede
  writable : ∀ off ∈ ([192,200,208,216] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + off) 8
  codeApart : ∀ off ∈ ([192,200,208,216] : List (BitVec 64)), ∀ offset len : Nat,
    offset + len ≤ 118431 → RangeApart (stackPtr s + off) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def zeroBytes : List UInt8 := [72,199,132,36,216,0,0,0,0,0,0,0,72,199,132,36,208,0,0,0,0,0,0,0,72,199,132,36,200,0,0,0,0,0,0,0,72,199,132,36,192,0,0,0,0,0,0,0]

def zeroEffect (s : RamState) : Effect :=
  { rip := 0x10ff0e
    writes := [⟨(.mem (stackPtr s + 216) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 208) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 200) : Operand 64), 0⟩,
      ⟨(.mem (stackPtr s + 192) : Operand 64), 0⟩] }

theorem zero [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ZeroPre (codeRange 0x10fede zeroBytes) (Effect.post zeroEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10fede 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl 0)
  case pre =>
    intro s hP
    exact ⟨hP.rip, hP.writable 216 (by simp), hP.codeApart 216 (by simp) 0xfede 12 (by decide)⟩
  case av =>
    intro s hP
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    exact hP.codeApart 216 (by simp) 0xfede 48 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfeea (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10feea 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 208)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fede zeroBytes 12 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 208 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 208 (by simp) 0xfeea 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 208 (by simp) 0xfede 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfef6 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10fef6 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fede zeroBytes 24 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 200 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 200 (by simp) 0xfef6 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 200 (by simp) 0xfede 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xff02 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10ff02 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fede zeroBytes 36 12
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm [stackPtr]
      exact hP.writable 192 (by simp)
    · x86_norm [stackPtr]
      exact hP.codeApart 192 (by simp) 0xff02 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hP.codeApart 192 (by simp) 0xfede 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xff0e (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [zeroEffect, stackPtr, Operand.read_reg64]
  · x86_norm [zeroEffect, stackPtr, Operand.read_reg64]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [zeroEffect, stackPtr, Operand.read_reg64]
  · x86_norm [zeroEffect, stackPtr, Operand.read_reg64]

theorem zeroBytes_extracted : Extracted.textBytes.toListFrom 0xfede 48 = zeroBytes := by decide +kernel

end P256.Proofs.Sec1.Decompress.Select
