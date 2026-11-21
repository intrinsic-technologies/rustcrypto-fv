import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Scalar

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field P256.Proofs.Program

structure ClearPre (s : RamState) : Prop where
  rip : s.RIP = 0x106892
  writable : ∀ off ∈ ([72,64,56,48] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s+off) 8
  codeApart : ∀ off ∈ ([72,64,56,48] : List (BitVec 64)), ∀ offset len : Nat,
    offset+len ≤ 118431 → RangeApart (stackPtr s+off) 8
      (Extracted.textAddress+BitVec.ofNat 64 offset) len

def clearBytes : List UInt8 :=
  [0x48,0xc7,0x44,0x24,0x48,0,0,0,0,0x48,0xc7,0x44,0x24,0x40,0,0,0,0,
    0x48,0xc7,0x44,0x24,0x38,0,0,0,0,0x48,0xc7,0x44,0x24,0x30,0,0,0,0]

def clearEffect (s : RamState) : Effect :=
  { rip := 0x1068b6
    writes := [⟨(.mem (stackPtr s+72) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+64) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+56) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+48) : Operand 64),0⟩] }

theorem clear_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x106892 clearBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x6892 _ (by decide) (by decide +kernel)

theorem clear_words [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvanceTriple boundary ClearPre (codeRange 0x106892 clearBytes) (Effect.post clearEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x106892 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl 0)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 72 (by simp),h.codeApart 72 (by simp) 0x6892 9 (by decide)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x689b (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    exact h.codeApart 72 (by simp) 0x6892 36 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x10689b 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x106892 clearBytes 9 9
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 64 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 64 (by simp) 0x689b 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 64 (by simp) 0x6892 36 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x68a4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1068a4 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 56)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x106892 clearBytes 18 9
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 56 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 56 (by simp) 0x68a4 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 56 (by simp) 0x6892 36 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x68ad (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1068ad 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x106892 clearBytes 27 9
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 48 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 48 (by simp) 0x68ad 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 48 (by simp) 0x6892 36 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x68b6 (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [clearEffect]
  · x86_norm [clearEffect,stackPtr]
    simp [Operand.read]
  · intro i; cases i <;> x86_norm [clearEffect]
  · x86_norm [clearEffect,stackPtr]
    simp [Operand.read]

end P256.Proofs.EcdhWrapper.Scalar
