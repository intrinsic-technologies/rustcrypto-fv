import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Nonzero.ClearBlock

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field P256.Proofs.Program

structure ClearPre (s : RamState) : Prop where
  rip : s.RIP = 0x100c48
  writable : ∀ off ∈ ([104,96,88,80] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s+off) 8
  codeApart : ∀ off ∈ ([104,96,88,80] : List (BitVec 64)), ∀ offset len : Nat,
    offset+len ≤ 118431 → RangeApart (stackPtr s+off) 8
      (Extracted.textAddress+BitVec.ofNat 64 offset) len

def clearBytes : List UInt8 :=
  [0x48,0xc7,0x44,0x24,0x68,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x60,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x58,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x50,0x0,0x0,0x0,0x0]

def clearEffect (s : RamState) : Effect :=
  { rip := 0x100c6c
    writes := [⟨(.mem (stackPtr s+104) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+96) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+88) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+80) : Operand 64),0⟩] }

theorem clear_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x100c48 clearBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xc48 _ (by decide) (by decide +kernel)

theorem clear_words [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvanceTriple boundary ClearPre (codeRange 0x100c48 clearBytes) (Effect.post clearEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x100c48 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl 0)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 104 (by simp),h.codeApart 104 (by simp) 0xc48 9 (by decide)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0xc51 (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    exact h.codeApart 104 (by simp) 0xc48 36 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x100c51 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x100c48 clearBytes 9 9
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 96 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 96 (by simp) 0xc51 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 96 (by simp) 0xc48 36 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc5a (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x100c5a 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x100c48 clearBytes 18 9
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 88 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 88 (by simp) 0xc5a 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 88 (by simp) 0xc48 36 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc63 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x100c63 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x100c48 clearBytes 27 9
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 80 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 80 (by simp) 0xc63 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 80 (by simp) 0xc48 36 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xc6c (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [clearEffect]
  · x86_norm [clearEffect,stackPtr]
    simp [Operand.read]
  · intro i; cases i <;> x86_norm [clearEffect]
  · x86_norm [clearEffect,stackPtr]
    simp [Operand.read]

end P256.Proofs.Generate.Sampler.Nonzero.ClearBlock
