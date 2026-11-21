import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Nonzero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field P256.Proofs.Program

structure ClearPre (s : RamState) : Prop where
  rip : s.RIP = 0x1068d7
  writable : ∀ off ∈ ([192,184,176,168] : List (BitVec 64)),
    P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s+off) 8
  codeApart : ∀ off ∈ ([192,184,176,168] : List (BitVec 64)), ∀ offset len : Nat,
    offset+len ≤ 118431 → RangeApart (stackPtr s+off) 8
      (Extracted.textAddress+BitVec.ofNat 64 offset) len

def clearBytes : List UInt8 :=
  [0x48,0xc7,0x84,0x24,0xc0,0,0,0,0,0,0,0,0x48,0xc7,0x84,0x24,0xb8,0,0,0,0,0,0,0,
    0x48,0xc7,0x84,0x24,0xb0,0,0,0,0,0,0,0,0x48,0xc7,0x84,0x24,0xa8,0,0,0,0,0,0,0]

def clearEffect (s : RamState) : Effect :=
  { rip := 0x106907
    writes := [⟨(.mem (stackPtr s+192) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+184) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+176) : Operand 64),0⟩,
      ⟨(.mem (stackPtr s+168) : Operand 64),0⟩] }

theorem clear_loaded {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1068d7 clearBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x68d7 _ (by decide) (by decide +kernel)

theorem clear_words [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvanceTriple boundary ClearPre (codeRange 0x1068d7 clearBytes) (Effect.post clearEffect) := by
  advance_begin (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1068d7 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 192)) (by decide) rfl rfl 0)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 192 (by simp),h.codeApart 192 (by simp) 0x68d7 12 (by decide)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x68e3 (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    exact h.codeApart 192 (by simp) 0x68d7 48 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1068e3 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 184)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1068d7 clearBytes 12 12
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 184 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 184 (by simp) 0x68e3 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 184 (by simp) 0x68d7 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x68ef (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1068ef 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1068d7 clearBytes 24 12
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 176 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 176 (by simp) 0x68ef 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 176 (by simp) 0x68d7 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x68fb (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any 0x1068fb 0x48
    (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1068d7 clearBytes 36 12
  case mid =>
    intro s t hp hh ho
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hh (ho true) (by x86_norm) ?_ ?_,?_,?_⟩
    · x86_norm [stackPtr]
      exact hp.writable 168 (by simp)
    · x86_norm [stackPtr]
      exact hp.codeApart 168 (by simp) 0x68fb 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (ho true)
      apply Effect.avoids_codeRange
      x86_norm [stackPtr]
      exact hp.codeApart 168 (by simp) 0x68d7 48 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x6907 (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [clearEffect]
  · x86_norm [clearEffect,stackPtr]
    simp [Operand.read]
  · intro i; cases i <;> x86_norm [clearEffect]
  · x86_norm [clearEffect,stackPtr]
    simp [Operand.read]

end P256.Proofs.EcdhWrapper.Nonzero
