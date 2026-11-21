import Md5.Proofs.Buffered.Finalize.Streams.Slices.Layout
import Md5.Proofs.Buffered.Finalize.Contracts
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

attribute [local x86_compose] relocated

def entryBytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x10, 0x48, 0x8d, 0xb4, 0x24, 0xc0, 0, 0, 0,
    0xb9, 0x0b, 0, 0, 0]

def entryEffect (s : RamState) (update : Bool := false) : Effect where
  rip := (BitVec.ofNat 64 (relocated update 0x10043d))
  writes := [⟨(.reg 7 : Operand 64), stackPtr s + 16⟩,
    ⟨(.reg 6 : Operand 64), stackPtr s + 192⟩,
    ⟨(.reg 1 : Operand 64), 11⟩]

theorem entry {update : Bool} [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = (BitVec.ofNat 64 (relocated update 0x10042b)))
      (codeRange (BitVec.ofNat 64 (relocated update 0x10042b)) entryBytes) (entryEffect (update := update)) := by
  cases update
  case false =>
    unfold entryBytes
    md5_run_begin lea_r64_effect_step (BitVec.ofNat 64 0x10042b) 0x48
      (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 16))
      (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x430 (by decide +kernel)
    md5_run_then lea_r64_effect_step (BitVec.ofNat 64 0x100430) 0x48
      (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 192))
      (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x10042b)) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x438 (by decide +kernel)
    md5_run_then mov_r32_imm32_effect_step (BitVec.ofNat 64 0x100438) 0xb9 (by decide) 11
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x10042b)) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x43d (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [entryEffect]
    · x86_norm [entryEffect, stackPtr]
      exact ⟨rfl, rfl⟩
    · intro i; cases i <;> x86_norm [entryEffect]
    · x86_norm [entryEffect]

  case true =>
    unfold entryBytes
    md5_run_begin lea_r64_effect_step (BitVec.ofNat 64 0x1019db) 0x48
      (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 16))
      (by decide) (by decide) (by decide)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19e0 (by decide +kernel)
    md5_run_then lea_r64_effect_step (BitVec.ofNat 64 0x1019e0) 0x48
      (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 192))
      (by decide) (by decide) (by decide)
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x1019db)) 5 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19e8 (by decide +kernel)
    md5_run_then mov_r32_imm32_effect_step (BitVec.ofNat 64 0x1019e8) 0xb9 (by decide) 11
    case sub => exact codeRange_mem_of_drop (p := (BitVec.ofNat 64 0x1019db)) 13 (by decide +kernel)
    case boundary => intro _ _; exact text_address_ne_return hOutside 0x19ed (by decide +kernel)
    apply AdvancesBlock.block_end
    intro s t _ hE
    apply hE.weaken
    · x86_norm [entryEffect]
    · x86_norm [entryEffect, stackPtr]
      exact ⟨rfl, rfl⟩
    · intro i; cases i <;> x86_norm [entryEffect]
    · x86_norm [entryEffect]

theorem prepare {update : Bool} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Pre (streamKind update) boundary message s) :
    ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧
      CodeIn Extracted.programImage u ∧ (entryEffect (update := update) s).Holds s u := by
  cases update
  case false =>
    have hc : CodeIn (codeRange (BitVec.ofNat 64 0x10042b) entryBytes) s :=
      by
        have hc := program_text_slice h.code 0x42b 18 (by decide +kernel)
        have he : Extracted.textBytes.toListFrom 0x42b 18 = entryBytes :=
          by decide +kernel
        rw [he] at hc
        exact hc
    obtain ⟨fuel, u, ha, hr, _, he⟩ := entry (update := false) boundary h.boundaryOutside s h.ready hc h.rip
    refine ⟨fuel, u, ha, hr, ?_, he⟩
    apply he.codeIn _ h.code
    apply Effect.Avoids.of_noMem
    simp [entryEffect, Effect.components, Component.Covers]

  case true =>
    have hc : CodeIn (codeRange (BitVec.ofNat 64 0x1019db) entryBytes) s :=
      by
        have hc := program_text_slice h.code 0x19db 18 (by decide +kernel)
        have he : Extracted.textBytes.toListFrom 0x19db 18 = entryBytes :=
          by decide +kernel
        rw [he] at hc
        exact hc
    obtain ⟨fuel, u, ha, hr, _, he⟩ := entry (update := true) boundary h.boundaryOutside s h.ready hc h.rip
    refine ⟨fuel, u, ha, hr, ?_, he⟩
    apply he.codeIn _ h.code
    apply Effect.Avoids.of_noMem
    simp [entryEffect, Effect.components, Component.Covers]

end Md5.Proofs.Buffered.Finalize.Streams.Slices
