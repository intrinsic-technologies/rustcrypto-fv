import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Contracts
import Md5.Proofs.Block.Entry
import Md5.Proofs.Block.Execution

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare

open Md5.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Block

def entryBytes (variant : Variant := .original) : List UInt8 :=
  match variant with
  | .original | .finalize => [0x48, 0x8d, 0x7c, 0x24, 0x60, 0x48, 0x8d, 0x74, 0x24, 0x8, 0xb9, 0xb, 0x0, 0x0, 0x0]
  | .discard => [0x48, 0x8d, 0xbc, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8d, 0x74, 0x24, 0x20, 0xb9, 0xb, 0x0, 0x0, 0x0]

def entryEffect (s : RamState) (variant : Variant := .original) : Effect where
  rip := match variant with
    | .original => 0x100a9f
    | .finalize => 0x10112f
    | .discard => 0x10160f
  writes := [⟨(.reg 7 : Operand 64), stackPtr s + BitVec.ofNat 64 variant.tailOffset⟩,
    ⟨(.reg 6 : Operand 64), stackPtr s + BitVec.ofNat 64 variant.toKind.contextOffset⟩,
    ⟨(.reg 1 : Operand 64), 11⟩]

theorem entry [Bindings] {variant : Variant} (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = variant.toKind.entry)
      (codeRange variant.toKind.entry (entryBytes variant)) (fun s ↦ entryEffect s variant) := by
  cases variant with
  | original =>
      change AdvancesBlock boundary (fun s ↦ s.RIP = 0x100a90) _ _
      unfold entryBytes
      md5_run_begin lea_r64_effect_step 0x100a90 0x48
        (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 96))
        (by decide) (by decide) (by decide)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xa95 (by decide +kernel)
      md5_run_then lea_r64_effect_step 0x100a95 0x48
        (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 8))
        (by decide) (by decide) (by decide)
      case sub => exact codeRange_mem_of_drop (p := 0x100a90) 5 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xa9a (by decide +kernel)
      md5_run_then mov_r32_imm32_effect_step 0x100a9a 0xb9 (by decide) 11
      case sub => exact codeRange_mem_of_drop (p := 0x100a90) 10 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0xa9f (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset, stackPtr]
        exact ⟨rfl, rfl⟩
      · intro i; cases i <;> x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset]
  | finalize =>
      change AdvancesBlock boundary (fun s ↦ s.RIP = 0x101120) _ _
      unfold entryBytes
      md5_run_begin lea_r64_effect_step 0x101120 0x48
        (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 96))
        (by decide) (by decide) (by decide)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1125 (by decide +kernel)
      md5_run_then lea_r64_effect_step 0x101125 0x48
        (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 8))
        (by decide) (by decide) (by decide)
      case sub => exact codeRange_mem_of_drop (p := 0x101120) 5 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x112a (by decide +kernel)
      md5_run_then mov_r32_imm32_effect_step 0x10112a 0xb9 (by decide) 11
      case sub => exact codeRange_mem_of_drop (p := 0x101120) 10 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x112f (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset, stackPtr]
        exact ⟨rfl, rfl⟩
      · intro i; cases i <;> x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset]
  | discard =>
      change AdvancesBlock boundary (fun s ↦ s.RIP = 0x1015fd) _ _
      unfold entryBytes
      md5_run_begin lea_r64_effect_step 0x1015fd 0x48
        (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d32 136))
        (by decide) (by decide) (by decide)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x1605 (by decide +kernel)
      md5_run_then lea_r64_effect_step 0x101605 0x48
        (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d8 32))
        (by decide) (by decide) (by decide)
      case sub => exact codeRange_mem_of_drop (p := 0x1015fd) 8 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x160a (by decide +kernel)
      md5_run_then mov_r32_imm32_effect_step 0x10160a 0xb9 (by decide) 11
      case sub => exact codeRange_mem_of_drop (p := 0x1015fd) 13 (by decide +kernel)
      case boundary => intro _ _; exact text_address_ne_return hOutside 0x160f (by decide +kernel)
      apply AdvancesBlock.block_end
      intro s t _ hE
      apply hE.weaken
      · x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset, stackPtr]
        exact ⟨rfl, rfl⟩
      · intro i; cases i <;> x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset]
      · x86_norm [entryEffect, Variant.tailOffset, Variant.toKind, Kind.contextOffset]

theorem entry_state [Bindings] {variant : Variant} {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Pre variant.toKind boundary message s) :
    ∃ fuel u, Advances boundary fuel s u ∧ ReadyToStep u ∧
      CodeIn Extracted.programImage u ∧ (entryEffect s variant).Holds s u := by
  have hc : CodeIn (codeRange variant.toKind.entry (entryBytes variant)) s := by
    cases variant with
    | original => exact program_text_slice h.code 0xa90 15 (by decide +kernel)
    | finalize => exact program_text_slice h.code 0x1120 15 (by decide +kernel)
    | discard => exact program_text_slice h.code 0x15fd 18 (by decide +kernel)
  obtain ⟨fuel, u, ha, hr, _, he⟩ := entry boundary h.boundaryOutside s h.ready hc h.rip
  refine ⟨fuel, u, ha, hr, ?_, he⟩
  apply he.codeIn _ h.code
  apply Effect.Avoids.of_noMem
  simp [entryEffect, Effect.components, Component.Covers]

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Prepare
