import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Block.Execution

namespace Md5.Proofs.Buffered.Finalize.Digest.Entry

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

def bytes : List UInt8 :=
  [0x48, 0x8d, 0x7c, 0x24, 0x18, 0x48, 0x8d, 0xb4, 0x24, 0xb0, 0, 0, 0,
    0xb9, 0x0b, 0, 0, 0]

def effect (s : RamState) : Effect :=
  { rip := 0x1000e1
    writes := [⟨(.reg 7 : Operand 64), stackPtr s + 24⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 176⟩,
      ⟨(.reg 1 : Operand 64), 11⟩] }

theorem execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1000cf) (codeRange 0x1000cf bytes) effect := by
  unfold bytes
  md5_run_begin lea_r64_effect_step 0x1000cf 0x48 (by unfold RexWPrefix; decide)
    7 (.sib 4 none 0 (.d8 24)) (by decide) (by decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xd4 (by decide +kernel)
  md5_run_then lea_r64_effect_step 0x1000d4 0x48 (by unfold RexWPrefix; decide)
    6 (.sib 4 none 0 (.d32 176)) (by decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x1000cf) 5 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xdc (by decide +kernel)
  md5_run_then mov_r32_imm32_effect_step 0x1000dc 0xb9 (by decide) 11
  case sub => exact codeRange_mem_of_drop (p := 0x1000cf) 13 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0xe1 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ hE
  apply hE.weaken
  · x86_norm [effect]
  · x86_norm [effect, stackPtr]
    exact ⟨rfl, rfl⟩
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

theorem run [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Pre .digest boundary message s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  have hc : CodeIn (codeRange 0x1000cf bytes) s :=
    program_text_slice h.code 0xcf 18 (by decide +kernel)
  obtain ⟨fuel, t, ha, hr, _, he⟩ := execution boundary h.boundaryOutside s h.ready hc h.rip
  refine ⟨fuel, t, ha, hr, he.codeIn ?_ h.code, he⟩
  apply Effect.Avoids.of_noMem
  simp [effect, Effect.components, Component.Covers]

end Md5.Proofs.Buffered.Finalize.Digest.Entry
