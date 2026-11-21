import Md5.Proofs.Buffered.Xor
import Md5.Proofs.Block.Execution
import Md5.Proofs.Block.Entry

namespace Md5.Proofs.Buffered.Finalize.Digest.Prefix

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

def bytes : List UInt8 := [0x4d, 0x89, 0xe6, 0x49, 0x83, 0xf6, 0x3f]

def effect (s : RamState) : Effect :=
  { rip := 0x100107
    writes := [⟨(.reg 14 : Operand 64), (.reg 12 : Operand 64).read s ^^^ 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem execution [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x100100) (codeRange 0x100100 bytes) effect := by
  unfold bytes
  md5_run_begin mov_r64_r64_effect_step 0x100100 0x4d 0xe6
    (by unfold RexWPrefix; decide) (by decide)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x103 (by decide +kernel)
  md5_run_then xor_r64_imm8_effect_step 0x100103 0x49 0xf6 63
    (by unfold RexWPrefix; decide) (by decide) (by decide)
  case sub => exact codeRange_mem_of_drop (p := 0x100100) 3 (by decide +kernel)
  case boundary => intro _ _; exact text_address_ne_return hOutside 0x107 (by decide +kernel)
  apply AdvancesBlock.block_end
  intro s t _ he
  apply he.weaken
  · x86_norm [effect]
  · x86_norm [effect]
    rfl
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

theorem run [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hip : s.RIP = 0x100100) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect s).Holds s t := by
  have hb : CodeIn (codeRange 0x100100 bytes) s :=
    program_text_slice hc 0x100 7 (by decide +kernel)
  obtain ⟨n, t, ha, ht, _, he⟩ := execution boundary hout s hr hb hip
  refine ⟨n, t, ha, ht, he.codeIn ?_ hc, he⟩
  exact Effect.Avoids.of_noMem (by simp [effect, Effect.components, Component.Covers]) _

end Md5.Proofs.Buffered.Finalize.Digest.Prefix
