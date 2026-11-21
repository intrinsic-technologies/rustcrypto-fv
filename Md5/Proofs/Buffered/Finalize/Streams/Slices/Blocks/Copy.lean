import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Execution
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy.Properties

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem run {update : Bool} [Bindings] {kind : Kind} {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hStorage : Storage (streamKind update) s) (hOutside : ¬ InProgram boundary.rip)
    (hRip : s.RIP = (kind.entry (update := update))) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (effect (update := update) kind s).Holds s t := by
  have hBytes : CodeIn (codeRange (kind.entry (update := update)) kind.bytes) s := by
    cases update <;> cases kind
    · exact program_text_slice hCode 0x48d 108 (by decide +kernel)
    · exact program_text_slice hCode 0x555 95 (by decide +kernel)
    · exact program_text_slice hCode 0x1a3d 108 (by decide +kernel)
    · exact program_text_slice hCode 0x1b05 95 (by decide +kernel)
  obtain ⟨fuel, t, hRun, hReady', _, hEffect⟩ :=
    execution (update := update) kind boundary hOutside s hReady hBytes ⟨hStorage, hRip⟩
  exact ⟨fuel, t, hRun, hReady', hEffect.codeIn (effect_avoids (update := update) hStorage) hCode, hEffect⟩

end Md5.Proofs.Buffered.Finalize.Streams.Slices.Blocks.Copy
