import Sha1.Proofs.Compress.Machine.Projection

namespace Sha1.Proofs.Compress.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Spec.Program

theorem cut000_of_blockData {stack input : BitVec 64} {H : Vector (BitVec 32) 5}
    {M : Vector (BitVec 32) 16} {s : RamState} (h : BlockData stack input H M s) :
    Write.AllHold s (cut000 stack input H M) :=
  ⟨h.registers.2.2.2.2, h.registers.2.2.1, h.inputPointer,
    h.registers.2.1, h.registers.2.2.2.1, h.registers.1⟩

theorem blockCorrect_of_segment
    (hSegments : ∀ [Bindings] (boundary : ReturnBoundary),
      OutsideCompression boundary.rip →
      Segment boundary 0x102530 0x1036a2 cut000 cut083) : BlockCorrect := by
  intro _ boundary s stack input H M hOutside hReady hCode hRip hBlock
  obtain ⟨n, t, hAdvance, hReady', hCode', hRip', hFrame', hWords', hAgree⟩ :=
    hSegments boundary hOutside stack input H M s hReady hCode hRip
      (FrameData.of_blockData hBlock) (cut000_of_blockData hBlock)
  exact ⟨n, t, hAdvance, hReady', hCode', hRip',
    blockData_of_snapshot80 hFrame' hWords', hAgree⟩

end Sha1.Proofs.Compress.Machine
