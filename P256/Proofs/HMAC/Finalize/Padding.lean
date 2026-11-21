import P256.Proofs.HMAC.Finalize.Padding.Fill
import P256.Proofs.HMAC.Finalize.Padding.Block
import P256.Proofs.HMAC.Finalize.Padding.Compression

open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem padding_compress [Bindings] (outer : Bool)
    {initial s : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Buffered initial s message)
    (rip : s.RIP = paddingStart outer) (small : message.size % 64 < 56) :
    ∃ fuel t, Advances boundary fuel s t ∧ Compressed initial t message ∧
      t.RIP = paddingEnd outer ∧ MemoryWriteFrame s t #v[scratchRegion initial] := by
  obtain ⟨fillFuel, filled, fillRun, filledState, filledRip, fillMemory⟩ :=
    Padding.fill outer pre state rip small
  obtain ⟨blockFuel, prepared, blockRun, preparedState, preparedRip, blockMemory⟩ :=
    Padding.block outer pre filledState filledRip small
  obtain ⟨compressFuel, final, compressRun, finalState, finalRip, compressMemory⟩ :=
    Padding.compress outer pre preparedState preparedRip
  exact ⟨fillFuel + blockFuel + compressFuel, final,
    (fillRun.trans blockRun).trans compressRun, finalState, finalRip,
    memoryWriteFrame_trans (memoryWriteFrame_trans fillMemory blockMemory) compressMemory⟩

end P256.Proofs.HMAC.Finalize
