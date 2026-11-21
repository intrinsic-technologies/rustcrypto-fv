import P256.Proofs.HMAC.Finalize.Padding.Fill.Mark
import P256.Proofs.HMAC.Finalize.Padding.Fill.Finish

open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem fill [Bindings] (outer : Bool)
    {initial s : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Buffered initial s message)
    (rip : s.RIP = paddingStart outer) (small : message.size % 64 < 56) :
    ∃ fuel t, Advances boundary fuel s t ∧ Padded initial t message outer ∧
      t.RIP = lengthStart outer ∧ MemoryWriteFrame s t #v[scratchRegion initial] := by
  obtain ⟨markFuel, marked, markRun, markedState, markedRip, markMemory⟩ :=
    mark outer pre state rip
  obtain ⟨fillFuel, filled, fillRun, filledState, filledRip, fillMemory⟩ :=
    finish_fill outer pre markedState markedRip small
  exact ⟨markFuel + fillFuel, filled, markRun.trans fillRun, filledState, filledRip,
    memoryWriteFrame_trans markMemory fillMemory⟩

end P256.Proofs.HMAC.Finalize.Padding
