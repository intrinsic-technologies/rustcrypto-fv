import P256.Proofs.Nonce.Fill.Tail.Decode.Scan
import P256.Proofs.Nonce.Fill.Tail.Decode.Read
import P256.Proofs.Nonce.Fill.Tail.Decode.Shift

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem decode [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Updated initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Decoded initial t orderAddress state := by
  obtain ⟨scanFuel, scanned, scanRun, scanResult⟩ := Decode.scan pre input
  obtain ⟨readFuel, read, readRun, readResult⟩ := Decode.read pre scanResult
  obtain ⟨shiftFuel, t, shiftRun, result⟩ := Decode.shift pre readResult
  exact ⟨scanFuel + readFuel + shiftFuel, t, (scanRun.trans readRun).trans shiftRun, result⟩

end P256.Proofs.Nonce.Fill.Tail
