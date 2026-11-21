import P256.Proofs.Nonce.Fill.Tail.Decode.Scan.Count
import P256.Proofs.Nonce.Fill.Tail.Decode.Scan.Finish

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem scan [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Updated initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ ScanReady initial t orderAddress state := by
  obtain ⟨t, first, stage, rip, order, scratch, shift, bits, zero⟩ := Scan.count pre input
  obtain ⟨u, last, result⟩ := Scan.finish pre stage rip order scratch shift bits zero
  exact ⟨57, u, first.trans last, result⟩

end P256.Proofs.Nonce.Fill.Tail.Decode
