import P256.Proofs.Nonce.Fill.Tail.Compare.Zero
import P256.Proofs.Nonce.Fill.Tail.Compare.Borrow.Run
import P256.Proofs.Nonce.Fill.Tail.Compare.Borrow.Select

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Signing.Search

open Classical in
theorem compare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Decoded initial s orderAddress state) :
    ∃ fuel t, Advances boundary fuel s t ∧ Compared initial t orderAddress state ∧
      t.RIP = if ValidNonce (nextCandidate state).1 then 0x1076e5 else 0x1076c3 := by
  obtain ⟨zeroFuel, t, zeroRun, compared, zeroRip, zero⟩ := Compare.zero pre input
  obtain ⟨borrowFuel, u, borrowRun, checked, borrowRip, nonzero, smaller⟩ :=
    Compare.Borrow.run pre compared zeroRip zero
  obtain ⟨v, selectRun, selected, target⟩ :=
    Compare.Borrow.select pre checked borrowRip nonzero smaller
  exact ⟨zeroFuel + borrowFuel + 5, v, (zeroRun.trans borrowRun).trans selectRun,
    selected, target⟩

end P256.Proofs.Nonce.Fill.Tail
