import ChaCha20Poly1305.Proofs.Core.Segments

namespace ChaCha20Poly1305.Proofs.Core

open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract

theorem core_call [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (boundary : ReturnBoundary)
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip)
    (hReturnLow : (returnBoundary s).rip.toNat < 2 ^ 32) :
    ∃ fuel t, Advances boundary fuel s t ∧
      CorePost s t key nonce associatedData plaintext outPtr := by
  obtain ⟨f1, t1, h1, c1⟩ := setup boundary hPre hBoundaryOutside hBoundaryDifferent
  obtain ⟨f2, t2, h2, c2⟩ :=
    absorb_associated_data boundary hPre hBoundaryOutside hBoundaryDifferent c1
  obtain ⟨f3, t3, h3, c3⟩ := encrypt boundary hPre hBoundaryOutside hBoundaryDifferent c2
  obtain ⟨f4, t4, h4, c4⟩ := absorb_ciphertext boundary hPre hBoundaryOutside hBoundaryDifferent c3
  obtain ⟨f5, t5, h5, c5⟩ := absorb_lengths boundary hPre hBoundaryOutside hBoundaryDifferent c4
  obtain ⟨f6, t6, h6, c6⟩ := finish boundary hPre hBoundaryOutside hBoundaryDifferent hReturnLow c5
  exact ⟨_, t6, ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6, c6⟩

end ChaCha20Poly1305.Proofs.Core
