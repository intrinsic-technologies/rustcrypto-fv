import ChaCha20Poly1305.Proofs.Core.Cuts
import ChaCha20Poly1305.Proofs.Core.Segments.Lengths
import ChaCha20Poly1305.Proofs.Core.Segments.Absorb
import ChaCha20Poly1305.Proofs.Core.Segments.Encrypt
import ChaCha20Poly1305.Proofs.Core.Segments.Setup
import ChaCha20Poly1305.Proofs.Core.Segments.Finish

namespace ChaCha20Poly1305.Proofs.Core

open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract

variable [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
  {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}

theorem setup (boundary : ReturnBoundary)
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip) :
    ∃ fuel t, Advances boundary fuel s t ∧
      Cut1 s t key nonce associatedData plaintext inPtr outPtr := by
  exact Setup.setup boundary hPre hBoundaryOutside hBoundaryDifferent

theorem absorb_associated_data (boundary : ReturnBoundary) {t : RamState}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip)
    (hCut : Cut1 s t key nonce associatedData plaintext inPtr outPtr) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Cut2 s u key nonce associatedData plaintext inPtr outPtr := by
  exact Absorb.absorb_associated_data boundary hPre hBoundaryOutside hBoundaryDifferent hCut

theorem encrypt (boundary : ReturnBoundary) {t : RamState}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip)
    (hCut : Cut2 s t key nonce associatedData plaintext inPtr outPtr) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Cut3 s u key nonce associatedData plaintext outPtr := by
  exact Encrypt.encrypt_segment boundary hPre hBoundaryOutside hBoundaryDifferent hCut


theorem absorb_ciphertext (boundary : ReturnBoundary) {t : RamState}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip)
    (hCut : Cut3 s t key nonce associatedData plaintext outPtr) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Cut4 s u key nonce associatedData plaintext outPtr := by
  exact Absorb.absorb_ciphertext boundary hPre hBoundaryOutside hBoundaryDifferent hCut


end ChaCha20Poly1305.Proofs.Core
