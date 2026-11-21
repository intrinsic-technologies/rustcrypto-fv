import ChaCha20Poly1305.Proofs.Decrypt.Segment
import ChaCha20Poly1305.Proofs.Decrypt.FullKernel0
import ChaCha20Poly1305.Proofs.Decrypt.FullKernel2
import ChaCha20Poly1305.Proofs.Decrypt.FullKernel3
import ChaCha20Poly1305.Proofs.Decrypt.FullKernelRound

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Full
open X86 X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

theorem run (x : Input) (j : BitVec 64) {fr a} (h : (layout x j).Rel fnCode fr (unitLoc .setup) a) :
    Ahead lifted fnCode ((layout x j).Rel fnCode fr (unitLoc .finished)) a := by
  apply aheadBind (segment (layout x j) (j := .round) (setupStep x j) rfl h); intro _ h
  apply aheadBind (segment (layout x j) (j := .feed) (roundStep x j) rfl h); intro _ h
  apply aheadBind (segment (layout x j) (j := .second) (feedStep x j) rfl h); intro _ h
  exact segment (layout x j) (j := .finished) (secondStep x j) rfl h

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Full
