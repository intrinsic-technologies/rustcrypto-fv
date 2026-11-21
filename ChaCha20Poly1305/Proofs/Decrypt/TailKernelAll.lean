import ChaCha20Poly1305.Proofs.Decrypt.Segment
import ChaCha20Poly1305.Proofs.Decrypt.TailKernel0
import ChaCha20Poly1305.Proofs.Decrypt.TailKernel1
import ChaCha20Poly1305.Proofs.Decrypt.TailKernel2
import ChaCha20Poly1305.Proofs.Decrypt.TailKernel4
import ChaCha20Poly1305.Proofs.Decrypt.TailKernel5
import ChaCha20Poly1305.Proofs.Decrypt.TailKernel6
import ChaCha20Poly1305.Proofs.Decrypt.TailKernelRound

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Tail
open X86 X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program

theorem run (x : Input) {fr a} (h : (layout x).Rel fnCode fr (unitLoc .setup) a) :
    Ahead lifted fnCode ((layout x).Rel fnCode fr (unitLoc .store)) a := by
  apply aheadBind (segment (layout x) (j := .loads) (setupStep x) rfl h); intro _ h
  apply aheadBind (segment (layout x) (j := .save) (loadsStep x) rfl h); intro _ h
  apply aheadBind (segment (layout x) (j := .round) (saveStep x) rfl h); intro _ h
  apply aheadBind (segment (layout x) (j := .feed) (roundStep x) rfl h); intro _ h
  apply aheadBind (segment (layout x) (j := .counter) (feedStep x) rfl h); intro _ h
  exact segment (layout x) (j := .store) (counterStep x) rfl h

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Tail
