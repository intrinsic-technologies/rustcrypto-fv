import ChaCha20Poly1305.Proofs.Decrypt.ShortEntry
import ChaCha20Poly1305.Proofs.Decrypt.ShortShim
import ChaCha20Poly1305.Proofs.Decrypt.ShortAlloc
import ChaCha20Poly1305.Proofs.Decrypt.ShortCopy
import ChaCha20Poly1305.Proofs.Decrypt.ShortFinish

namespace ChaCha20Poly1305.Proofs.Decrypt.Short

open ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Decrypt.Lifted

theorem blocks (e : Env) (hg : Geometry e) :
    ∀ l, (Layout.withFrame frameAt Decrypt.doneAt (core e)).BlockSimulation fnCode l
  | .entry => entryBlock e hg
  | .shim => shimBlock e hg
  | .alloc => allocBlock e hg
  | .copy => copyBlock e hg
  | .finish => finishBlock e hg

end ChaCha20Poly1305.Proofs.Decrypt.Short
