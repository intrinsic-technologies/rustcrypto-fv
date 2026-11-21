import ChaCha20Poly1305.Proofs.Decrypt.PolyFinish0
import ChaCha20Poly1305.Proofs.Decrypt.PolyFinish1
import ChaCha20Poly1305.Proofs.Decrypt.PolyFinish2
import ChaCha20Poly1305.Proofs.Decrypt.PolyFinish3
import ChaCha20Poly1305.Proofs.Decrypt.PolyFinish4
import ChaCha20Poly1305.Proofs.Decrypt.PolyFinish5

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
open ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Decrypt.Lifted

theorem blocks (x : Input) : ∀ l,
    (Layout.withFrame Fn101ce0.active Fn101ce0.doneAt (core x)).BlockSimulation fnCode l
  | .s0 => step0 x
  | .s1 => step1 x
  | .s2 => step2 x
  | .s3 => step3 x
  | .s4 => step4 x
  | .s5 => step5 x

theorem executes : program.Exec Empty.semantics ⟨⟨.s0,#v[],()⟩,[]⟩ ⟨#v[],none,()⟩ :=
  .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done rfl)))))

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Finish
