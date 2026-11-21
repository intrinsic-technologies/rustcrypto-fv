import ChaCha20Poly1305.Proofs.Decrypt.PolyMul0
import ChaCha20Poly1305.Proofs.Decrypt.PolyMul1
import ChaCha20Poly1305.Proofs.Decrypt.PolyMul2
import ChaCha20Poly1305.Proofs.Decrypt.PolyMul3
import ChaCha20Poly1305.Proofs.Decrypt.PolyMul4
import ChaCha20Poly1305.Proofs.Decrypt.PolyMul5
import ChaCha20Poly1305.Proofs.Decrypt.PolyMul6
import ChaCha20Poly1305.Proofs.Decrypt.PolyMul7
import ChaCha20Poly1305.Proofs.Decrypt.PolyMul8

namespace ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
open ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.Decrypt.Lifted

theorem blocks (x : Input) : ∀ l,
    (Layout.withFrame Fn101e30.active Fn101e30.doneAt (core x)).BlockSimulation fnCode l
  | .s0 => step0 x
  | .s1 => step1 x
  | .s2 => step2 x
  | .s3 => step3 x
  | .s4 => step4 x
  | .s5 => step5 x
  | .s6 => step6 x
  | .s7 => step7 x
  | .s8 => step8 x

theorem executes : program.Exec Empty.semantics ⟨⟨.s0,#v[],()⟩,[]⟩ ⟨#v[],none,()⟩ :=
  .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.done rfl))))))))

end ChaCha20Poly1305.Proofs.Decrypt.Poly1305.Mul
