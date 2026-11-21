import P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.Correct
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb

theorem correct : Correct := by
  intro bindings initial start s secret message pre initialized
  obtain ⟨a, entered⟩ := enter pre initialized
  by_cases short : message.size < 64
  · exact Short.correct pre entered short
  · exact Long.correct pre entered (by omega)

end P256.Proofs.Signing.Wrapper.Hash.Absorb
