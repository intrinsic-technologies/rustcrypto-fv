import P256.Proofs.Signing.Wrapper.Hash.Finalize.Interface
import P256.Proofs.Signing.Wrapper.Hash.Call.Correct
import P256.Proofs.Signing.Wrapper.Hash.Output.Correct
import P256.Proofs.Signing.Wrapper.Hash.Absorb
import P256.Proofs.Signing.Wrapper.Hash.Finalize

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem hash_of_stages (absorb : Absorb.Correct) (finalize : Finalize.Correct) :
    HashContract := by
  intro core bindings initial start secret message pre
  obtain ⟨a, initialized⟩ := initialize_correct pre
  obtain ⟨b, buffered⟩ := absorb pre initialized
  obtain ⟨c, hashed⟩ := finalize pre buffered
  obtain ⟨d, prepared⟩ := Call.prepare pre hashed
  have signed := Call.run_core core pre prepared
  refine ⟨?_, signed.2⟩
  intro attempts signature found
  obtain ⟨e, result⟩ := signed.1 attempts signature found
  exact Output.correct result

theorem correct : HashContract := hash_of_stages Absorb.correct Finalize.correct

end P256.Proofs.Signing.Wrapper.Hash
