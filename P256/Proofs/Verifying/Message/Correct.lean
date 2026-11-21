import P256.Proofs.Verifying.Message.Convert.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct_of_hash_core (hash : Hash.Correct) (core : Core.Correct) : Correct := by
  intro bindings initial boundary message key r scalarS pre input valid nonidentity
    rPositive rBound sPositive sBound
  obtain ⟨initialized, initializedState⟩ := initialize_correct pre.toCalleePre
  obtain ⟨hashed, hashedState⟩ := hash pre initializedState
  obtain ⟨prepared, preparedState⟩ := Convert.correct pre input nonidentity hashedState
  exact Call.correct core pre input valid rPositive rBound sPositive sBound preparedState

end P256.Proofs.Verifying.Message
