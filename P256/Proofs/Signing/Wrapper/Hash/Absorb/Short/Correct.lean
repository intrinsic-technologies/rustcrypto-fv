import P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.Copy
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Short.Finish

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Short

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) (state : Entered initial start s message)
    (short : message.size < 64) : ∃ t, Result initial start t message := by
  obtain ⟨a, ready⟩ := prepare pre state short
  obtain ⟨b, copied⟩ := copy pre state ready short
  exact finish pre copied short

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Short
