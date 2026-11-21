import P256.Proofs.Signing.Wrapper.Hash.Enter
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Prepare
import P256.Proofs.Signing.Wrapper.Hash.Absorb.Long.Tail.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Absorb.Long

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (entered : Entered initial start s message) (large : 64 ≤ message.size) :
    ∃ t, Result initial start t message := by
  obtain ⟨b, prepared⟩ := prepare pre entered large
  obtain ⟨c, compressed⟩ := compress pre prepared
  obtain ⟨d, ready⟩ := Tail.prepare pre compressed
  exact Tail.finish pre ready

end P256.Proofs.Signing.Wrapper.Hash.Absorb.Long
