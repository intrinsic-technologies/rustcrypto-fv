import P256.Proofs.Verifying.Message.Hash.Short.Copy
import P256.Proofs.Verifying.Message.Hash.Short.Finish

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Short

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (initialized : Initialized initial s boundary) (short : message.size < 64) :
    ∃ t, Buffered initial t boundary message := by
  obtain ⟨a, entered⟩ := enter pre initialized
  obtain ⟨b, ready⟩ := prepare pre entered short
  obtain ⟨c, copied⟩ := copy pre initialized ready short
  exact finish pre copied short

end P256.Proofs.Verifying.Message.Hash.Short
