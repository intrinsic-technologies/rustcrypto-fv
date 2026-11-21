import P256.Proofs.Verifying.Message.Hash.Short.Correct
import P256.Proofs.Verifying.Message.Hash.Long.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem absorb [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (initialized : Initialized initial s boundary) :
    ∃ t, Buffered initial t boundary message := by
  by_cases short : message.size < 64
  · exact Short.correct pre initialized short
  · exact Long.correct pre initialized (by omega)

end P256.Proofs.Verifying.Message.Hash
