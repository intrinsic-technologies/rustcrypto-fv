import P256.Proofs.Verifying.Message.Hash.Entry
import P256.Proofs.Verifying.Message.Hash.Long.Tail.Prepare
import P256.Proofs.Verifying.Message.Hash.Long.Tail.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Long

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (initialized : Initialized initial s boundary) (large : 64 ≤ message.size) :
    ∃ t, Buffered initial t boundary message := by
  obtain ⟨a, entered⟩ := enter pre initialized
  obtain ⟨b, prepared⟩ := prepare pre initialized entered large
  obtain ⟨c, compressed⟩ := compress pre prepared
  obtain ⟨d, ready⟩ := Tail.prepare pre compressed
  exact Tail.finish pre ready

end P256.Proofs.Verifying.Message.Hash.Long
