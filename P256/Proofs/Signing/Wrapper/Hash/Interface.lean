import P256.Proofs.Signing.Wrapper.Interface
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash

open P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def frameBase (s : RamState) : BitVec 64 := stackPtr s - 520

abbrev workRegion (s : RamState) := ScalarFrame.Work.region s 5112 240

structure Frame [Bindings] (initial start t : RamState) (offset : Nat := 520) : Prop
    extends State initial t offset where
  run : ∃ fuel, Advances (returnBoundary initial) fuel start t
  stackFrame : MemoryWriteFrame start t #v[workRegion initial]

end P256.Proofs.Signing.Wrapper.Hash
