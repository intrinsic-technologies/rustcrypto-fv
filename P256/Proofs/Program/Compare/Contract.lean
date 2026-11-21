import P256.Proofs.Program.Interface
import P256.Proofs.Program.Call

set_option autoImplicit false

namespace P256.Proofs.Program.Compare

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ComparePre [Bindings] (s : RamState) (boundary : ReturnBoundary) (size : Nat := 39) : Prop
    extends CalleePre s boundary 0x11c860 size 0 64 where
  leftBounded : (registerRegion s .rdi size).Bounded
  leftAllocated : (registerRegion s .rdi size).Allocated s.external
  stackLeft : (Stack.region s 64).Disjoint (registerRegion s .rdi size)
  count : s.regValue .rdx = BitVec.ofNat 64 size

structure CompareResult [Bindings] (s t : RamState) (boundary : ReturnBoundary) (size : Nat := 39) : Prop
    extends CalleeResult s t boundary 0 64 where
  stackFrame : MemoryWriteFrame s t #v[Stack.region s 64]
  zero_iff : (t.regValue .rax).setWidth 32 = 0 ↔
    ∀ i < size, s.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      s.external[s.regValue .rsi + BitVec.ofNat 64 i]?

end P256.Proofs.Program.Compare
