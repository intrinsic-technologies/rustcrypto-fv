import P256.Proofs.Program.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

def word (n k : Nat) : BitVec 64 := BitVec.ofNat 64 (n / 2^(64*k))

structure StateAt (s : RamState) (address source : BitVec 64) (n k : Nat) : Prop where
  pointer : memLoad s.external address 64 = source + BitVec.ofNat 64 (8 * min (k+2) 4)
  remaining : memLoad s.external (address + 8) 64 = BitVec.ofNat 64 (8 * (4-(k+2)))
  index : memLoad s.external (address + 16) 64 = BitVec.ofNat 64 k
  low : memLoad s.external (address + 24) 64 = word n k
  high : memLoad s.external (address + 32) 64 = word n (k+1)

structure AdvancePre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (source : BitVec 64) : Prop extends CalleePre s boundary 0x1181b0 0 40 24 where
  sourceBounded : (⟨source.toNat, 32⟩ : MemoryRegion).Bounded
  sourceAllocated : (⟨source.toNat, 32⟩ : MemoryRegion).Allocated s.external
  sourceOutput : (⟨source.toNat, 32⟩ : MemoryRegion).Disjoint (registerRegion s .rdi 40)
  sourceStack : (⟨source.toNat, 32⟩ : MemoryRegion).Disjoint (Stack.region s 24)

end P256.Proofs.Verifying.Combination.Naf.Iterator
