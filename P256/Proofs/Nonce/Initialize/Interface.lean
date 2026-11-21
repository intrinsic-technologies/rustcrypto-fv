import P256.Proofs.Nonce.Interface

set_option autoImplicit false

namespace P256.Proofs.Nonce

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

structure InitializePre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (orderAddress : BitVec 64) : Prop extends CalleePre s boundary 0x107790 32 72 2144 where
  secretLength : s.regValue .rdx = 32
  digestLength : s.regValue .r8 = 32
  entropyPointer : s.regValue .r9 = 1
  digestBounded : (registerRegion s .rcx 32).Bounded
  digestAllocated : (registerRegion s .rcx 32).Allocated s.external
  digestOutput : (registerRegion s .rcx 32).Disjoint (registerRegion s .rdi 72)
  digestStack : (registerRegion s .rcx 32).Disjoint (Stack.region s 2144)
  orderBounded : ({ start := orderAddress.toNat, size := 32 } : MemoryRegion).Bounded
  orderAllocated : ({ start := orderAddress.toNat, size := 32 } : MemoryRegion).Allocated s.external
  orderOutput : ({ start := orderAddress.toNat, size := 32 } : MemoryRegion).Disjoint
    (registerRegion s .rdi 72)
  orderStack : ({ start := orderAddress.toNat, size := 32 } : MemoryRegion).Disjoint
    (Stack.region s 2144)
  argumentsBounded : ({ start := (s.regValue .rsp + 8).toNat, size := 16 } : MemoryRegion).Bounded
  argumentsAllocated : ({ start := (s.regValue .rsp + 8).toNat, size := 16 } : MemoryRegion).Allocated
    s.external
  argumentsOutput : ({ start := (s.regValue .rsp + 8).toNat, size := 16 } : MemoryRegion).Disjoint
    (registerRegion s .rdi 72)
  entropyLength : loadBytes s.external (s.regValue .rsp + 8) 8 = .ok (0 : BitVec 64)
  orderPointer : loadBytes s.external (s.regValue .rsp + 16) 8 = .ok orderAddress
  order : Nat256At s orderAddress P256.Spec.Operations.domain.n

end P256.Proofs.Nonce
