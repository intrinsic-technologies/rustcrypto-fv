import P256.Proofs.ProjectiveWrapper.Decode.Interface
import P256.Proofs.Projective.Multiply.Machine.Lookup.Interface
import P256.Proofs.Projective.Multiply.Correct

set_option autoImplicit false

namespace P256.Proofs.Ecdh

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Standards.SECG.ECC

def frameBase (s : RamState) : BitVec 64 := stackPtr s - 2056

abbrev Frame [Bindings] (s t : RamState) :=
  ScalarFrame.FrameState s t 32 3464 2056

structure Pre [Bindings] (s : RamState) (boundary : ReturnBoundary) : Prop extends
    CalleePre s boundary 0x100000 32 32 3464 where
  peerBounded : (registerRegion s .rdx 72).Bounded
  peerAllocated : (registerRegion s .rdx 72).Allocated s.external
  peerOutput : (registerRegion s .rdx 72).Disjoint (registerRegion s .rdi 32)
  peerStack : (registerRegion s .rdx 72).Disjoint (Stack.region s 3464)

structure Initial [Bindings] (s t : RamState) (point : Curve.Point) : Prop extends Frame s t where
  rip : t.RIP = 0x10014d
  output : t.regValue .rbx = s.regValue .rdi
  scalar : memLoad t.external (frameBase s + 8) 64 = s.regValue .rsi
  base : ProjectiveAt t (frameBase s + 1784) (ProjectiveWrapper.Decode.projective point)
  first : ProjectiveAt t (frameBase s + 1016) (ProjectiveWrapper.Decode.projective point)
  r15 : t.regValue .r15 = frameBase s + 1784

structure Prepared [Bindings] (s t : RamState) (point : Curve.Point) : Prop extends Frame s t where
  rip : t.RIP = 0x1002f2
  output : t.regValue .rbx = s.regValue .rdi
  scalar : memLoad t.external (frameBase s + 8) 64 = s.regValue .rsi
  table : Projective.Multiply.Machine.Lookup.TableAt t (frameBase s + 1016)
    (Projective.table (ProjectiveWrapper.Decode.projective point))

structure Ready [Bindings] (s t : RamState) (d : Nat) (point : Curve.Point) : Prop extends Frame s t where
  rip : t.RIP = 0x10033b
  output : t.regValue .rbx = s.regValue .rdi
  destination : t.regValue .rdi = frameBase s + 152
  source : t.regValue .rsi = frameBase s + 248
  tableCount : t.regValue .rdx = 1
  digitCount : t.regValue .r8 = 1
  digits : t.regValue .rcx = frameBase s + 80
  table : Projective.Multiply.Machine.Lookup.TableAt t (frameBase s + 248)
    (Projective.table (ProjectiveWrapper.Decode.projective point))
  digitBytes : Bytes t.external (frameBase s + 80) 65
    (fun i => UInt8.ofBitVec (Projective.Multiply.ProjectiveRadix.digitByte d i))

structure Multiplied [Bindings] (s t : RamState) (point : Projective) : Prop extends Frame s t where
  rip : t.RIP = 0x100340
  output : t.regValue .rbx = s.regValue .rdi
  value : ProjectiveAt t (frameBase s + 152) point

end P256.Proofs.Ecdh
