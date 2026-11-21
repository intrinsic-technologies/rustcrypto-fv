import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.Verifying.Combination.Interface
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Interface

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Scalar
open Projective.Multiply.Machine.Basepoint (basePoint)

structure Input [Bindings] (s t : RamState) (point : Projective) (u v r : Nat) : Prop extends
    Frame s t where
  rip : t.RIP = 0x10dd69
  key : ProjectiveAt t (frameBase s+1000) point
  output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi
  scalar1 : Nat256At t (frameBase s+800) u
  scalar2 : Nat256At t (frameBase s+832) v
  savedR : Nat256At t (frameBase s+704) r

structure PrefixReady [Bindings] (s t : RamState) (point : Projective) (u v r : Nat) : Prop extends
    Frame s t where
  rip : t.RIP = 0x10ddd9
  generatorPointer : t.regValue .rax = frameBase s+576
  keyPointer : t.regValue .rdx = frameBase s
  output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi
  generator : ProjectiveAt t (frameBase s+576) basePoint
  scalar1 : Nat256At t (frameBase s+672) u
  key : ProjectiveAt t (frameBase s) point
  scalar2 : Nat256At t (frameBase s+832) v
  savedR : Nat256At t (frameBase s+704) r

structure Ready [Bindings] (s t : RamState) (point : Projective) (u v r : Nat) : Prop extends
    Frame s t where
  rip : t.RIP = 0x10de3c
  destination : t.regValue .rdi = frameBase s
  source : t.regValue .rsi = frameBase s+128
  output : memLoad t.external (frameBase s+384) 64 = s.regValue .rdi
  input : Combination.InputAt t (frameBase s+128) basePoint point u v
  savedR : Nat256At t (frameBase s+704) r

end P256.Proofs.Verifying.Core.Combine
