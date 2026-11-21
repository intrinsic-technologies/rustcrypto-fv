import P256.Proofs.Signing.Core.State
import P256.Proofs.Sec1.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC

def LiveOffset (offset : Nat) : Prop :=
  (72 ≤ offset ∧ offset < 104) ∨
    (272 ≤ offset ∧ offset < 368) ∨ (1296 ≤ offset ∧ offset < 1328) ∨
    (2160 ≤ offset ∧ offset < 2232)

def Preserved (s t u : RamState) : Prop :=
  ∀ offset, LiveOffset offset →
    u.external[frameBase s + BitVec.ofNat 64 offset]? =
      t.external[frameBase s + BitVec.ofNat 64 offset]?

structure Input [Bindings] (s t : RamState) (nonce : Nat) : Prop where
  frame : Frame s t
  scalar : Nat256At t (frameBase s + 304) nonce
  positive : 0 < nonce
  canonical : nonce < Operations.domain.n
  rbp : t.regValue .rbp = frameBase s + 528
  r13 : t.regValue .r13 = frameBase s + 432
  rbx : t.regValue .rbx = frameBase s + 304
  r15 : t.regValue .r15 = frameBase s + 1328

structure Encoded [Bindings] (s t : RamState) (x y : Nat) : Prop where
  frame : Frame s t
  point : Sec1.AffineAt t (frameBase s + 104) (.affine x y)
  encoded : (MemoryRegion.mk (frameBase s + 432).toNat 32).HasBytes
    t.external (Encoding.natToOctets 32 x)
  rbp : t.regValue .rbp = frameBase s + 528
  r13 : t.regValue .r13 = frameBase s + 432
  r15 : t.regValue .r15 = frameBase s + 1328

def Contract : Prop :=
  ∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary} {nonce : Nat},
    SignPre s boundary → Input s t nonce → t.RIP = 0x10cd5b →
    ∃ fuel u x y, Advances boundary fuel t u ∧ u.RIP = 0x10d19f ∧
      Curve.scalarMul Operations.domain nonce Operations.domain.G = .affine x y ∧
      Encoded s u x y ∧ Preserved s t u

end P256.Proofs.Signing.Core.Iteration.Point
