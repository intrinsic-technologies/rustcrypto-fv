import P256.Proofs.Signing.Core.Iteration.Point.Interface

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)
open Standards.SECG.ECC

structure ComponentsInput [Bindings] (s t : RamState) (state : Nonce.State)
    (nonce x y : Nat) (digest : ByteArray) : Prop where
  encoded : Point.Encoded s t x y
  arguments : StoredArguments s t
  generator : Nonce.GeneratorAt t (frameBase s + 2160) (frameBase s + 272) state
  inverse : Nat256At t (frameBase s + 336) (Curve.inverse Operations.domain.n nonce)
  digest : Nat256At t (frameBase s + 1296) (Arith.uint digest % Operations.domain.n)
  positive : 0 < nonce
  canonical : nonce < Operations.domain.n
  affine : Curve.scalarMul Operations.domain nonce Operations.domain.G = .affine x y

structure Computed [Bindings] (s t : RamState) (state : Nonce.State)
    (secret nonce : Nat) (digest : ByteArray) (x y : Nat) : Prop where
  frame : Frame s t
  arguments : StoredArguments s t
  generator : Nonce.GeneratorAt t (frameBase s + 2160) (frameBase s + 272) state
  point : Sec1.AffineAt t (frameBase s + 104) (.affine x y)
  reducedX : Nat256At t (frameBase s + 176) (x % Operations.domain.n)
  rbp : t.regValue .rbp = frameBase s + 528
  r13 : t.regValue .r13 = frameBase s + 432
  r14 : t.regValue .r14 = frameBase s + 2160
  r15 : t.regValue .r15 = frameBase s + 1328
  decision :
    (Ecdsa.signWithNonce secret nonce digest = none ∧
      memLoad t.external (frameBase s + 528) 64 = 1 ∧
      memLoad t.external (frameBase s + 536) 64 = 0) ∨
    (∃ signature, Ecdsa.signWithNonce secret nonce digest = some signature ∧
      memLoad t.external (frameBase s + 528) 64 = 0 ∧
      Nat256At t (frameBase s + 536) signature.1 ∧
      Nat256At t (frameBase s + 568) signature.2)

def ComponentsContract : Prop :=
  ∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    {secret nonce x y : Nat} {digest : ByteArray},
    SignPre s boundary → SignInput s secret digest →
    ComponentsInput s t state nonce x y digest → t.RIP = 0x10d19f →
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d33e ∧
      Computed s u state secret nonce digest x y

def OutputContract : Prop :=
  ∀ [Bindings] {s t : RamState} {boundary : ReturnBoundary} {state : Nonce.State}
    {secret nonce x y : Nat} {digest : ByteArray},
    SignPre s boundary → Computed s t state secret nonce digest x y → t.RIP = 0x10d33e →
    (∃ fuel, Advances boundary fuel s t) →
    ∃ fuel u, Advances boundary fuel t u ∧
      ((Ecdsa.signWithNonce secret nonce digest = none ∧ u.RIP = 0x10caa5 ∧ Loop s u state) ∨
        ∃ signature, Ecdsa.signWithNonce secret nonce digest = some signature ∧
          CalleeResult s u boundary 65 4584 ∧
          Nat256At u (s.regValue .rdi) signature.1 ∧
          Nat256At u (s.regValue .rdi + 32) signature.2)

end P256.Proofs.Signing.Core.Iteration
