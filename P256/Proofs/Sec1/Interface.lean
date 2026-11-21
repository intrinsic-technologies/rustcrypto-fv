import P256.Proofs.Field.Interface
import P256.Spec.Points

set_option autoImplicit false

namespace P256.Proofs.Sec1

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC
open P256.Proofs.Program

def AffineAt (s : RamState) (address : BitVec 64) : Curve.Point → Prop
  | .infinity =>
      Field.MontgomeryAt s address 0 ∧ Field.MontgomeryAt s (address + 32) 0 ∧
        s.external[address + 64]? = some 1
  | .affine x y =>
      Field.MontgomeryAt s address x ∧ Field.MontgomeryAt s (address + 32) y ∧
        s.external[address + 64]? = some 0

def AffineResultAt (s : RamState) (address : BitVec 64) : Option Curve.Point → Prop
  | none => s.external[address + 72]? = some 0
  | some point => AffineAt s address point ∧ s.external[address + 72]? = some 1

def PublicKeyResultAt (s : RamState) (address : BitVec 64) : Option Curve.Point → Prop
  | none => memLoad s.external address 64 = 1
  | some .infinity => False
  | some (.affine x y) => memLoad s.external address 64 = 0 ∧
      AffineAt s (address + 8) (.affine x y)

structure DecodePre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (bytes : ByteArray) : Prop extends CalleePre s boundary 0x10e4e0 bytes.size 80 3680 where
  input : (registerRegion s .rsi bytes.size).HasBytes s.external bytes
  length : s.regValue .rdx = BitVec.ofNat 64 bytes.size

end P256.Proofs.Sec1
