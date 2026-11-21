import P256.Proofs.Sec1.Affine.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

def xCoordinate (bytes : ByteArray) : Nat := Encoding.octetsToNat (bytes.extract 1 33)

def yCoordinate (bytes : ByteArray) : Nat := Encoding.octetsToNat (bytes.extract 33 65)

def canonical (x : Nat) : Nat := if x < Operations.domain.p then x else 0

def valid (bytes : ByteArray) : Bool :=
  Curve.onCurve Operations.domain (.affine (xCoordinate bytes) (yCoordinate bytes))

structure Parsed [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x1109fa
  output : t.regValue .rbx = s.regValue .rdi
  xPointer : t.regValue .r13 = stackPtr s - 280
  yPointer : t.regValue .r14 = stackPtr s - 312
  xValid : t.regValue .r15 = if xCoordinate bytes < Operations.domain.p then 1 else 0
  yValid : t.external[stackPtr s - 748]? =
    some (if yCoordinate bytes < Operations.domain.p then 1 else 0)
  xValue : Field.MontgomeryAt t (stackPtr s - 280) (canonical (xCoordinate bytes))
  yValue : Field.MontgomeryAt t (stackPtr s - 312) (canonical (yCoordinate bytes))

structure Validated [Bindings] (s t : RamState) (bytes : ByteArray) : Prop extends Frame s t where
  rip : t.RIP = 0x110bfc
  output : t.regValue .rbx = s.regValue .rdi
  result : (Operand.reg 0 : Operand 8).read t = if valid bytes then 1 else 0
  xValue : Field.MontgomeryAt t (stackPtr s - 248) (canonical (xCoordinate bytes))
  yValue : Field.MontgomeryAt t (stackPtr s - 216) (canonical (yCoordinate bytes))

end P256.Proofs.Sec1.Affine.Uncompressed
