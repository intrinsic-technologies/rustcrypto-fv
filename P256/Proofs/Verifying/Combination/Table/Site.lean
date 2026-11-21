import P256.Proofs.Verifying.Combination.Table.AddSetup
import P256.Proofs.Verifying.Combination.Table.Registers
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Site

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Projective.Multiply.Machine.Loop (CallSite)

structure AddSite where
  offset : Nat
  bounded : offset + 6 < 118431
  bytes : Extracted.textBytes.toListFrom offset 6 = addSetupBytes
  call : CallSite 0x1051f0
  callOffset : call.offset = offset + 6

def copySetupEffect (slot : Slot) (endOffset : Nat) (s : RamState) : Effect :=
  { rip := Extracted.textAddress + BitVec.ofNat 64 endOffset
    writes := [⟨(Operand.reg 7 : Operand 64), stackPtr s + BitVec.ofNat 64 (1096-offset slot)⟩,
      ⟨(Operand.reg 1 : Operand 64), 12⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .r14⟩] }

structure CopySite (slot : Slot) where
  startOffset : Nat
  bytes : List UInt8
  bounded : startOffset + bytes.length ≤ 118431
  extracted : Extracted.textBytes.toListFrom startOffset bytes.length = bytes
  endOffset : Nat
  copyBound : endOffset + 3 < 118431
  copyBytes : Extracted.textBytes.toListFrom endOffset 3 = [0xf3,0x48,0xa5]
  correct : ∀ [Bindings] (boundary : ReturnBoundary), ¬ InProgram boundary.rip →
    AdvanceTriple boundary (fun s => s.RIP = Extracted.textAddress + BitVec.ofNat 64 startOffset)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 startOffset) bytes)
      (Effect.post (copySetupEffect slot endOffset))

end P256.Proofs.Verifying.Combination.Table
