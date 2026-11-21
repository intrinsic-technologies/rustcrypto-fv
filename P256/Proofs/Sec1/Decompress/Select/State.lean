import P256.Proofs.Sec1.Decompress.State

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Select
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def candidateRoot (x : Nat) : Nat :=
  (P256.Spec.Operations.sqrtMod (P256.Spec.Points.curveRhs (checkedX x))).getD 0

theorem root_result {t : RamState} {address : BitVec 64} (result : Option Nat)
    (h : SquareRoot.SquareRootResultAt.match_1 (fun _ => Prop) result
      (fun r => Field.MontgomeryAt t address r ∧ t.external[address + 32]? = some 1)
      (fun _ => Field.MontgomeryAt t address 0 ∧ t.external[address + 32]? = some 0)) :
    Field.MontgomeryAt t address (result.getD 0) ∧
      t.external[address + 32]? = some (if result.isSome then 1 else 0) := by
  cases result <;> exact h

theorem root_selected (result : Option Nat) :
    (if result.isSome then result.getD 0 else 0) = result.getD 0 := by
  cases result <;> rfl

theorem root_flag (valid : Bool) :
    (if valid then 1 else 0 : BitVec 8) = BitVec.ofNat 8 valid.toNat := by
  cases valid <;> rfl

structure CandidateState [Bindings] (s t : RamState) (x : Nat) (odd : Bool) : Prop
    extends Persistent s t x odd where
  rip : t.RIP = 0x10ff77
  base : t.regValue .r12 = stackPtr s - 256
  negativeBase : t.regValue .r13 = stackPtr s - 112
  root : Field.MontgomeryAt t (stackPtr s - 256) (candidateRoot x)
  negative : Field.MontgomeryAt t (stackPtr s - 112)
    ((P256.Spec.Operations.domain.p - candidateRoot x) % P256.Spec.Operations.domain.p)
  rootValid : (t.regValue .r15).setWidth 8 = BitVec.ofNat 8
    (P256.Spec.Operations.sqrtMod (P256.Spec.Points.curveRhs (checkedX x))).isSome.toNat
  r14 : t.regValue .r14 = 0xffffffff00000001

end P256.Proofs.Sec1.Decompress.Select
