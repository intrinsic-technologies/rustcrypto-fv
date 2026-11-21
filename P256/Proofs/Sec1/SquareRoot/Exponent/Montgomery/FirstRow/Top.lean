import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstRow.Frame
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.States

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem firstTop_values {p : BitVec 64} {s t : RamState} {c0 c1 a b next : BitVec 64}
    (effect : (firstTopEffect p s).Holds s t)
    (low : (Operand.reg 15#5 : Operand 64).read s = c0)
    (high : (Operand.reg 9#5 : Operand 64).read s = c1)
    (xlo : (Operand.reg 8#5 : Operand 64).read s = (product64 a b).1)
    (xhi : (Operand.reg 1#5 : Operand 64).read s = (product64 a b).2)
    (digit : (Operand.reg 11#5 : Operand 64).read s = b)
    (input : (Operand.mem ((Operand.mem (stackPtr s+24#64) : Operand 64).read s+8#64) : Operand 64).read s = next) :
    (Operand.reg 14#5 : Operand 64).read t = next ∧
    (Operand.reg 15#5 : Operand 64).read t = (firstTop c0 c1 a b next).low ∧
    (Operand.reg 9#5 : Operand 64).read t = (firstTop c0 c1 a b next).mid ∧
    (Operand.mem (stackPtr t+104#64) : Operand 64).read t = (firstTop c0 c1 a b next).high ∧
    (Operand.mem (stackPtr t+7#64) : Operand 8).read t =
      BitVec.ofNat 8 (firstTop c0 c1 a b next).carry.toNat := by
  have read {n : Nat} (op : Operand n) : op.read t = op.read ((firstTopEffect p s).after s true) :=
    P256.Proofs.Common.EffectCompose.Effect.Holds.read_after effect
      (by simp [firstTopEffect, Write.Full, Operand.Full])
      (by simp [firstTopEffect, Effect.components, Write.component, Operand.component]) op
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals try rw [Reduction.scratch_rsp (firstTop_frame effect)]
  all_goals rw [read]
  all_goals x86_norm [firstTopEffect, Rows.stackPtr_read]
  all_goals simp only [← Rows.stackPtr_read, low, high, xlo, xhi, digit, input]
  all_goals simp only [firstTop, add64, adc64, product64]
  all_goals first | rfl | exact Rows.boolByte_eq _

end P256.Proofs.Sec1.SquareRoot.Montgomery
