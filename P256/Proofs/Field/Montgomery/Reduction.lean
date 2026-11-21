import P256.Proofs.Field.Montgomery.Reduction.Value
import P256.Proofs.Field.Montgomery.Reduction.Return

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery

open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem reduction_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {low high : Nat} (hpre : BinaryFieldPre s boundary 0x113c10 56)
    (hlow : Nat256At s (s.regValue .rsi) low)
    (hhigh : Nat256At s (s.regValue .rdx) high)
    (hbound : low + 2^256*high < p * 2^256) :
    ∃ t, CalleeResult s t boundary 32 56 ∧
      Nat256At t (s.regValue .rdi) (subtractP
        (reduceFour (low + 2^256*high))) := by
  obtain ⟨t, entry⟩ := Reduction.entry_correct hpre
  have pre := Reduction.body_pre hpre entry.agrees entry.rip entry.rsp
  obtain ⟨u, execution, ready, rip, frame, trace⟩ := Reduction.body_correct hpre.outerBoundary
    entry.ready (programLoaded_codeIn entry.loaded) pre
  have lowPreserved := Reduction.prologue_nat256 hpre.toCalleePre entry.agrees
    hpre.inputBounded (hpre.separation (0 : Fin 3) (2 : Fin 3) (by decide)) hlow
  have highPreserved := Reduction.prologue_nat256 hpre.toCalleePre entry.agrees
    hpre.rightBounded hpre.rightStack hhigh
  have left : (Operand.reg 6 : Operand 64).read t = s.regValue .rsi :=
    entry.agrees.read (by simp [Reduction.prologueComponents, saveFrame])
  have right : (Operand.reg 2 : Operand 64).read t = s.regValue .rdx :=
    entry.agrees.read (by simp [Reduction.prologueComponents, saveFrame])
  have lowValue : (readLimbs t ((Operand.reg 6 : Operand 64).read t)).toNat = low := by
    rw [left]
    exact readLimbs_toNat lowPreserved
  have highValue : (readLimbs t ((Operand.reg 2 : Operand 64).read t)).toNat = high := by
    rw [right]
    exact readLimbs_toNat highPreserved
  have value := Reduction.body_value trace (by rw [lowValue, highValue]; exact hbound)
  rw [lowValue, highValue] at value
  obtain ⟨final, result, output⟩ := Reduction.finish_body hpre entry execution ready rip frame
  exact ⟨final, result, value ▸ output⟩


end P256.Proofs.Field.Montgomery
