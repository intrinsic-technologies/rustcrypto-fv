import P256.Proofs.Field.Subtract.Return

set_option autoImplicit false

namespace P256.Proofs.Field

open P256.Proofs.Program
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem field_subtract_body_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {x y : Nat} (pre : BinaryFieldPre s boundary 0x113f20 24)
    (left : MontgomeryAt s (s.regValue .rsi) x)
    (right : MontgomeryAt s (s.regValue .rdx) y) :
    ∃ t, CalleeResult s t boundary 32 24 ∧
      MontgomeryAt t (s.regValue .rdi) ((x+Operations.domain.p-y) % Operations.domain.p) := by
  obtain ⟨t, entry⟩ := Subtract.entry_correct pre
  have bp := Subtract.body_pre pre entry.agrees entry.rip entry.rsp
  obtain ⟨u, execution, ready, _, rip, frame, trace⟩ :=
    Subtract.body_correct pre.outerBoundary entry.ready entry.loaded bp
  have lp := Subtract.prologue_nat256 pre.toCalleePre entry.agrees pre.inputBounded
    (pre.separation (0 : Fin 3) (2 : Fin 3) (by decide)) left.2
  have rp := Subtract.prologue_nat256 pre.toCalleePre entry.agrees pre.rightBounded pre.rightStack right.2
  have lreg : t.regValue .rsi = s.regValue .rsi :=
    entry.agrees.read (n := 64) (r := 6) (by simp [Subtract.prologueComponents])
  have rreg : t.regValue .rdx = s.regValue .rdx :=
    entry.agrees.read (n := 64) (r := 2) (by simp [Subtract.prologueComponents])
  have lv : (readLimbs t (t.regValue .rsi)).toNat = x*2^256 % Operations.domain.p := by
    rw [lreg]
    exact readLimbs_toNat lp
  have rv : (readLimbs t (t.regValue .rdx)).toNat = y*2^256 % Operations.domain.p := by
    rw [rreg]
    exact readLimbs_toNat rp
  obtain ⟨final, result, output⟩ := Subtract.finish_body pre entry execution ready rip frame
  have value := Subtract.subLimbs_montgomery _ _ x y right.1 lv rv
  rw [Subtract.body_value trace, value] at output
  exact ⟨final, result, Nat.mod_lt _ Montgomery.p_pos, output⟩

end P256.Proofs.Field
