import P256.Proofs.Projective.Add.Combinations.XXMinus
import P256.Proofs.Projective.Add.Combinations.Payload
import P256.Proofs.Field.Add
import P256.Proofs.Field.Subtract
import P256.Proofs.Field.Double
import P256.Proofs.Field.Montgomery
import P256.Proofs.Projective.Add.Call.Sites
import P256.Proofs.Projective.Add.Call.Unary

set_option autoImplicit false


namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem XXMinus_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    { x y : Nat }
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (rip : t.RIP = 0x105ada)
    (hr15 : t.regValue .r15 = stackPtr s - 496)
    (hrbp : t.regValue .rbp = stackPtr s - 176)
    (hx : MontgomeryAt t (stackPtr s - 496) x)
    (hy : MontgomeryAt t (stackPtr s - 176) y)
    : ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x105af0 ∧ MontgomeryAt u (stackPtr s - 432) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p x y) ∧
      (u.regValue .rbx = t.regValue .rbx ∧
       u.regValue .rbp = t.regValue .rbp ∧
       u.regValue .r12 = t.regValue .r12 ∧
       u.regValue .r13 = stackPtr s - 432 ∧
       u.regValue .r14 = t.regValue .r14 ∧
       u.regValue .r15 = t.regValue .r15) ∧
      (∀ offset value : Nat, offset ≤ 560 → 24 ≤ offset →
        (offset + 32 ≤ 432 ∨ 432 + 32 ≤ offset) →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value) := by
  obtain ⟨fuel, v, run, frame, effect, keep⟩ := setup_run pre state (offset := 0x5ada)
    (XXMinus_block boundary pre.outerBoundary) (by decide) (by decide +kernel) rip
    (by simp [XXMinusEffect, Effect.components, setupComponents, stackPtr])
  have addr136 : stackPtr t + 136 = stackPtr s - 496 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 136) (by decide)
  have addr200 : stackPtr t + 200 = stackPtr s - 432 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 200) (by decide)
  have addr456 : stackPtr t + 456 = stackPtr s - 176 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 456) (by decide)
  have hxv : MontgomeryAt v (stackPtr s - 496) x := by
    exact keep 496 x (by decide) hx
  have hyv : MontgomeryAt v (stackPtr s - 176) y := by
    exact keep 176 y (by decide) hy
  have hrdiv : v.regValue .rdi = stackPtr s - 432 := by
    exact (effect.writes.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 200) (by decide))
  have hrsiv : v.regValue .rsi = stackPtr s - 496 := by
    exact (effect.writes.2.1).trans hr15
  have hrdxv : v.regValue .rdx = stackPtr s - 176 := by
    exact (effect.writes.1).trans hrbp
  obtain ⟨fuel', u, run', frame', rip', value, saved, bytes, _⟩ :=
    Call.binary_call pre frame Call.Sites.call_10379b (x := x) (y := y)
      (op := Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => by simpa only [Standards.SECG.ECC.Curve.fieldSub, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using field_subtract_correct hp hx hy)
      effect.rip hrsiv hrdxv hrdiv hxv hyv
  refine ⟨fuel + fuel', u, run.trans run', frame', rip', value, ?_, ?_⟩
  · refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
    · apply (saved .rbx (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 3) (by simp [XXMinusEffect, Effect.components]))
    · apply (saved .rbp (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 5) (by simp [XXMinusEffect, Effect.components]))
    · apply (saved .r12 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 12) (by simp [XXMinusEffect, Effect.components]))
    · apply (saved .r13 (by decide)).trans
      exact (effect.writes.2.2.2).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 200) (by decide))
    · apply (saved .r14 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 14) (by simp [XXMinusEffect, Effect.components]))
    · apply (saved .r15 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 15) (by simp [XXMinusEffect, Effect.components]))
  · intro offset val bound low apart hx
    exact call_keep bytes (by omega) low apart (keep offset val bound hx)

end P256.Proofs.Projective.Add.Combinations
