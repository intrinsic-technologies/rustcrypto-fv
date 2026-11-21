import P256.Proofs.Projective.Add.Combinations.BXZMinus
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

theorem BXZMinus_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    { x y : Nat }
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (rip : t.RIP = 0x105a16)
    (hr13 : t.regValue .r13 = stackPtr s - 80)
    (hr12 : t.regValue .r12 = stackPtr s - 496)
    (hx : MontgomeryAt t (stackPtr s - 80) x)
    (hy : MontgomeryAt t (stackPtr s - 496) y)
    : ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x105a2c ∧ MontgomeryAt u (stackPtr s - 144) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p x y) ∧
      (u.regValue .rbx = t.regValue .rbx ∧
       u.regValue .rbp = t.regValue .rbp ∧
       u.regValue .r12 = t.regValue .r12 ∧
       u.regValue .r13 = t.regValue .r13 ∧
       u.regValue .r14 = stackPtr s - 144 ∧
       u.regValue .r15 = t.regValue .r15) ∧
      (∀ offset value : Nat, offset ≤ 560 → 24 ≤ offset →
        (offset + 32 ≤ 144 ∨ 144 + 32 ≤ offset) →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value) := by
  obtain ⟨fuel, v, run, frame, effect, keep⟩ := setup_run pre state (offset := 0x5a16)
    (BXZMinus_block boundary pre.outerBoundary) (by decide) (by decide +kernel) rip
    (by simp [BXZMinusEffect, Effect.components, setupComponents, stackPtr])
  have addr136 : stackPtr t + 136 = stackPtr s - 496 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 136) (by decide)
  have addr488 : stackPtr t + 488 = stackPtr s - 144 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 488) (by decide)
  have addr552 : stackPtr t + 552 = stackPtr s - 80 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 552) (by decide)
  have hxv : MontgomeryAt v (stackPtr s - 80) x := by
    exact keep 80 x (by decide) hx
  have hyv : MontgomeryAt v (stackPtr s - 496) y := by
    exact keep 496 y (by decide) hy
  have hrdiv : v.regValue .rdi = stackPtr s - 144 := by
    exact (effect.writes.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 488) (by decide))
  have hrsiv : v.regValue .rsi = stackPtr s - 80 := by
    exact (effect.writes.2.1).trans hr13
  have hrdxv : v.regValue .rdx = stackPtr s - 496 := by
    exact (effect.writes.1).trans hr12
  obtain ⟨fuel', u, run', frame', rip', value, saved, bytes, _⟩ :=
    Call.binary_call pre frame Call.Sites.call_1036d7 (x := x) (y := y)
      (op := Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => by simpa only [Standards.SECG.ECC.Curve.fieldSub, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using field_subtract_correct hp hx hy)
      effect.rip hrsiv hrdxv hrdiv hxv hyv
  refine ⟨fuel + fuel', u, run.trans run', frame', rip', value, ?_, ?_⟩
  · refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
    · apply (saved .rbx (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 3) (by simp [BXZMinusEffect, Effect.components]))
    · apply (saved .rbp (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 5) (by simp [BXZMinusEffect, Effect.components]))
    · apply (saved .r12 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 12) (by simp [BXZMinusEffect, Effect.components]))
    · apply (saved .r13 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 13) (by simp [BXZMinusEffect, Effect.components]))
    · apply (saved .r14 (by decide)).trans
      exact (effect.writes.2.2.2).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 488) (by decide))
    · apply (saved .r15 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 15) (by simp [BXZMinusEffect, Effect.components]))
  · intro offset val bound low apart hx
    exact call_keep bytes (by omega) low apart (keep offset val bound hx)

end P256.Proofs.Projective.Add.Combinations
