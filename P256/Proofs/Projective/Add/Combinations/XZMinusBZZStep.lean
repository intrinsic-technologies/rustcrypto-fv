import P256.Proofs.Projective.Add.Combinations.XZMinusBZZ
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

theorem XZMinusBZZ_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    { x y : Nat }
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (rip : t.RIP = 0x1057bf)
    (hr14 : t.regValue .r14 = stackPtr s - 496)
    (hx : MontgomeryAt t (stackPtr s - 336) x)
    (hy : MontgomeryAt t (stackPtr s - 496) y)
    : ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x10580b ∧ MontgomeryAt u (stackPtr s - 240) (Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p x y) ∧
      (u.regValue .rbx = t.regValue .rbx ∧
       u.regValue .rbp = t.regValue .rbp ∧
       u.regValue .r12 = t.regValue .r12 ∧
       u.regValue .r13 = t.regValue .r13 ∧
       u.regValue .r14 = t.regValue .r14 ∧
       u.regValue .r15 = stackPtr s - 240) ∧
      (∀ offset value : Nat, offset ≤ 560 → 24 ≤ offset →
        (offset + 32 ≤ 240 ∨ 240 + 32 ≤ offset) →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value) := by
  obtain ⟨fuel, v, run, frame, effect, keep⟩ := setup_run pre state (offset := 0x57bf)
    (XZMinusBZZ_block boundary pre.outerBoundary) (by decide) (by decide +kernel) rip
    (by simp [XZMinusBZZEffect, Effect.components, setupComponents, stackPtr])
  have w8 : (Operand.mem (stackPtr t + 8) : Operand 64).read v = (Operand.mem (stackPtr t + 296) : Operand 64).read t := effect.writes.2.2.2.2.2.2.1
  have w16 : (Operand.mem (stackPtr t + 16) : Operand 64).read v = (Operand.mem (stackPtr t + 304) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.1
  have w24 : (Operand.mem (stackPtr t + 24) : Operand 64).read v = (Operand.mem (stackPtr t + 312) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.2.1
  have w32 : (Operand.mem (stackPtr t + 32) : Operand 64).read v = (Operand.mem (stackPtr t + 320) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.2.2
  have addr8 : stackPtr t + 8 = stackPtr s - 624 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 8) (by decide)
  have addr136 : stackPtr t + 136 = stackPtr s - 496 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 136) (by decide)
  have addr296 : stackPtr t + 296 = stackPtr s - 336 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 296) (by decide)
  have addr392 : stackPtr t + 392 = stackPtr s - 240 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 392) (by decide)
  have hxv : MontgomeryAt v (stackPtr s - 624) x := by
    rw [← addr8]
    apply copy_value (src := stackPtr t + 296)
    · simpa only [addr296] using hx
    · rw [addr8]
      exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) frame.allocated
    · exact w8
    · simp only [BitVec.add_assoc]
      exact w16
    · simp only [BitVec.add_assoc]
      exact w24
    · simp only [BitVec.add_assoc]
      exact w32
  have hyv : MontgomeryAt v (stackPtr s - 496) y := by
    exact keep 496 y (by decide) hy
  have hrdiv : v.regValue .rdi = stackPtr s - 240 := by
    exact (effect.writes.2.2.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 392) (by decide))
  have hrsiv : v.regValue .rsi = stackPtr s - 624 := by
    exact (effect.writes.2.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 8) (by decide))
  have hrdxv : v.regValue .rdx = stackPtr s - 496 := by
    exact (effect.writes.2.2.1).trans hr14
  obtain ⟨fuel', u, run', frame', rip', value, saved, bytes, _⟩ :=
    Call.binary_call pre frame Call.Sites.call_1034b6 (x := x) (y := y)
      (op := Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => by simpa only [Standards.SECG.ECC.Curve.fieldSub, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using field_subtract_correct hp hx hy)
      effect.rip hrsiv hrdxv hrdiv hxv hyv
  refine ⟨fuel + fuel', u, run.trans run', frame', rip', value, ?_, ?_⟩
  · refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
    · apply (saved .rbx (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 3) (by simp [XZMinusBZZEffect, Effect.components]))
    · apply (saved .rbp (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 5) (by simp [XZMinusBZZEffect, Effect.components]))
    · apply (saved .r12 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 12) (by simp [XZMinusBZZEffect, Effect.components]))
    · apply (saved .r13 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 13) (by simp [XZMinusBZZEffect, Effect.components]))
    · apply (saved .r14 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 14) (by simp [XZMinusBZZEffect, Effect.components]))
    · apply (saved .r15 (by decide)).trans
      exact (effect.writes.2.2.2.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 392) (by decide))
  · intro offset val bound low apart hx
    exact call_keep bytes (by omega) low apart (keep offset val bound hx)

end P256.Proofs.Projective.Add.Combinations
