import P256.Proofs.Projective.Add.Combinations.YYPlus
import P256.Proofs.Projective.Add.Combinations.Payload
import P256.Proofs.Field.Add
import P256.Proofs.Field.Subtract
import P256.Proofs.Field.Double
import P256.Proofs.Field.Montgomery
import P256.Proofs.Projective.Add.Call.Sites
import P256.Proofs.Projective.Add.Call.Unary

set_option autoImplicit false

open P256.Proofs.Field (field_add_correct)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem YYPlus_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    { x y : Nat }
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (rip : t.RIP = 0x1058e6)
    (hr13 : t.regValue .r13 = stackPtr s - 208)
    (hx : MontgomeryAt t (stackPtr s - 464) x)
    (hy : MontgomeryAt t (stackPtr s - 208) y)
    : ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x1058fe ∧ MontgomeryAt u (stackPtr s - 272) ((x + y) % P256.Spec.Operations.domain.p) ∧
      (u.regValue .rbx = t.regValue .rbx ∧
       u.regValue .rbp = t.regValue .rbp ∧
       u.regValue .r12 = t.regValue .r12 ∧
       u.regValue .r13 = t.regValue .r13 ∧
       u.regValue .r14 = t.regValue .r14 ∧
       u.regValue .r15 = t.regValue .r15) ∧
      (∀ offset value : Nat, offset ≤ 560 → 24 ≤ offset →
        (offset + 32 ≤ 272 ∨ 272 + 32 ≤ offset) →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value) := by
  obtain ⟨fuel, v, run, frame, effect, keep⟩ := setup_run pre state (offset := 0x58e6)
    (YYPlus_block boundary pre.outerBoundary) (by decide) (by decide +kernel) rip
    (by simp [YYPlusEffect, Effect.components, setupComponents, stackPtr])
  have addr168 : stackPtr t + 168 = stackPtr s - 464 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 168) (by decide)
  have addr360 : stackPtr t + 360 = stackPtr s - 272 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 360) (by decide)
  have addr424 : stackPtr t + 424 = stackPtr s - 208 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 424) (by decide)
  have hxv : MontgomeryAt v (stackPtr s - 464) x := by
    exact keep 464 x (by decide) hx
  have hyv : MontgomeryAt v (stackPtr s - 208) y := by
    exact keep 208 y (by decide) hy
  have hrdiv : v.regValue .rdi = stackPtr s - 272 := by
    exact (effect.writes.2.2).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 360) (by decide))
  have hrsiv : v.regValue .rsi = stackPtr s - 464 := by
    exact (effect.writes.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 168) (by decide))
  have hrdxv : v.regValue .rdx = stackPtr s - 208 := by
    exact (effect.writes.1).trans hr13
  obtain ⟨fuel', u, run', frame', rip', value, saved, bytes, _⟩ :=
    Call.binary_call pre frame Call.Sites.call_1035a9 (x := x) (y := y)
      (op := fun a b => (a + b) % P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_add_correct hp hx hy)
      effect.rip hrsiv hrdxv hrdiv hxv hyv
  refine ⟨fuel + fuel', u, run.trans run', frame', rip', value, ?_, ?_⟩
  · refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
    · apply (saved .rbx (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 3) (by simp [YYPlusEffect, Effect.components]))
    · apply (saved .rbp (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 5) (by simp [YYPlusEffect, Effect.components]))
    · apply (saved .r12 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 12) (by simp [YYPlusEffect, Effect.components]))
    · apply (saved .r13 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 13) (by simp [YYPlusEffect, Effect.components]))
    · apply (saved .r14 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 14) (by simp [YYPlusEffect, Effect.components]))
    · apply (saved .r15 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 15) (by simp [YYPlusEffect, Effect.components]))
  · intro offset val bound low apart hx
    exact call_keep bytes (by omega) low apart (keep offset val bound hx)

end P256.Proofs.Projective.Add.Combinations
