import P256.Proofs.Projective.Add.Combinations.ZZ3PlusXX
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

theorem ZZ3PlusXX_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    { x y : Nat }
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (rip : t.RIP = 0x1059a0)
    (hx : MontgomeryAt t (stackPtr s - 176) x)
    (hy : MontgomeryAt t (stackPtr s - 560) y)
    : ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x105a16 ∧ MontgomeryAt u (stackPtr s - 496) ((x + y) % P256.Spec.Operations.domain.p) ∧
      (u.regValue .rbx = t.regValue .rbx ∧
       u.regValue .rbp = t.regValue .rbp ∧
       u.regValue .r12 = stackPtr s - 496 ∧
       u.regValue .r13 = t.regValue .r13 ∧
       u.regValue .r14 = t.regValue .r14 ∧
       u.regValue .r15 = t.regValue .r15) ∧
      (∀ offset value : Nat, offset ≤ 560 → 24 ≤ offset →
        (offset + 32 ≤ 496 ∨ 496 + 32 ≤ offset) →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value) := by
  obtain ⟨fuel, v, run, frame, effect, keep⟩ := setup_run pre state (offset := 0x59a0)
    (ZZ3PlusXX_block boundary pre.outerBoundary) (by decide) (by decide +kernel) rip
    (by simp [ZZ3PlusXXEffect, Effect.components, setupComponents, stackPtr])
  have w8 : (Operand.mem (stackPtr t + 8) : Operand 64).read v = (Operand.mem (stackPtr t + 456) : Operand 64).read t := effect.writes.2.2.2.2.2.2.1
  have w16 : (Operand.mem (stackPtr t + 16) : Operand 64).read v = (Operand.mem (stackPtr t + 464) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.1
  have w24 : (Operand.mem (stackPtr t + 24) : Operand 64).read v = (Operand.mem (stackPtr t + 472) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.2.1
  have w32 : (Operand.mem (stackPtr t + 32) : Operand 64).read v = (Operand.mem (stackPtr t + 480) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.2.2.1
  have w40 : (Operand.mem (stackPtr t + 40) : Operand 64).read v = (Operand.mem (stackPtr t + 72) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.2.2.2.1
  have w48 : (Operand.mem (stackPtr t + 48) : Operand 64).read v = (Operand.mem (stackPtr t + 80) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.2.2.2.2.1
  have w56 : (Operand.mem (stackPtr t + 56) : Operand 64).read v = (Operand.mem (stackPtr t + 88) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.1
  have w64 : (Operand.mem (stackPtr t + 64) : Operand 64).read v = (Operand.mem (stackPtr t + 96) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.2.2.2.2.2.2
  have addr8 : stackPtr t + 8 = stackPtr s - 624 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 8) (by decide)
  have addr40 : stackPtr t + 40 = stackPtr s - 592 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 40) (by decide)
  have addr72 : stackPtr t + 72 = stackPtr s - 560 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 72) (by decide)
  have addr136 : stackPtr t + 136 = stackPtr s - 496 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 136) (by decide)
  have addr456 : stackPtr t + 456 = stackPtr s - 176 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 456) (by decide)
  have hxv : MontgomeryAt v (stackPtr s - 624) x := by
    rw [← addr8]
    apply copy_value (src := stackPtr t + 456)
    · simpa only [addr456] using hx
    · rw [addr8]
      exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) frame.allocated
    · exact w8
    · simp only [BitVec.add_assoc]
      exact w16
    · simp only [BitVec.add_assoc]
      exact w24
    · simp only [BitVec.add_assoc]
      exact w32
  have hyv : MontgomeryAt v (stackPtr s - 592) y := by
    rw [← addr40]
    apply copy_value (src := stackPtr t + 72)
    · simpa only [addr72] using hy
    · rw [addr40]
      exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) frame.allocated
    · exact w40
    · simp only [BitVec.add_assoc]
      exact w48
    · simp only [BitVec.add_assoc]
      exact w56
    · simp only [BitVec.add_assoc]
      exact w64
  have hrdiv : v.regValue .rdi = stackPtr s - 496 := by
    exact (effect.writes.2.2.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 136) (by decide))
  have hrsiv : v.regValue .rsi = stackPtr s - 624 := by
    exact (effect.writes.2.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 8) (by decide))
  have hrdxv : v.regValue .rdx = stackPtr s - 592 := by
    exact (effect.writes.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 40) (by decide))
  obtain ⟨fuel', u, run', frame', rip', value, saved, bytes, _⟩ :=
    Call.binary_call pre frame Call.Sites.call_1036c1 (x := x) (y := y)
      (op := fun a b => (a + b) % P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_add_correct hp hx hy)
      effect.rip hrsiv hrdxv hrdiv hxv hyv
  refine ⟨fuel + fuel', u, run.trans run', frame', rip', value, ?_, ?_⟩
  · refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
    · apply (saved .rbx (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 3) (by simp [ZZ3PlusXXEffect, Effect.components]))
    · apply (saved .rbp (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 5) (by simp [ZZ3PlusXXEffect, Effect.components]))
    · apply (saved .r12 (by decide)).trans
      exact (effect.writes.2.2.2.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 136) (by decide))
    · apply (saved .r13 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 13) (by simp [ZZ3PlusXXEffect, Effect.components]))
    · apply (saved .r14 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 14) (by simp [ZZ3PlusXXEffect, Effect.components]))
    · apply (saved .r15 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 15) (by simp [ZZ3PlusXXEffect, Effect.components]))
  · intro offset val bound low apart hx
    exact call_keep bytes (by omega) low apart (keep offset val bound hx)

end P256.Proofs.Projective.Add.Combinations
