import P256.Proofs.Projective.Add.Combinations.ZZ3
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

theorem ZZ3_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    { x y : Nat }
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (rip : t.RIP = 0x10590e)
    (hr13 : t.regValue .r13 = stackPtr s - 592)
    (hx : MontgomeryAt t (stackPtr s - 592) x)
    (hy : MontgomeryAt t (stackPtr s - 528) y)
    : ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x105951 ∧ MontgomeryAt u (stackPtr s - 176) ((x + y) % P256.Spec.Operations.domain.p) ∧
      (u.regValue .rbx = t.regValue .rbx ∧
       u.regValue .rbp = stackPtr s - 176 ∧
       u.regValue .r12 = t.regValue .r12 ∧
       u.regValue .r13 = t.regValue .r13 ∧
       u.regValue .r14 = t.regValue .r14 ∧
       u.regValue .r15 = t.regValue .r15) ∧
      (∀ offset value : Nat, offset ≤ 560 → 24 ≤ offset →
        (offset + 32 ≤ 176 ∨ 176 + 32 ≤ offset) →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value) := by
  obtain ⟨fuel, v, run, frame, effect, keep⟩ := setup_run pre state (offset := 0x590e)
    (ZZ3_block boundary pre.outerBoundary) (by decide) (by decide +kernel) rip
    (by simp [ZZ3Effect, Effect.components, setupComponents, stackPtr])
  have w8 : (Operand.mem (stackPtr t + 8) : Operand 64).read v = (Operand.mem (stackPtr t + 104) : Operand 64).read t := effect.writes.2.2.2.2.2.2.1
  have w16 : (Operand.mem (stackPtr t + 16) : Operand 64).read v = (Operand.mem (stackPtr t + 112) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.1
  have w24 : (Operand.mem (stackPtr t + 24) : Operand 64).read v = (Operand.mem (stackPtr t + 120) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.2.1
  have w32 : (Operand.mem (stackPtr t + 32) : Operand 64).read v = (Operand.mem (stackPtr t + 128) : Operand 64).read t := effect.writes.2.2.2.2.2.2.2.2.2
  have addr8 : stackPtr t + 8 = stackPtr s - 624 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 8) (by decide)
  have addr40 : stackPtr t + 40 = stackPtr s - 592 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 40) (by decide)
  have addr104 : stackPtr t + 104 = stackPtr s - 528 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 104) (by decide)
  have addr456 : stackPtr t + 456 = stackPtr s - 176 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 456) (by decide)
  have hxv : MontgomeryAt v (stackPtr s - 592) x := by
    rw [← addr40]
    apply preserve_value (by simpa only [addr40] using hx) effect.agrees
    intro i hi c hc cover
    simp only [ZZ3Effect, Effect.components, List.map_cons, List.map_nil, Write.component, Operand.component, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals obtain ⟨j, hj, he⟩ := cover
    · exact OffsetsApart.ne (c₁ := 40) (len₁ := 32) (c₂ := 8) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr t) hi hj (by decide) he
    · exact OffsetsApart.ne (c₁ := 40) (len₁ := 32) (c₂ := 16) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr t) hi hj (by decide) he
    · exact OffsetsApart.ne (c₁ := 40) (len₁ := 32) (c₂ := 24) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr t) hi hj (by decide) he
    · exact OffsetsApart.ne (c₁ := 40) (len₁ := 32) (c₂ := 32) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr t) hi hj (by decide) he
  have hyv : MontgomeryAt v (stackPtr s - 624) y := by
    rw [← addr8]
    apply copy_value (src := stackPtr t + 104)
    · simpa only [addr104] using hy
    · rw [addr8]
      exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) frame.allocated
    · exact w8
    · simp only [BitVec.add_assoc]
      exact w16
    · simp only [BitVec.add_assoc]
      exact w24
    · simp only [BitVec.add_assoc]
      exact w32
  have hrdiv : v.regValue .rdi = stackPtr s - 176 := by
    exact (effect.writes.2.2.2.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 456) (by decide))
  have hrsiv : v.regValue .rsi = stackPtr s - 592 := by
    exact (effect.writes.2.2.2.2.1).trans hr13
  have hrdxv : v.regValue .rdx = stackPtr s - 624 := by
    exact (effect.writes.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 8) (by decide))
  obtain ⟨fuel', u, run', frame', rip', value, saved, bytes, _⟩ :=
    Call.binary_call pre frame Call.Sites.call_1035fc (x := x) (y := y)
      (op := fun a b => (a + b) % P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_add_correct hp hx hy)
      effect.rip hrsiv hrdxv hrdiv hxv hyv
  refine ⟨fuel + fuel', u, run.trans run', frame', rip', value, ?_, ?_⟩
  · refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
    · apply (saved .rbx (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 3) (by simp [ZZ3Effect, Effect.components]))
    · apply (saved .rbp (by decide)).trans
      exact (effect.writes.2.2.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 456) (by decide))
    · apply (saved .r12 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 12) (by simp [ZZ3Effect, Effect.components]))
    · apply (saved .r13 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 13) (by simp [ZZ3Effect, Effect.components]))
    · apply (saved .r14 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 14) (by simp [ZZ3Effect, Effect.components]))
    · apply (saved .r15 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 15) (by simp [ZZ3Effect, Effect.components]))
  · intro offset val bound low apart hx
    exact call_keep bytes (by omega) low apart (keep offset val bound hx)

end P256.Proofs.Projective.Add.Combinations
