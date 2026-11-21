import P256.Proofs.Projective.Add.Combinations.DoubleZZ
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

theorem DoubleZZ_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    { x : Nat }
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (rip : t.RIP = 0x1058fe)
    (hrbp : t.regValue .rbp = stackPtr s - 528)
    (hx : MontgomeryAt t (stackPtr s - 528) x)
    : ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧
      u.RIP = 0x10590e ∧ MontgomeryAt u (stackPtr s - 592) ((x + x) % P256.Spec.Operations.domain.p) ∧
      (u.regValue .rbx = t.regValue .rbx ∧
       u.regValue .rbp = t.regValue .rbp ∧
       u.regValue .r12 = t.regValue .r12 ∧
       u.regValue .r13 = stackPtr s - 592 ∧
       u.regValue .r14 = t.regValue .r14 ∧
       u.regValue .r15 = t.regValue .r15) ∧
      (∀ offset value : Nat, offset ≤ 560 → 24 ≤ offset →
        (offset + 32 ≤ 592 ∨ 592 + 32 ≤ offset) →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value) := by
  obtain ⟨fuel, v, run, frame, effect, keep⟩ := setup_run pre state (offset := 0x58fe)
    (DoubleZZ_block boundary pre.outerBoundary) (by decide) (by decide +kernel) rip
    (by simp [DoubleZZEffect, Effect.components, setupComponents, stackPtr])
  have addr40 : stackPtr t + 40 = stackPtr s - 592 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 40) (by decide)
  have addr104 : stackPtr t + 104 = stackPtr s - 528 := scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 104) (by decide)
  have hxv : MontgomeryAt v (stackPtr s - 528) x := by
    exact keep 528 x (by decide) hx
  have hrdiv : v.regValue .rdi = stackPtr s - 592 := by
    exact (effect.writes.2.1).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 40) (by decide))
  have hrsiv : v.regValue .rsi = stackPtr s - 528 := by
    exact (effect.writes.1).trans hrbp
  obtain ⟨fuel', u, run', frame', rip', value, saved, bytes, _⟩ :=
    Call.unary_call pre frame (entry := 0x1137f0) (reserve := 16)
      (resultAt := fun u dst => MontgomeryAt u dst ((x + x) % P256.Spec.Operations.domain.p))
      ⟨640, 528, 592, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ rfl (by decide)
      0x5909 0xdee2 (by decide) (by decide +kernel) (by decide +kernel)
      (by decide) (inProgram_of_textOffset 0x137f0 (by decide))
      (fun _ hp hx => field_double_correct hp hx) effect.rip hrsiv hrdiv hxv
  refine ⟨fuel + fuel', u, run.trans run', frame', rip', value, ?_, ?_⟩
  · refine ⟨?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
    · apply (saved .rbx (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 3) (by simp [DoubleZZEffect, Effect.components]))
    · apply (saved .rbp (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 5) (by simp [DoubleZZEffect, Effect.components]))
    · apply (saved .r12 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 12) (by simp [DoubleZZEffect, Effect.components]))
    · apply (saved .r13 (by decide)).trans
      exact (effect.writes.2.2).trans (scalar_stack_address (frameOffset := 632) state.rsp (by decide) (offset := 40) (by decide))
    · apply (saved .r14 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 14) (by simp [DoubleZZEffect, Effect.components]))
    · apply (saved .r15 (by decide)).trans
      exact (effect.agrees.read (n := 64) (r := 15) (by simp [DoubleZZEffect, Effect.components]))
  · intro offset val bound low apart hx
    exact call_keep bytes (by omega) low apart (keep offset val bound hx)

end P256.Proofs.Projective.Add.Combinations
