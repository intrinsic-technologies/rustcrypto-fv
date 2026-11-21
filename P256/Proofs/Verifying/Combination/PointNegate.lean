import P256.Proofs.Verifying.Combination.Output.MultiReturn
import P256.Proofs.Program.FieldCall.Unary
import P256.Proofs.Projective.Multiply.Machine.Lookup.Negate.Correct

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Projective P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open P256.Proofs.Field P256.Proofs.Program.FieldCall

def digitNegateLayout : StackCallLayout 1432 32 32 24 :=
  ⟨416, 368, 112, by decide, by decide, by decide, by decide,
    by decide, by decide, Or.inl (by decide)⟩

theorem negate_y [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {selected : Projective}
    (pre : Return.Pre s boundary) (state : State s t)
    (rip : t.RIP = 0x10f23c)
    (dst : t.regValue .rdi = stackPtr s - 112)
    (src : t.regValue .rsi = stackPtr s - 368)
    (input : MontgomeryAt t (stackPtr s - 368) selected.y) :
    ∃ fuel w, Advances boundary fuel t w ∧ State s w ∧ w.RIP = 0x10f241 ∧
      MontgomeryAt w (stackPtr s - 112) selected.negate.y ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        w.regValue r = t.regValue r) ∧
      (∀ off len : Nat, off ≤ 408 → len ≤ off+8 →
        (off+32 ≤ 112 ∨ 112+len ≤ off) → ∀ i<len,
        w.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]? =
          t.external[stackPtr s-BitVec.ofNat 64 off+BitVec.ofNat 64 i]?) := by
  obtain ⟨fuel, w, run, frame, ret, value, kept, bytes, _⟩ :=
    unary_call (frameOffset := 408) pre state digitNegateLayout rfl
      (by decide) 0xf23c 0x458f (by decide)
      (by decide +kernel) (entry := 0x1137d0)
      (by decide +kernel) (by decide)
      (inProgram_of_textOffset 0x137d0 (by decide))
      (x := selected.y) (resultAt := fun w addr => MontgomeryAt w addr selected.negate.y)
      (fun v cp hx => by
        obtain ⟨w, result, value⟩ := Projective.Multiply.Machine.Lookup.Negate.negate_correct cp hx
        refine ⟨w, result, ?_⟩
        simpa only [Projective.negate, Standards.SECG.ECC.Curve.fieldSub,
          Nat.zero_add, Nat.zero_mod, Nat.mod_eq_of_lt hx.1] using value)
      rip src dst input
  exact ⟨fuel, w, run, frame, ret, value, kept, bytes⟩

end P256.Proofs.Verifying.Combination.Loop.Multi
