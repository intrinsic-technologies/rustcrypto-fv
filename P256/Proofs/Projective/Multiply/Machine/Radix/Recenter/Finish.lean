import P256.Proofs.Projective.Multiply.Machine.Radix.Recenter.Loop

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix.Recenter

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Spec.Program.Routines
open ProjectiveRadix

theorem loop_initial [Bindings] {s t : RamState} {d : Nat} (state : NibbleState s t d) :
    LoopState s t d 0 := by
  refine ⟨state.toState, ⟨?_, ?_, ?_⟩, state.rip, state.rcx, ?_⟩
  · change (t.regValue .rax).setWidth 8 = rawDigit d 0 + BitVec.ofNat 8 (carry d 0)
    simpa only [rawDigit, carry, show (0 : Nat) < 64 from by decide, ite_true,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero] using state.rax
  · intro j hj
    omega
  · intro j _ hj
    exact state.digits j hj
  · change (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 0) : Operand 8).read t =
      rawDigit d 0 + BitVec.ofNat 8 (carry d 0)
    simpa only [carry, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using state.digits 0 (by decide)

theorem loop_all [Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : LoopState s t d 0) :
    ∀ n, n ≤ 32 → ∃ fuel u, Advances boundary fuel t u ∧ LoopState s u d n ∧
      AgreesExcept (Radix.digitComponents s) t u := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨0,t,(advances_zero boundary t t).mpr rfl,state,AgreesExcept.refl _ _⟩
  | succ n ih =>
    intro hn
    obtain ⟨f,v,run,loop,agrees⟩ := ih (by omega)
    obtain ⟨f',u,run',loop',agrees'⟩ := loop_iteration pre loop (by omega)
    exact ⟨f+f',u,run.trans run',loop',(agrees.trans agrees').mono (by simp)⟩

theorem loop_final [Bindings] {s t : RamState} {d : Nat} (state : LoopState s t d 32) :
    DigitsState s t d := by
  refine ⟨state.toState, state.rip, ?_⟩
  intro j hj
  by_cases hlt : j < 64
  · exact state.centered j hlt
  · have he : j = 64 := by omega
    subst j
    have h := state.stored
    change (Operand.mem (stackPtr s - 112 + BitVec.ofNat 64 64) : Operand 8).read t =
      rawDigit d 64 + BitVec.ofNat 8 (carry d 64) at h
    simpa only [rawDigit, digitByte, digitInt, show ¬ (64 : Nat) < 64 from by decide,
      ite_false, BitVec.ofNat_eq_ofNat, BitVec.zero_add, BitVec.ofInt_natCast] using h

end P256.Proofs.Projective.Multiply.Machine.Radix.Recenter
