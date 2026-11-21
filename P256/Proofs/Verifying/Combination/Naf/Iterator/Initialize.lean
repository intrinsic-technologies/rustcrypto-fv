import P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize.Epilogue

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

theorem initialize_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {n reserve : Nat} (pre : CalleePre s boundary 0x118290 32 40 reserve)
    (reserved : 24 ≤ reserve) (length : s.regValue .rdx = 32)
    (input : Nat256At s (s.regValue .rsi) n) :
    ∃ t, CalleeResult s t boundary 40 reserve ∧
      StateAt t (s.regValue .rdi) (s.regValue .rsi) n 0 ∧
      t.regValue .rax = s.regValue .rdi ∧ Nat256At t (s.regValue .rsi) n := by
  obtain ⟨fuel, u, run, state⟩ := Initialize.body pre reserved length input
  obtain ⟨t, result, memory, rax⟩ := Initialize.epilogue pre reserved state ⟨fuel, run⟩
  refine ⟨t, result, ?_, rax, input.1, ?_⟩
  · constructor
    · rw [memory]; exact state.state.pointer
    · rw [memory]; exact state.state.remaining
    · rw [memory]; exact state.state.index
    · rw [memory]; exact state.state.low
    · rw [memory]; exact state.state.high
  · intro i hi
    have hin : (registerRegion s .rsi 32).Contains (s.regValue .rsi + BitVec.ofNat 64 i).toNat :=
      memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
    rw [result.frame _]
    · exact input.2 i hi
    · intro region hr covered
      have hr' : region = registerRegion s .rdi 40 ∨ region = Stack.region s reserve := by simpa using hr
      rcases hr' with rfl | rfl
      · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ hin covered
      · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hin covered

end P256.Proofs.Verifying.Combination.Naf.Iterator
