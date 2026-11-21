import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Finish.Epilogue

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Program (CalleeResult programLoaded_codeIn programText_slice readyToStep)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {select : Bool} {fuel : Nat}
    (pre : BinaryFieldPre s boundary 0x114380 128) (state : ReturnedState s t select)
    (run : Advances boundary fuel s t) :
    ∃ u, CalleeResult s u boundary 32 128 ∧
      ∀ i < 32, u.external[s.regValue .rdi + BitVec.ofNat 64 i]? = outputBytes s select i := by
  obtain ⟨n, u, advance, ready, _, effect⟩ :=
    finish_copy boundary pre.outerBoundary t (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x143bf finishCopyBytes
        (by decide +kernel) rfl) (finish_copy_pre pre state)
  exact finish_return pre state effect ready (run.trans advance)

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
