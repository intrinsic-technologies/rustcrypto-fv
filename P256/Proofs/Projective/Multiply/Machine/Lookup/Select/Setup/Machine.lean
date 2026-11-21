import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Setup.Transfer

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

open P256.Proofs.Program (CalleePre programLoaded_codeIn programText_slice)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Select

open P256.Proofs.Field P256.Proofs.Program P256.Spec.Program.Routines
open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup_machine [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x114380 32 32 128) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (setupEffect s).Holds s t := by
  obtain ⟨m, u, run, ready, loaded, prepare⟩ := setup_prepare pre
  obtain ⟨n, t, run', ready', _, suffix⟩ := setup_suffix boundary pre.outerBoundary u ready
    (programText_slice (programLoaded_codeIn loaded) 0x1438b setupSuffixBytes
      (by decide) (by decide +kernel)) (setup_suffix_pre pre prepare)
  exact ⟨m + n, t, run.trans run', ready', setup_effect_of_parts pre prepare suffix⟩

end P256.Proofs.Projective.Multiply.Machine.Lookup.Select
