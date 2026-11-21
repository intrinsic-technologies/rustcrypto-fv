import P256.Proofs.Projective.Double.Combinations.Finish.Finish

set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Combinations
open CrossTerms (slot_add store_writes)

theorem Combinations.finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x106296)
    (input : TripledAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x10635a ∧ CombinationsAt s u point := by
  obtain ⟨_, u, run, state, rip, input⟩ := finish_prepare pre state rip input
  obtain ⟨_, v, run', state', rip', input'⟩ := finish_finish pre state rip input
  exact ⟨_, v, run.trans run', state', rip', input'⟩

end P256.Proofs.Projective.Double
