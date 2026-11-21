import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.Negate
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.Select
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.Output

set_option autoImplicit false


namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} {digit : BitVec 8}
    (pre : CalleePre s boundary 0x1044a0 768 96 496)
    (hdigit : (s.regValue .rdx).setWidth 8 = digit)
    (execution : ∃ fuel, Advances boundary fuel s t) (state : SignState s t table digit) :
    ∃ u, CalleeResult s u boundary 96 496 ∧
      ProjectiveAt u (s.regValue .rdi) (signedLookup table digit) := by
  obtain ⟨m,u,negated,negative⟩ := Finishing.negate pre hdigit state
  obtain ⟨n,v,selected,value⟩ := Finishing.select_negated pre negative
  apply Finishing.output_result pre value.toFrameState ?_ value.rip value.value value.r14 value.output
  obtain ⟨fuel,run⟩ := execution
  exact ⟨fuel+m+n,(run.trans negated).trans selected⟩

end P256.Proofs.Projective.Multiply.Machine.Lookup
