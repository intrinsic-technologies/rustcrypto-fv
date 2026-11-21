import Sha3.Proofs.Finalize.Prepare
import Sha3.Proofs.Finalize.Call
import Sha3.Proofs.Finalize.Finish
import Sha3.Proofs.Finalize.Finish.FullReset

namespace Sha3.Proofs.Finalize

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def steps (v : Variant) (reset : Bool) : Nat :=
  6352 + Output.steps v + (if reset then 52 else 4)

theorem call_advance [bindings : Bindings] (hstride : UnitStringStride bindings)
    (v : Variant) (reset : Bool) (state : Incremental.State)
    (boundary : ReturnBoundary) (hboundary : ¬ InProgram boundary.rip) (keccak : Bool := false) :
    AdvanceTriple boundary (steps v reset) (CallPre (keccak := keccak) boundary v reset state)
      Extracted.programImage (CallResult (keccak := keccak) v reset state) := by
  intro initial hready hcode hp
  obtain ⟨padded, hprepare, hpadready, hpadcode, hpad⟩ :=
    prepare_advance (keccak := keccak) (fullState := false) v reset state boundary hboundary initial hready hcode hp
  obtain ⟨permuted, hperm, hpermready, hpermcode, hpermuted⟩ :=
    permutation_advance hp hboundary padded hpadready hpadcode hpad
  obtain ⟨final, hfinish, hfinalready, hfinalcode, hresult⟩ :=
    finish_advance hstride hp hboundary permuted hpermready hpermcode hpermuted
  refine ⟨final, ?_, hfinalready, hfinalcode, hresult⟩
  have hrun := (hprepare.trans hperm).trans hfinish
  change Advances boundary (6352 + (Output.steps v + if reset then 52 else 4))
    initial final at hrun
  simpa only [steps, Nat.add_assoc] using hrun

theorem full_call_advance [bindings : Bindings] (hstride : UnitStringStride bindings)
    (reset : Bool) (state : Incremental.State) (boundary : ReturnBoundary)
    (hboundary : ¬ InProgram boundary.rip) (initial : RamState)
    (hready : ReadyToStep initial) (hcode : CodeIn Extracted.programImage initial)
    (hp : CallPre boundary .sha256 reset state initial true true)
    (hinside : initial.regValue .rsp - (if reset then 32 else 0) ≠ boundary.rsp) :
    ∃ final, Advances boundary
      (6352 + (if reset then 56 else 7) + Memcpy.memcpy200Steps (initial.regValue .rsi))
      initial final ∧ ReadyToStep final ∧ CodeIn Extracted.programImage final ∧
      CallResult .sha256 reset state initial final true true := by
  obtain ⟨padded, hprepare, hpadready, hpadcode, hpad⟩ :=
    prepare_advance (keccak := true) (fullState := true) .sha256 reset state boundary
      hboundary initial hready hcode hp
  obtain ⟨permuted, hperm, hpermready, hpermcode, hpermuted⟩ :=
    permutation_advance hp hboundary padded hpadready hpadcode hpad
  cases reset with
  | false =>
    have hi : initial.regValue .rsp ≠ boundary.rsp := by simpa using hinside
    obtain ⟨final, hfinish, hr, hc, hf⟩ :=
      full_finish_plain_advance hstride hp hboundary hi permuted hpermready hpermcode hpermuted
    refine ⟨final, ?_, hr, hc, hf⟩
    simpa [← Nat.add_assoc] using (hprepare.trans hperm).trans hfinish
  | true =>
    obtain ⟨final, hfinish, hr, hc, hf⟩ :=
      full_finish_reset_advance hstride hp hboundary hinside permuted hpermready hpermcode hpermuted
    refine ⟨final, ?_, hr, hc, hf⟩
    simpa [← Nat.add_assoc] using (hprepare.trans hperm).trans hfinish

end Sha3.Proofs.Finalize
