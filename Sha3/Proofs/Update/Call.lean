import Sha3.Proofs.Update.Body
import Sha3.Proofs.Update.EntryExit

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

theorem call_advance [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    (boundary : ReturnBoundary) (hb : ¬InProgram boundary.rip) :
    ∃ fuel final, Advances boundary fuel initial final ∧ ReadyToStep final ∧
      ProgramLoaded final ∧
      CallResult initial final (Incremental.update Keccak.keccakLanes v.rate state bytes) := by
  obtain ⟨s, hs, hi, hip, hptr, h14, h2, h0, h7, hstate⟩ := entry_advance hc hb
  obtain ⟨fuel, t, ht, it, ipt, pt, lt, ct⟩ :=
    body_advance hc hi boundary hb hip hptr (h7.trans hc.cursorPointer) h14
      (h2.trans hc.length) h0 hstate.lanes
  obtain ⟨final, hf, rf, result⟩ := exit_advance hc it hb ipt lt pt ct
    (Incremental.update_cursor_lt _ _ v.rate_pos state hc.cursor_lt bytes)
  exact ⟨_, final, (hs.trans ht).trans hf, rf, result.programLoaded hc, result⟩

theorem call_canonical_advance [Bindings] {v : Variant} {initial : RamState}
    {prior bytes : ByteArray}
    (hc : CallContext v initial bytes (Incremental.canonicalState Keccak.keccakLanes v.rate prior))
    (boundary : ReturnBoundary) (hb : ¬InProgram boundary.rip) :
    ∃ fuel final, Advances boundary fuel initial final ∧ ReadyToStep final ∧
      ProgramLoaded final ∧
      CallResult initial final (Incremental.canonicalState Keccak.keccakLanes v.rate (prior ++ bytes)) := by
  simpa only [Incremental.update_canonicalState _ _ v.rate_pos] using call_advance hc boundary hb

end Sha3.Proofs.Update
