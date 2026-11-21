import P256.Proofs.Sec1.Affine.Dispatch.Compact

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem dispatch_identity [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : AffineDecodePre s boundary ⟨#[0]⟩) :
    ∃ fuel t, Advances boundary fuel s t ∧ Tagged s t 0 ∧ t.RIP = 0x110612 := by
  obtain ⟨fuel, a, runA, stateA, ripA⟩ := tag_entry pre
  obtain ⟨t, runT, stateT, ripT⟩ := range_branch pre stateA ripA
  exact ⟨fuel+1, t, runA.trans runT, stateT, by simpa using ripT⟩

theorem dispatch_nonidentity [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (nonzero : bytes.data[0]?.getD 0 ≠ 0) :
    ∃ fuel t, Advances boundary fuel s t ∧ Routed s t (bytes.data[0]?.getD 0) ∧
      t.RIP = (if bytes.data[0]?.getD 0 = 2 ∨ bytes.data[0]?.getD 0 = 3 then
        0x110108 else 0x110207) := by
  obtain ⟨fuel, a, runA, stateA, ripA⟩ := tag_entry pre
  obtain ⟨b, runB, stateB, ripB⟩ := range_branch pre stateA ripA
  obtain ⟨t, runT, stateT, ripT⟩ := mask_route pre stateB (by
    simpa only [nonzero, ↓reduceIte] using ripB)
  exact ⟨fuel+1+5, t, (runA.trans runB).trans runT, stateT, ripT⟩

theorem dispatch_compressed [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (tag : bytes.data[0]?.getD 0 = 2 ∨ bytes.data[0]?.getD 0 = 3) :
    ∃ fuel t, Advances boundary fuel s t ∧ Routed s t (bytes.data[0]?.getD 0) ∧
      t.RIP = 0x110108 := by
  have nonzero : bytes.data[0]?.getD 0 ≠ 0 := by
    rcases tag with h | h <;> rw [h] <;> decide
  obtain ⟨fuel, t, run, state, rip⟩ := dispatch_nonidentity pre nonzero
  exact ⟨fuel, t, run, state, by simpa only [tag, ↓reduceIte] using rip⟩

theorem dispatch_uncompressed_or_compact [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes)
    (tag : bytes.data[0]?.getD 0 = 4 ∨ bytes.data[0]?.getD 0 = 5) :
    ∃ fuel t, Advances boundary fuel s t ∧ Routed s t (bytes.data[0]?.getD 0) ∧
      t.RIP = (if bytes.data[0]?.getD 0 = 5 then 0x11020f else 0x110635) := by
  have nonzero : bytes.data[0]?.getD 0 ≠ 0 := by
    rcases tag with h | h <;> rw [h] <;> decide
  have uncompressed : ¬(bytes.data[0]?.getD 0 = 2 ∨ bytes.data[0]?.getD 0 = 3) := by
    rcases tag with h | h <;> rw [h] <;> decide
  obtain ⟨fuel, a, runA, stateA, ripA⟩ := dispatch_nonidentity pre nonzero
  obtain ⟨t, runT, stateT, ripT⟩ := compact_route pre stateA (by
    simpa only [uncompressed, ↓reduceIte] using ripA)
  exact ⟨fuel+2, t, runA.trans runT, stateT, ripT⟩

end P256.Proofs.Sec1.Affine
