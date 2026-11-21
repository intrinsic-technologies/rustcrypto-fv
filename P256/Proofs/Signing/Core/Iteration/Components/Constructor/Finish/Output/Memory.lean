import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Frame
import P256.Proofs.Program.Memory
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_writable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t) :
    P256.Proofs.Common.Instructions.CrossPageStore.Writable t (s.regValue .rdi) 72 := by
  have readable := Program.readable_of_grow
    (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (Nat.le_refl _))
    state.allocated
  refine ⟨readable, ?_⟩
  apply tables_of_not_reserved (by change 0 < 72; decide) readable.low
  intro i hi hreserved
  exact pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) (.inr hreserved)

theorem output_code [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) {offset len : Nat}
    (bound : offset + len ≤ 118431) : RangeApart (s.regValue .rdi) 72
      (Extracted.textAddress + BitVec.ofNat 64 offset) len := by
  intro i hi j hj he
  apply pre.avoids _ (by simp) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  left
  rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset (offset + j) (by omega)

theorem output_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) {offset len : Nat} {a : BitVec 64}
    (bound : offset + len ≤ 72)
    (covered : (Component.mem (s.regValue .rdi + BitVec.ofNat 64 offset) len).Covers a) :
    (registerRegion s .rdi 72).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := covered
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show offset + i < 72 by omega)

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish
