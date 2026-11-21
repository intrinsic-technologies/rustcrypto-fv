import P256.Proofs.Projective.Representation
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs

open Prelude X86 X86.Machine X86Proofs

theorem ProjectiveAt.of_bytes_eq {s t : RamState} {source destination : BitVec 64}
    {point : Projective} (represented : ProjectiveAt s source point)
    (bytes : ∀ i < 96, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]?) : ProjectiveAt t destination point := by
  refine ⟨represented.1.of_bytes_eq (fun i hi => bytes i (by omega)), ?_, ?_⟩
  · apply represented.2.1.of_bytes_eq
    intro i hi
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using bytes (32+i) (by omega)
  · apply represented.2.2.of_bytes_eq
    intro i hi
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using bytes (64+i) (by omega)

theorem ProjectiveAt.of_frame {s t : RamState} {address : BitVec 64}
    {point : Projective} {n : Nat} {written : Vector MemoryRegion n}
    (represented : ProjectiveAt s address point) (frame : MemoryWriteFrame s t written)
    (bounded : (MemoryRegion.mk address.toNat 96).Bounded)
    (disjoint : ∀ other ∈ written, (MemoryRegion.mk address.toNat 96).Disjoint other) :
    ProjectiveAt t address point := by
  apply represented.of_bytes_eq
  intro i hi
  exact Program.frame_read frame disjoint
    (Program.memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi)

end P256.Proofs
