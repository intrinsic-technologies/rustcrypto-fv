import P256.Proofs.Field.Interface
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Field

open Prelude X86 X86.Machine X86Proofs

theorem MontgomeryAt.of_bytes_eq {s t : RamState} {source destination : BitVec 64}
    {value : Nat} (represented : MontgomeryAt s source value)
    (bytes : ∀ i < 32, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]?) : MontgomeryAt t destination value :=
  ⟨represented.1, represented.2.1, fun i hi => (bytes i hi).trans (represented.2.2 i hi)⟩

theorem MontgomeryAt.of_frame {s t : RamState} {address : BitVec 64}
    {value n : Nat} {written : Vector MemoryRegion n}
    (represented : MontgomeryAt s address value)
    (frame : MemoryWriteFrame s t written)
    (bounded : (MemoryRegion.mk address.toNat 32).Bounded)
    (disjoint : ∀ other ∈ written, (MemoryRegion.mk address.toNat 32).Disjoint other) :
    MontgomeryAt t address value := by
  apply represented.of_bytes_eq
  intro i hi
  exact Program.frame_read frame disjoint
    (Program.memoryRegion_contains_add bounded (Nat.le_refl _) (Nat.le_refl _) hi)

end P256.Proofs.Field
