import P256.Proofs.Sec1.Interface
import P256.Proofs.Field.Preserve
import X86Proofs.Program.ReadWrite.RepString

set_option autoImplicit false

namespace P256.Proofs.Sec1

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

theorem AffineAt.of_bytes_eq {s t : RamState} {source destination : BitVec 64}
    {point : Curve.Point} (represented : AffineAt s source point)
    (bytes : ∀ i < 65, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]?) : AffineAt t destination point := by
  cases point with
  | infinity =>
    refine ⟨represented.1.of_bytes_eq (fun i hi ↦ bytes i (by omega)),
      represented.2.1.of_bytes_eq ?_, ?_⟩
    · intro i hi
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        bytes (32 + i) (by omega)
    · exact (bytes 64 (by decide)).trans represented.2.2
  | affine x y =>
    refine ⟨represented.1.of_bytes_eq (fun i hi ↦ bytes i (by omega)),
      represented.2.1.of_bytes_eq ?_, ?_⟩
    · intro i hi
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        bytes (32 + i) (by omega)
    · exact (bytes 64 (by decide)).trans represented.2.2

theorem AffineResultAt.of_bytes_eq {s t : RamState} {source destination : BitVec 64}
    {point : Option Curve.Point} (represented : AffineResultAt s source point)
    (bytes : ∀ i < 73, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]?) : AffineResultAt t destination point := by
  cases point with
  | none => exact (bytes 72 (by decide)).trans represented
  | some point => exact ⟨represented.1.of_bytes_eq (fun i hi ↦ bytes i (by omega)),
      (bytes 72 (by decide)).trans represented.2⟩

theorem PublicKeyResultAt.of_bytes_eq {s t : RamState} {source destination : BitVec 64}
    {point : Option Curve.Point} (represented : PublicKeyResultAt s source point)
    (bytes : ∀ i < 73, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]?) : PublicKeyResultAt t destination point := by
  have tag : memLoad t.external destination 64 = memLoad s.external source 64 := by
    apply memLoad_congr
    intro i hi
    apply memByte_congr
    exact bytes i (by omega)
  cases point with
  | none => exact tag.trans represented
  | some point =>
    cases point with
    | infinity => exact represented.elim
    | affine x y =>
      refine ⟨tag.trans represented.1, represented.2.of_bytes_eq ?_⟩
      intro i hi
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
        bytes (8 + i) (by omega)

end P256.Proofs.Sec1
