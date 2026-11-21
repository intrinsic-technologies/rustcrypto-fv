import K256.Proofs.Verify.Core.State

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86Proofs K256.Proofs.Refine Standards.SECG.ECC
open Generate.Generator.Affine (ProjectiveAt)
open Generate.Generator.Multiply (scalarWords)

namespace Entry

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}
    (e : Entry fr a p digest r s) {m : Ram}

include e

theorem low_toNat : fr.low.toNat = fr.rsp.toNat - 12456 := by
  rw [e.stackBase, BitVec.toNat_sub_of_le (show (12456 : BitVec 64) ≤ fr.rsp from
    BitVec.le_def.mpr e.stackRoom)]
  rfl

theorem above {off len : Nat} (fits : off + len ≤ 512) :
    Outside [fr.region] (fr.rsp + BitVec.ofNat 64 off) len := by
  have upper := e.low
  have bottom := e.low_toNat
  have room := e.stackRoom
  have addr : (fr.rsp + BitVec.ofNat 64 off).toNat = fr.rsp.toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  refine ⟨by rw [addr]; omega, fun reg hr => Or.inr ?_⟩
  obtain rfl := List.mem_singleton.mp hr
  change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
  rw [addr]
  omega

theorem loaded_of_frame (hf : RamWriteFrame fr.original m [fr.region]) :
    ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2 := by
  intro v hv
  apply (hf.outside _ ⟨by have := v.1.isLt; omega, ?_⟩).trans (e.image v hv)
  intro reg hreg
  obtain rfl := List.mem_singleton.mp hreg
  have lo := e.low_toNat
  have room := e.stackRoom
  change v.1.toNat + 1 ≤ fr.low.toNat ∨ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ _
  apply Classical.byContradiction
  intro denied
  apply e.stack.notCode v hv (v.1.toNat - fr.low.toNat) (by omega)
  rw [← ofNat_toNat_add, Nat.add_sub_cancel' (by omega), BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem peer_of_frame (hf : RamWriteFrame fr.original m [fr.region]) :
    ∃ q : Generate.Generator.Multiply.Projective, q.Stored m fr.rsi ∧ q.valid ∧ q.value = p := by
  obtain ⟨q, stored, valid, value⟩ := e.peer
  exact ⟨q, stored.of_frame hf (by rw [e.key]; exact e.above (off := 16) (by decide)), valid, value⟩

theorem scalarWords_of_frame (hf : RamWriteFrame fr.original m [fr.region]) :
    WordsAt m fr.r8 64 (scalarWords r) ∧ WordsAt m (fr.r8 + 32) 64 (scalarWords s) := by
  refine ⟨e.rAt.of_frame hf (by decide) ?_, e.sAt.of_frame hf (by decide) ?_⟩
  · rw [e.sig]
    exact e.above (off := 360) (by decide)
  · rw [e.sig, BitVec.add_assoc]
    exact e.above (off := 392) (by decide)

end Entry
end K256.Proofs.Verify.Core
