import K256.Proofs.Generate.Generator.Multiply.State
import K256.Spec.Ecdsa

namespace K256.Proofs.Verify.Transfer

open K256.Spec K256.Spec.Program Prelude X86.Machine X86Proofs
open Refine ParseSignature Common Generate.Generator.Multiply
open Standards.SECG.DomainParameters.Secp256k1

theorem signatureValues {m : Ram} {src : BitVec 64} {bytes : ByteArray} {r s : Nat}
    (input : (⟨src.toNat,64⟩ : MemoryRegion).HasBytes m bytes)
    (valid : Ecdsa.signatureScalars bytes = some (r,s)) :
    scalarValue m src = r ∧ scalarValue m (src+32) = s ∧
      0 < r ∧ r < domain.n ∧ 0 < s ∧ s < domain.n := by
  unfold Ecdsa.signatureScalars at valid
  dsimp only at valid
  split at valid
  next h =>
    cases valid
    have first := octetsToNat_extract_eq_words input (off := 0) (by omega)
    have second := octetsToNat_extract_eq_words input (off := 32) (by omega)
    simp only [Nat.add_zero, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      Nat.reduceAdd] at first second
    exact ⟨first.symm, second.symm, h.2⟩
  next => contradiction

theorem wordsAt_of_scalarLimbsAt {m n : Ram} {dst src : BitVec 64}
    (stored : scalarLimbsAt m dst n src) :
    WordsAt m dst 64 (scalarWords (scalarValue n src)) := by
  intro i hi
  rw [stored i hi]
  let w := scalarWord n src
  have b₀ := (w 0).isLt
  have b₁ := (w 1).isLt
  have b₂ := (w 2).isLt
  have b₃ := (w 3).isLt
  apply BitVec.eq_of_toNat_eq
  simp only [scalarWords, Vector.getElem_ofFn, BitVec.toNat_ofNat]
  change (w i).toNat =
    (((((w 3).toNat * 2^64 + (w 2).toNat) * 2^128 + (w 1).toNat * 2^64 + (w 0).toNat) /
      2^(64*i)) % 2^64)
  obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals omega

end K256.Proofs.Verify.Transfer
