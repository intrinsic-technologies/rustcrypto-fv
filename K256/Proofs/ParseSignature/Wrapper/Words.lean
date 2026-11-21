import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Common.WordCopy

namespace K256.Proofs.ParseSignature.Wrapper

open K256.Proofs.Common Prelude X86.Machine X86Proofs K256.Proofs.Refine

theorem scalarValue_of_inputWords {before after : Ram} {src : BitVec 64}
    (words : ∀ i < 8, memLoad after (wordAddr src 64 i) 64 =
      memLoad before (wordAddr src 64 i) 64) (off : Fin 2) :
    scalarValue after (wordAddr src 64 (4 * off.val)) =
      scalarValue before (wordAddr src 64 (4 * off.val)) := by
  have each (i : Nat) (bound : i < 4) :
      scalarWord after (wordAddr src 64 (4 * off.val)) i =
        scalarWord before (wordAddr src 64 (4 * off.val)) i := by
    unfold scalarWord
    apply congrArg bswapSpec
    have addr : wordAddr src 64 (4 * off.val) + BitVec.ofNat 64 (8 * (3 - i)) =
        wordAddr src 64 (4 * off.val + (3 - i)) := by
      simp only [wordAddr, Nat.reduceDiv, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
    rw [addr]
    exact words _ (by have := off.isLt; omega)
  dsimp only [scalarValue]
  rw [each 3 (by decide), each 2 (by decide), each 1 (by decide), each 0 (by decide)]

theorem serializedWords {mem source : Ram} {sp src : BitVec 64}
    (first : scalarLimbsAt mem (sp + 16) source src)
    (second : scalarLimbsAt mem (sp + 48) source (src + 32)) {i : Nat} (bound : i < 8) :
    bswapSpec (memLoad mem (wordAddr (sp + 16) 64 (4 * (i / 4) + (3 - i % 4))) 64) =
      memLoad source (wordAddr src 64 i) 64 := by
  have h₁ (j : Fin 4) : bswapSpec (memLoad mem (wordAddr (sp + 16) 64 (3-j.val)) 64) =
      memLoad source (wordAddr src 64 j.val) 64 := by
    rw [first _ (by omega), scalarWord, bswapSpec_bswapSpec, show 3-(3-j.val) = j.val by omega]
    rfl
  have h₂ (j : Fin 4) : bswapSpec (memLoad mem (wordAddr (sp + 16) 64 (4 + (3-j.val))) 64) =
      memLoad source (wordAddr src 64 (4 + j.val)) 64 := by
    have addr : wordAddr (sp + 16) 64 (4 + (3-j.val)) = wordAddr (sp + 48) 64 (3-j.val) := by
      simp only [wordAddr, Nat.reduceDiv, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      rw [BitVec.add_assoc sp, show (16 : BitVec 64) + BitVec.ofNat 64 (8*4) = 48 by decide]
    rw [addr, second _ (by omega), scalarWord, bswapSpec_bswapSpec, show 3-(3-j.val)=j.val by omega]
    simp only [wordAddr, Nat.reduceDiv, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  by_cases low : i < 4
  · simpa only [Nat.div_eq_of_lt low, Nat.mod_eq_of_lt low, Nat.mul_zero, Nat.zero_add] using
      (show _ from h₁ ⟨i, low⟩)
  · have div : i / 4 = 1 := by omega
    have index : 4 + i % 4 = i := by omega
    simpa only [div, Nat.mul_one, index] using h₂ ⟨i % 4, Nat.mod_lt _ (by decide)⟩

end K256.Proofs.ParseSignature.Wrapper
