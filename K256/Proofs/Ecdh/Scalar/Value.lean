import K256.Proofs.Generate.Sampling.Predicate
import K256.Proofs.Generate.Generator.Multiply.Split.Addition.Arithmetic
import K256.Spec.Program

namespace K256.Proofs.Ecdh.Scalar

open K256.Spec.Program Prelude X86.Machine X86Proofs Standards.SECG.ECC
  Standards.SECG.DomainParameters K256.Proofs.Generate

private theorem words_of_limbsValue (w : Nat → BitVec 64) :
    (Vector.ofFn fun i : Fin 4 => w i.val) =
      Generator.Multiply.scalarWords (Sampling.limbsValue (w 0) (w 1) (w 2) (w 3)) := by
  let q : Common.Invert.LinearCombination.Limbs := ⟨w 0, w 1, w 2, w 3⟩
  calc
    _ = Common.Invert.ModularShift.words q := by
      apply Vector.ext
      intro j hj
      rcases show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega with rfl | rfl | rfl | rfl <;> rfl
    _ = Generator.Multiply.scalarWords q.toNat := Generator.Multiply.Split.Addition.limbWords_eq q
    _ = _ := by
      apply congrArg Generator.Multiply.scalarWords
      simp only [q, Common.Invert.LinearCombination.Limbs.toNat, Sampling.limbsValue]
      omega

theorem acceptedSecret {s : RamState} {secret peer : ByteArray}
    (call : ValidCall ecdhDiffieHellman s [secret, peer]) :
    let w := Common.scalarWord s.external (s.regValue .rsi)
    let d := Sampling.limbsValue (w 0) (w 1) (w 2) (w 3)
    Keys.decodeSecret Secp256k1.domain secret = some d ∧
      Sampling.orderFlag (w 0) (w 1) (w 2) (w 3) = 1 ∧
      ¬ (∀ i < 4, w i = 0) ∧
      (Vector.ofFn fun i : Fin 4 => w i.val) = Generator.Multiply.scalarWords d := by
  let w := Common.scalarWord s.external (s.regValue .rsi)
  have input : ValidInput s (registerRegion s .rsi 32) secret := call.inputsInMemory.1
  have decoded := Sampling.decodeSecret_eq_words input.2.2 (show secret.size = 32 from input.2.2.1)
  simp only [registerRegion, BitVec.ofNat_toNat, BitVec.setWidth_eq] at decoded
  change Keys.decodeSecret Secp256k1.domain secret =
    (if Sampling.orderFlag (w 0) (w 1) (w 2) (w 3) = 1 ∧
        ¬ (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0) then
      some (Sampling.limbsValue (w 0) (w 1) (w 2) (w 3)) else none) at decoded
  have accepted : (Keys.decodeSecret Secp256k1.domain secret).isSome = true := call.inputsHoldValues.1
  by_cases h : Sampling.orderFlag (w 0) (w 1) (w 2) (w 3) = 1 ∧
      ¬ (w 0 = 0 ∧ w 1 = 0 ∧ w 2 = 0 ∧ w 3 = 0)
  · rw [ite_eq_left h] at decoded
    exact ⟨decoded, h.1, fun hz => h.2 ((Sampling.words_all_zero_iff w).mp hz), words_of_limbsValue w⟩
  · rw [ite_eq_right h] at decoded
    rw [decoded] at accepted
    contradiction

end K256.Proofs.Ecdh.Scalar
