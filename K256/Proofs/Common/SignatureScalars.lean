import K256.Proofs.Common.ScalarWords
import K256.Spec.Ecdsa
import K256.Spec.Program

namespace K256.Proofs.Common

open K256.Spec K256.Spec.Program Prelude X86 X86Proofs Standards.SECG.ECC

theorem signatureScalars_of_words {initial : Machine.RamState} {bytes : ByteArray}
    (call : ValidCall signatureFromSlice initial [bytes]) (size : bytes.size = 64) :
    let scalar := fun base =>
      let w := scalarWord initial.external base
      ((w 3).toNat * 2^64 + (w 2).toNat) * 2^128 + (w 1).toNat * 2^64 + (w 0).toNat
    let r := scalar (initial.regValue .rsi)
    let s := scalar (initial.regValue .rsi + 32)
    let n := Standards.SECG.DomainParameters.Secp256k1.domain.n
    Ecdsa.signatureScalars bytes = if 0 < r ∧ r < n ∧ 0 < s ∧ s < n then some (r, s) else none := by
  have hb : (registerRegion initial .rsi bytes.size).HasBytes initial.external bytes :=
    call.inputsInMemory.1.2.2
  have hr := octetsToNat_extract_eq_words hb (off := 0) (by omega)
  have hs := octetsToNat_extract_eq_words hb (off := 32) (by omega)
  simp only [registerRegion, Nat.add_zero, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    Nat.reduceAdd] at hr hs
  simp only [Ecdsa.signatureScalars, size, true_and, hr, hs]
  rfl

end K256.Proofs.Common
