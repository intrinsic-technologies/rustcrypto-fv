import P256.Spec.Program.Functions
import P256.Proofs.SecretKeyFromBytes.Encoding

set_option autoImplicit false

namespace P256.Proofs.SecretKeyFromBytes

open P256.Spec Standards.SECG.ECC

theorem secretOfBytes_eq (bytes : ByteArray) :
    Keys.secretOfBytes bytes =
      if bytes.size = 32 ∧ 0 < Arith.uint bytes ∧ Arith.uint bytes < Operations.domain.n
      then some (Arith.uint bytes) else none := by
  have width : (Operations.domain.n.log2 + 8) / 8 = 32 := by decide +kernel
  simp only [Keys.secretOfBytes, Standards.SECG.ECC.Keys.decodeSecret, width, Arith.uint,
    Arith.decodeBigEndian, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  congr 1
  exact propext and_assoc

end P256.Proofs.SecretKeyFromBytes
