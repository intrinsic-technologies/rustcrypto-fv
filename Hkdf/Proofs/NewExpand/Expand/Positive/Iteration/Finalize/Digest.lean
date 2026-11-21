import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.InnerPrefix.Frame
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Bytes
import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad.Payload

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize

open Hkdf.Proofs.Common Hkdf.Proofs.Common.SHA256 Hkdf.Proofs.Common.StreamPadding
open Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare Hkdf.Proofs.NIST.Encoding

theorem digest_eq_hmac (key message : ByteArray) :
    let inner := HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message
    let hash := Hkdf.Proofs.NIST.SHA256.compress (InnerPrefix.prefixHash inner)
      (octetsToBits (finalBlock inner))
    let outer := compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash
      (HMAC.xorPad (HMAC.keyBlock key) 0x5c)
    serializeHash (Hkdf.Proofs.NIST.SHA256.compress outer
      (octetsToBits (Pad.padded (serializeHash hash)))) =
      Standards.RFC.HMAC.hmac Standards.NIST.SHA2.SHA256.hashBytes 64 key message := by
  let inner := HMAC.xorPad (HMAC.keyBlock key) 0x36 ++ message
  have digest : serializeHash (Hkdf.Proofs.NIST.SHA256.compress (InnerPrefix.prefixHash inner)
      (octetsToBits (finalBlock inner))) = Standards.NIST.SHA2.SHA256.hashBytes inner := by
    have standard := serializeHash_tail_compressions_eq_hashBytes inner
    by_cases small : inner.size % 64 < 56
    all_goals simpa only [InnerPrefix.prefixHash, finalBlock, finalPrefix, tailFirst, tailLast,
      small, ↓reduceIte] using standard
  dsimp only
  rw [digest]
  simpa only [inner, Pad.padded, tailFirst_outer] using serializeHash_hmac_sha256_outer key message

end Hkdf.Proofs.NewExpand.Expand.Finalize
