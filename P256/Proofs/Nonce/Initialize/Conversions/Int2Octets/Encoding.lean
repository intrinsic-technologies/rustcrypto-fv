import P256.Proofs.SecretKeyFromBytes.Encoding
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Encoding
import P256.Proofs.Nonce.Mathematics

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC.Encoding P256.Proofs.Program
open P256.Proofs.Projective.Multiply.Machine.Radix.Serialize P256.Proofs.SecretKeyFromBytes.Encoding
open P256.Proofs.Common.Instructions (bswap64)

theorem intToOctets_hasBytes {s : RamState} {address : BitVec 64} {value : Nat}
    (allocated : ∀ i < 32, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (words : ∀ i < 4, memLoad s.external (address + BitVec.ofNat 64 (8*i)) 64 =
      bswap64 (canonicalLimb value (3-i))) :
    (⟨address.toNat, 32⟩ : MemoryRegion).HasBytes s.external
      (Standards.RFC.DeterministicSigning.Nonce.intToOctets P256.Spec.Operations.domain.n value) := by
  rw [intToOctets_eq]
  refine ⟨natToOctets_size _ _, ?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [natToOctets_size] using i.isLt
  have byte := canonical_bigEndian_bytes allocated words i.val hi
  change s.external[BitVec.ofNat 64 (address.toNat+i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simpa only [ByteArray.getElem_eq_getElem_data, natToOctets_getElem 32 value i.val hi, show 32 - 1 = 31 from rfl] using byte

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets
