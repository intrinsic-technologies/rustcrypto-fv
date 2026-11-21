import K256.Spec.Program

namespace K256.Proofs.Generate

open K256.Spec.Program Prelude X86 X86.Machine Standards.SECG.ECC Standards.SECG.DomainParameters

private theorem signingKeyBytes {dst : BitVec 64} {mem : Ram} {scalar encoded : ByteArray}
    (secret : (MemoryRegion.mk dst.toNat 32).HasBytes mem scalar)
    (pointBytes : (MemoryRegion.mk (dst + 32).toNat 65).HasBytes mem encoded) :
    (MemoryRegion.mk dst.toNat 97).HasBytes mem (scalar ++ encoded) := by
  have hs : scalar.size = 32 := secret.1
  have hp : encoded.size = 65 := pointBytes.1
  refine ⟨by change (scalar ++ encoded).size = 97; rw [ByteArray.size_append, hs, hp], fun i => ?_⟩
  by_cases first : i.val < scalar.size
  · simpa only [ByteArray.getElem_append_left first] using secret.2 ⟨i.val, first⟩
  · have limit : i.val < scalar.size + encoded.size := by
      simpa only [ByteArray.size_append] using i.isLt
    have after : scalar.size ≤ i.val := by omega
    have j : i.val - scalar.size < encoded.size := by omega
    have byte := pointBytes.2 ⟨i.val - scalar.size, j⟩
    change mem[BitVec.ofNat 64 ((dst + 32).toNat + (i.val - scalar.size))]? =
      some encoded[i.val - scalar.size] at byte
    change mem[BitVec.ofNat 64 (dst.toNat + i.val)]? = some (scalar ++ encoded)[i.val]
    rw [ByteArray.getElem_append_right after]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte ⊢
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 scalar.size by rw [hs]; rfl,
      BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le after] at byte
    exact byte

theorem output_hasBytes {initial : RamState} {mem : Ram} {random : ByteArray} {d : Nat}
    {point : Curve.Point} (draw : K256.Spec.Secp256k1.randomSecret random = some d)
    (publicKey : Keys.publicKey Secp256k1.domain (Encoding.natToOctets 32 d) = some point)
    (secret : (⟨(initial.regValue .rdi).toNat, 32⟩ : MemoryRegion).HasBytes mem
      (Encoding.natToOctets 32 d))
    (pointBytes : (⟨(initial.regValue .rdi + 32).toNat, 65⟩ : MemoryRegion).HasBytes mem
      (Points.encodePoint Secp256k1.domain false point)) :
    (outputRegion signingKeyGenerateFromRng initial).HasBytes mem
      (K256.Spec.Secp256k1.generatedSigningKey random) := by
  simp only [K256.Spec.Secp256k1.generatedSigningKey, draw, K256.Spec.Secp256k1.publicKeyOf,
    publicKey, Option.map_some, Option.getD_some]
  exact signingKeyBytes secret pointBytes

end K256.Proofs.Generate
