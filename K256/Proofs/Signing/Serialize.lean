import K256.Proofs.Common.Refine.Lemma.Store
import K256.Proofs.Generate.Wrapper.Scalar.Octets
import K256.Proofs.Generate.Generator.Multiply.State
import K256.Spec.Ecdsa

namespace K256.Proofs.Signing

open K256.Spec Prelude X86.Machine X86Proofs K256.Proofs.Refine
open Standards.SECG.ECC

private theorem signatureBytes_append {mem : Ram} {dst : BitVec 64} {x y : ByteArray}
    (first : (MemoryRegion.mk dst.toNat 32).HasBytes mem x)
    (last : (MemoryRegion.mk (dst+32).toNat 32).HasBytes mem y) :
    (MemoryRegion.mk dst.toNat 64).HasBytes mem (x ++ y) := by
  have hx : x.size = 32 := first.1
  have hy : y.size = 32 := last.1
  refine ⟨by change (x ++ y).size = 64; rw [ByteArray.size_append, hx, hy], fun i => ?_⟩
  by_cases h : i.val < x.size
  · simpa only [ByteArray.getElem_append_left h] using first.2 ⟨i.val, h⟩
  · have bound : i.val < x.size + y.size := by
      simpa only [ByteArray.size_append] using i.isLt
    have after := Nat.le_of_not_gt h
    have byte := last.2 ⟨i.val-x.size, by omega⟩
    change mem[BitVec.ofNat 64 ((dst+32).toNat + (i.val-x.size))]? = some y[i.val-x.size] at byte
    change mem[BitVec.ofNat 64 (dst.toNat+i.val)]? = some (x++y)[i.val]
    rw [ByteArray.getElem_append_right after]
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at byte ⊢
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 x.size by rw [hx]; rfl,
      BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le after] at byte
    exact byte

theorem signatureBytes_of_words {mem : Ram} {dst : BitVec 64} {r s : Nat}
    (readable : Readable mem dst 64)
    (words : ∀ i < 8, memLoad mem (wordAddr dst 64 i) 64 =
      bswapSpec (BitVec.ofNat 64 ((if i < 4 then r else s) / 2^(64*(3-i%4))))) :
    (⟨dst.toNat, 64⟩ : MemoryRegion).HasBytes mem (Ecdsa.signatureBytes r s) := by
  have first : (⟨dst.toNat, 32⟩ : MemoryRegion).HasBytes mem (Encoding.natToOctets 32 r) := by
    apply Generate.Wrapper.scalarOctets ?_ (readable.of_offsets (addr_self dst) (addr_self dst) (by decide))
    intro i hi
    simpa only [Vector.getElem_ofFn, ite_eq_left hi, Nat.mod_eq_of_lt hi] using words i (by omega)
  have last : (⟨(dst+32).toNat, 32⟩ : MemoryRegion).HasBytes mem (Encoding.natToOctets 32 s) := by
    apply Generate.Wrapper.scalarOctets ?_ (readable.of_offsets rfl (addr_self dst) (by decide))
    intro i hi
    have h := words (4+i) (by omega)
    have addr : wordAddr dst 64 (4+i) = wordAddr (dst+32) 64 i := by
      simp only [wordAddr, Nat.reduceDiv, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    simpa only [addr, ite_eq_right (by omega : ¬ 4+i < 4), show (4+i)%4=i by omega,
      Vector.getElem_ofFn] using h
  apply signatureBytes_append first last

open Generate.Generator.Multiply Standards.SECG.DomainParameters.Secp256k1

theorem normalizedBytes_of_serialization {before after : Ram} {src dst : BitVec 64} {r s : Nat}
    (first : WordsAt before src 64 (scalarWords r))
    (last : WordsAt before (src + 32) 64
      (scalarWords (if s > domain.n / 2 then domain.n - s else s)))
    (read : Readable after dst 64)
    (stored : ∀ i < 8, memLoad after (wordAddr dst 64 i) 64 =
      bswapSpec (memLoad before (wordAddr src 64 (4 * (i / 4) + (3 - i % 4))) 64)) :
    (⟨dst.toNat, 64⟩ : MemoryRegion).HasBytes after (Ecdsa.normalizeS r s) := by
  apply signatureBytes_of_words read
  intro i hi
  rw [stored i hi]
  congr 1
  by_cases h : i < 4
  · simpa (disch := omega) only [Nat.div_eq_of_lt h, Nat.mul_zero, Nat.zero_add, ite_eq_left h,
      scalarWords, Vector.getElem_ofFn] using first (3 - i%4) (by omega)
  · have eq : wordAddr src 64 (4 * (i / 4) + (3 - i % 4)) =
        wordAddr (src + 32) 64 (3 - i % 4) := by
      rw [show i/4=1 by omega]
      simp only [wordAddr, Nat.mul_one, Nat.reduceDiv, Nat.mul_add, Nat.reduceMul,
        BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    simpa (disch := omega) only [eq, ite_eq_right h, scalarWords, Vector.getElem_ofFn] using last (3 - i%4) (by omega)

end K256.Proofs.Signing

