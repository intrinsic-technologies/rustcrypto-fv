import K256.Proofs.Sec1.Serialize.Normalize.Correct
import K256.Proofs.Common.Refine.Lemma.Store
import K256.Proofs.Sec1.Serialize.Pack
import K256.Spec.Secp256k1

namespace K256.Proofs.Sec1.Serialize

open Prelude X86.Machine X86Proofs K256.Proofs.Common K256.Proofs.Refine
open K256.Proofs.Common.Field
open Standards.SECG.ECC Standards.SECG.DomainParameters

private theorem hasBytes_append {memory : Ram} {address : BitVec 64} {first second : ByteArray}
    (left : (MemoryRegion.mk address.toNat first.size).HasBytes memory first)
    (right : (MemoryRegion.mk (address + BitVec.ofNat 64 first.size).toNat second.size).HasBytes
      memory second) :
    (MemoryRegion.mk address.toNat (first ++ second).size).HasBytes memory (first ++ second) := by
  refine ⟨rfl, fun i => ?_⟩
  by_cases before : i.val < first.size
  · have h := left.2 ⟨i.val, before⟩
    simpa only [ByteArray.getElem_append_left before] using h
  · have after : i.val - first.size < second.size := by
      have bound : i.val < first.size + second.size := by
        simpa only [ByteArray.size_append] using i.isLt
      omega
    have h := right.2 ⟨i.val - first.size, after⟩
    change memory[BitVec.ofNat 64 ((address + BitVec.ofNat 64 first.size).toNat +
      (i.val - first.size))]? = some second[i.val - first.size] at h
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.add_sub_of_le (by omega : first.size ≤ i.val)] at h
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ByteArray.getElem_append_right (by omega : first.size ≤ i.val)] using h

private theorem hasBytes_singleton {memory : Ram} {address : BitVec 64} {byte : UInt8}
    (present : memory[address]? = some byte) :
    (MemoryRegion.mk address.toNat 1).HasBytes memory ⟨#[byte]⟩ := by
  refine ⟨rfl, fun i => ?_⟩
  have eq : i.val = 0 := by have bound : i.val < 1 := i.isLt; omega
  simpa [eq, ByteArray.getElem_eq_getElem_data] using present

theorem uncompressed_hasBytes {mem : Ram} {dst : BitVec 64} {x y : Nat}
    (tag : mem[dst]? = some 4)
    (hx : (⟨(dst + 1).toNat, 32⟩ : MemoryRegion).HasBytes mem (Encoding.natToOctets 32 x))
    (hy : (⟨(dst + 33).toNat, 32⟩ : MemoryRegion).HasBytes mem (Encoding.natToOctets 32 y)) :
    (⟨dst.toNat, 65⟩ : MemoryRegion).HasBytes mem
      (Points.encodePoint Secp256k1.domain false (.affine x y)) := by
  let head : ByteArray := ⟨#[4]⟩
  have headSize : head.size = 1 := rfl
  have header : (⟨dst.toNat, head.size⟩ : MemoryRegion).HasBytes mem head :=
    hasBytes_singleton tag
  have first := hasBytes_append header (second := Encoding.natToOctets 32 x) (by
    rw [headSize, Encoding.natToOctets_size]
    exact hx)
  have all := hasBytes_append first (second := Encoding.natToOctets 32 y) (by
    simp only [ByteArray.size_append, headSize, Encoding.natToOctets_size]
    exact hy)
  change (⟨dst.toNat, 65⟩ : MemoryRegion).HasBytes mem
    (head ++ Encoding.natToOctets 32 x ++ Encoding.natToOctets 32 y)
  simpa only [ByteArray.size_append, headSize, Encoding.natToOctets_size] using all

private theorem normalized_hasBytes {mem : Ram} {dst : BitVec 64} {a : Limbs}
    {x : Fin modulus} {m : Nat} (repr : FieldRepr a x m) (bound : m ≤ 2047)
    (words : WordsAt mem dst 64 (packWords (Normalize.normalize a))) (hr : Readable mem dst 32) :
    (⟨dst.toNat, 32⟩ : MemoryRegion).HasBytes mem (Encoding.natToOctets 32 x.val) := by
  obtain ⟨width, value⟩ := Normalize.normalize_correct a x m repr bound
  rw [← value]
  exact packWords_hasBytes width words hr

theorem normalizedPoint_hasBytes {mem : Ram} {dst : BitVec 64} {a b : Limbs}
    {x y : Fin modulus} {m : Nat} (hx : FieldRepr a x m) (hy : FieldRepr b y m) (bound : m ≤ 2047)
    (tag : mem[dst]? = some 4)
    (xs : WordsAt mem (dst + 1) 64 (packWords (Normalize.normalize a)))
    (ys : WordsAt mem (dst + 33) 64 (packWords (Normalize.normalize b)))
    (hr : Readable mem dst 65) :
    (⟨dst.toNat, 65⟩ : MemoryRegion).HasBytes mem
      (Points.encodePoint Secp256k1.domain false (.affine x.val y.val)) :=
  uncompressed_hasBytes tag
    (normalized_hasBytes hx bound xs (hr.of_offsets rfl (addr_self dst) (by decide)))
    (normalized_hasBytes hy bound ys (hr.of_offsets rfl (addr_self dst) (by decide)))

end K256.Proofs.Sec1.Serialize
