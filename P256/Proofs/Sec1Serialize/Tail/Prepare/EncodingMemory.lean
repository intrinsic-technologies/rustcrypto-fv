import P256.Proofs.Sec1Serialize.Tail.Prepare.Encoding

set_option autoImplicit false

open P256.Proofs.Common.Instructions (bswap64)

namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem canonical_bigEndian_bytes {t : RamState} {a : BitVec 64} {value : Nat}
    (allocated : ∀ i < 32, (t.external[a + BitVec.ofNat 64 i]?).isSome)
    (words : ∀ j < 4, (Operand.mem (a + BitVec.ofNat 64 (8*j)) : Operand 64).read t =
      bswap64 (canonicalLimb value (3-j))) :
    Bytes t.external a 32 (fun i => UInt8.ofNat (value / 256^(31-i) % 256)) := by
  intro i hi
  have hbytes : Bytes t.external (a + BitVec.ofNat 64 (8*(i/8))) 8
      (storedByte (bswap64 (canonicalLimb value (3-i/8)))) := by
    have h := Bytes.of_memLoad (n := 64) (a := a + BitVec.ofNat 64 (8*(i/8)))
      (m := t.external) (by
        intro j hj
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact allocated _ (by omega))
    change Bytes _ _ 8 (storedByte ((Operand.mem _ : Operand 64).read t)) at h
    rw [words (i/8) (by omega)] at h
    exact h
  have h := hbytes (i%8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 8*(i/8)+i%8 = i by omega, canonicalLimb_bigEndian_byte value i hi] at h
  exact h

theorem encoded_hasBytes {t : RamState} {a : BitVec 64} {x y : Nat}
    (allocated : ∀ i < 65, (t.external[a + BitVec.ofNat 64 i]?).isSome)
    (tag : (Operand.mem a : Operand 8).read t = 4)
    (xwords : ∀ j < 4, (Operand.mem (a + BitVec.ofNat 64 (1+8*j)) : Operand 64).read t =
      bswap64 (canonicalLimb x (3-j)))
    (ywords : ∀ j < 4, (Operand.mem (a + BitVec.ofNat 64 (33+8*j)) : Operand 64).read t =
      bswap64 (canonicalLimb y (3-j))) :
    (⟨a.toNat, 65⟩ : MemoryRegion).HasBytes t.external
      (Points.encode (.affine x y)) := by
  have hx : Bytes t.external (a + BitVec.ofNat 64 1) 32 (fun i => UInt8.ofNat (x / 256^(31-i)%256)) :=
    canonical_bigEndian_bytes
      (fun i hi => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact allocated _ (by omega))
      (fun j hj => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact xwords j hj)
  have hy : Bytes t.external (a + BitVec.ofNat 64 33) 32 (fun i => UInt8.ofNat (y / 256^(31-i)%256)) :=
    canonical_bigEndian_bytes
      (fun i hi => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact allocated _ (by omega))
      (fun j hj => by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact ywords j hj)
  have htag : t.external[a]? = some 4 := by
    have h := Bytes.of_memLoad (n := 8) (a := a) (m := t.external) (by
      intro i hi
      exact allocated i (by omega))
    change Bytes _ _ 1 (storedByte ((Operand.mem a : Operand 8).read t)) at h
    rw [tag] at h
    simpa only [BitVec.add_zero, show storedByte (4 : BitVec 8) 0 = 4 from rfl] using h 0 (by decide)
  refine ⟨encodePoint_uncompressed_size x y, ?_⟩
  intro i
  have hi : i.val < 65 := by
    simpa only [encodePoint_uncompressed_size] using i.isLt
  change t.external[BitVec.ofNat 64 (a.toNat+i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hbyte : t.external[a + BitVec.ofNat 64 i.val]? =
      (Points.encode (.affine x y)).data[i.val]? := by
    by_cases hz : i.val = 0
    · simpa only [hz, BitVec.reduceOfNat, BitVec.add_zero,
        encodePoint_uncompressed_tag] using htag
    · by_cases hxi : i.val < 33
      · have hh := hx (i.val-1) (by omega)
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 1+(i.val-1)=i.val by omega] at hh
        rw [show i.val = 1+(i.val-1) by omega,
          encodePoint_uncompressed_x x y (i.val-1) (by omega)]
        simpa only [show 1+(i.val-1)=i.val by omega] using hh
      · have hh := hy (i.val-33) (by omega)
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 33+(i.val-33)=i.val by omega] at hh
        rw [show i.val = 33+(i.val-33) by omega,
          encodePoint_uncompressed_y x y (i.val-33) (by omega)]
        simpa only [show 33+(i.val-33)=i.val by omega] using hh
  simpa only [ByteArray.getElem_eq_getElem_data, Array.getElem?_eq_getElem (show i.val <
    (Points.encode (.affine x y)).data.size from i.isLt)] using hbyte

end P256.Proofs.Sec1Serialize.Prepare
