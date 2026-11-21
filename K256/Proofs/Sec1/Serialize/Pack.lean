import K256.Proofs.Common.WordCopy
import K256.Proofs.Common.ScalarWords
import K256.Proofs.Common.Field.SquareValue
import K256.Proofs.Common.Encoding

namespace K256.Proofs.Sec1.Serialize

open Prelude X86.Machine X86Proofs K256.Proofs.Common K256.Proofs.Refine
open Standards.SECG.ECC

def packWords (a : Vector (BitVec 64) 5) : Vector (BitVec 64) 4 :=
  #v[bswapSpec (a[4] <<< 16 ||| a[3] >>> 36),
     bswapSpec (a[3] <<< 28 ||| a[2] >>> 24),
     bswapSpec (a[2] <<< 40 ||| a[1] >>> 12),
     bswapSpec (a[1] <<< 52 ||| a[0])]

private theorem packWord_toNat (high low : BitVec 64) (shift : Nat)
    (h : low.toNat < 2^shift) :
    ((high <<< shift) ||| low).toNat = (high.toNat * 2^shift + low.toNat) % 2^64 := by
  rw [BitVec.toNat_or, BitVec.toNat_shiftLeft,
    ← Nat.mod_eq_of_lt low.isLt, ← Nat.or_mod_two_pow,
    ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt low.isLt]

theorem packWords_value (a : Vector (BitVec 64) 5)
    (width : ∀ i : Fin 5, a[i].toNat < 2^(if i.val = 4 then 48 else 52)) :
    let w := fun i : Fin 4 => (bswapSpec (packWords a)[i]).toNat
    (w 0 * 2^64 + w 1) * 2^128 + w 2 * 2^64 + w 3 = Field.limbValue a := by
  have h0 := width 0
  have h1 := width 1
  have h2 := width 2
  have h3 := width 3
  have h4 := width 4
  change a[0].toNat < 2^52 at h0
  change a[1].toNat < 2^52 at h1
  change a[2].toNat < 2^52 at h2
  change a[3].toNat < 2^52 at h3
  change a[4].toNat < 2^48 at h4
  rw [Field.SquareValue.limbValue_eq]
  simp only [getElem!_pos a (0 : Nat) (by decide), getElem!_pos a (1 : Nat) (by decide),
    getElem!_pos a (2 : Nat) (by decide), getElem!_pos a (3 : Nat) (by decide),
    getElem!_pos a (4 : Nat) (by decide)]
  change ((bswapSpec (bswapSpec _)).toNat * 2^64 + (bswapSpec (bswapSpec _)).toNat) *
    2^128 + (bswapSpec (bswapSpec _)).toNat * 2^64 + (bswapSpec (bswapSpec _)).toNat = _
  simp only [bswapSpec_bswapSpec]
  rw [packWord_toNat _ _ 16, packWord_toNat _ _ 28, packWord_toNat _ _ 40,
    packWord_toNat _ _ 52 h0] <;>
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] <;> omega

theorem packWords_hasBytes {mem : Ram} {dst : BitVec 64} {a : Vector (BitVec 64) 5}
    (width : ∀ i : Fin 5, a[i].toNat < 2^(if i.val = 4 then 48 else 52))
    (words : WordsAt mem dst 64 (packWords a)) (readable : Readable mem dst 32) :
    (⟨dst.toNat, 32⟩ : MemoryRegion).HasBytes mem (Encoding.natToOctets 32 (Field.limbValue a)) := by
  let bytes : ByteArray := ⟨Array.ofFn fun i : Fin 32 => memByte mem (dst + BitVec.ofNat 64 i)⟩
  have size : bytes.size = 32 := Array.size_ofFn ..
  have content : (⟨dst.toNat, 32⟩ : MemoryRegion).HasBytes mem bytes := by
    refine ⟨size, ?_⟩
    intro i
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (readable.present i (by omega))
    change mem[BitVec.ofNat 64 (dst.toNat + i.val)]? = some bytes[i.val]
    rw [ofNat_toNat_add, hb]
    simp only [bytes, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn]
    change some b = some ((mem[dst + BitVec.ofNat 64 i.val]?).getD 0)
    rw [hb]
    rfl
  have val := octetsToNat_extract_eq_words (off := 0) content (by omega)
  have whole : bytes.extract 0 32 = bytes := by rw [← size, ByteArray.extract_zero_size]
  change Encoding.octetsToNat (bytes.extract 0 32) = _ at val
  rw [whole] at val
  have get (i : Fin 4) : scalarWord mem dst (3-i.val) = bswapSpec (packWords a)[i] := by
    change bswapSpec (memLoad mem (wordAddr dst 64 (3-(3-i.val))) 64) = _
    rw [show 3-(3-i.val) = i.val by omega, words i i.isLt]
    rfl
  simp only [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] at val
  have num : Encoding.octetsToNat bytes = Field.limbValue a :=
    val.trans (by
      have correct := packWords_value a width
      dsimp only at correct
      rw [← get 0, ← get 1, ← get 2, ← get 3] at correct
      exact correct)
  have enc := Encoding.natToOctets_octetsToNat bytes
  rw [size, num] at enc
  rwa [enc]

end K256.Proofs.Sec1.Serialize
