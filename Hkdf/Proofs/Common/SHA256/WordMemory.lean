import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.Field.Montgomery.Schoolbook.Compose

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256

open X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Field.Montgomery.Schoolbook

theorem memLoad_extractLsb (memory : Ram) (address : BitVec 64)
    {width len offset : Nat} (span : 8*offset + len ≤ width) (align : len % 8 = 0) :
    (memLoad memory address width).extractLsb' (8*offset) len =
      memLoad memory (address + BitVec.ofNat 64 offset) len := by
  apply storedByte_injective align
  intro i hi
  have extract : storedByte ((memLoad memory address width).extractLsb' (8*offset) len) i =
      storedByte (memLoad memory address width) (offset+i) := by
    simp only [storedByte_eq_extract]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_extractLsb', decide_eq_true hk, Bool.true_and,
      decide_eq_true (by omega : 8*i+k < len)]
    congr 1
    omega
  rw [extract, storedByte_memLoad _ _ _ (by omega), storedByte_memLoad _ _ _ hi,
    BitVec.add_assoc, ← BitVec.ofNat_add]

theorem memLoad64_eq_words32 (memory : Ram) (address : BitVec 64) :
    memLoad memory address 64 =
      memLoad memory (address+4) 32 ++ memLoad memory address 32 := by
  have high := memLoad_extractLsb memory address (width := 64) (len := 32) (offset := 4)
    (by decide) (by decide)
  have low := memLoad_extractLsb memory address (width := 64) (len := 32) (offset := 0)
    (by decide) (by decide)
  have low' : (memLoad memory address 64).extractLsb' 0 32 = memLoad memory address 32 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using low
  change (memLoad memory address 64).extractLsb' 32 32 = memLoad memory (address + 4) 32 at high
  rw [← low', ← high]
  exact (BitVec.extractLsb'_append_extractLsb' (w := 32) (len := 32)
    (x := memLoad memory address 64)).symm

theorem memLoad32_memStore64_high (memory : Ram) (address : BitVec 64) (value : BitVec 64) :
    memLoad (memStore memory address value) (address+4) 32 = value.extractLsb' 32 32 := by
  have high := memLoad_extractLsb (memStore memory address value) address
    (width := 64) (len := 32) (offset := 4) (by decide) (by decide)
  rw [memLoad_memStore _ _ (by decide) (by decide)] at high
  exact high.symm

theorem memLoad32_store32_aligned (memory : Ram) (base : BitVec 64) (value : BitVec 32)
    {offset index : Nat} (offsetAlign : offset % 4 = 0) (indexAlign : index % 4 = 0)
    (offsetBound : offset + 4 ≤ 2^64) (indexBound : index + 4 ≤ 2^64) :
    memLoad (memStore memory (base + BitVec.ofNat 64 offset) value)
      (base + BitVec.ofNat 64 index) 32 =
      if index = offset then value else memLoad memory (base + BitVec.ofNat 64 index) 32 := by
  by_cases he : index = offset
  · subst index
    rw [ite_eq_left rfl]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · rw [ite_eq_right he]
    apply memLoad_memStore_rangeApart
    exact RangeApart.offsets base offsetBound indexBound (by omega)

theorem memLoad32_store64_aligned (memory : Ram) (base : BitVec 64) (value : BitVec 64)
    {offset index : Nat} (offsetAlign : offset % 4 = 0) (indexAlign : index % 4 = 0)
    (offsetBound : offset + 8 ≤ 2^64) (indexBound : index + 4 ≤ 2^64) :
    memLoad (memStore memory (base + BitVec.ofNat 64 offset) value)
      (base + BitVec.ofNat 64 index) 32 =
      if index = offset then value.setWidth 32 else
      if index = offset+4 then value.extractLsb' 32 32 else
      memLoad memory (base + BitVec.ofNat 64 index) 32 := by
  by_cases hlo : index = offset
  · subst index
    rw [ite_eq_left rfl]
    exact Hkdf.Proofs.Common.EffectCompose.memLoad_memStore_narrow _ _ _ (by decide) (by decide) (by decide)
  · rw [ite_eq_right hlo]
    by_cases hhi : index = offset+4
    · rw [ite_eq_left hhi, hhi, BitVec.ofNat_add, ← BitVec.add_assoc]
      exact memLoad32_memStore64_high _ _ _
    · rw [ite_eq_right hhi]
      apply memLoad_memStore_rangeApart
      exact RangeApart.offsets base offsetBound indexBound (by omega)

end Hkdf.Proofs.Common.SHA256
