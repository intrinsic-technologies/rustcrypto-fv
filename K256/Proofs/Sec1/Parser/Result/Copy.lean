import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Sec1.Parser.Result

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine

theorem memLoad_memCopy {len off width : Nat} (mem : Ram) (dst src : BitVec 64)
    (bound : len ≤ 2 ^ 64) (inside : off + width / 8 ≤ len) :
    memLoad (memCopy mem dst src len) (dst + BitVec.ofNat 64 off) width =
      memLoad mem (src + BitVec.ofNat 64 off) width := by
  apply memLoad_congr
  intro i hi
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hi' : off + i < (8 * len) / 8 := by omega
  change ((memStore mem dst (memLoad mem src (8 * len)))[dst + BitVec.ofNat 64 (off + i)]?).getD 0 = _
  rw [memStore_getElem?_self_of_le _ _ _ (by omega) _ hi']
  exact storedByte_memLoad mem src (off + i) hi'

theorem output_load {off width : Nat} (inside : off + width / 8 ≤ 88)
    (mem : Ram) (sp out : BitVec 64) (flag : BitVec 8) :
    let staged := memCopy mem (sp + 72) (sp + 160) 88
    let selected := memStore staged (sp + 160) flag
    let copied := memCopy selected (out + 8) (sp + 72) 88
    memLoad copied (out + 8 + BitVec.ofNat 64 off) width =
      memLoad mem (sp + 160 + BitVec.ofNat 64 off) width := by
  dsimp only
  rw [memLoad_memCopy _ _ _ (by decide) (by omega)]
  rw [memLoad_memStore_of_rangeApart]
  · exact memLoad_memCopy _ _ _ (by decide) (by omega)
  · apply RangeApart.right_sub (off := off) (m := 88) _ inside
    exact RangeApart.of_offsets (x := sp) (c := 160) (d := 72) rfl rfl (by decide)

end K256.Proofs.Sec1.Parser.Result
