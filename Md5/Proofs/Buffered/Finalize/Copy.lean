import Md5.Proofs.Buffered.Invariant
import X86Proofs.Program.ReadWrite.Bytes

namespace Md5.Proofs.Buffered.Finalize

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem absorbed_of_copy {src dst : BitVec 64} {message : ByteArray} {s t : RamState}
    (h : Absorbed src message s)
    (hc : ∀ i < 88, t.external[dst + BitVec.ofNat 64 i]? =
      s.external[src + BitVec.ofNat 64 i]?) : Absorbed dst message t := by
  have hload (offset n : Nat) (ho : offset + n / 8 ≤ 88) :
      memLoad t.external (dst + BitVec.ofNat 64 offset) n =
        memLoad s.external (src + BitVec.ofNat 64 offset) n := by
    apply memLoad_congr
    intro i hi
    change (t.external[dst + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[src + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [hc _ (by omega)]
  refine ⟨⟨h.buffer.1, ?_⟩, ⟨h.tail.1, ?_⟩, ?_, ?_⟩
  · intro i
    have hi : i.val < 16 := by
      simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
    have hh := hc (64 + i.val) (by omega)
    have hb := h.buffer.2 i
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_assoc] at hb hh ⊢
    exact hh.trans hb
  · intro i
    have hi : i.val < message.size % 64 := by
      simpa only [size_tailBytes] using i.isLt
    have hh := hc i.val (by omega)
    have ht := h.tail.2 i
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at ht ⊢
    exact hh.trans ht
  · exact (hload 63 8 (by decide)).trans h.position
  · exact (hload 80 64 (by decide)).trans h.blocks

end Md5.Proofs.Buffered.Finalize
