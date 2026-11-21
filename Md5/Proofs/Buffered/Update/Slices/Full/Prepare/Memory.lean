import Md5.Proofs.Buffered.Update.Slices.Full.Prepare.Increment
import Md5.Proofs.Buffered.Update.Slices.Full.Prepare.Clear
import Md5.Proofs.Buffered.Update.Preservation
import Md5.Proofs.Buffered.Update.Preservation.Compression

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem fill_increment_preserves {variant : Bool} [Bindings] {boundary : ReturnBoundary}
    {message input bytes : ByteArray} {s u v : RamState}
    (h : UpdatePre (kind variant) boundary message input s) (hsp : stackPtr u = stackPtr s)
    (he : (fillIncrementEffect variant u).Holds u v) {offset : Nat}
    (hoff : offset + bytes.size ≤ 80)
    (hb : (⟨((kind variant).context s).toNat + offset, bytes.size⟩ : MemoryRegion).HasBytes
      u.external bytes) :
    (⟨((kind variant).context s).toNat + offset, bytes.size⟩ : MemoryRegion).HasBytes
      v.external bytes := by
  apply h.bytes_before_counter_of_agrees he.agrees ?_ hoff hb
  intro c hc address hcover
  rw [fillIncrementEffect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · have heq : stackPtr u + 272 = (kind variant).context s + 80 := by
      rw [hsp]
      rw [kind_context]
      change stackPtr s + 272 = stackPtr s + 192 + 80
      rw [BitVec.add_assoc]
      rfl
    simpa only [heq] using hcover
  · exact hcover.elim
  · exact hcover.elim

set_option maxRecDepth 4096 in
theorem fill_clear_preserves {variant : Bool} [Bindings] {boundary : ReturnBoundary}
    {message input : ByteArray} {buffer : Standards.RFC.MD5.Buffer} {s u v : RamState}
    (h : UpdatePre (kind variant) boundary message input s) (hsp : stackPtr u = stackPtr s)
    (he : (fillClearEffect variant u).Holds u v)
    (hb : (⟨((kind variant).context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      u.external ⟨buffer.toBytes.toArray⟩) :
    (⟨((kind variant).context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      v.external ⟨buffer.toBytes.toArray⟩ ∧
    (Operand.mem ((kind variant).context s + 80) : Operand 64).read v =
      (Operand.mem ((kind variant).context s + 80) : Operand 64).read u := by
  apply h.state_of_tail_frame ?_ hb
  apply he.agrees.memoryWriteFrame
  intro c hc address hcover
  rw [fillClearEffect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · refine ⟨⟨((kind variant).context s).toNat, 64⟩, by simp, ?_⟩
    have hctx : ((kind variant).context s).toNat + 88 < 2^32 := h.contextBounded
    have heq : stackPtr u + 255 = (kind variant).context s + 63 := by
      rw [hsp]
      rw [kind_context]
      change stackPtr s + 255 = stackPtr s + 192 + 63
      rw [BitVec.add_assoc]
      rfl
    rw [heq] at hcover
    change (Component.mem ((kind variant).context s + 63#64) 1).Covers address at hcover
    have hx := contains_of_mem_covers
      (region := (⟨((kind variant).context s).toNat + 63, 1⟩ : MemoryRegion))
      (by change ((kind variant).context s).toNat + 63 + 1 < 2^32; omega)
      (by simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hcover)
    dsimp only [MemoryRegion.Contains] at hx ⊢
    omega
  · exact hcover.elim

end Md5.Proofs.Buffered.Update.Slices
