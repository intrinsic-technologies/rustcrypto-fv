import Sha1.Proofs.Buffered.Update.Slices.Frame
import Sha1.Proofs.Buffered.Update.Slices.Mathematics

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Wrapper.Absorb

theorem buffer_after_copy [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u v : RamState} {ret : BitVec 64} {len : Nat}
    (h : UpdatePre .updateFinalize boundary message input s)
    (hext : u.external = s.external) (hsp : stackPtr u = stackPtr s)
    (hdi : rdi.read u = UpdateKind.updateFinalize.context s + BitVec.ofNat 64 (message.size % 64))
    (hsi : rsi.read u = (Operand.reg 14 : Operand 64).read s)
    (hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 len)
    (hlen : len ≤ input.size) (hfit : message.size % 64 + len ≤ 64)
    (hc : MemcpySiteResult boundary ret u v) :
    let base := UpdateKind.updateFinalize.context s
    let bytes := tailBytes message ++ input.extract 0 len
    (⟨base.toNat, bytes.size⟩ : MemoryRegion).HasBytes v.external bytes ∧
    (⟨(base + 72).toNat, 20⟩ : MemoryRegion).HasBytes v.external (absorbedStateBytes message) ∧
    (Operand.mem (base + 64) : Operand 64).read v = BitVec.ofNat 64 (message.size / 64) := by
  intro base bytes
  have hhigh : (stackPtr s).toNat + 216 + 92 < 2^32 := h.stackHigh
  have hbase : base.toNat = (stackPtr s).toNat + 216 := toNat_add_ofNat _ 216 (by omega)
  have hcount : (MemoryRoutines.rdx.read u).toNat = len := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hslot : (pushAddr u).toNat = (stackPtr s).toNat - 8 := by
    have hlo := h.stackLow
    rw [pushAddr, hsp, BitVec.toNat_sub_of_le (by change 8 ≤ (stackPtr s).toNat; omega)]
    rfl
  have preserve {i : Nat} (hi : i < 92)
      (hout : i < message.size % 64 ∨ message.size % 64 + len ≤ i) :
      v.external[base + BitVec.ofNat 64 i]? = s.external[base + BitVec.ofNat 64 i]? := by
    rw [← hext]
    apply hc.agrees.byte
    intro c hm hx
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hx.elim
    · obtain ⟨j, hj, he⟩ := hx
      rw [hcount] at hj
      rw [hdi, BitVec.add_assoc, ← BitVec.ofNat_add] at he
      change base + _ = base + _ at he
      have heq := congrArg BitVec.toNat he
      rw [toNat_add_ofNat _ i (by omega), toNat_add_ofNat _ _ (by omega)] at heq
      omega
    · obtain ⟨j, hj, he⟩ := hx
      have heq := congrArg BitVec.toNat he
      rw [toNat_add_ofNat _ i (by omega), toNat_add_ofNat _ j (by omega)] at heq
      omega
  refine ⟨hasBytes_append ?_ ?_, ?_, ?_⟩
  · refine ⟨rfl, fun i ↦ Eq.trans ?_ (h.absorbed.tail.2 i)⟩
    have hi : i.val < message.size % 64 := (size_tailBytes message) ▸ i.isLt
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      preserve (i := i.val) (by omega) (.inl hi)
  · rw [size_tailBytes]
    refine ⟨rfl, fun i ↦ ?_⟩
    have hi := i.isLt
    simp only [ByteArray.size_extract, Nat.min_eq_left hlen, Nat.sub_zero] at hi
    have hcop := hc.copy i.val (by omega)
    have hin := h.inputBytes.2 ⟨i.val, by omega⟩
    change s.external[BitVec.ofNat 64 (((Operand.reg 14 : Operand 64).read s).toNat + i.val)]? = _ at hin
    simp only [ByteArray.getElem_extract, Nat.zero_add, BitVec.ofNat_add, BitVec.ofNat_toNat,
      BitVec.setWidth_eq, hdi, hsi, hext, BitVec.add_assoc] at hcop hin ⊢
    exact hcop.trans hin
  · refine ⟨h.absorbed.state.1, fun i ↦ Eq.trans ?_ (h.absorbed.state.2 i)⟩
    have hi : i.val < 20 := (absorbedStateBytes_size message) ▸ i.isLt
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat,
      BitVec.add_assoc] using preserve (i := 72 + i.val) (by omega) (by omega)
  · rw [← h.absorbed.blocks]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    change v.external[base + 64 + BitVec.ofNat 64 i]? = s.external[base + 64 + BitVec.ofNat 64 i]?
    simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
      preserve (i := 64 + i) (by omega) (by omega)

end Sha1.Proofs.Buffered.Update.Slices
