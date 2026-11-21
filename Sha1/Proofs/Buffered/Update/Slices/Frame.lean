import Sha1.Proofs.Buffered.Update.Slices.Copy

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 2048 in
private theorem memory_changes {s : RamState} {c : Component} {x : BitVec 64}
    (hc : c ∈ UpdateKind.updateFinalize.changes s) (hx : c.Covers x) :
    (Component.mem (UpdateKind.updateFinalize.context s) 92).Covers x ∨
    (Component.mem (BitVec.ofNat 64 ((stackPtr s).toNat - 344)) 344).Covers x := by
  simp only [UpdateKind.changes, UpdateKind.workRegisters, List.map_cons, List.map_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((h | h | h | h | h | h | h | h | h | h | h) | (h | h | h | h)) | h | h
  all_goals subst c
  all_goals first | exact hx.elim | exact Or.inl hx | exact Or.inr hx

theorem inputBytes_of_agrees [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre .updateFinalize boundary message input s)
    (ha : AgreesExcept (UpdateKind.updateFinalize.changes s) s u) :
    (UpdateKind.updateFinalize.inputRegion s input).HasBytes u.external input := by
  have hhigh : (stackPtr s).toNat + 0xd8 + 92 < 2^32 := h.stackHigh
  have hlow := h.stackLow
  have hctx : (UpdateKind.updateFinalize.context s).toNat = (stackPtr s).toNat + 0xd8 :=
    toNat_add_ofNat _ 0xd8 (by omega)
  let r := UpdateKind.updateFinalize.inputRegion s input
  have hb : r.start + input.size < 2^32 := h.inputBounded
  refine ⟨rfl, fun i ↦ Eq.trans (ha.byte ?_) (h.inputBytes.2 i)⟩
  intro c hc hcov
  have hi := i.isLt
  let a := BitVec.ofNat 64 (r.start + i.val)
  have han : a.toNat = r.start + i.val := by
    apply Nat.mod_eq_of_lt
    omega
  have hin : r.Contains a.toNat := by rw [han]; exact ⟨by omega, by change _ < r.start + input.size; omega⟩
  rcases memory_changes hc hcov with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · apply h.inputContext _ hin
    change (UpdateKind.updateFinalize.context s).toNat ≤ a.toNat ∧ a.toNat < (UpdateKind.updateFinalize.context s).toNat + 92
    change a = _ at he
    rw [he, toNat_add_ofNat _ _ (by omega)]
    omega
  · apply h.inputScratch _ hin
    change (stackPtr s).toNat - 344 ≤ a.toNat ∧ a.toNat < (stackPtr s).toNat - 344 + 344
    change a = _ at he
    rw [he, ← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega

set_option maxRecDepth 2048 in
theorem copy_agrees [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u v : RamState} {ret : BitVec 64} {dst len : Nat}
    (h : UpdatePre .updateFinalize boundary message input s) (hp : MemcpySiteResult boundary ret u v)
    (hsp : stackPtr u = stackPtr s)
    (hdi : rdi.read u = UpdateKind.updateFinalize.context s + BitVec.ofNat 64 dst)
    (hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 len) (hbound : dst + len ≤ 92) :
    AgreesExcept (UpdateKind.updateFinalize.changes s) u v := by
  have hlo := h.stackLow
  have hlen : (MemoryRoutines.rdx.read u).toNat = len := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply hp.agrees.widen
  · intro c hc hm
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | contradiction | simp [UpdateKind.changes]
  · intro x c hc hcov
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    · obtain ⟨i, hi, rfl⟩ := hcov
      refine ⟨_, show Component.mem (UpdateKind.updateFinalize.context s) 92 ∈ _ by simp [UpdateKind.changes],
        dst + i, by omega, ?_⟩
      rw [hdi, BitVec.add_assoc, BitVec.ofNat_add]
    · obtain ⟨i, hi, rfl⟩ := hcov
      refine ⟨_, show Component.mem (BitVec.ofNat 64 ((stackPtr s).toNat - 344)) 344 ∈ _ by simp [UpdateKind.changes],
        336 + i, by omega, ?_⟩
      have he : pushAddr u = BitVec.ofNat 64 ((stackPtr s).toNat - 8) := by
        apply BitVec.eq_of_toNat_eq
        rw [pushAddr, hsp, BitVec.toNat_sub_of_le (by change 8 ≤ (stackPtr s).toNat; omega),
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := (stackPtr s).isLt; omega)]
        rfl
      rw [he, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
      congr 1
      omega

end Sha1.Proofs.Buffered.Update.Slices
