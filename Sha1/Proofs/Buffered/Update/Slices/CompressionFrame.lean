import Sha1.Proofs.Buffered.Update.Slices.Full.Compress
import Sha1.Proofs.Buffered.Finalize.Digest.Prepare

namespace Sha1.Proofs.Buffered.Update.Slices.Full

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered.Finalize.Digest (read_of_agrees covers_apart)
open Sha1.Proofs.Buffered.DigestPrepare (writableRange_of_region)

theorem stack_same {s u : RamState}
    (h : AgreesExcept (UpdateKind.updateFinalize.changes s) s u) :
    stackPtr u = stackPtr s :=
  h.read (n := 64) (r := 4) (by simp [UpdateKind.changes, UpdateKind.workRegisters])

theorem counter_address (s : RamState) :
    stackPtr s + 0x118 = UpdateKind.updateFinalize.context s + 64 := by
  rw [UpdateKind.context, BitVec.add_assoc]
  rfl

private theorem context_change {s : RamState} {address : BitVec 64} {start len : Nat}
    (hbound : start + len ≤ 92)
    (hc : (Component.mem (UpdateKind.updateFinalize.context s + BitVec.ofNat 64 start) len).Covers
      address) :
    ∃ c ∈ UpdateKind.updateFinalize.changes s, c.Covers address := by
  obtain ⟨i, hi, rfl⟩ := hc
  refine ⟨.mem (UpdateKind.updateFinalize.context s) 92, by simp [UpdateKind.changes],
    start + i, by omega, ?_⟩
  rw [BitVec.ofNat_add, BitVec.add_assoc]

theorem counter_writable [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} (h : UpdatePre .updateFinalize boundary message input s)
    (ha : AgreesExcept (UpdateKind.updateFinalize.changes s) s u) :
    MemoryRoutines.WritableRange u (stackPtr u + 0x118) 8 := by
  rw [stack_same ha, counter_address]
  have hhigh : (stackPtr s).toNat + 0xd8 + 92 < 2^32 := h.stackHigh
  have hctx : (UpdateKind.updateFinalize.context s).toNat = (stackPtr s).toNat + 0xd8 :=
    toNat_add_ofNat _ 0xd8 (by omega)
  have haddr := toNat_add_ofNat (UpdateKind.updateFinalize.context s) 64 (by rw [hctx]; omega)
  have hb : (UpdateKind.updateFinalize.contextRegion s).Bounded := by
    change (UpdateKind.updateFinalize.context s).toNat + 92 < 2^32
    omega
  refine writableRange_of_region hb (Update.allocated_of_agrees ha h.contextAllocated)
    h.contextAvoids ?_ ?_
  · change (UpdateKind.updateFinalize.context s).toNat ≤
      (UpdateKind.updateFinalize.context s + BitVec.ofNat 64 64).toNat
    rw [haddr]
    omega
  · change (UpdateKind.updateFinalize.context s + BitVec.ofNat 64 64).toNat + 8 ≤
      (UpdateKind.updateFinalize.context s).toNat + 92
    rw [haddr]
    omega

theorem counter_agrees {s u v : RamState} (hsp : stackPtr u = stackPtr s)
    (h : AgreesExcept [.mem (stackPtr u + 0x118) 8, .flags, .rip] u v) :
    AgreesExcept (UpdateKind.updateFinalize.changes s) u v := by
  apply h.widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · cases hm
    · simp [UpdateKind.changes]
    · simp [UpdateKind.changes]
  · intro address c hc hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · rw [hsp, counter_address] at hx
      exact context_change (start := 64) (by decide) hx
    · exact hx.elim
    · exact hx.elim

theorem compression_agrees {s u v : RamState}
    (h : AgreesExcept (compressChanges s) u v) :
    AgreesExcept (UpdateKind.updateFinalize.changes s) u v := by
  apply h.widen
  · intro c hc hm
    simp only [compressChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact Bool.noConfusion hm | simp [UpdateKind.changes]
  · intro address c hc hx
    simp only [compressChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hx.elim
    · exact context_change (start := 72) (by decide) hx
    · exact ⟨_, by simp [UpdateKind.changes], hx⟩

theorem counter_preserved {s u v : RamState}
    (hlow : 344 ≤ (stackPtr s).toNat)
    (hhigh : (stackPtr s).toNat + 0xd8 + 92 < 2^32)
    (h : AgreesExcept (compressChanges s) u v) :
    (Operand.mem (UpdateKind.updateFinalize.context s + 64) : Operand 64).read v =
      (Operand.mem (UpdateKind.updateFinalize.context s + 64) : Operand 64).read u := by
  apply read_of_agrees h
  intro i hi c hc hx
  simp only [compressChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hx.elim
  · exact covers_apart (base := UpdateKind.updateFinalize.context s) (a := 72) (b := 64)
      (len := 20) (count := 8) rfl hi (by decide) (by decide) (Or.inr (by decide)) hx
  · obtain ⟨j, hj, he⟩ := hx
    rw [← counter_address, BitVec.add_assoc, ← BitVec.ofNat_add] at he
    change stackPtr s + (BitVec.ofNat 64 280 + BitVec.ofNat 64 i) = _ at he
    rw [← BitVec.ofNat_add] at he
    have hn := congrArg BitVec.toNat he
    rw [toNat_add_ofNat _ _ (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
    omega

theorem counter_preserves_bytes {u v : RamState} {base : BitVec 64}
    {off len : Nat} {bytes : ByteArray}
    (ha : AgreesExcept [.mem (base + 64) 8, .flags, .rip] u v)
    (hb : (⟨(base + BitVec.ofNat 64 off).toNat, len⟩ : MemoryRegion).HasBytes u.external bytes)
    (hbound : off + len ≤ 2^64) (hapart : off + len ≤ 64 ∨ 72 ≤ off) :
    (⟨(base + BitVec.ofNat 64 off).toNat, len⟩ : MemoryRegion).HasBytes v.external bytes := by
  refine ⟨hb.1, fun i ↦ (ha.byte ?_).trans (hb.2 i)⟩
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · apply Finalize.Digest.covers_apart (base := base) (a := 64) (b := off) (i := i.val) (count := len)
    · simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · have hlen : bytes.size = len := hb.1
      omega
    · decide
    · exact hbound
    · omega
  · exact id
  · exact id

end Sha1.Proofs.Buffered.Update.Slices.Full
