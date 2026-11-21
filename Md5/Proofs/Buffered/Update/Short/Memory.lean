import Md5.Proofs.Buffered.Update.Calls
import Md5.Proofs.Buffered.Update.Short.Absorbed

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

theorem short_copy_frame [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {initial s t : RamState}
    (h : UpdatePre kind boundary message input initial)
    (hshort : message.size % 64 + input.size < 64) {ret : BitVec 64}
    (hc : CallSiteResult boundary ret s t) (hsp : stackPtr s = stackPtr initial)
    (hdi : rdi.read s = kind.context initial + BitVec.ofNat 64 (message.size % 64))
    (hdx : MemoryRoutines.rdx.read s = BitVec.ofNat 64 input.size) :
    MemoryWriteFrame s t (shortWriteRegions kind initial message input) := by
  have hctx : (kind.context initial).toNat + 88 < 2^32 := h.contextBounded
  have hcount : (MemoryRoutines.rdx.read s).toNat = input.size := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply hc.agrees.memoryWriteFrame
  intro c hc address hcover
  simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  all_goals try exact hcover.elim
  · refine ⟨⟨(kind.context initial).toNat + message.size % 64, input.size⟩,
      by simp [shortWriteRegions], ?_⟩
    obtain ⟨i, hi, rfl⟩ := hcover
    rw [hcount] at hi
    have hsum : rdi.read s + BitVec.ofNat 64 i =
        kind.context initial + BitVec.ofNat 64 (message.size % 64 + i) := by
      rw [hdi, BitVec.ofNat_add, BitVec.add_assoc]
    change (kind.context initial).toNat + message.size % 64 ≤ _ ∧
      _ < (kind.context initial).toNat + message.size % 64 + input.size
    rw [hsum, toNat_add_ofNat _ _ (by omega)]
    omega
  · refine ⟨UpdateKind.scratchRegion initial, by simp [shortWriteRegions], ?_⟩
    obtain ⟨i, hi, rfl⟩ := hcover
    have hlow := h.stackLow
    have hpush : (pushAddr s).toNat = (stackPtr initial).toNat - 8 := by
      simp only [pushAddr, hsp]
      rw [BitVec.toNat_sub_of_le]
      · rfl
      · rw [BitVec.le_def]
        change 8 ≤ (stackPtr initial).toNat
        omega
    have hhigh := h.stackHigh
    change (stackPtr initial).toNat - 320 ≤ _ ∧
      _ < (stackPtr initial).toNat - 320 + 320
    rw [toNat_add_ofNat _ _ (by unfold userAddressLimit at hhigh; rw [hpush]; omega), hpush]
    omega

theorem short_copy_bytes [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {initial s t : RamState}
    (h : UpdatePre kind boundary message input initial)
    (hshort : message.size % 64 + input.size < 64) {ret : BitVec 64}
    (hc : MemcpySiteResult boundary ret s t) (hext : s.external = initial.external)
    (hdi : rdi.read s = kind.context initial + BitVec.ofNat 64 (message.size % 64))
    (hsi : rsi.read s = (Operand.reg kind.inputRegister : Operand 64).read initial)
    (hdx : MemoryRoutines.rdx.read s = BitVec.ofNat 64 input.size) :
    (⟨(kind.context initial).toNat + message.size % 64, input.size⟩ : MemoryRegion).HasBytes
      t.external input := by
  refine ⟨rfl, ?_⟩
  intro i
  have hcount : (MemoryRoutines.rdx.read s).toNat = input.size := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb := hc.copy i.val (by rw [hcount]; exact i.isLt)
  have hi := h.inputBytes.2 i
  change initial.external[BitVec.ofNat 64
    (((Operand.reg kind.inputRegister : Operand 64).read initial).toNat + i.val)]? = _ at hi
  simp only [hdi, hsi, hext, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, BitVec.add_assoc] at hi hb ⊢
  exact hb.trans hi

theorem short_position_frame [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {initial s t : RamState}
    (h : UpdatePre kind boundary message input initial)
    {changes : List Component} (ha : AgreesExcept changes s t)
    (hm : ∀ c ∈ changes, ∀ address, c.Covers address → address = kind.context initial + 63) :
    MemoryWriteFrame s t (shortWriteRegions kind initial message input) := by
  apply ha.memoryWriteFrame
  intro c hc address hcover
  refine ⟨⟨(kind.context initial).toNat + 63, 1⟩, by simp [shortWriteRegions], ?_⟩
  rw [hm c hc address hcover]
  have hctx : (kind.context initial).toNat + 88 < 2^32 := h.contextBounded
  have he : (kind.context initial + 63).toNat = (kind.context initial).toNat + 63 :=
    toNat_add_ofNat _ 63 (by omega)
  change (kind.context initial).toNat + 63 ≤ _ ∧ _ < (kind.context initial).toNat + 63 + 1
  rw [he]
  omega


theorem short_position_preserves_copy [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {initial s t : RamState}
    (h : UpdatePre kind boundary message input initial)
    (hshort : message.size % 64 + input.size < 64)
    {changes : List Component} (ha : AgreesExcept changes s t)
    (hm : ∀ c ∈ changes, ∀ address, c.Covers address → address = kind.context initial + 63)
    (hb : (⟨(kind.context initial).toNat + message.size % 64, input.size⟩ : MemoryRegion).HasBytes
      s.external input) :
    (⟨(kind.context initial).toNat + message.size % 64, input.size⟩ : MemoryRegion).HasBytes
      t.external input := by
  refine ⟨rfl, fun i ↦ ?_⟩
  refine Eq.trans (ha.byte ?_) (hb.2 i)
  intro c hc hcover
  have hx := congrArg BitVec.toNat (hm c hc _ hcover)
  have hctx : (kind.context initial).toNat + 88 < 2^32 := h.contextBounded
  have hi := i.isLt
  change ((kind.context initial).toNat + message.size % 64 + i.val) % 2^64 =
    (kind.context initial + 63).toNat at hx
  have hright : (kind.context initial + 63).toNat = (kind.context initial).toNat + 63 :=
    toNat_add_ofNat _ 63 (by omega)
  rw [Nat.mod_eq_of_lt (by omega), hright] at hx
  omega

theorem short_absorbed_after_finish [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input : ByteArray} {initial s u t : RamState}
    (h : UpdatePre kind boundary message input initial)
    (hshort : message.size % 64 + input.size < 64) {ret : BitVec 64}
    (hc : MemcpySiteResult boundary ret s u) (hext : s.external = initial.external)
    (hsp : stackPtr s = stackPtr initial)
    (hdi : rdi.read s = kind.context initial + BitVec.ofNat 64 (message.size % 64))
    (hsi : rsi.read s = (Operand.reg kind.inputRegister : Operand 64).read initial)
    (hdx : MemoryRoutines.rdx.read s = BitVec.ofNat 64 input.size)
    {changes : List Component} (ha : AgreesExcept changes u t)
    (hm : ∀ c ∈ changes, ∀ address, c.Covers address → address = kind.context initial + 63)
    (hp : (Operand.mem (kind.context initial + 63) : Operand 8).read t =
      BitVec.ofNat 8 (message.size % 64 + input.size)) :
    Absorbed (kind.context initial) (message ++ input) t := by
  have hf := memoryWriteFrame_trans
    (short_copy_frame h hshort hc.toCallSiteResult hsp hdi hdx) (short_position_frame h ha hm)
  apply absorbed_append_short_of_frame h hshort
  · intro address hout
    exact (hf address hout).trans (congrArg (fun m : Ram ↦ m[address]?) hext)
  · exact short_position_preserves_copy h hshort ha hm
      (short_copy_bytes h hshort hc hext hdi hsi hdx)
  · exact hp

end Md5.Proofs.Buffered
