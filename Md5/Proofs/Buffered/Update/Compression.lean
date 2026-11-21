import Md5.Proofs.Buffered.Update.Memory
import Md5.Proofs.Buffered.Update.Algebra
import Md5.Proofs.Buffered.FinalizeReset.CompressCall

namespace Md5.Proofs.Buffered

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

namespace UpdatePre

theorem compressionOutputRegion [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {s u : RamState}
    (h : UpdatePre kind boundary message input s)
    (hdi : u.regValue .rdi = kind.context s + 64) :
    Compress.outputRegion u = ⟨(kind.context s).toNat + 64, 16⟩ := by
  have hh : (kind.context s).toNat + 88 < 2^32 := h.contextBounded
  change (⟨(u.regValue .rdi).toNat, 16⟩ : MemoryRegion) = _
  rw [hdi]
  congr 1
  exact toNat_add_ofNat _ 64 (by omega)

set_option maxRecDepth 4096 in
theorem compressionPre [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input blocks : ByteArray} {buffer : Standards.RFC.MD5.Buffer} {s u : RamState}
    {changes : List Component} (h : UpdatePre kind boundary message input s)
    (ha : AgreesExcept changes s u) (hsp : stackPtr u = stackPtr s)
    (hdi : u.regValue .rdi = kind.context s + 64)
    (hi : Call.Compress.ValidInput u blocks)
    (hb : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      u.external ⟨buffer.toBytes.toArray⟩)
    (his : (Compress.inputRegion u blocks).Disjoint (UpdateKind.scratchRegion s))
    (hib : (Compress.inputRegion u blocks).Disjoint
      (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion)) :
    FinalizeReset.CompressCall.Pre buffer blocks u := by
  have hout := h.compressionOutputRegion hdi
  have hctx := h.context_toNat
  have hlo := h.stackLow
  have hhi : (kind.context s).toNat + 88 < 2^32 := h.contextBounded
  have hscratch : FinalizeReset.CompressCall.scratchRegion u = UpdateKind.scratchRegion s := by
    change (⟨(stackPtr u).toNat - 320, 320⟩ : MemoryRegion) =
      ⟨(stackPtr s).toNat - 320, 320⟩
    rw [hsp]
  refine ⟨hi, ?_, hsp ▸ h.stackLow, ?_, hsp ▸ h.stackAligned, ?_,
    hscratch ▸ his, ?_, hout ▸ hib, ?_⟩
  · change (Compress.outputRegion u).Bounded ∧ _
    rw [hout]
    exact ⟨by change (kind.context s).toNat + 64 + 16 < 2^32; omega, hb⟩
  · rw [hsp]
    change (stackPtr s).toNat < 2^32
    omega
  · rw [hsp]
    exact h.scratchWritable_of_agrees ha 320 320 (by decide) (by decide)
  · rw [hout, hscratch]
    intro address hbuffer hstack
    change (kind.context s).toNat + 64 ≤ address ∧
      address < (kind.context s).toNat + 64 + 16 at hbuffer
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + 320 at hstack
    omega
  · rw [hout]
    intro address hmem hp
    apply h.contextAvoids address ?_ hp
    change (kind.context s).toNat ≤ address.toNat ∧
      address.toNat < (kind.context s).toNat + 88
    change (kind.context s).toNat + 64 ≤ address.toNat ∧
      address.toNat < (kind.context s).toNat + 64 + 16 at hmem
    omega

set_option maxRecDepth 4096 in
theorem compressionPre_context [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input blocks : ByteArray} {buffer : Standards.RFC.MD5.Buffer} {s u : RamState}
    {changes : List Component} (h : UpdatePre kind boundary message input s)
    (ha : AgreesExcept changes s u) (hsp : stackPtr u = stackPtr s)
    (hdi : u.regValue .rdi = kind.context s + 64)
    (hsi : u.regValue .rsi = kind.context s) (hdx : u.regValue .rdx = 1)
    (hsize : blocks.size = 64)
    (hi : (⟨(kind.context s).toNat, 64⟩ : MemoryRegion).HasBytes u.external blocks)
    (hb : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      u.external ⟨buffer.toBytes.toArray⟩) :
    FinalizeReset.CompressCall.Pre buffer blocks u := by
  have hctx := h.context_toNat
  have hlo := h.stackLow
  have hhi : (kind.context s).toNat + 88 < 2^32 := h.contextBounded
  have hir : Compress.inputRegion u blocks = ⟨(kind.context s).toNat, 64⟩ := by
    simp only [Compress.inputRegion, registerRegion, hsi, hsize]
  refine h.compressionPre ha hsp hdi ?_ hb ?_ ?_
  · change (Compress.inputRegion u blocks).Bounded ∧
      (Compress.inputRegion u blocks).HasLength (64 * (u.regValue .rdx).toNat) ∧ _
    rw [hir, hdx]
    exact ⟨by change (kind.context s).toNat + 64 < 2^32; omega, rfl, hi⟩
  · rw [hir]
    intro address hin hs
    change (kind.context s).toNat ≤ address ∧ address < (kind.context s).toNat + 64 at hin
    change (stackPtr s).toNat - 320 ≤ address ∧
      address < (stackPtr s).toNat - 320 + 320 at hs
    omega
  · rw [hir]
    intro address hin hb
    change (kind.context s).toNat ≤ address ∧ address < (kind.context s).toNat + 64 at hin
    change (kind.context s).toNat + 64 ≤ address ∧
      address < (kind.context s).toNat + 64 + 16 at hb
    omega

set_option maxRecDepth 4096 in
theorem compressionPre_input [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input blocks : ByteArray} {buffer : Standards.RFC.MD5.Buffer} {s u : RamState}
    {changes : List Component} (h : UpdatePre kind boundary message input s)
    (ha : AgreesExcept changes s u) (hsp : stackPtr u = stackPtr s)
    (hdi : u.regValue .rdi = kind.context s + 64) (offset : Nat)
    (hsi : (u.regValue .rsi).toNat = (kind.inputRegion s input).start + offset)
    (hsize : offset + blocks.size ≤ input.size)
    (hdx : 64 * (u.regValue .rdx).toNat = blocks.size)
    (hi : (⟨(kind.inputRegion s input).start + offset, blocks.size⟩ : MemoryRegion).HasBytes
      u.external blocks)
    (hb : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      u.external ⟨buffer.toBytes.toArray⟩) :
    FinalizeReset.CompressCall.Pre buffer blocks u := by
  have hir : Compress.inputRegion u blocks =
      ⟨(kind.inputRegion s input).start + offset, blocks.size⟩ := by
    simp only [Compress.inputRegion, registerRegion, hsi]
  have hin (address : Nat) (ha : (Compress.inputRegion u blocks).Contains address) :
      (kind.inputRegion s input).Contains address := by
    rw [hir] at ha
    change (kind.inputRegion s input).start + offset ≤ address ∧
      address < (kind.inputRegion s input).start + offset + blocks.size at ha
    change (kind.inputRegion s input).start ≤ address ∧
      address < (kind.inputRegion s input).start + input.size
    omega
  refine h.compressionPre ha hsp hdi ?_ hb ?_ ?_
  · change (Compress.inputRegion u blocks).Bounded ∧
      (Compress.inputRegion u blocks).HasLength (64 * (u.regValue .rdx).toNat) ∧ _
    rw [hir, hdx]
    refine ⟨?_, rfl, hi⟩
    have hbnd : (kind.inputRegion s input).start + input.size < 2^32 := h.inputBounded
    change (kind.inputRegion s input).start + offset + blocks.size < 2^32
    omega
  · intro address hblock hs
    exact h.inputScratch address (hin address hblock) hs
  · intro address hblock hout
    apply h.inputContext address (hin address hblock)
    change (kind.context s).toNat ≤ address ∧ address < (kind.context s).toNat + 88
    change (kind.context s).toNat + 64 ≤ address ∧
      address < (kind.context s).toNat + 64 + 16 at hout
    omega

set_option maxRecDepth 4096 in
theorem compressionPre_fullInput [Bindings] {kind : UpdateKind} {boundary : ReturnBoundary}
    {message input : ByteArray} {buffer : Standards.RFC.MD5.Buffer} {s u : RamState}
    (h : UpdatePre kind boundary message input s)
    (ha : AgreesExcept (kind.changes s) s u) (hsp : stackPtr u = stackPtr s)
    (hdi : u.regValue .rdi = kind.context s + 64) (offset : Nat)
    (hoffset : offset ≤ input.size)
    (hsi : u.regValue .rsi =
      (Operand.reg kind.inputRegister : Operand 64).read s + BitVec.ofNat 64 offset)
    (hdx : u.regValue .rdx = BitVec.ofNat 64 ((input.size - offset) / 64))
    (hb : (⟨(kind.context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      u.external ⟨buffer.toBytes.toArray⟩) :
    FinalizeReset.CompressCall.Pre buffer (fullBytes (input.extract offset input.size)) u := by
  have hinput : ((Operand.reg kind.inputRegister : Operand 64).read s).toNat + input.size < 2^32 :=
    h.inputBounded
  have hsize : (input.extract offset input.size).size = input.size - offset := by
    simp only [ByteArray.size_extract, Nat.min_self]
  have hi := hasBytes_extract (hasBytes_extract (h.inputBytes_of_agrees ha) offset input.size)
    0 ((input.extract offset input.size).size / 64 * 64)
  refine h.compressionPre_input ha hsp hdi offset ?_ ?_ ?_ ?_ hb
  · rw [hsi]
    exact toNat_add_ofNat _ _ (by omega)
  · rw [size_fullBytes, hsize]
    omega
  · rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), size_fullBytes, hsize]
    omega
  · simpa only [fullBytes, Nat.add_zero] using hi

end UpdatePre

set_option maxRecDepth 4096 in
theorem FinalizeReset.CompressCall.Post.update_agrees [Bindings] {kind : UpdateKind}
    {boundary : ReturnBoundary} {message input blocks : ByteArray} {buffer : Standards.RFC.MD5.Buffer}
    {initial s t : RamState} (h : UpdatePre kind boundary message input initial)
    {ret : BitVec 64} (hr : FinalizeReset.CompressCall.Post boundary ret buffer blocks s t)
    (hsp : stackPtr s = stackPtr initial)
    (hdi : s.regValue .rdi = kind.context initial + 64) :
    AgreesExcept (kind.changes initial) s t := by
  have hs : stackPtr s - 320 =
      BitVec.ofNat 64 (UpdateKind.scratchRegion initial).start := by
    rw [hsp]
    change stackPtr initial - 320 = BitVec.ofNat 64 ((stackPtr initial).toNat - 320)
    have hn : (stackPtr initial - 320).toNat = (stackPtr initial).toNat - 320 :=
      BitVec.toNat_sub_of_le h.stackLow
    rw [← hn, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  apply hr.agrees.widen
  · intro c hc hm
    simp only [FinalizeReset.CompressCall.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [UpdateKind.changes, Component.isMem]
  · intro address c hc hcover
    simp only [FinalizeReset.CompressCall.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    · refine ⟨.mem (kind.context initial) 88, by simp [UpdateKind.changes], ?_⟩
      obtain ⟨i, hi, rfl⟩ := hcover
      refine ⟨64 + i, by omega, ?_⟩
      rw [hdi, BitVec.add_assoc, BitVec.ofNat_add]
      rfl
    · rw [hs] at hcover
      exact ⟨_, by simp [UpdateKind.changes], hcover⟩

end Md5.Proofs.Buffered
