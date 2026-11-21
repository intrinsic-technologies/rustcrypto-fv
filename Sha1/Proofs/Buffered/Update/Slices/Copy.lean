import Sha1.Proofs.Buffered.DigestPrepare.Copy
import Sha1.Proofs.Buffered.Update.Memory

namespace Sha1.Proofs.Buffered.Update.Slices

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered.Finalize (text_address_ne_return rangeApart_text)
open Sha1.Proofs.Buffered.DigestPrepare (callMem_effect_step SlotWritable)

set_option maxRecDepth 2048 in
private theorem call_instruction [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {p : BitVec 64} (hStride : UnitStringStride bindings)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = p)
    (hSite : p = 0x101cc1 ∨ p = 0x101d29 ∨ p = 0x101da9)
    (hp : MemcpySitePre (p + 6) s) (hw : SlotWritable s) :
    ∃ t, MemcpySiteResult boundary (p + 6) s t := by
  let am : AddrMode := .rip ((0x200000 - (p + 6)).setWidth 32)
  have ht : callMemPtr p am s = 0x103730 := by
    rcases hSite with rfl | rfl | rfl <;> exact memcpy_pointer hCode
  have hm : MemReadable s (am.addr s (p + BitVec.ofNat 64 (callMemLen am))) 8 := by
    rcases hSite with rfl | rfl | rfl <;> exact memcpy_pointer_readable hCode
  have hb : CodeIn (codeRange p (encodeCallM64 am)) s := by
    rcases hSite with rfl | rfl | rfl
    · simp only [am, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceSetWidth]
      change CodeIn (codeRange 0x101cc1 [0xff, 0x15, 0x39, 0xe3, 0xf, 0]) s
      exact Sha1.Proofs.Compress.Machine.program_text_slice hCode 0x1cc1 6 (by decide +kernel)
    · simp only [am, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceSetWidth]
      change CodeIn (codeRange 0x101d29 [0xff, 0x15, 0xd1, 0xe2, 0xf, 0]) s
      exact Sha1.Proofs.Compress.Machine.program_text_slice hCode 0x1d29 6 (by decide +kernel)
    · simp only [am, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceSetWidth]
      change CodeIn (codeRange 0x101da9 [0xff, 0x15, 0x51, 0xe2, 0xf, 0]) s
      exact Sha1.Proofs.Compress.Machine.program_text_slice hCode 0x1da9 6 (by decide +kernel)
  have hcodeApart : RangeApart (pushAddr s) 8 p (callMemLen am) := by
    rcases hSite with rfl | rfl | rfl
    · exact rangeApart_text (offset := 0x1cc1) hp.slotCode (by decide +kernel)
    · exact rangeApart_text (offset := 0x1d29) hp.slotCode (by decide +kernel)
    · exact rangeApart_text (offset := 0x1da9) hp.slotCode (by decide +kernel)
  have hret : p + 6 ≠ boundary.rip := by
    rcases hSite with rfl | rfl | rfl
    · exact text_address_ne_return hOutside 0x1cc7 (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1d2f (by decide +kernel)
    · exact text_address_ne_return hOutside 0x1daf (by decide +kernel)
  have hout := outside_text_range_of_not_inProgram hOutside 0x103730 0x10375f
    (by decide) (by decide +kernel)
  exact memcpy_call hStride hout
    (callMem_effect_step p am (by simp [am, AddrMode.Valid]) rfl rfl) hReady hCode hb
    ⟨⟨⟨hRip, hw, hcodeApart⟩, by rw [ht]; decide⟩, hm⟩ hp ht hret

set_option maxRecDepth 2048 in
theorem copy_input [bindings : Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {p : BitVec 64} {src dst len : Nat} {changes : List Component}
    (h : UpdatePre .updateFinalize boundary message input s)
    (ha : AgreesExcept changes s u) (hsp : stackPtr u = stackPtr s)
    (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u) (hdf : DirectionFlagClear u.RFLAGS)
    (hrip : u.RIP = p) (hsite : p = 0x101cc1 ∨ p = 0x101d29 ∨ p = 0x101da9)
    (hsi : rsi.read u = (Operand.reg 14 : Operand 64).read s + BitVec.ofNat 64 src)
    (hdi : rdi.read u = UpdateKind.updateFinalize.context s + BitVec.ofNat 64 dst)
    (hdx : MemoryRoutines.rdx.read u = BitVec.ofNat 64 len)
    (hsrc : src + len ≤ input.size) (hdst : dst + len ≤ 64) :
    ∃ t, MemcpySiteResult boundary (p + 6) u t := by
  have hlow := h.stackLow
  have hhigh : (stackPtr s).toNat + 0xd8 + 92 < 2^32 := h.stackHigh
  have hin : ((Operand.reg 14 : Operand 64).read s).toNat + input.size < 2^32 := h.inputBounded
  have hctx : (UpdateKind.updateFinalize.context s).toNat = (stackPtr s).toNat + 0xd8 :=
    toNat_add_ofNat _ 0xd8 (by omega)
  have hdn : (rdi.read u).toNat = (stackPtr s).toNat + 0xd8 + dst := by
    rw [hdi, toNat_add_ofNat _ _ (by rw [hctx]; omega), hctx]
  have hsn : (rsi.read u).toNat = ((Operand.reg 14 : Operand 64).read s).toNat + src := by
    rw [hsi, toNat_add_ofNat _ _ (by omega)]
  have hlen : (MemoryRoutines.rdx.read u).toNat = len := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hslot : (pushAddr u).toNat = (stackPtr s).toNat - 8 := by
    rw [pushAddr, hsp, BitVec.toNat_sub_of_le]
    · rfl
    · change 8 ≤ (stackPtr s).toNat
      omega
  have hw : MemoryRoutines.WritableRange u (pushAddr u) 8 := by
    refine DigestPrepare.writableRange_of_region ?_ (allocated_of_agrees ha h.scratchAllocated)
      h.scratchAvoids ?_ ?_
    · change (stackPtr s).toNat - 344 + 344 < 2^32
      omega
    · change (stackPtr s).toNat - 344 ≤ _
      omega
    · change _ ≤ (stackPtr s).toNat - 344 + 344
      omega
  have hdstw : MemoryRoutines.WritableRange u (rdi.read u) len := by
    refine DigestPrepare.writableRange_of_region ?_ (allocated_of_agrees ha h.contextAllocated)
      h.contextAvoids ?_ ?_
    · change (UpdateKind.updateFinalize.context s).toNat + 92 < 2^32
      omega
    · change (UpdateKind.updateFinalize.context s).toNat ≤ _
      omega
    · change _ ≤ (UpdateKind.updateFinalize.context s).toNat + 92
      omega
  have hsread : MemReadable u (rsi.read u) len := by
    apply DigestPrepare.memReadable_of_allocated (allocated_of_agrees ha (allocated_of_hasBytes h.inputBytes))
    · omega
    · change ((Operand.reg 14 : Operand 64).read s).toNat ≤ _
      omega
    · change _ ≤ ((Operand.reg 14 : Operand 64).read s).toNat + input.size
      omega
  have hretn : (p + 6).toNat < 0x103730 := by rcases hsite with rfl | rfl | rfl <;> decide
  apply call_instruction h.stride hr hc h.boundaryOutside hrip hsite _ ⟨hw.readable.low, hw.readable.mem, hw.tables⟩
  refine ⟨⟨hdf, hlen ▸ hdstw, hw.readable, hw.code, ?_, by omega, .inl hretn⟩, hlen ▸ hsread, ?_, ?_⟩
  · apply RangeApart.of_toNat <;> omega
  · intro i hi j hj he
    apply h.inputScratch (rsi.read u + BitVec.ofNat 64 i).toNat
    · change ((Operand.reg 14 : Operand 64).read s).toNat ≤ _ ∧ _ < ((Operand.reg 14 : Operand 64).read s).toNat + input.size
      rw [toNat_add_ofNat _ _ (by omega)]
      omega
    · rw [he, toNat_add_ofNat _ _ (by omega)]
      change (stackPtr s).toNat - 344 ≤ _ ∧ _ < (stackPtr s).toNat - 344 + 344
      omega
  · apply Classical.byContradiction
    intro hn
    let x := max (rsi.read u).toNat (rdi.read u).toNat
    apply h.inputContext x
    · change ((Operand.reg 14 : Operand 64).read s).toNat ≤ x ∧ x < ((Operand.reg 14 : Operand 64).read s).toNat + input.size
      dsimp only [x]
      omega
    · change (UpdateKind.updateFinalize.context s).toNat ≤ x ∧ x < (UpdateKind.updateFinalize.context s).toNat + 92
      dsimp only [x]
      omega

end Sha1.Proofs.Buffered.Update.Slices
