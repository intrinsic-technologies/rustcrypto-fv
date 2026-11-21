import Md5.Proofs.Buffered.DigestPrepare.Geometry
import Md5.Proofs.Buffered.Update.Calls
import Md5.Proofs.Buffered.Update.Rodata
import Md5.Proofs.Buffered.Stack
import Md5.Proofs.MemoryRoutines.Memcpy

namespace Md5.Proofs.Buffered.DigestPrepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {initial s : RamState} {input : ByteArray}

theorem input_stack_disjoint (hCall : Digest.ValidCall bindings initial input) :
    (Digest.inputRegion initial input).Disjoint (Stack.region initial Digest.minStackBytes) :=
  (hCall.stackSeparation.2 _ (by simp)).1 _ (by simp)

theorem input_size_bounded (hCall : Digest.ValidCall bindings initial input) : input.size < 2^64 := by
  have hb : (initial.regValue .rdi).toNat + input.size < 2^32 := hCall.inputInMemory.2.1
  omega


theorem Frame.inputBytes (hCall : Digest.ValidCall bindings initial input)
    (h : Frame initial (returnBoundary initial) s) :
    (Digest.inputRegion initial input).HasBytes s.external input := by
  refine ⟨rfl, fun i ↦ ?_⟩
  apply Eq.trans _ (hCall.inputInMemory.2.2.2 i)
  apply h.agrees.byte
  intro c hc hcov
  simp only [digestPreparationChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  have hx := Block.contains_of_mem_covers hCall.stackAvailable.1 hcov
  have hd := input_stack_disjoint hCall
  apply hd _ _ hx
  have hb : (Digest.inputRegion initial input).start + input.size < 2^32 := hCall.inputInMemory.2.1
  change (Digest.inputRegion initial input).start ≤ _ ∧
    _ < (Digest.inputRegion initial input).start + input.size
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

set_option maxRecDepth 2048 in
theorem memcpy_site_pre (hCall : Digest.ValidCall bindings initial input)
    (h : Frame initial (returnBoundary initial) s) {offset length : Nat} {ret : BitVec 64}
    (hEnd : offset + length ≤ input.size) (hLength : length ≤ 63)
    (hBytes : (Digest.inputRegion initial input).HasBytes s.external input)
    (hdi : rdi.read s = stackPtr s + 176)
    (hsi : rsi.read s = initial.regValue .rdi + BitVec.ofNat 64 offset)
    (hdx : MemoryRoutines.rdx.read s = BitVec.ofNat 64 length)
    (hRetLow : ret.toNat < 2^32) (hRetOutside : ret.toNat < 0x1024b0) :
    MemcpySitePre ret s := by
  have hlen : (MemoryRoutines.rdx.read s).toNat = length := by
    rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsrcBound : (initial.regValue .rdi).toNat + input.size < 2^32 := hCall.inputInMemory.2.1
  have hsn : (rsi.read s).toNat = (initial.regValue .rdi).toNat + offset := by
    rw [hsi, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read s).toNat = (stackPtr s).toNat + 176 := by
    rw [hdi]
    exact h.address (by decide)
  have hlow := h.stackLow
  have hhigh : (stackPtr s).toNat + 264 < 2^32 := h.stackHigh
  have hslot : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
    change (stackPtr s - 8).toNat = _
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · change 8 ≤ (stackPtr s).toNat
      omega
  have hw := h.scratchWritable (AgreesExcept.refl [] s) 8 8 (by decide) (by decide)
  have hd := h.writable (AgreesExcept.refl [] s) 176 length (by omega)
  have hsrc : MemReadable s (rsi.read s) length := by
    apply memReadable_of_allocated (allocated_of_hasBytes hBytes)
    · rw [hsn]
      change _ ≤ 2^32
      omega
    · change (initial.regValue .rdi).toNat ≤ _
      rw [hsn]
      omega
    · change _ ≤ (initial.regValue .rdi).toNat + input.size
      rw [hsn]
      omega
  have hsep := input_stack_disjoint hCall
  have hstack := h.stackNat hCall.stackAvailable
  have hstackLow : 616 ≤ (stackPtr initial).toNat := hCall.stackAvailable.2.2.1
  refine ⟨⟨h.df.df, ?_, hw.readable, hw.code, ?_, hRetLow, Or.inl hRetOutside⟩,
    ?_, ?_, ?_⟩
  · rw [hdi, hlen]
    exact hd
  · apply RangeApart.of_toNat
    · rw [hlen, hdn]
      omega
    · rw [hslot]
      omega
    · rw [hlen, hdn, hslot]
      omega
  · rw [hlen]
    exact hsrc
  · intro i hi j hj he
    rw [hlen] at hi
    apply hsep (rsi.read s + BitVec.ofNat 64 i).toNat
    · rw [toNat_add_ofNat _ _ (by rw [hsn]; omega), hsn]
      change (initial.regValue .rdi).toNat ≤ _ ∧
        _ < (initial.regValue .rdi).toNat + input.size
      omega
    · rw [he, toNat_add_ofNat _ _ (by rw [hslot]; omega), hslot, hstack]
      change (stackPtr initial).toNat - 616 ≤ _ ∧
        _ < (stackPtr initial).toNat - 616 +
          ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 616))
      omega
  · rw [hlen, hsn, hdn]
    apply Classical.byContradiction
    intro hnot
    have hcontain : (Digest.inputRegion initial input).Contains
        (max ((initial.regValue .rdi).toNat + offset) ((stackPtr s).toNat + 176)) := by
      change (initial.regValue .rdi).toNat ≤ _ ∧
        _ < (initial.regValue .rdi).toNat + input.size
      omega
    apply hsep _ hcontain
    change (stackPtr initial).toNat - 616 ≤ _ ∧
      _ < (stackPtr initial).toNat - 616 +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 616))
    omega


theorem Frame.after_memcpy (hCall : Digest.ValidCall bindings initial input)
    (h : Frame initial (returnBoundary initial) s) {t : RamState} {ret : BitVec 64}
    (hr : MemcpySiteResult (returnBoundary initial) ret s t)
    (hdi : rdi.read s = stackPtr s + 176)
    (hlen : (MemoryRoutines.rdx.read s).toNat ≤ 63) :
    Frame initial (returnBoundary initial) t := by
  have hlow := h.stackLow
  have hhigh : (stackPtr s).toNat + 264 < 2^32 := h.stackHigh
  apply h.preserve hCall.stackAvailable hr.agrees hr.ready hr.code
  · intro c hc hm
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, digestPreparationChanges]
  · intro c hc a hcov
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    · obtain ⟨i, hi, rfl⟩ := hcov
      rw [hdi]
      change (Finalize.Kind.digest.stackRegion s).Contains
        (stackPtr s + BitVec.ofNat 64 176 + BitVec.ofNat 64 i).toNat
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, h.address (by omega)]
      change (stackPtr s).toNat - 320 ≤ _ ∧ _ < (stackPtr s).toNat - 320 + 584
      omega
    · obtain ⟨i, hi, rfl⟩ := hcov
      have hn : (pushAddr s).toNat = (stackPtr s).toNat - 8 := by
        rw [pushAddr, BitVec.toNat_sub_of_le]
        · rfl
        · change 8 ≤ (stackPtr s).toNat
          omega
      rw [toNat_add_ofNat _ _ (by rw [hn]; omega), hn]
      change (stackPtr s).toNat - 320 ≤ _ ∧ _ < (stackPtr s).toNat - 320 + 584
      omega
  · exact hr.rsp
  · exact hr.agrees.read (r := 3) (n := 64) (by simp [callSiteChanges])
  · exact hr.agrees.read (r := 14) (n := 64) (by simp [callSiteChanges])

set_option maxRecDepth 2048 in
theorem memcpy_call_of_run {boundary : ReturnBoundary} {p : BitVec 64}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = p)
    (hSite : p = 0x100078 ∨ p = 0x1000c9)
    (hp : MemcpySitePre (p + 6) s)
    (hw : Memory.MemWritable s (pushAddr s) 8)
    (hRun : ∀ u, ReadyToStep u → CodeIn Extracted.programImage u →
      MemoryRoutines.MemcpyPre u → (returnBoundary u).rip ≠ boundary.rip →
      ∃ fuel t, Advances boundary fuel u t ∧ MemoryRoutines.MemcpyResult u t) :
    ∃ t, MemcpySiteResult boundary (p + 6) s t := by
  let am : AddrMode := .rip (if p = 0x100078 then 0xfff82 else 0xfff31)
  have ht : callMemPtr p am s = 0x1024b0 := by
    rcases hSite with rfl | rfl
    all_goals simp only [am, ↓reduceIte, BitVec.reduceEq]
    all_goals change (Operand.mem 0x200000 : Operand 64).read s = _
    all_goals exact memcpy_pointer hCode
  have hm : MemReadable s (am.addr s (p + BitVec.ofNat 64 (callMemLen am))) 8 := by
    rcases hSite with rfl | rfl
    all_goals simp only [am, ↓reduceIte, BitVec.reduceEq]
    all_goals change MemReadable s 0x200000 8
    all_goals exact memcpy_pointer_readable hCode
  have hb : CodeIn (codeRange p (encodeCallM64 am)) s := by
    rcases hSite with rfl | rfl
    · simp only [am, ↓reduceIte]
      change CodeIn (codeRange 0x100078 [0xff, 0x15, 0x82, 0xff, 0x0f, 0]) s
      exact Block.program_text_slice hCode 0x78 6 (by decide +kernel)
    · simp only [am, BitVec.reduceEq, ↓reduceIte]
      change CodeIn (codeRange 0x1000c9 [0xff, 0x15, 0x31, 0xff, 0x0f, 0]) s
      exact Block.program_text_slice hCode 0xc9 6 (by decide +kernel)
  have hret : p + 6 ≠ boundary.rip := by
    rcases hSite with rfl | rfl
    · exact Block.text_address_ne_return hOutside 0x7e (by decide +kernel)
    · exact Block.text_address_ne_return hOutside 0xcf (by decide +kernel)
  exact memcpy_call_of_advance
    (Stack.call_m64_effect_step p am (by simp [am, AddrMode.Valid]) rfl rfl)
    hReady hCode hb ⟨⟨⟨hRip, hw⟩, by rw [ht]; decide⟩, hm⟩ hp ht
    (Block.text_address_ne_return hOutside 0x24b0 (by decide +kernel)) hret hRun


theorem memcpy_call {boundary : ReturnBoundary} {p : BitVec 64}
    (hStride : UnitStringStride bindings)
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = p)
    (hSite : p = 0x100078 ∨ p = 0x1000c9)
    (hp : MemcpySitePre (p + 6) s)
    (hw : Memory.MemWritable s (pushAddr s) 8) :
    ∃ t, MemcpySiteResult boundary (p + 6) s t := by
  have hout : boundary.rip.toNat < 0x1024b0 ∨ 0x1024df ≤ boundary.rip.toNat := by
    apply Classical.byContradiction
    intro hn
    have htext : 0x24df ≤ Extracted.textBytes.size := by decide +kernel
    have hlow : 0x1024b0 ≤ boundary.rip.toNat := by omega
    have hhigh : boundary.rip.toNat < 0x1024df := by omega
    have he : Extracted.textAddress + BitVec.ofNat 64 (boundary.rip.toNat - 0x100000) =
        boundary.rip := by
      change BitVec.ofNat 64 0x100000 + BitVec.ofNat 64 (boundary.rip.toNat - 0x100000) = _
      rw [← BitVec.ofNat_add, Nat.add_sub_of_le (by omega), BitVec.ofNat_toNat,
        BitVec.setWidth_eq]
    exact hOutside (he ▸ Block.text_address_in_program _ (by omega))
  exact memcpy_call_of_run hReady hCode hOutside hRip hSite hp hw
    (MemoryRoutines.memcpy_advances hStride boundary hout)

end Md5.Proofs.Buffered.DigestPrepare
