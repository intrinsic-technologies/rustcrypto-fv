import ChaCha20Poly1305.Proofs.MemoryRoutines.Memset.Pattern
import ChaCha20Poly1305.Proofs.MemoryRoutines.Memset.Body

namespace ChaCha20Poly1305.Proofs.MemoryRoutines.Memset

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Common ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

structure Prepared [Bindings] (s t : RamState) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  stores : StoresPre t (rdx.read s).toNat
  destination : rdi.read t = rdi.read s
  saved : rdx.read t = rdi.read s
  byte : (rax.read t).setWidth 8 = (rsi.read s).setWidth 8
  rsp : stackPtr t = stackPtr s
  agrees : AgreesExcept (callChanges s) s t

theorem prepare [Bindings] (boundary : ReturnBoundary) (hb : Outside boundary)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hp : MemsetPre s) : ∃ fuel t, Advances boundary fuel s t ∧ Prepared s t := by
  have hcp : CodeIn (codeRange 0x102d70 patternBytes) s :=
    (memset_code hc).mono (codeRange_mem_of_take (by decide +kernel))
  obtain ⟨n₁, u, ha₁, hru, _, heu⟩ := pattern_prepare boundary hb s hr hcp hp.rip
  have hcu : CodeIn Extracted.programImage u := heu.agrees.codeIn
    (by simp [patternEffect, Effect.components, Component.Covers, r8]) hc
  have hcs : CodeIn (codeRange 0x102d88 selectBytes) u :=
    program_text_slice hcu 0x2d88 14 (by decide +kernel)
  obtain ⟨n₂, v, ha₂, hrv, _, hev⟩ := select_prepare boundary hb u hru hcs heu.rip
  have hcv : CodeIn Extracted.programImage v := hev.agrees.codeIn
    (by simp [selectEffect, Effect.components, Component.Covers]) hcu
  have hcc : CodeIn (codeRange 0x102d96 countsBytes) v :=
    program_text_slice hcv 0x2d96 14 (by decide +kernel)
  obtain ⟨n₃, t, ha₃, hrt, _, het⟩ := counts_prepare boundary hb v hrv hcc hev.rip
  have hct : CodeIn Extracted.programImage t := het.agrees.codeIn
    (by simp [countsEffect, Effect.components, Component.Covers, r8]) hcv
  have hag := (heu.agrees.trans hev.agrees).trans het.agrees
  have hdst : rdi.read t = rdi.read s := hag.read (by
    simp [patternEffect, selectEffect, countsEffect, Effect.components, r8, rdx])
  have hsp : stackPtr t = stackPtr s := hag.read (r := 4) (n := 64) (by
    simp [patternEffect, selectEffect, countsEffect, Effect.components, r8, rdx])
  have hsaved : rdx.read t = rdi.read s :=
    (het.agrees.read (by simp [countsEffect, Effect.components, r8])).trans
      ((hev.agrees.read (by simp [selectEffect, Effect.components])).trans heu.writes.2.1)
  have hax : rax.read t = broadcast ((rsi.read s).setWidth 8) :=
    (het.agrees.read (by simp [countsEffect, Effect.components, r8])).trans
      ((hev.agrees.read (by simp [selectEffect, Effect.components])).trans heu.writes.2.2.2)
  have haxlow : (rax.read t).setWidth 8 = (rsi.read s).setWidth 8 := by
    rw [hax, broadcast_lowByte]
  have hr8v : r8.read v = rdx.read s :=
    (hev.agrees.read (by simp [selectEffect, Effect.components])).trans heu.writes.1
  have hheadv : (rcx.read v).toNat = alignmentPrefix (rdi.read s) (rdx.read s).toNat := by
    rw [show rcx.read v = selectedCount u from hev.writes, selectedCount_toNat,
      heu.writes.1, heu.writes.2.1]
  have hheadt : (rcx.read t).toNat = alignmentPrefix (rdi.read s) (rdx.read s).toNat := by
    rw [het.agrees.read (r := 1) (n := 64) (by simp [countsEffect, Effect.components, r8])]
    exact hheadv
  have hremaining : (r8.read v - rcx.read v).toNat =
      (rdx.read s).toNat - alignmentPrefix (rdi.read s) (rdx.read s).toNat := by
    rw [sub_toNat _ _ (by rw [hr8v, hheadv]; exact alignmentPrefix_le_length _ _), hr8v, hheadv]
  have hag' : AgreesExcept (callChanges s) s t := hag.mono (by
    simp [patternEffect, selectEffect, countsEffect, Effect.components, callChanges, r8, rdx])
  refine ⟨n₁ + n₂ + n₃, t, (ha₁.trans ha₂).trans ha₃,
    ⟨hrt, hct, ?_, hdst, hsaved, haxlow, hsp, hag'⟩⟩
  refine ⟨het.rip, (hag'.directionFlagClear (by simp [callChanges]) ⟨hp.df⟩).df,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdst]; exact hp.dst.of_agrees hag'
  · rw [haxlow]; exact hax
  · rw [hdst]; exact hheadt
  · rw [show rsi.read t = (r8.read v - rcx.read v) >>> 3 from het.writes.1,
      shr_three_toNat, hremaining, hdst]
  · rw [show r8.read t = (((r8.read v - rcx.read v).setWidth 32) &&&
        (7 : BitVec 32)).setWidth 64 from het.writes.2, low32_mask_toNat, hremaining, hdst]

end ChaCha20Poly1305.Proofs.MemoryRoutines.Memset
