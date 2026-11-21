import Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.Control.Entry

namespace Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine

open Base16ct.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs Base16ct.Proofs.Copied.Md5.Proofs.Block

def mixedDispatchEffect (s : RamState) : Effect where
  rip := if (s.regValue .rsi).toNat % 2 = 0 then
      if (s.regValue .rsi).toNat / 2 ≤ (s.regValue .r8).toNat then
        if s.regValue .rsi = 0 then 0x1002fb else 0x1001e7
      else 0x1002fa
    else 0x1002fa
  writes := [⟨(.reg 9 : Operand 64),
    if (s.regValue .rsi).toNat % 2 = 0 then s.regValue .rsi >>> 1 else s.regValue .r9⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem mixed_dispatch [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideMixed boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1001c5) Extracted.programImage
      mixedDispatchEffect := by
  intro s hReady hCode hRip
  obtain ⟨a, runA, readyA, codeA, ripA, frameA⟩ :=
    mixed_parity_entry hReady hCode hRip hOutside
  have asi : a.regValue .rsi = s.regValue .rsi := frameA.read (n := 64) (r := 6) (by simp)
  have acx : a.regValue .r8 = s.regValue .r8 := frameA.read (n := 64) (r := 8) (by simp)
  by_cases heven : (s.regValue .rsi).toNat % 2 = 0
  · have ripA' : a.RIP = 0x1001cf := by simpa only [heven, ↓reduceIte] using ripA
    obtain ⟨b, runB, readyB, codeB, ripB, bx, frameB⟩ :=
      mixed_capacity_entry readyA codeA ripA' hOutside
    rw [asi, acx] at ripB
    rw [asi] at bx
    have frameAB : AgreesExcept [.reg 9, .flags, .rip] s b :=
      (frameA.trans frameB).mono (by simp [or_assoc, or_left_comm, or_comm])
    by_cases hFit : (s.regValue .rsi).toNat / 2 ≤ (s.regValue .r8).toNat
    · have ripB' : b.RIP = 0x1001de := by simpa only [hFit, ↓reduceIte] using ripB
      obtain ⟨c, runC, readyC, codeC, ripC, frameC⟩ :=
        mixed_empty_entry readyB codeB ripB' hOutside
      have bsi : b.regValue .rsi = s.regValue .rsi := frameAB.read (n := 64) (r := 6) (by simp)
      rw [bsi] at ripC
      refine ⟨8, c, (runA.trans runB).trans runC, readyC, codeC, ?_, ?_, by trivial, ?_⟩
      · simpa only [mixedDispatchEffect, heven, hFit, ↓reduceIte] using ripC
      · change c.regValue .r9 =
          if (s.regValue .rsi).toNat % 2 = 0 then s.regValue .rsi >>> 1 else s.regValue .r9
        simp only [heven, ↓reduceIte]
        exact (frameC.read (n := 64) (r := 9) (by simp)).trans bx
      · exact (frameAB.trans frameC).mono (by simp [mixedDispatchEffect, Effect.components])
    · refine ⟨6, b, runA.trans runB, readyB, codeB, ?_, ?_, by trivial, ?_⟩
      · simpa only [mixedDispatchEffect, heven, hFit, ↓reduceIte] using ripB
      · change b.regValue .r9 =
          if (s.regValue .rsi).toNat % 2 = 0 then s.regValue .rsi >>> 1 else s.regValue .r9
        simp only [heven, ↓reduceIte]
        exact bx
      · exact frameAB
  · refine ⟨2, a, runA, readyA, codeA, ?_, ?_, by trivial, ?_⟩
    · simpa only [mixedDispatchEffect, heven, ↓reduceIte] using ripA
    · change a.regValue .r9 =
        if (s.regValue .rsi).toNat % 2 = 0 then s.regValue .rsi >>> 1 else s.regValue .r9
      simp only [heven, ↓reduceIte]
      exact frameA.read (n := 64) (r := 9) (by simp)
    · exact frameA.mono (by simp [mixedDispatchEffect, Effect.components])

def mixedEntryEffect (s : RamState) : Effect where
  rip := (mixedDispatchEffect s).rip
  writes := [⟨(.reg 0 : Operand 64), 1⟩,
    ⟨(.reg 9 : Operand 64), if (s.regValue .rsi).toNat % 2 = 0 then
      s.regValue .rsi >>> 1 else s.regValue .r9⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem mixed_entry [Bindings] (boundary : ReturnBoundary)
    (hOutside : OutsideMixed boundary.rip) :
    AdvancesBlock boundary (fun s ↦ s.RIP = 0x1001c0) Extracted.programImage
      mixedEntryEffect := by
  intro s hReady hCode hRip
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (mov_r32_imm32_effect_step 0x1001c0 0xb8 (by decide) 1).advances
      hReady (program_text_slice hCode 0x1c0 5 (by decide +kernel)) hRip
      (outsideMixed_ne (pc := 0x1001c5) hOutside (by decide) (by decide))
  have frameA : AgreesExcept [.reg 0, .rip] s a := effectA.agrees
  have codeA := frameA.codeIn (by simp [Component.Covers]) hCode
  obtain ⟨fuel, t, runT, readyT, codeT, effectT⟩ :=
    mixed_dispatch boundary hOutside a readyA codeA effectA.rip
  have frameT : AgreesExcept [.reg 9, .flags, .rip] a t := effectT.agrees
  have si : a.regValue .rsi = s.regValue .rsi := frameA.read (n := 64) (r := 6) (by simp)
  have r8 : a.regValue .r8 = s.regValue .r8 := frameA.read (n := 64) (r := 8) (by simp)
  have r9 : a.regValue .r9 = s.regValue .r9 := frameA.read (n := 64) (r := 9) (by simp)
  refine ⟨1 + fuel, t, runA.trans runT, readyT, codeT, ?_, ?_, by trivial, ?_⟩
  · simpa only [mixedEntryEffect, mixedDispatchEffect, si, r8] using effectT.rip
  · constructor
    · exact (frameT.read (n := 64) (r := 0) (by simp)).trans effectA.writes
    · simpa only [mixedEntryEffect, mixedDispatchEffect, si, r9] using effectT.writes
  · exact (frameA.trans frameT).mono (by simp [mixedEntryEffect, Effect.components])

end Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
