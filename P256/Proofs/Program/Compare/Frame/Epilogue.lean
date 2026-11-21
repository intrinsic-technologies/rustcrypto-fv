import P256.Proofs.Program.Compare.Frame.Prologue
import P256.Proofs.Program.Compare.Frame.Restore

namespace P256.Proofs.Program.Compare.Frame

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

structure Saved (initial s : RamState) : Prop where
  rsp : stackPtr s = stackPtr initial - 56
  rbx : word s 16 = initial.regValue .rbx
  rbp : word s 48 = initial.regValue .rbp
  r12 : word s 24 = initial.regValue .r12
  r13 : s.regValue .r13 = initial.regValue .r13
  r14 : word s 32 = initial.regValue .r14
  r15 : word s 40 = initial.regValue .r15

theorem prologue_saved {initial s : RamState}
    (h : (prologueEffect initial).Holds initial s) : Saved initial s := by
  obtain ⟨h5, h15, h14, h12, h3, _, hsp, _, _, _, _⟩ := h.writes
  change stackPtr s = stackPtr initial - 56 at hsp
  have h13 : s.regValue .r13 = initial.regValue .r13 :=
    h.agrees.read (n := 64) (r := 13) (by simp [prologueEffect, Effect.components])
  refine ⟨hsp, ?_, ?_, ?_, h13, ?_, ?_⟩
  all_goals
    dsimp only [word]
    rw [hsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd] at *
  · exact h3
  · exact h5
  · exact h12
  · exact h14
  · exact h15

theorem prologue_return_word {initial s : RamState}
    (h : (prologueEffect initial).Holds initial s) :
    word s 56 = (returnBoundary initial).rip := by
  have hsp := (prologue_saved h).rsp
  change memLoad s.external (stackPtr s + 56) 64 =
    memLoad initial.external (stackPtr initial) 64
  rw [hsp, BitVec.sub_add_cancel]
  apply memLoad_congr
  intro i hi
  change (s.external[stackPtr initial + BitVec.ofNat 64 i]?).getD 0 =
    (initial.external[stackPtr initial + BitVec.ofNat 64 i]?).getD 0
  rw [h.agrees.byte]
  have apart (back : BitVec 64) (hb : back = 8 ∨ back = 16 ∨ back = 24 ∨ back = 32 ∨ back = 40) :
      RangeApart (stackPtr initial - back) 8 (stackPtr initial) 8 := by
    have ho : OffsetsApart (-back) 8 0 8 := by
      rcases hb with rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel
    intro j hj k hk
    simpa [BitVec.sub_eq_add_neg] using
      ho.ne (stackPtr initial) hj hk (by decide +kernel)
  intro c hc hcov
  simp only [prologueEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_mem, Write.component_reg, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hcov
    | (obtain ⟨j, hj, he⟩ := hcov
       first
       | exact apart 8 (by simp) j hj i hi he.symm
       | exact apart 16 (by simp) j hj i hi he.symm
       | exact apart 24 (by simp) j hj i hi he.symm
       | exact apart 32 (by simp) j hj i hi he.symm
       | exact apart 40 (by simp) j hj i hi he.symm)

theorem prologue_frame_readable [Bindings] {initial s : RamState}
    (hPre : CallPre initial) (h : (prologueEffect initial).Holds initial s) :
    MemReadable s (stackPtr s + 16) 48 := by
  rw [(prologue_saved h).rsp]
  have he : stackPtr initial - (56 : BitVec 64) + 16 = stackPtr initial - 40 := by
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  rw [he]
  exact (hPre.frame.stack_sub_readable (offset := 40) (by decide +kernel) (by decide +kernel)).of_holds h

theorem Saved.of_memory {initial s t : RamState} (h : Saved initial s)
    (hm : t.external = s.external) (hsp : stackPtr t = stackPtr s)
    (h13 : t.regValue .r13 = s.regValue .r13) : Saved initial t := by
  refine ⟨hsp.trans h.rsp, ?_, ?_, ?_, h13.trans h.r13, ?_, ?_⟩
  · simpa only [word, hsp, Operand.read, hm] using h.rbx
  · simpa only [word, hsp, Operand.read, hm] using h.rbp
  · simpa only [word, hsp, Operand.read, hm] using h.r12
  · simpa only [word, hsp, Operand.read, hm] using h.r14
  · simpa only [word, hsp, Operand.read, hm] using h.r15

theorem effect_calleeSaved {initial s t : RamState} (hs : Saved initial s)
    (h : (effect s).Holds s t) : CalleeSavedRegistersUnchanged initial t := by
  obtain ⟨h3, h12, h14, h15, h5, _⟩ := h.writes
  have h13 : t.regValue .r13 = s.regValue .r13 :=
    h.agrees.read (n := 64) (r := 13) (by simp [effect, Effect.components])
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h3.trans hs.rbx
  · exact h5.trans hs.rbp
  · exact h12.trans hs.r12
  · exact h13.trans hs.r13
  · exact h14.trans hs.r14
  · exact h15.trans hs.r15

theorem effect_rsp {initial s t : RamState} (hs : Saved initial s)
    (h : (effect s).Holds s t) : stackPtr t = stackPtr initial + 8 := by
  have ht : stackPtr t = stackPtr s + 64 := h.writes.2.2.2.2.2
  rw [ht, hs.rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  rfl

theorem restore_code {s : RamState} (h : CodeIn Extracted.programSections.toCodeMap s) :
    CodeIn restoreCode s :=
  program_text_slice h 0x1c923 13 (by decide +kernel)

theorem epilogue [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programSections.toCodeMap s)
    (hPre : RestorePre s) (hSaved : Saved initial s)
    (hOutside : Outside boundary.rip) (hLow : (word s 56).toNat < 2^32)
    (hDifferent : word s 56 ≠ boundary.rip ∨ stackPtr initial + 8 ≠ boundary.rsp) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programSections.toCodeMap t ∧ (effect s).Holds s t ∧
      CalleeSavedRegistersUnchanged initial t ∧ stackPtr t = stackPtr initial + 8 ∧
      (Operand.reg 0 : Operand 32).read t = (Operand.reg 0 : Operand 32).read s := by
  have hDifferent' : word s 56 ≠ boundary.rip ∨ stackPtr s + 64 ≠ boundary.rsp := by
    have hs : stackPtr s + 64 = stackPtr initial + 8 := by
      rw [hSaved.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
      rfl
    rw [hs]
    exact hDifferent
  obtain ⟨fuel, t, ha, hr, hc, he⟩ := restore_return_code hReady hCode
    (restore_code hCode) hPre hOutside hLow hDifferent'
  exact ⟨fuel, t, ha, hr, hc, he, effect_calleeSaved hSaved he,
    effect_rsp hSaved he, effect_eax he⟩

end P256.Proofs.Program.Compare.Frame
