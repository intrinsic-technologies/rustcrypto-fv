import P256.Proofs.Field.Inverse.Setup.ParameterMemory

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

def SavedWords (s t : RamState) : Prop :=
  memLoad t.external (stackPtr s - 16) 64 = s.regValue .rbx ∧
  memLoad t.external (stackPtr s - 8) 64 = s.regValue .rbp ∧
  memLoad t.external (stackPtr s) 64 = (returnBoundary s).rip

theorem entry_saved_words {s t : RamState} (memory : t.external = entryMemory s) :
    SavedWords s t := by
  unfold SavedWords
  rw [memory]
  constructor
  · exact memLoad_memStore _ _ (by decide) (by decide) _
  constructor
  · simp only [entryMemory, pushSequenceMemory, BitVec.sub_eq_add_neg]
    rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _
  · change memLoad (entryMemory s) (stackPtr s) 64 = memLoad s.external (stackPtr s) 64
    simp only [entryMemory, pushSequenceMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

theorem SavedWords.after_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (saved : SavedWords s t)
    (frame : MemoryWriteFrame t u #v[registerRegion s .rdi 40, ScalarFrame.Work.region s 880 16]) :
    SavedWords s u := by
  have read (offset : Nat) (bound : offset ≤ 16) :
      memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
        memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 :=
    ScalarFrame.Work.read pre (by decide) frame bound (by omega)
  refine ⟨(read 16 (by decide)).trans saved.1, (read 8 (by decide)).trans saved.2.1, ?_⟩
  have ret := read 0 (by decide)
  simp only [BitVec.sub_zero] at ret
  exact ret.trans saved.2.2

theorem parameter_word_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (sp : stackPtr t = stackPtr s - 168) (i : Fin 8)
    (effect : (wordEffect i t).Holds t u) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 40, ScalarFrame.Work.region s 880 16] := by
  have offsets : ∀ i : Fin 8,
      parameterWords[i].2.2.signExtend 64 = BitVec.ofNat 64 (parameterOffset i) ∧
      40 ≤ parameterOffset i ∧ parameterOffset i + 8 ≤ 112 := by decide +kernel
  have ag : AgreesExcept [.reg 0, .mem (stackPtr t + parameterWords[i].2.2.signExtend 64) 8, .rip] t u := by
    simpa [wordEffect, RipCopy.effect, Effect.components, stackPtr, gprIndex] using effect.agrees
  apply ag.memoryWriteFrame
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> try exact ha.elim
  refine ⟨ScalarFrame.Work.region s 880 16, by simp, ScalarFrame.Work.contains pre (offset := 128) (len := 72)
    (by decide) (by decide) ?_⟩
  rw [(offsets i).1] at ha
  exact setup_parameter_covers sp (offsets i).2.1 (offsets i).2.2 ha

theorem parameter_middle_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (sp : stackPtr t = stackPtr s - 168)
    (effect : (parameterMiddleEffect t).Holds t u) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 40, ScalarFrame.Work.region s 880 16] := by
  have ag : AgreesExcept [.mem (stackPtr t + 104) 8, .reg 8, .rip] t u := by
    simpa [parameterMiddleEffect, Effect.components, stackPtr, gprIndex] using effect.agrees
  apply ag.memoryWriteFrame
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> try exact ha.elim
  exact ⟨ScalarFrame.Work.region s 880 16, by simp, ScalarFrame.Work.contains pre (offset := 128) (len := 72)
    (by decide) (by decide) (setup_parameter_covers sp (offset := 104) (by decide) (by decide) ha)⟩

theorem saved_words_arguments {s t u : RamState} (saved : SavedWords s t)
    (effect : (parameterArgumentEffect t).Holds t u) : SavedWords s u := by
  have memory := effect.agrees.external
    (by simp [parameterArgumentEffect, Effect.components, Component.Covers])
  simpa only [SavedWords, memory] using saved

end P256.Proofs.Field.Inverse
