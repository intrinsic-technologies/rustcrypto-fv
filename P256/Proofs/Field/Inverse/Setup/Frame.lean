import P256.Proofs.Field.Inverse.Setup.Start
import P256.Proofs.Field.Inverse.Setup.ParameterPre

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

abbrev setupComponents (s : RamState) : List Component :=
  entryComponents s ++ [.reg 3, .reg 0, .reg 8, .reg 7, .reg 2, .reg 1,
    .mem (stackPtr s - 128) 72, .rip]

theorem setup_writes [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) : WritesWithin (setupComponents s) #v[Stack.region s 880] := by
  intro c hc a ha
  simp only [setupComponents, entryComponents, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with (hc | (rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨_, by simp, pushSequenceFrame_covers saveSources pre.stack (by decide) hc ha⟩
  all_goals try exact ha.elim
  exact ⟨_, by simp, ScalarFrame.stack_contains pre (offset := 128) (by decide) (by decide) ha⟩

theorem setup_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (agrees : AgreesExcept (setupComponents s) s t) :
    MemoryWriteFrame s t #v[Stack.region s 880] :=
  agrees.memoryWriteFrame (setup_writes pre)

theorem setup_loaded [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) (agrees : AgreesExcept (setupComponents s) s t) :
    ProgramLoaded t := by
  have frame := setup_frame pre agrees
  intro a b hb
  rw [frame a]
  · exact pre.loaded a b hb
  · intro region hr ha
    have hr' : region = Stack.region s 880 := by simpa using hr
    subst region
    exact pre.avoids _ (by simp) a ha (.inl ⟨b, hb⟩)

theorem setup_trans {s t u : RamState} (first : AgreesExcept (setupComponents s) s t)
    (second : AgreesExcept (setupComponents s) t u) :
    AgreesExcept (setupComponents s) s u :=
  (first.trans second).mono (fun _ hc => (List.mem_append.mp hc).elim id id)

theorem setup_parameter_covers {s t : RamState} (sp : stackPtr t = stackPtr s - 168)
    {offset len : Nat} (low : 40 ≤ offset) (high : offset + len ≤ 112) {a : BitVec 64}
    (covered : (Component.mem (stackPtr t + BitVec.ofNat 64 offset) len).Covers a) :
    (Component.mem (stackPtr s - 128) 72).Covers a := by
  obtain ⟨i, hi, rfl⟩ := covered
  refine ⟨offset - 40 + i, by omega, ?_⟩
  rw [sp, BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le offset 40 (by omega) low]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  congr 1
  change ((-128 : BitVec 64) + -40) + _ = _
  rw [BitVec.add_assoc]
  congr 1
  rw [← BitVec.add_assoc, BitVec.add_comm (-40), BitVec.add_assoc]
  rfl

theorem parameter_effect_agrees {s t u : RamState}
    (sp : stackPtr t = stackPtr s - 168) (i : Fin 8)
    (effect : (RipCopy.effect (Extracted.textAddress + BitVec.ofNat 64 parameterWords[i].1)
      parameterWords[i].2.1 parameterWords[i].2.2 t).Holds t u) :
    AgreesExcept (setupComponents s) t u := by
  have facts : ∀ i : Fin 8,
      parameterWords[i].2.2.signExtend 64 = BitVec.ofNat 64 (parameterOffset i) ∧
      40 ≤ parameterOffset i ∧ parameterOffset i + 8 ≤ 112 := by decide +kernel
  have ag : AgreesExcept [.reg 0, .mem (stackPtr t + parameterWords[i].2.2.signExtend 64) 8, .rip] t u := by
    simpa [RipCopy.effect, Effect.components, stackPtr, gprIndex] using effect.agrees
  apply ag.widen
  · intro c hc hm
    change c ∈ [.reg 0, .mem (stackPtr t + parameterWords[i].2.2.signExtend 64) 8, .rip] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals simp [Component.isMem, setupComponents] at hm ⊢
  · intro a c hc ha
    change c ∈ [.reg 0, .mem (stackPtr t + parameterWords[i].2.2.signExtend 64) 8, .rip] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals try exact ha.elim
    refine ⟨.mem (stackPtr s-128) 72, by simp [setupComponents], ?_⟩
    change (Component.mem (stackPtr t + parameterWords[i].2.2.signExtend 64) 8).Covers a at ha
    rw [(facts i).1] at ha
    exact setup_parameter_covers sp (facts i).2.1 (facts i).2.2 ha

end P256.Proofs.Field.Inverse
