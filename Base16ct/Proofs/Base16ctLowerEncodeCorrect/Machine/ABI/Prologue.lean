import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Interface
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Instructions.Call.Triple

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def lowerPrologueEffect (s : RamState) : Effect where
  rip := 0x100530
  writes :=
    [⟨(.reg 4 : Operand 64), stackPtr s - 32⟩,
     ⟨(.reg 3 : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
     ⟨(.reg 2 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
     ⟨(.reg 6 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
     ⟨(.reg 7 : Operand 64), stackPtr s - 24⟩,
     ⟨(.mem (stackPtr s - 32) : Operand 64), 0x100156⟩,
     ⟨(.mem (stackPtr s - 8) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩]
  flags := some ⟨none, none, none, none, none, none⟩

theorem lower_prologue_run [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hEntry : s.RIP = 0x100140)
    (hWrite : MemWritable s (stackPtr s - 32) 8)
    (hApart : ∀ i < 8, ¬ InProgram (stackPtr s - 32 + BitVec.ofNat 64 i))
    (hSaveWrite : MemWritable s (stackPtr s - 8) 8)
    (hSaveApart : ∀ i < 8, ¬ InProgram (stackPtr s - 8 + BitVec.ofNat 64 i))
    (hOutside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (lowerPrologueEffect s).Holds s t := by
  have hBytes₁ : CodeIn (codeRange 0x100140 [0x53]) s :=
    program_text_slice hCode 0x140 1 (by decide +kernel)
  have hp₁ : PushPre 0x100140 1 s := by
    refine ⟨hEntry, hSaveWrite, ?_⟩
    intro i hi j hj heq
    have hj0 : j = 0 := by omega
    subst j
    apply hSaveApart i hi
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      heq ▸ text_address_in_program 0x140 (by decide +kernel)
  obtain ⟨s₁, ha₁, hr₁, he₁⟩ :=
    (push_r64_effect_step 0x100140 0x53 (by decide)).advances
      hReady hBytes₁ hp₁ (text_address_ne_return hOutside 0x141 (by decide +kernel))
  change (pushR64Effect 0x100140 1 3 s).Holds s s₁ at he₁
  have hc₁ := he₁.codeIn (by
    intro x hx c hc hcov
    simp only [pushR64Effect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨i, hi, heq⟩ := hcov
      exact hSaveApart i hi (heq ▸ (show InProgram x.1 from ⟨x.2, hx⟩))
    · exact hcov) hCode
  have hBytes₂ : CodeIn (codeRange 0x100141 [0x48, 0x83, 0xec, 0x10]) s₁ :=
    program_text_slice hc₁ 0x141 4 (by decide +kernel)
  obtain ⟨s₂, ha₂, hr₂, he₂⟩ :=
    (sub_r64_imm8_effect_step 0x100141 0x48 0xec 0x10
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      hr₁ hBytes₂ he₁.rip (text_address_ne_return hOutside 0x145 (by decide +kernel))
  change (subR64Imm8Effect 0x100141 4 16 s₁).Holds s₁ s₂ at he₂
  have hc₂ := he₂.codeIn (subR64Imm8Effect_avoids _ _ _ _ _) hc₁
  have hBytes₃ : CodeIn (codeRange 0x100145 [0x48, 0x89, 0xd3]) s₂ :=
    program_text_slice hc₂ 0x145 3 (by decide +kernel)
  obtain ⟨s₃, ha₃, hr₃, he₃⟩ :=
    (mov_r64_r64_effect_step 0x100145 0x48 0xd3
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel)).advances hr₂ hBytes₃ he₂.rip
      (text_address_ne_return hOutside 0x148 (by decide +kernel))
  change (movR64R64Effect 0x100145 3 2 s₂).Holds s₂ s₃ at he₃
  have hc₃ := he₃.codeIn (Effect.avoids_of_components_reg_rip rfl _) hc₂
  have hBytes₄ : CodeIn (codeRange 0x100148 [0x48, 0x89, 0xf2]) s₃ :=
    program_text_slice hc₃ 0x148 3 (by decide +kernel)
  obtain ⟨s₄, ha₄, hr₄, he₄⟩ :=
    (mov_r64_r64_effect_step 0x100148 0x48 0xf2
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel)).advances hr₃ hBytes₄ he₃.rip
      (text_address_ne_return hOutside 0x14b (by decide +kernel))
  change (movR64R64Effect 0x100148 2 6 s₃).Holds s₃ s₄ at he₄
  have hc₄ := he₄.codeIn (Effect.avoids_of_components_reg_rip rfl _) hc₃
  have hBytes₅ : CodeIn (codeRange 0x10014b [0x48, 0x89, 0xfe]) s₄ :=
    program_text_slice hc₄ 0x14b 3 (by decide +kernel)
  obtain ⟨s₅, ha₅, hr₅, he₅⟩ :=
    (mov_r64_r64_effect_step 0x10014b 0x48 0xfe
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel)).advances hr₄ hBytes₅ he₄.rip
      (text_address_ne_return hOutside 0x14e (by decide +kernel))
  change (movR64R64Effect 0x10014b 6 7 s₄).Holds s₄ s₅ at he₅
  have hc₅ := he₅.codeIn (Effect.avoids_of_components_reg_rip rfl _) hc₄
  have hBytes₆ : CodeIn (codeRange 0x10014e [0x48, 0x89, 0xe7]) s₅ :=
    program_text_slice hc₅ 0x14e 3 (by decide +kernel)
  obtain ⟨s₆, ha₆, hr₆, he₆⟩ :=
    (mov_r64_r64_effect_step 0x10014e 0x48 0xe7
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel)).advances
      hr₅ hBytes₆ he₅.rip (text_address_ne_return hOutside 0x151 (by decide +kernel))
  change (movR64R64Effect 0x10014e 7 4 s₅).Holds s₅ s₆ at he₆
  have hc₆ := he₆.codeIn (Effect.avoids_of_components_reg_rip rfl _) hc₅
  have hg₆ : AgreesExcept [.reg 3, .reg 2, .reg 6, .reg 7, .rip] s₂ s₆ :=
    (he₃.agrees.trans (he₄.agrees.trans (he₅.agrees.trans he₆.agrees))).mono (by simp)
  have hsp₁ : stackPtr s₁ = stackPtr s - 8 := he₁.writes.1
  have hsp₂ : stackPtr s₂ = stackPtr s - 24 := by
    have hw : stackPtr s₂ = stackPtr s₁ - 16 := he₂.writes
    rw [hsp₁, BitVec.sub_sub] at hw
    exact hw
  have hsp₆ : stackPtr s₆ = stackPtr s - 24 :=
    (hg₆.read (r := 4) (n := 64) (by simp)).trans hsp₂
  have hpush : pushAddr s₆ = stackPtr s - 32 := by
    rw [pushAddr, hsp₆, BitVec.sub_sub]
    rfl
  have hBytes₇ : CodeIn (codeRange 0x100151 [0xe8, 0xda, 0x03, 0x00, 0x00]) s₆ :=
    program_text_slice hc₆ 0x151 5 (by decide +kernel)
  have hp₇ : PushPre 0x100151 5 s₆ := by
    refine ⟨he₆.rip, ?_, ?_⟩
    · rw [hpush]
      exact ⟨hWrite.low, fun i hi ↦
        (he₁.agrees.trans (he₂.agrees.trans hg₆)).grow _ (hWrite.mem i hi), hWrite.tables⟩
    · rw [hpush]
      intro i hi j hj heq
      apply hApart i hi
      rw [heq]
      have hp := text_address_in_program (0x151 + j) (by
        have hs : 0x156 ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      have he : 0x100151#64 + BitVec.ofNat 64 j =
          Extracted.textAddress + BitVec.ofNat 64 (0x151 + j) := by
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        rfl
      exact Eq.mpr (congrArg InProgram he) hp
  obtain ⟨t, ha₇, hr₇, he₇⟩ :=
    (call_rel32_effect_step 0x100151 0x3da (by decide +kernel)).advances
      hr₆ hBytes₇ hp₇ (text_address_ne_return hOutside 0x530 (by decide +kernel))
  change (callEffect (fun _ ↦ 0x100530) 0x100156 s₆).Holds s₆ t at he₇
  have hc₇ : CodeIn Extracted.programImage t := he₇.codeIn (by
    intro x hx c hc hcov
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨i, hi, heq⟩ := hcov
      rw [hpush] at heq
      exact hApart i hi (heq ▸ (show InProgram x.1 from ⟨x.2, hx⟩))
    · exact hcov) hc₆
  have hag : AgreesExcept (lowerPrologueEffect s).components s t :=
    (he₁.agrees.trans (he₂.agrees.trans (hg₆.trans he₇.agrees))).mono (by
      simp [lowerPrologueEffect, subR64Imm8Effect, callEffect, pushEffect,
        Effect.components, pushR64Effect, pushAddr, hsp₆, BitVec.sub_sub])
  refine ⟨t, ha₁.trans (ha₂.trans (ha₃.trans (ha₄.trans
    (ha₅.trans (ha₆.trans ha₇))))), hr₇, hc₇, he₇.rip, ?_, ?_, hag⟩
  · change stackPtr t = stackPtr s - 32 ∧ _
    refine ⟨he₇.writes.1.trans hpush, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((he₄.agrees.trans (he₅.agrees.trans (he₆.agrees.trans he₇.agrees))).read
        (r := 3) (n := 64) (by simp)).trans
        (he₃.writes.trans ((he₁.agrees.trans he₂.agrees).read (r := 2) (n := 64) (by simp)))
    · exact ((he₅.agrees.trans (he₆.agrees.trans he₇.agrees)).read
        (r := 2) (n := 64) (by simp)).trans
        (he₄.writes.trans ((he₁.agrees.trans (he₂.agrees.trans he₃.agrees)).read
          (r := 6) (n := 64) (by simp)))
    · exact ((he₆.agrees.trans he₇.agrees).read (r := 6) (n := 64) (by simp)).trans
        (he₅.writes.trans ((he₁.agrees.trans (he₂.agrees.trans
          (he₃.agrees.trans he₄.agrees))).read (r := 7) (n := 64) (by simp)))
    · have hsp₅ : stackPtr s₅ = stackPtr s - 24 :=
        ((he₃.agrees.trans (he₄.agrees.trans he₅.agrees)).read
          (r := 4) (n := 64) (by simp)).trans hsp₂
      exact ((he₇.agrees.read (r := 7) (n := 64) (by simp)).trans he₆.writes).trans hsp₅
    · have hw : (Operand.mem (pushAddr s₆) : Operand 64).read t = 0x100156 := he₇.writes.2
      simpa only [hpush] using hw
    · change (Operand.mem (stackPtr s - 8) : Operand 64).read t =
        (Operand.reg 3 : Operand 64).read s
      apply Eq.trans (b := (Operand.mem (stackPtr s - 8) : Operand 64).read s₁) ?_ he₁.writes.2
      apply memLoad_congr
      intro i hi
      change i < 8 at hi
      change (t.external[stackPtr s - 8 + BitVec.ofNat 64 i]?).getD 0 =
        (s₁.external[stackPtr s - 8 + BitVec.ofNat 64 i]?).getD 0
      apply congrArg (fun v : Option UInt8 ↦ v.getD 0)
      apply (he₂.agrees.trans (hg₆.trans he₇.agrees)).byte
      intro c hc hcov
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        subR64Imm8Effect_components, callEffect, pushEffect_components, hpush] at hc
      rcases hc with (rfl | rfl | rfl) | ((rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl))
      all_goals try exact hcov
      obtain ⟨j, hj, heq⟩ := hcov
      apply (show OffsetsApart (-32) 8 (-8) 8 from by unfold OffsetsApart; decide +kernel).ne
        (stackPtr s) hj hi (by decide +kernel)
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg] using heq.symm
  · exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end Base16ct.Proofs.LowerEncode
