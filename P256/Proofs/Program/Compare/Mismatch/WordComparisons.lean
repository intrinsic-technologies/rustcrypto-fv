import P256.Proofs.Program.Compare.Mismatch.Comparisons
import P256.Proofs.Program.Compare.WordInstructions.Cmp

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

open WordInstructions

theorem main_low16 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c8f1) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
        then 0x11c8f6 else 0x11c900 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11c8f1 3 16 0 7
    (codeRange 0x11c8f1 [0x66, 0x39, 0xf8]) 5 0xa
    (X86Proofs.cmp_r16_r16_effect_step 0x11c8f1 0xf8 (by decide)) hr hc hb hp
    (program_text_slice hc 0x1c8f1 3 (by decide +kernel))
    (program_text_slice hc 0x1c8f4 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 0 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
  · have he : ((Operand.reg 0 : Operand 16).read s == (Operand.reg 7 : Operand 16).read s) = true :=
      beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 16).read s ==
      (Operand.reg 7 : Operand 16).read s) = false :=
      beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem main_shifted8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c911) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
        then 0x11c916 else 0x11c91a := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11c911 3 16 0 7
    (codeRange 0x11c911 [0x66, 0x39, 0xf8]) 5 0x4
    (X86Proofs.cmp_r16_r16_effect_step 0x11c911 0xf8 (by decide)) hr hc hb hp
    (program_text_slice hc 0x1c911 3 (by decide +kernel))
    (program_text_slice hc 0x1c914 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 0 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
  · have he : ((Operand.reg 0 : Operand 16).read s == (Operand.reg 7 : Operand 16).read s) = true :=
      beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 16).read s ==
      (Operand.reg 7 : Operand 16).read s) = false :=
      beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem tail_low16 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce1f) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
        then 0x11ce24 else 0x11ce2e := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce1f 3 16 0 7
    (codeRange 0x11ce1f [0x66, 0x39, 0xf8]) 5 0xa
    (X86Proofs.cmp_r16_r16_effect_step 0x11ce1f 0xf8 (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce1f 3 (by decide +kernel))
    (program_text_slice hc 0x1ce22 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 0 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
  · have he : ((Operand.reg 0 : Operand 16).read s == (Operand.reg 7 : Operand 16).read s) = true :=
      beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 16).read s ==
      (Operand.reg 7 : Operand 16).read s) = false :=
      beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem tail_shifted8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce3f) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
        then 0x11ce91 else 0x11ce44 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce3f 3 16 0 7
    (codeRange 0x11ce3f [0x66, 0x39, 0xf8]) 4 0x4d
    (X86Proofs.cmp_r16_r16_effect_step 0x11ce3f 0xf8 (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce3f 3 (by decide +kernel))
    (program_text_slice hc 0x1ce42 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_eq] at hip
  by_cases heq : (Operand.reg 0 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
  · have he : ((Operand.reg 0 : Operand 16).read s == (Operand.reg 7 : Operand 16).read s) = true :=
      beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 16).read s ==
      (Operand.reg 7 : Operand 16).read s) = false :=
      beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem four_low16 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce4d) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 6 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
        then 0x11ce52 else 0x11ce5c := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce4d 3 16 6 7
    (codeRange 0x11ce4d [0x66, 0x39, 0xfe]) 5 0xa
    (X86Proofs.cmp_r16_r16_effect_step 0x11ce4d 0xfe (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce4d 3 (by decide +kernel))
    (program_text_slice hc 0x1ce50 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 6 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
  · have he : ((Operand.reg 6 : Operand 16).read s == (Operand.reg 7 : Operand 16).read s) = true :=
      beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 6 : Operand 16).read s ==
      (Operand.reg 7 : Operand 16).read s) = false :=
      beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem four_shifted8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce6d) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 6 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
        then 0x11ce91 else 0x11ce72 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce6d 3 16 6 7
    (codeRange 0x11ce6d [0x66, 0x39, 0xfe]) 4 0x1f
    (X86Proofs.cmp_r16_r16_effect_step 0x11ce6d 0xfe (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce6d 3 (by decide +kernel))
    (program_text_slice hc 0x1ce70 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_eq] at hip
  by_cases heq : (Operand.reg 6 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
  · have he : ((Operand.reg 6 : Operand 16).read s == (Operand.reg 7 : Operand 16).read s) = true :=
      beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 6 : Operand 16).read s ==
      (Operand.reg 7 : Operand 16).read s) = false :=
      beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem two_shifted8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce8b) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 8 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
        then 0x11ce91 else 0x11ce94 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce8b 4 16 8 7
    (codeRange 0x11ce8b [0x66, 0x41, 0x39, 0xf8]) 5 0x3
    (X86Proofs.cmp_r16_r16_rex_effect_step 0x11ce8b 0x41 0xf8
      (by unfold RexNoWPrefix; decide) (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce8b 4 (by decide +kernel))
    (program_text_slice hc 0x1ce8f 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 8 : Operand 16).read s = (Operand.reg 7 : Operand 16).read s
  · have he : ((Operand.reg 8 : Operand 16).read s == (Operand.reg 7 : Operand 16).read s) = true :=
      beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 8 : Operand 16).read s ==
      (Operand.reg 7 : Operand 16).read s) = false :=
      beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

end P256.Proofs.Program.Compare.Mismatch
