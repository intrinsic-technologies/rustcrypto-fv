import P256.Proofs.Program.Compare.Mismatch.Support

namespace P256.Proofs.Program.Compare.Mismatch

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem condition_eq {n : Nat} (x y : BitVec n) :
    condHolds 4 (cmpSpec x y) = (x == y) := cmp_zf x y

theorem condition_ne {n : Nat} (x y : BitVec n) :
    condHolds 5 (cmpSpec x y) = !(x == y) := congrArg Bool.not (cmp_zf x y)

theorem main_first [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c8d0) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 64).read s = (Operand.reg 7 : Operand 64).read s then 0x11c8d5 else 0x11c8e0 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11c8d0 3 64 0 7
    (codeRange 0x11c8d0 [0x48, 0x39, 0xf8]) 5 0xb
    (cmp_r64_r64_effect_step 0x11c8d0 0x48 0xf8 (by unfold RexWPrefix; decide) (by decide)) hr hc hb hp
    (program_text_slice hc 0x1c8d0 3 (by decide +kernel))
    (program_text_slice hc 0x1c8d3 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 0 : Operand 64).read s = (Operand.reg 7 : Operand 64).read s
  · have he : ((Operand.reg 0 : Operand 64).read s == (Operand.reg 7 : Operand 64).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 64).read s == (Operand.reg 7 : Operand 64).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem main_second [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c8d5) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 3 : Operand 64).read s = (Operand.reg 14 : Operand 64).read s then 0x11c916 else 0x11c8da := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11c8d5 3 64 3 14
    (codeRange 0x11c8d5 [0x4c, 0x39, 0xf3]) 4 0x3c
    (cmp_r64_r64_effect_step 0x11c8d5 0x4c 0xf3 (by unfold RexWPrefix; decide) (by decide)) hr hc hb hp
    (program_text_slice hc 0x1c8d5 3 (by decide +kernel))
    (program_text_slice hc 0x1c8d8 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_eq] at hip
  by_cases heq : (Operand.reg 3 : Operand 64).read s = (Operand.reg 14 : Operand 64).read s
  · have he : ((Operand.reg 3 : Operand 64).read s == (Operand.reg 14 : Operand 64).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 3 : Operand 64).read s == (Operand.reg 14 : Operand 64).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem main_low32 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c8e0) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 32).read s = (Operand.reg 7 : Operand 32).read s then 0x11c8e4 else 0x11c8f1 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11c8e0 2 32 0 7
    (codeRange 0x11c8e0 [0x39, 0xf8]) 5 0xd
    (cmp_r32_r32_effect_step 0x11c8e0 0xf8 (by decide)) hr hc hb hp
    (program_text_slice hc 0x1c8e0 2 (by decide +kernel))
    (program_text_slice hc 0x1c8e2 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 0 : Operand 32).read s = (Operand.reg 7 : Operand 32).read s
  · have he : ((Operand.reg 0 : Operand 32).read s == (Operand.reg 7 : Operand 32).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 32).read s == (Operand.reg 7 : Operand 32).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem main_shifted32 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c8ec) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 64).read s = (Operand.reg 7 : Operand 64).read s then 0x11c916 else 0x11c8f1 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11c8ec 3 64 0 7
    (codeRange 0x11c8ec [0x48, 0x39, 0xf8]) 4 0x25
    (cmp_r64_r64_effect_step 0x11c8ec 0x48 0xf8 (by unfold RexWPrefix; decide) (by decide)) hr hc hb hp
    (program_text_slice hc 0x1c8ec 3 (by decide +kernel))
    (program_text_slice hc 0x1c8ef 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_eq] at hip
  by_cases heq : (Operand.reg 0 : Operand 64).read s = (Operand.reg 7 : Operand 64).read s
  · have he : ((Operand.reg 0 : Operand 64).read s == (Operand.reg 7 : Operand 64).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 64).read s == (Operand.reg 7 : Operand 64).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem main_shifted16 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c8fc) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 32).read s = (Operand.reg 7 : Operand 32).read s then 0x11c916 else 0x11c900 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11c8fc 2 32 0 7
    (codeRange 0x11c8fc [0x39, 0xf8]) 4 0x16
    (cmp_r32_r32_effect_step 0x11c8fc 0xf8 (by decide)) hr hc hb hp
    (program_text_slice hc 0x1c8fc 2 (by decide +kernel))
    (program_text_slice hc 0x1c8fe 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_eq] at hip
  by_cases heq : (Operand.reg 0 : Operand 32).read s = (Operand.reg 7 : Operand 32).read s
  · have he : ((Operand.reg 0 : Operand 32).read s == (Operand.reg 7 : Operand 32).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 32).read s == (Operand.reg 7 : Operand 32).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem main_low8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11c900) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 8).read s = (Operand.reg 7 : Operand 8).read s then 0x11c905 else 0x11c91a := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11c900 3 8 0 7
    (codeRange 0x11c900 [0x40, 0x38, 0xf8]) 5 0x15
    (cmp_r8_r8_rex_effect_step 0x11c900 0x40 0xf8 (by unfold RexPrefix; decide) (by decide)) hr hc hb hp
    (program_text_slice hc 0x1c900 3 (by decide +kernel))
    (program_text_slice hc 0x1c903 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 0 : Operand 8).read s = (Operand.reg 7 : Operand 8).read s
  · have he : ((Operand.reg 0 : Operand 8).read s == (Operand.reg 7 : Operand 8).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 8).read s == (Operand.reg 7 : Operand 8).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem tail_low32 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce0e) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 32).read s = (Operand.reg 7 : Operand 32).read s then 0x11ce12 else 0x11ce1f := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce0e 2 32 0 7
    (codeRange 0x11ce0e [0x39, 0xf8]) 5 0xd
    (cmp_r32_r32_effect_step 0x11ce0e 0xf8 (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce0e 2 (by decide +kernel))
    (program_text_slice hc 0x1ce10 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 0 : Operand 32).read s = (Operand.reg 7 : Operand 32).read s
  · have he : ((Operand.reg 0 : Operand 32).read s == (Operand.reg 7 : Operand 32).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 32).read s == (Operand.reg 7 : Operand 32).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem tail_shifted32 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce1a) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 64).read s = (Operand.reg 7 : Operand 64).read s then 0x11ce91 else 0x11ce1f := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce1a 3 64 0 7
    (codeRange 0x11ce1a [0x48, 0x39, 0xf8]) 4 0x72
    (cmp_r64_r64_effect_step 0x11ce1a 0x48 0xf8 (by unfold RexWPrefix; decide) (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce1a 3 (by decide +kernel))
    (program_text_slice hc 0x1ce1d 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_eq] at hip
  by_cases heq : (Operand.reg 0 : Operand 64).read s = (Operand.reg 7 : Operand 64).read s
  · have he : ((Operand.reg 0 : Operand 64).read s == (Operand.reg 7 : Operand 64).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 64).read s == (Operand.reg 7 : Operand 64).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem tail_shifted16 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce2a) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 32).read s = (Operand.reg 7 : Operand 32).read s then 0x11ce91 else 0x11ce2e := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce2a 2 32 0 7
    (codeRange 0x11ce2a [0x39, 0xf8]) 4 0x63
    (cmp_r32_r32_effect_step 0x11ce2a 0xf8 (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce2a 2 (by decide +kernel))
    (program_text_slice hc 0x1ce2c 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_eq] at hip
  by_cases heq : (Operand.reg 0 : Operand 32).read s = (Operand.reg 7 : Operand 32).read s
  · have he : ((Operand.reg 0 : Operand 32).read s == (Operand.reg 7 : Operand 32).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 32).read s == (Operand.reg 7 : Operand 32).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem tail_low8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce2e) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 0 : Operand 8).read s = (Operand.reg 7 : Operand 8).read s then 0x11ce33 else 0x11ce44 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce2e 3 8 0 7
    (codeRange 0x11ce2e [0x40, 0x38, 0xf8]) 5 0x11
    (cmp_r8_r8_rex_effect_step 0x11ce2e 0x40 0xf8 (by unfold RexPrefix; decide) (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce2e 3 (by decide +kernel))
    (program_text_slice hc 0x1ce31 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 0 : Operand 8).read s = (Operand.reg 7 : Operand 8).read s
  · have he : ((Operand.reg 0 : Operand 8).read s == (Operand.reg 7 : Operand 8).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 0 : Operand 8).read s == (Operand.reg 7 : Operand 8).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem four_shifted16 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce58) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 6 : Operand 32).read s = (Operand.reg 7 : Operand 32).read s then 0x11ce91 else 0x11ce5c := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce58 2 32 6 7
    (codeRange 0x11ce58 [0x39, 0xfe]) 4 0x35
    (cmp_r32_r32_effect_step 0x11ce58 0xfe (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce58 2 (by decide +kernel))
    (program_text_slice hc 0x1ce5a 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_eq] at hip
  by_cases heq : (Operand.reg 6 : Operand 32).read s = (Operand.reg 7 : Operand 32).read s
  · have he : ((Operand.reg 6 : Operand 32).read s == (Operand.reg 7 : Operand 32).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 6 : Operand 32).read s == (Operand.reg 7 : Operand 32).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem four_low8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce5c) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 6 : Operand 8).read s = (Operand.reg 7 : Operand 8).read s then 0x11ce61 else 0x11ce72 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce5c 3 8 6 7
    (codeRange 0x11ce5c [0x40, 0x38, 0xfe]) 5 0x11
    (cmp_r8_r8_rex_effect_step 0x11ce5c 0x40 0xfe (by unfold RexPrefix; decide) (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce5c 3 (by decide +kernel))
    (program_text_slice hc 0x1ce5f 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 6 : Operand 8).read s = (Operand.reg 7 : Operand 8).read s
  · have he : ((Operand.reg 6 : Operand 8).read s == (Operand.reg 7 : Operand 8).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 6 : Operand 8).read s == (Operand.reg 7 : Operand 8).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

theorem two_low8 [Bindings] (boundary : ReturnBoundary) (s : RamState)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (hb : RegisterBoundary boundary s) (hp : s.RIP = 0x11ce78) :
    ∃ t, Run boundary s t ∧ AgreesExcept [.flags, .rip] s t ∧
      t.RIP = if (Operand.reg 8 : Operand 8).read s = (Operand.reg 7 : Operand 8).read s then 0x11ce7d else 0x11ce94 := by
  obtain ⟨t, ht, hf, hip⟩ := compare_branch 0x11ce78 3 8 8 7
    (codeRange 0x11ce78 [0x41, 0x38, 0xf8]) 5 0x17
    (cmp_r8_r8_rex_effect_step 0x11ce78 0x41 0xf8 (by unfold RexPrefix; decide) (by decide)) hr hc hb hp
    (program_text_slice hc 0x1ce78 3 (by decide +kernel))
    (program_text_slice hc 0x1ce7b 2 (by decide +kernel))
    (by constructor <;> decide +kernel) (by constructor <;> decide +kernel)
    (by constructor <;> decide +kernel)
  refine ⟨t, ht, hf, ?_⟩
  rw [condition_ne] at hip
  by_cases heq : (Operand.reg 8 : Operand 8).read s = (Operand.reg 7 : Operand 8).read s
  · have he : ((Operand.reg 8 : Operand 8).read s == (Operand.reg 7 : Operand 8).read s) = true := beq_iff_eq.mpr heq
    rw [he] at hip
    rw [ite_eq_left heq]
    simpa [branchTarget] using hip
  · have he : ((Operand.reg 8 : Operand 8).read s == (Operand.reg 7 : Operand 8).read s) = false := beq_eq_false_iff_ne.mpr heq
    rw [he] at hip
    rw [ite_eq_right heq]
    simpa [branchTarget] using hip

end P256.Proofs.Program.Compare.Mismatch
