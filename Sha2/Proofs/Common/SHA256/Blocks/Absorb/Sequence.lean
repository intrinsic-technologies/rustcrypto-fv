import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Instruction
import Sha2.Proofs.Common.Instructions.ForgetFlags

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Blocks

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

attribute [local x86_compose] readReg

theorem count_run [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (rest : BitVec 4)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes (.count rest)).length) :
    Contract boundary p (.count rest) := by
  unfold Contract
  advance_reloc_begin (move_step p 2 rest)
    next (boundary_ne_program outside (inside 3 (by
      simp [bytes, encodeMovR64R64, encodeShrR64Imm8])))
  try (case sub => exact codeRange_mem_of_take (by rfl))
  advance_reloc_then (shift_right_step (p + 3) 2)
    next (boundary_ne_program outside (inside 7 (by
      simp [bytes, encodeMovR64R64, encodeShrR64Imm8])))
  try (case sub => exact codeRange_mem_of_drop 3 (by rfl))
  advance_finish [effect, bytes, encodeMovR64R64, encodeShrR64Imm8]

theorem prepare_run [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (r : Registers)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes (.prepare r)).length) :
    Contract boundary p (.prepare r) := by
  intro initial ready loaded pre
  have distinct := pre.distinct
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true,
    List.Pairwise.nil] at distinct
  rcases distinct with ⟨⟨htl, htr, ht2⟩, ⟨hlr, hl2⟩, hr2⟩
  have ht2' : r.tail.setWidth 5 ≠ 2#5 := by
    change r.tail.setWidth 5 ≠ (2 : BitVec 4).setWidth 5
    exact fun h => ht2 ((widened_eq _ _).mp h)
  have hl2' : r.length.setWidth 5 ≠ 2#5 := by
    change r.length.setWidth 5 ≠ (2 : BitVec 4).setWidth 5
    exact fun h => hl2 ((widened_eq _ _).mp h)
  have hr2' : r.remaining.setWidth 5 ≠ 2#5 := by
    change r.remaining.setWidth 5 ≠ (2 : BitVec 4).setWidth 5
    exact fun h => hr2 ((widened_eq _ _).mp h)
  have hlr' : r.length.setWidth 5 ≠ r.remaining.setWidth 5 :=
    fun h => hlr ((widened_eq _ _).mp h)
  have block : Contract boundary p (.prepare r) := by
    unfold Contract
    advance_reloc_begin (constant_step p 2 64)
      next (boundary_ne_program outside (inside 5 (by
        simp [bytes, encodeMovR32Imm32, encodeSubR64R64, encodeMovR64R64])))
    try (case sub => exact codeRange_mem_of_take (by rfl))
    try (case full =>
      intro s _
      x86_norm [ht2', hl2', hr2', hlr', Ne.symm ht2', Ne.symm hl2', Ne.symm hr2',
        Ne.symm hlr', List.forall_mem_cons, List.forall_mem_nil])
    try x86_norm [ht2', hl2', hr2', hlr', Ne.symm ht2', Ne.symm hl2', Ne.symm hr2', Ne.symm hlr']
    advance_reloc_then (subtract_step (p + 5) 2 r.tail)
      next (boundary_ne_program outside (inside 8 (by
        simp [bytes, encodeMovR32Imm32, encodeSubR64R64, encodeMovR64R64])))
    try (case sub => exact codeRange_mem_of_drop 5 (by rfl))
    try (case full =>
      intro s _
      x86_norm [ht2', hl2', hr2', hlr', Ne.symm ht2', Ne.symm hl2', Ne.symm hr2',
        Ne.symm hlr', List.forall_mem_cons, List.forall_mem_nil])
    try x86_norm [ht2', hl2', hr2', hlr', Ne.symm ht2', Ne.symm hl2', Ne.symm hr2', Ne.symm hlr']
    advance_reloc_then (move_step (p + 8) r.remaining r.length)
      next (boundary_ne_program outside (inside 11 (by
        simp [bytes, encodeMovR32Imm32, encodeSubR64R64, encodeMovR64R64])))
    try (case sub => exact codeRange_mem_of_drop 8 (by rfl))
    try (case full =>
      intro s _
      x86_norm [ht2', hl2', hr2', hlr', Ne.symm ht2', Ne.symm hl2', Ne.symm hr2',
        Ne.symm hlr', List.forall_mem_cons, List.forall_mem_nil])
    try x86_norm [ht2', hl2', hr2', hlr', Ne.symm ht2', Ne.symm hl2', Ne.symm hr2', Ne.symm hlr']
    advance_reloc_then (subtract_step (p + 11) r.remaining 2)
      next (boundary_ne_program outside (inside 14 (by
        simp [bytes, encodeMovR32Imm32, encodeSubR64R64, encodeMovR64R64])))
    try (case sub => exact codeRange_mem_of_drop 11 (by rfl))
    try (case full =>
      intro s _
      x86_norm [ht2', hl2', hr2', hlr', Ne.symm ht2', Ne.symm hl2', Ne.symm hr2',
        Ne.symm hlr', List.forall_mem_cons, List.forall_mem_nil])
    try x86_norm [ht2', hl2', hr2', hlr', Ne.symm ht2', Ne.symm hl2', Ne.symm hr2', Ne.symm hlr']
    advance_finish [effect, bytes, encodeMovR32Imm32, encodeSubR64R64, encodeMovR64R64,
      ht2', hl2', hr2', hlr', Ne.symm ht2', Ne.symm hl2', Ne.symm hr2', Ne.symm hlr']
  exact block initial ready loaded pre

macro "sha256_absorb_split " n:num "," pc:term "," src:term "," rest:term
    "," outside:term "," inside:term "," low:ident
    " [" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let hs := hs.getElems
  let lastPC ← `($pc + $(Lean.quote (16 + n.getNat)))
  let ls ← `(Lean.Parser.Tactic.simpLemma| $low:ident)
  let simplify ← `(tactic| try x86_norm [$hs,*])
  let mut steps : Array (Lean.TSyntax `term × Nat × Nat) := #[]
  steps := steps.push (← `(move_step $pc 0 $rest), 0, 3)
  steps := steps.push (← `(constant64_step ($pc + 3) 1 0x7fffffffffffffc0), 3, 10)
  steps := steps.push (← `(StepEffect.forgetFlags (h := and_step ($pc + 13) 0 1)), 13, 3)
  steps := steps.push (← `(StepEffect.forgetFlags (h :=
    (show StepEffect _ _ (andR32Imm8Effect ($pc + 16) $n (($rest).setWidth 5) 63) from by
      simpa only [encodeAndR32Imm8, $ls, ↓reduceIte, List.length_cons, immBytes_length]
        using and32_step ($pc + 16) $rest))), 16, n.getNat)
  steps := steps.push (← `(StepEffect.forgetFlags (h := add_step $lastPC $src 0)),
    16 + n.getNat, 3)
  let mut result ← `(tactic| advance_finish [effect, bytes, encodeMovR64R64,
    encodeMovR64Imm64, encodeAndR64R64, encodeAndR32Imm8, encodeAddR64R64, $ls, $hs,*])
  for (step, offset, len) in steps.reverse do
    let off := Lean.quote offset
    let hn ← `(boundary_ne_program $outside ($inside $(Lean.quote (offset + len)) (by
      simp [bytes, encodeMovR64R64, encodeMovR64Imm64, encodeAndR64R64,
        encodeAndR32Imm8, encodeAddR64R64, $ls])))
    let first ← if offset = 0 then `(tactic| (
      advance_reloc_begin $step next $hn
      try (case sub => exact codeRange_mem_of_take (by rfl))))
      else `(tactic| (
        advance_reloc_then $step next $hn
        try (case sub => exact codeRange_mem_of_drop $off (by
          simp [bytes, encodeMovR64R64, encodeMovR64Imm64, encodeAndR64R64,
            encodeAndR32Imm8, encodeAddR64R64, immBytes, List.drop_append, $ls] <;> rfl))))
    result ← `(tactic| (
      $first:tactic
      try (case full => intro s _; x86_norm [$hs,*, List.forall_mem_cons, List.forall_mem_nil])
      $simplify:tactic
      $result:tactic))
  pure result

theorem splitTail_run [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (src rest : BitVec 4) (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p (bytes (.splitTail src rest)).length) :
    Contract boundary p (.splitTail src rest) := by
  intro initial ready loaded pre
  have distinct := pre.distinct
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true,
    List.Pairwise.nil] at distinct
  rcases distinct with ⟨⟨hsr, hs0, hs1⟩, ⟨hr0, hr1⟩, _⟩
  have hsr' : src.setWidth 5 ≠ rest.setWidth 5 :=
    fun h => hsr ((widened_eq _ _).mp h)
  have hs0' : src.setWidth 5 ≠ 0#5 := by
    change src.setWidth 5 ≠ (0#4).setWidth 5
    exact fun h => hs0 ((widened_eq _ _).mp h)
  have hs1' : src.setWidth 5 ≠ 1#5 := by
    change src.setWidth 5 ≠ (1#4).setWidth 5
    exact fun h => hs1 ((widened_eq _ _).mp h)
  have hr0' : rest.setWidth 5 ≠ 0#5 := by
    change rest.setWidth 5 ≠ (0#4).setWidth 5
    exact fun h => hr0 ((widened_eq _ _).mp h)
  have hr1' : rest.setWidth 5 ≠ 1#5 := by
    change rest.setWidth 5 ≠ (1#4).setWidth 5
    exact fun h => hr1 ((widened_eq _ _).mp h)
  have block : Contract boundary p (.splitTail src rest) := by
    unfold Contract
    by_cases low : rest.toNat < 8
    · sha256_absorb_split 3, p, src, rest, outside, inside, low
        [hsr', hs0', hs1', hr0', hr1', Ne.symm hsr', Ne.symm hs0', Ne.symm hs1',
          Ne.symm hr0', Ne.symm hr1']
    · sha256_absorb_split 4, p, src, rest, outside, inside, low
        [hsr', hs0', hs1', hr0', hr1', Ne.symm hsr', Ne.symm hs0', Ne.symm hs1',
          Ne.symm hr0', Ne.symm hr1']
  exact block initial ready loaded pre

end Sha2.Proofs.Common.SHA256.Absorb.Blocks
