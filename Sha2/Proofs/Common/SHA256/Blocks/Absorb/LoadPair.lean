import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Instruction

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Blocks

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

private theorem ofNat_add64 (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

attribute [local x86_compose] readReg BitVec.add_zero ofNat_add64 Nat.add_assoc

macro "advance_absorb_then " step:term " next " hn:term
    " using " "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let hs := hs.getElems
  let (s, t, hP, hH, hO) := (Lean.mkIdent `s, Lean.mkIdent `t, Lean.mkIdent `hP,
    Lean.mkIdent `hH, Lean.mkIdent `hO)
  `(tactic| (
    refine AdvanceTriple.block_then ?k $step ?loc ?sub ?full ?mid
    try (case loc => x86_local)
    try (case sub => x86_sub)
    try (case full => x86_full)
    (case' mid =>
      intro $s $t $hP $hH $hO
      refine (fun h : (_ ∧ _) ∧ _ => ⟨h.1.1, h.1.2, h.2⟩) ?_
      constructor
      · x86_carry_mid $hP $hH $hO
        all_goals try x86_norm [$hs,*]
        all_goals first | assumption | rfl | (congr 1 <;> omega)
      · x86_norm [$hs,*]
        have here := $hn
        x86_norm [$hs,*] at here
        exact here)
    case' k => x86_norm [$hs,*]))

set_option maxHeartbeats 500000 in
theorem loadPair_run [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (index src len : BitVec 4) (pointers lengths : Disp)
    (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p (bytes (.loadPair index src len pointers lengths)).length) :
    Contract boundary p (.loadPair index src len pointers lengths) := by
  intro initial ready loaded pre
  have distinct := pre.distinct.map (S := fun a b : BitVec 5 => a ≠ b)
    (fun r => r.setWidth 5)
    (fun a b hab he => hab ((widened_eq _ _).mp he))
  change [index.setWidth 5, src.setWidth 5, len.setWidth 5, 0#5, 4#5].Pairwise
    (· ≠ ·) at distinct
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true,
    List.Pairwise.nil] at distinct
  rcases distinct with ⟨⟨his, hil, hi0, hi4⟩, ⟨hsl, hs0, hs4⟩, ⟨hl0, hl4⟩, _⟩
  let c₁ := encodeMovR64M64 0 (.sib 4 none 0 pointers)
  let c₂ := encodeMovR64M64 src (.sib 0 (some index) 3 .none)
  let c₃ := encodeMovR64M64 0 (.sib 4 none 0 lengths)
  let c₄ := encodeMovR64M64 len (.sib 0 (some index) 3 .none)
  have length₂ : c₂.length = 4 := rfl
  have length₄ : c₄.length = 4 := rfl
  have length₁ : c₁.length = movLoadLen (.sib 4 none 0 pointers) := by
    dsimp only [c₁, encodeMovR64M64, movLoadLen]
    simp only [List.length_cons]
    omega
  have length₃ : c₃.length = movLoadLen (.sib 4 none 0 lengths) := by
    dsimp only [c₃, encodeMovR64M64, movLoadLen]
    simp only [List.length_cons]
    omega
  have total : (bytes (.loadPair index src len pointers lengths)).length =
      c₁.length + 4 + c₃.length + 4 := by
    change (c₁ ++ c₂ ++ c₃ ++ c₄).length = _
    simp only [List.length_append, length₂, length₄]
  have part (before current suffix : List UInt8) :
      ∀ x ∈ codeRange (p + BitVec.ofNat 64 before.length) current,
        x ∈ codeRange p (before ++ current ++ suffix) := by
    intro x hx
    rw [List.append_assoc, codeRange_append, codeRange_append]
    exact List.mem_append_right _ (List.mem_append_left _ hx)
  have part₁ : ∀ x ∈ codeRange p c₁,
      x ∈ codeRange p (bytes (.loadPair index src len pointers lengths)) := by
    intro x hx
    change x ∈ codeRange p (c₁ ++ c₂ ++ c₃ ++ c₄)
    rw [List.append_assoc, List.append_assoc, codeRange_append]
    exact List.mem_append_left _ hx
  have part₂ : ∀ x ∈ codeRange (p + BitVec.ofNat 64 c₁.length) c₂,
      x ∈ codeRange p (bytes (.loadPair index src len pointers lengths)) := by
    change ∀ x ∈ codeRange (p + BitVec.ofNat 64 c₁.length) c₂,
      x ∈ codeRange p (c₁ ++ c₂ ++ c₃ ++ c₄)
    simpa only [List.append_assoc] using part c₁ c₂ (c₃ ++ c₄)
  have part₃ : ∀ x ∈ codeRange (p + BitVec.ofNat 64 (c₁.length + 4)) c₃,
      x ∈ codeRange p (bytes (.loadPair index src len pointers lengths)) := by
    change ∀ x ∈ codeRange (p + BitVec.ofNat 64 (c₁.length + 4)) c₃,
      x ∈ codeRange p (c₁ ++ c₂ ++ c₃ ++ c₄)
    simpa only [List.length_append, length₂] using part (c₁ ++ c₂) c₃ c₄
  have part₄ : ∀ x ∈ codeRange (p + BitVec.ofNat 64 (c₁.length + 4 + c₃.length)) c₄,
      x ∈ codeRange p (bytes (.loadPair index src len pointers lengths)) := by
    change ∀ x ∈ codeRange (p + BitVec.ofNat 64 (c₁.length + 4 + c₃.length)) c₄,
      x ∈ codeRange p (c₁ ++ c₂ ++ c₃ ++ c₄)
    simpa only [List.length_append, length₂, List.append_nil] using
      part (c₁ ++ c₂ ++ c₃) c₄ []
  have block : Contract boundary p (.loadPair index src len pointers lengths) := by
    unfold Contract
    advance_reloc_begin
      (load64_step p 0 (.sib 4 none 0 pointers) pre.validPointer)
      next (by
        have here := boundary_ne_program outside (inside c₁.length (by rw [total]; omega))
        x86_norm [length₁] at here
        exact here)
    try (case sub => exact part₁)
    advance_absorb_then (load64_step (p + BitVec.ofNat 64 c₁.length)
      src (.sib 0 (some index) 3 .none) pre.validIndex)
      next (boundary_ne_program outside (inside (c₁.length + 4) (by rw [total]; omega)))
      using [length₁, length₃, hi0, hi4, his, hil, hsl, hs0, hs4, hl0, hl4,
        Ne.symm hi0, Ne.symm hi4, Ne.symm his, Ne.symm hil, Ne.symm hsl,
        Ne.symm hs0, Ne.symm hs4, Ne.symm hl0, Ne.symm hl4]
    try (case sub => exact part₂)
    advance_absorb_then (load64_step (p + BitVec.ofNat 64 (c₁.length + 4))
      0 (.sib 4 none 0 lengths) pre.validLength)
      next (boundary_ne_program outside (inside (c₁.length + 4 + c₃.length)
        (by rw [total]; omega)))
      using [length₁, length₃, hi0, hi4, his, hil, hsl, hs0, hs4, hl0, hl4,
        Ne.symm hi0, Ne.symm hi4, Ne.symm his, Ne.symm hil, Ne.symm hsl,
        Ne.symm hs0, Ne.symm hs4, Ne.symm hl0, Ne.symm hl4]
    try (case sub => exact part₃)
    advance_absorb_then (load64_step (p + BitVec.ofNat 64 (c₁.length + 4 + c₃.length))
      len (.sib 0 (some index) 3 .none) pre.validIndex)
      next (boundary_ne_program outside (inside (c₁.length + 4 + c₃.length + 4)
        (by rw [total]; omega)))
      using [length₁, length₃, hi0, hi4, his, hil, hsl, hs0, hs4, hl0, hl4,
        Ne.symm hi0, Ne.symm hi4, Ne.symm his, Ne.symm hil, Ne.symm hsl,
        Ne.symm hs0, Ne.symm hs4, Ne.symm hl0, Ne.symm hl4]
    try (case sub => exact part₄)
    advance_finish [effect, total, length₁, length₃,
      hi0, hi4, his, hil, hsl, hs0, hs4, hl0, hl4,
      Ne.symm hi0, Ne.symm hi4, Ne.symm his, Ne.symm hil, Ne.symm hsl,
      Ne.symm hs0, Ne.symm hs4, Ne.symm hl0, Ne.symm hl4]
  exact block initial ready loaded pre

end Sha2.Proofs.Common.SHA256.Absorb.Blocks
