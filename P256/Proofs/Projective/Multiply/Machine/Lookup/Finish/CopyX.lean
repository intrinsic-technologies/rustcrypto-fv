import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.Copy32

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def copyXBytes : List UInt8 := [0x48,0x8b,0x44,0x24,0x10,0x48,0x8b,0x4c,0x24,0x18,0x48,0x89,0x84,0x24,0xd8,0x0,0x0,0x0,0x48,0x89,0x8c,0x24,0xe0,0x0,0x0,0x0,0x48,0x8b,0x44,0x24,0x20,0x48,0x89,0x84,0x24,0xe8,0x0,0x0,0x0,0x48,0x8b,0x44,0x24,0x28,0x48,0x89,0x84,0x24,0xf0,0x0,0x0,0x0]

set_option maxHeartbeats 1200000 in
theorem copyX_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (CopyPre 0x1048bd (fun s => (Operand.reg 4 : Operand 64).read s + 16) (fun s => (Operand.reg 4 : Operand 64).read s + 216))
      (codeRange 0x1048bd copyXBytes)
      (Effect.post (copyEffect 0x1048f1 16 216 24 true)) := by
  advance_begin (mov_r64_m64_effect_step 0x1048bd 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.readable 0 (by simp)
  case next => intro s hP; exact boundary_ne_program hout (inProgram_of_textOffset 0x48c2 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1048c2 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1048bd copyXBytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.readable 8 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x48c7 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1048c7 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1048bd copyXBytes 10 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyXBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x48c7 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyXBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x48bd 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x48cf (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1048cf 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 224)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1048bd copyXBytes 18 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyXBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x48cf 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyXBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x48bd 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x48d7 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1048d7 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1048bd copyXBytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.readable 16 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x48dc (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1048dc 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 232)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1048bd copyXBytes 31 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyXBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x48dc 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyXBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x48bd 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x48e4 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1048e4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1048bd copyXBytes 39 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.readable 24 (by simp)
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x48e9 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1048e9 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 240)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1048bd copyXBytes 44 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyXBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x48e9 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyXBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x48bd 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x48f1 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64) (hi : i+8≤32) (hj : j+8≤32) :
      memLoad (memStore mem ((Operand.reg 4 : Operand 64).read s + 216 + BitVec.ofNat 64 i) v)
        ((Operand.reg 4 : Operand 64).read s + 16 + BitVec.ofNat 64 j) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + 16 + BitVec.ofNat 64 j) 64 := by
    apply memLoad_memStore_rangeApart
    intro k hk l hl he
    apply hP.apart (i+k) (by omega) (j+l) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using he
  have h0_16 := fun mem v => hread mem 0 16 v (by decide) (by decide)
  have h8_16 := fun mem v => hread mem 8 16 v (by decide) (by decide)
  have h0_24 := fun mem v => hread mem 0 24 v (by decide) (by decide)
  have h8_24 := fun mem v => hread mem 8 24 v (by decide) (by decide)
  have h16_24 := fun mem v => hread mem 16 24 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at h0_16 h8_16 h0_24 h8_24 h16_24
  apply hH.weaken
  · x86_norm [copyEffect, stackPtr_read]
    all_goals solve_by_elim (maxDepth := 25) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [copyEffect, stackPtr_read, h0_16, h8_16, h0_24, h8_24, h16_24, BitVec.add_assoc]
    all_goals solve_by_elim (maxDepth := 25) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> x86_norm [copyEffect, stackPtr_read]
    all_goals solve_by_elim (maxDepth := 25) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [copyEffect, stackPtr_read]
    all_goals solve_by_elim (maxDepth := 25) only [And.intro, Or.inl, Or.inr, Eq.refl]

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
