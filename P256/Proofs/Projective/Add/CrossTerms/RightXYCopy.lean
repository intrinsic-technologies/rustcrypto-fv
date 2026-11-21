import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.ScalarFrame.Copy32
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.MovLoad.Triple

open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.CrossTerms

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def rightXY0Bytes : List UInt8 :=
  [0x49, 0x8b, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x40, 0x49, 0x8b, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24, 0x38, 0x49, 0x8b, 0x6, 0x49, 0x8b, 0x4e, 0x8, 0x48, 0x89, 0x4c, 0x24, 0x30, 0x48, 0x89, 0x44, 0x24, 0x28]

theorem rightXY0_copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Copy32.Pre 0x105380
      (fun s => (Operand.reg 14 : Operand 64).read s + 0) (fun s => (Operand.reg 4 : Operand 64).read s + 40))
      (codeRange 0x105380 rightXY0Bytes)
      (Effect.post (Copy32.effect 0x1053a3 (fun s => (Operand.reg 14 : Operand 64).read s + 0) (fun s => (Operand.reg 4 : Operand 64).read s + 40))) := by
  advance_begin (mov_r64_m64_effect_step 0x105380 0x49 (by simp [RexWPrefix]) 0 (.base 14 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 24 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5384 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105384 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105380 rightXY0Bytes 4 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 24 (by simp)
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x5384 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x5380 35 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5389 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105389 0x49 (by simp [RexWPrefix]) 0 (.base 14 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105380 rightXY0Bytes 9 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x538d (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10538d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105380 rightXY0Bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 16 (by simp)
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x538d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x5380 35 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5392 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105392 0x49 (by simp [RexWPrefix]) 0 (.base 14 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105380 rightXY0Bytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5395 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105395 0x49 (by simp [RexWPrefix]) 1 (.base 14 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105380 rightXY0Bytes 21 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5399 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105399 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105380 rightXY0Bytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 8 (by simp)
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x5399 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x5380 35 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x539e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10539e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105380 rightXY0Bytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 0 (by simp)
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x539e 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY0Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x5380 35 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53a3 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64) (hi : i + 8 ≤ 32) (hj : j + 8 ≤ 32) :
      memLoad (memStore mem (((Operand.reg 4 : Operand 64).read s + 40) + BitVec.ofNat 64 i) v)
        (((Operand.reg 14 : Operand 64).read s + 0) + BitVec.ofNat 64 j) 64 =
      memLoad mem (((Operand.reg 14 : Operand 64).read s + 0) + BitVec.ofNat 64 j) 64 := by
    apply memLoad_memStore_rangeApart
    intro k hk l hl he
    apply hP.apart (i+k) (by omega) (j+l) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using he
  have h24_16 := fun mem v => hread mem 24 16 v (by decide) (by decide)
  have h24_0 := fun mem v => hread mem 24 0 v (by decide) (by decide)
  have h24_8 := fun mem v => hread mem 24 8 v (by decide) (by decide)
  have h16_0 := fun mem v => hread mem 16 0 v (by decide) (by decide)
  have h16_8 := fun mem v => hread mem 16 8 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at h24_16 h24_0 h24_8 h16_0 h16_8
  apply hH.weaken
  · x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect, BitVec.add_zero, BitVec.add_assoc, h24_16, h24_0, h24_8, h16_0, h16_8]
    all_goals (repeat constructor <;> rfl)
  · intro i
    cases i <;> x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect]

def rightXY1Bytes : List UInt8 :=
  [0x49, 0x8b, 0x46, 0x38, 0x48, 0x89, 0x44, 0x24, 0x20, 0x49, 0x8b, 0x46, 0x30, 0x48, 0x89, 0x44, 0x24, 0x18, 0x49, 0x8b, 0x46, 0x20, 0x49, 0x8b, 0x4e, 0x28, 0x48, 0x89, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x8]

theorem rightXY1_copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Copy32.Pre 0x1053a3
      (fun s => (Operand.reg 14 : Operand 64).read s + 32) (fun s => (Operand.reg 4 : Operand 64).read s + 8))
      (codeRange 0x1053a3 rightXY1Bytes)
      (Effect.post (Copy32.effect 0x1053c7 (fun s => (Operand.reg 14 : Operand 64).read s + 32) (fun s => (Operand.reg 4 : Operand 64).read s + 8))) := by
  advance_begin (mov_r64_m64_effect_step 0x1053a3 0x49 (by simp [RexWPrefix]) 0 (.base 14 (.d8 56)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 24 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x53a7 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1053a7 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1053a3 rightXY1Bytes 4 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 24 (by simp)
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x53a7 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x53a3 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53ac (by decide))
  advance_then (mov_r64_m64_effect_step 0x1053ac 0x49 (by simp [RexWPrefix]) 0 (.base 14 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1053a3 rightXY1Bytes 9 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53b0 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1053b0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1053a3 rightXY1Bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 16 (by simp)
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x53b0 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x53a3 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53b5 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1053b5 0x49 (by simp [RexWPrefix]) 0 (.base 14 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1053a3 rightXY1Bytes 18 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53b9 (by decide))
  advance_then (mov_r64_m64_effect_step 0x1053b9 0x49 (by simp [RexWPrefix]) 1 (.base 14 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1053a3 rightXY1Bytes 22 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53bd (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1053bd 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1053a3 rightXY1Bytes 26 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 8 (by simp)
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x53bd 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x53a3 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53c2 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1053c2 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x1053a3 rightXY1Bytes 31 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 0 (by simp)
    · x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x53c2 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, rightXY1Bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x53a3 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x53c7 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64) (hi : i + 8 ≤ 32) (hj : j + 8 ≤ 32) :
      memLoad (memStore mem (((Operand.reg 4 : Operand 64).read s + 8) + BitVec.ofNat 64 i) v)
        (((Operand.reg 14 : Operand 64).read s + 32) + BitVec.ofNat 64 j) 64 =
      memLoad mem (((Operand.reg 14 : Operand 64).read s + 32) + BitVec.ofNat 64 j) 64 := by
    apply memLoad_memStore_rangeApart
    intro k hk l hl he
    apply hP.apart (i+k) (by omega) (j+l) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using he
  have h24_16 := fun mem v => hread mem 24 16 v (by decide) (by decide)
  have h24_0 := fun mem v => hread mem 24 0 v (by decide) (by decide)
  have h24_8 := fun mem v => hread mem 24 8 v (by decide) (by decide)
  have h16_0 := fun mem v => hread mem 16 0 v (by decide) (by decide)
  have h16_8 := fun mem v => hread mem 16 8 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at h24_16 h24_0 h24_8 h16_0 h16_8
  apply hH.weaken
  · x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect, BitVec.add_zero, BitVec.add_assoc, h24_16, h24_0, h24_8, h16_0, h16_8]
    all_goals (repeat constructor <;> rfl)
  · intro i
    cases i <;> x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect]

end P256.Proofs.Projective.Add.CrossTerms
