import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Program.ScalarFrame.Copy32
import P256.Proofs.Common.EffectCompose.Memory

open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def copyZBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xa0, 0x0, 0x0, 0x0, 0x48, 0x89, 0x43, 0x58, 0x48, 0x8b, 0x84, 0x24, 0x98, 0x0, 0x0, 0x0, 0x48, 0x89, 0x43, 0x50, 0x48, 0x8b, 0x84, 0x24, 0x88, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0x90, 0x0, 0x0, 0x0, 0x48, 0x89, 0x4b, 0x48, 0x48, 0x89, 0x43, 0x40]

theorem copy_z_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Copy32.Pre 0x105d3d (fun s => (Operand.reg 4 : Operand 64).read s + 136) (fun s => (Operand.reg 3 : Operand 64).read s + 64))
      (codeRange 0x105d3d copyZBytes)
      (Effect.post (Copy32.effect 0x105d6d (fun s => (Operand.reg 4 : Operand 64).read s + 136) (fun s => (Operand.reg 3 : Operand 64).read s + 64))) := by
  advance_begin (mov_r64_m64_effect_step 0x105d3d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 160)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 24 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5d45 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105d45 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 88)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105d3d copyZBytes 8 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyZBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x5d45 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyZBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x5d3d 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d49 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105d49 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105d3d copyZBytes 12 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d51 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105d51 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 80)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105d3d copyZBytes 20 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyZBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x5d51 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyZBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x5d3d 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d55 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105d55 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 136)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105d3d copyZBytes 24 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d5d (by decide))
  advance_then (mov_r64_m64_effect_step 0x105d5d 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105d3d copyZBytes 32 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d65 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105d65 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105d3d copyZBytes 40 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyZBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x5d65 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyZBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x5d3d 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d69 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105d69 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105d3d copyZBytes 44 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyZBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x5d69 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyZBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x5d3d 48 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5d6d (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64) (hi : i + 8 ≤ 32) (hj : j + 8 ≤ 32) :
      memLoad (memStore mem ((Operand.reg 3 : Operand 64).read s + 64 + BitVec.ofNat 64 i) v)
        ((Operand.reg 4 : Operand 64).read s + 136 + BitVec.ofNat 64 j) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + 136 + BitVec.ofNat 64 j) 64 := by
    apply memLoad_memStore_rangeApart
    intro k hk l hl he
    apply hP.apart (i+k) (by omega) (j+l) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using he
  have h2416 := fun mem v => hread mem 24 16 v (by decide) (by decide)
  have h240 := fun mem v => hread mem 24 0 v (by decide) (by decide)
  have h248 := fun mem v => hread mem 24 8 v (by decide) (by decide)
  have h160 := fun mem v => hread mem 16 0 v (by decide) (by decide)
  have h168 := fun mem v => hread mem 16 8 v (by decide) (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at h2416 h240 h248 h160 h168
  apply hH.weaken
  · x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect, h2416, h240, h248, h160, h168, BitVec.add_assoc]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect]

end P256.Proofs.Projective.Add.Output
