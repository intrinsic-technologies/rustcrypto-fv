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

def copyYYMinusBytes : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0x60, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x84, 0x24, 0x58, 0x1, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x84, 0x24, 0x48, 0x1, 0x0, 0x0, 0x48, 0x8b, 0x8c, 0x24, 0x50, 0x1, 0x0, 0x0, 0x48, 0x89, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x8]

theorem copy_yy_minus_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Copy32.Pre 0x105c27 (fun s => (Operand.reg 4 : Operand 64).read s + 328) (fun s => (Operand.reg 4 : Operand 64).read s + 8))
      (codeRange 0x105c27 copyYYMinusBytes)
      (Effect.post (Copy32.effect 0x105c5b (fun s => (Operand.reg 4 : Operand 64).read s + 328) (fun s => (Operand.reg 4 : Operand 64).read s + 8))) := by
  advance_begin (mov_r64_m64_effect_step 0x105c27 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 352)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 24 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5c2f (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105c2f 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105c27 copyYYMinusBytes 8 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYYMinusBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x5c2f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYYMinusBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x5c27 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5c34 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105c34 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 344)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105c27 copyYYMinusBytes 13 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5c3c (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105c3c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105c27 copyYYMinusBytes 21 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYYMinusBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x5c3c 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYYMinusBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x5c27 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5c41 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105c41 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 328)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105c27 copyYYMinusBytes 26 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5c49 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105c49 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 336)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105c27 copyYYMinusBytes 34 8
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5c51 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105c51 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105c27 copyYYMinusBytes 42 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYYMinusBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x5c51 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYYMinusBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x5c27 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5c56 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105c56 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105c27 copyYYMinusBytes 47 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYYMinusBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x5c56 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYYMinusBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x5c27 52 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5c5b (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect, BitVec.add_assoc]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect]

end P256.Proofs.Projective.Add.Output
