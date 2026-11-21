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

def copyYBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x43, 0x38, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x89, 0x43, 0x30, 0x48, 0x8b, 0x44, 0x24, 0x8, 0x48, 0x8b, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x4b, 0x28, 0x48, 0x89, 0x43, 0x20]

theorem copy_y_block [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Copy32.Pre 0x105cd1 (fun s => (Operand.reg 4 : Operand 64).read s + 8) (fun s => (Operand.reg 3 : Operand 64).read s + 32))
      (codeRange 0x105cd1 copyYBytes)
      (Effect.post (Copy32.effect 0x105cf5 (fun s => (Operand.reg 4 : Operand 64).read s + 8) (fun s => (Operand.reg 3 : Operand 64).read s + 32))) := by
  advance_begin (mov_r64_m64_effect_step 0x105cd1 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 24 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x5cd6 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105cd6 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 56)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105cd1 copyYBytes 5 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x5cd6 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x5cd1 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5cda (by decide))
  advance_then (mov_r64_m64_effect_step 0x105cda 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105cd1 copyYBytes 9 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5cdf (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105cdf 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 48)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105cd1 copyYBytes 14 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x5cdf 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x5cd1 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5ce3 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105ce3 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105cd1 copyYBytes 18 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5ce8 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105ce8 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105cd1 copyYBytes 23 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5ced (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105ced 0x48 (by simp [RexWPrefix]) 1 (.base 3 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105cd1 copyYBytes 28 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x5ced 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x5cd1 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5cf1 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105cf1 0x48 (by simp [RexWPrefix]) 0 (.base 3 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x105cd1 copyYBytes 32 4
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x5cf1 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, copyYBytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x5cd1 36 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5cf5 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64) (hi : i + 8 ≤ 32) (hj : j + 8 ≤ 32) :
      memLoad (memStore mem ((Operand.reg 3 : Operand 64).read s + 32 + BitVec.ofNat 64 i) v)
        ((Operand.reg 4 : Operand 64).read s + 8 + BitVec.ofNat 64 j) 64 =
      memLoad mem ((Operand.reg 4 : Operand 64).read s + 8 + BitVec.ofNat 64 j) 64 := by
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
