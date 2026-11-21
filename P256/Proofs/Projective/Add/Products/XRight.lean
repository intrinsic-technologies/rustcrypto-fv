import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Program.ScalarFrame.Copy32

open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Products.XRight

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def source := (fun s : RamState => (Operand.reg 6 : Operand 64).read s + 0)
def destination := (fun s : RamState => (Operand.reg 4 : Operand 64).read s + 8)
def bytes : List UInt8 := [0x48, 0x8b, 0x46, 0x18, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x46, 0x10, 0x48, 0x89, 0x44, 0x24, 0x18, 0x48, 0x8b, 0x6, 0x48, 0x8b, 0x4e, 0x8, 0x48, 0x89, 0x4c, 0x24, 0x10, 0x48, 0x89, 0x44, 0x24, 0x8]

theorem copy [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Copy32.Pre 0x10522a source destination)
      (codeRange 0x10522a bytes) (Effect.post (Copy32.effect 0x10524d source destination)) := by
  advance_begin (mov_r64_m64_effect_step 0x10522a 0x48 (by simp [RexWPrefix]) 0 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 24 (by simp)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x522e (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x10522e 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10522a bytes 4 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 24 (by simp) 0x522e 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 24 (by simp) 0x522a 35 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5233 (by decide))
  advance_then (mov_r64_m64_effect_step 0x105233 0x48 (by simp [RexWPrefix]) 0 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10522a bytes 9 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5237 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105237 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10522a bytes 13 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 16 (by simp) 0x5237 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 16 (by simp) 0x522a 35 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x523c (by decide))
  advance_then (mov_r64_m64_effect_step 0x10523c 0x48 (by simp [RexWPrefix]) 0 (.base 6 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10522a bytes 18 3
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x523f (by decide))
  advance_then (mov_r64_m64_effect_step 0x10523f 0x48 (by simp [RexWPrefix]) 1 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10522a bytes 21 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [source, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5243 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105243 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10522a bytes 25 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 8 (by simp) 0x5243 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 8 (by simp) 0x522a 35 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x5248 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x105248 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10522a bytes 30 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [destination, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [destination, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 0 (by simp) 0x5248 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [destination, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hP.codeApart 0 (by simp) 0x522a 35 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x524d (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64)
      (hi : i + 8 ≤ 32) (hj : j + 8 ≤ 32) :
      memLoad (memStore mem (destination s + BitVec.ofNat 64 i) v)
        (source s + BitVec.ofNat 64 j) 64 = memLoad mem (source s + BitVec.ofNat 64 j) 64 := by
    apply memLoad_memStore_rangeApart
    intro k hk l hl he
    apply hP.apart (i+k) (by omega) (j+l) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he
  have h24_16 := fun mem v => hread mem 24 16 v (by decide) (by decide)
  have h24_0 := fun mem v => hread mem 24 0 v (by decide) (by decide)
  have h24_8 := fun mem v => hread mem 24 8 v (by decide) (by decide)
  have h16_0 := fun mem v => hread mem 16 0 v (by decide) (by decide)
  have h16_8 := fun mem v => hread mem 16 8 v (by decide) (by decide)
  simp only [source, destination, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd] at h24_16 h24_0 h24_8 h16_0 h16_8
  apply hH.weaken
  · x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect, source, destination, h24_16, h24_0, h24_8, h16_0, h16_8, BitVec.add_assoc, BitVec.add_zero]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect, source, destination, BitVec.add_assoc]

end P256.Proofs.Projective.Add.Products.XRight
