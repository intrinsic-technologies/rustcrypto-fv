import P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.Result
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame

namespace P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.FirstResult

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x4c, 0x24, 0x18, 0x48, 0x8b, 0x54, 0x24, 0x20, 0x48, 0x89, 0x54, 0x24, 0x78, 0x48, 0x8b, 0x54, 0x24, 0x28, 0x48, 0x89, 0x94, 0x24, 0x80, 0x0, 0x0, 0x0, 0x48, 0x89, 0x44, 0x24, 0x68, 0x48, 0x89, 0x4c, 0x24, 0x70]

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x109b1c bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x9b1c bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (Copy32.Pre 0x109b1c
      (fun s => (Operand.reg 4 : Operand 64).read s + 16)
      (fun s => (Operand.reg 4 : Operand 64).read s + 104))
      (codeRange 0x109b1c bytes)
      (Effect.post (Result.effect 0x109b47
        (fun s => (Operand.reg 4 : Operand 64).read s + 16)
        (fun s => (Operand.reg 4 : Operand 64).read s + 104))) := by
  advance_begin (mov_r64_m64_effect_step 0x109b1c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.readable 0 (by simp)
  case next =>
    intro _ _
    exact boundary_ne_program hout (inProgram_of_textOffset 0x9b21 (by decide))
  advance_then (mov_r64_m64_effect_step 0x109b21 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109b1c bytes 5 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x9b26 (by decide))
  advance_then (mov_r64_m64_effect_step 0x109b26 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109b1c bytes 10 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x9b2b (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109b2b 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 120)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109b1c bytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress] using hP.codeApart 16 (by simp) 0x9b2b 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) 0x9b1c 43 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x9b30 (by decide))
  advance_then (mov_r64_m64_effect_step 0x109b30 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109b1c bytes 20 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.readable 24 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x9b35 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109b35 0x48 (by simp [RexWPrefix]) 2 (.sib 4 none 0 (.d32 128)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109b1c bytes 25 8
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress] using hP.codeApart 24 (by simp) 0x9b35 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) 0x9b1c 43 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x9b3d (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109b3d 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109b1c bytes 33 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress] using hP.codeApart 0 (by simp) 0x9b3d 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) 0x9b1c 43 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x9b42 (by decide))
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x109b42 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x109b1c bytes 38 5
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress] using hP.codeApart 8 (by simp) 0x9b42 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) 0x9b1c 43 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x9b47 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [Result.effect]
  · x86_norm [Result.effect, BitVec.add_assoc]
    all_goals (repeat constructor <;> rfl)
  · intro i
    cases i <;> x86_norm [Result.effect]
  · x86_norm [Result.effect]

end P256.Proofs.SignatureFromDer.Fixed.Decode.Copy.FirstResult
