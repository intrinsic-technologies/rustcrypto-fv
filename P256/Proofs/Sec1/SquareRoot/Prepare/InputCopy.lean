import P256.Proofs.SecretKeyFromBytes.Scalar.Borrow
import P256.Proofs.Program.ScalarFrame.Copy32
import P256.Proofs.Common.Field.Montgomery.Schoolbook.Compose
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)
open P256.Proofs.Program.ScalarFrame

namespace P256.Proofs.Sec1.SquareRoot.Prepare.InputCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x46, 0x18, 0x48, 0x89, 0x84, 0x24, 0xd8, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24, 0xd0, 0x0, 0x0, 0x0, 0x48, 0x8b, 0x6, 0x48, 0x8b, 0x4e, 0x8, 0x48, 0x89, 0x8c, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x48, 0x89, 0x84, 0x24, 0xc0, 0x0, 0x0, 0x0]

set_option maxHeartbeats 800000 in
theorem run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip)
    (offset : Nat) (bound : offset + 47 < 118431) :
    AdvanceTriple boundary (Copy32.Pre (Extracted.textAddress + BitVec.ofNat 64 offset)
      (fun s => (Operand.reg 6 : Operand 64).read s + 0) (fun s => (Operand.reg 4 : Operand 64).read s + 192))
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes)
      (Effect.post (Copy32.effect (Extracted.textAddress + BitVec.ofNat 64 offset + 47) (fun s => (Operand.reg 6 : Operand 64).read s + 0) (fun s => (Operand.reg 4 : Operand 64).read s + 192))) := by
  have next (i : Nat) (hi : i ≤ 47) :
      Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 i ≠ boundary.rip := by
    have h := boundary_ne_program hout (inProgram_of_textOffset (offset+i) (by omega))
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
  advance_begin (mov_r64_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset) 0x48 (by simp [RexWPrefix]) 0 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 24 (by simp)
  case next =>
    intro _ _
    exact next 4 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (Extracted.textAddress + BitVec.ofNat 64 offset + 4) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) (offset + 4) 8 (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) (offset + 0) 47 (by omega)
    · x86_norm
      simpa only [BitVec.add_assoc] using next 12 (by decide)
  advance_then (mov_r64_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset + 12) 0x48 (by simp [RexWPrefix]) 0 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using next 16 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (Extracted.textAddress + BitVec.ofNat 64 offset + 16) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 208)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) (offset + 16) 8 (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) (offset + 0) 47 (by omega)
    · x86_norm
      simpa only [BitVec.add_assoc] using next 24 (by decide)
  advance_then (mov_r64_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset + 24) 0x48 (by simp [RexWPrefix]) 0 (.base 6 .none) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using next 27 (by decide)
  advance_then (mov_r64_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset + 27) 0x48 (by simp [RexWPrefix]) 1 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using next 31 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (Extracted.textAddress + BitVec.ofNat 64 offset + 31) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) (offset + 31) 8 (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) (offset + 0) 47 (by omega)
    · x86_norm
      simpa only [BitVec.add_assoc] using next 39 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (Extracted.textAddress + BitVec.ofNat 64 offset + 39) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) (offset + 39) 8 (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) (offset + 0) 47 (by omega)
    · x86_norm
      simpa only [BitVec.add_assoc] using next 47 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64) (hi : i + 8 ≤ 32) (hj : j + 8 ≤ 32) :
      memLoad (memStore mem (((Operand.reg 4 : Operand 64).read s + 192) + BitVec.ofNat 64 i) v)
        (((Operand.reg 6 : Operand 64).read s + 0) + BitVec.ofNat 64 j) 64 =
      memLoad mem (((Operand.reg 6 : Operand 64).read s + 0) + BitVec.ofNat 64 j) 64 := by
    apply memLoad_memStore_rangeApart
    intro k hk l hl he
    apply hP.apart (i+k) (by omega) (j+l) (by omega)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc] using he
  have h24_16 := fun mem v => hread mem 24 16 v (by decide) (by omega)
  have h24_0 := fun mem v => hread mem 24 0 v (by decide) (by omega)
  have h24_8 := fun mem v => hread mem 24 8 v (by decide) (by omega)
  have h16_0 := fun mem v => hread mem 16 0 v (by decide) (by omega)
  have h16_8 := fun mem v => hread mem 16 8 v (by decide) (by omega)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd] at h24_16 h24_0 h24_8 h16_0 h16_8
  apply hH.weaken
  · x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect, BitVec.add_zero, BitVec.add_assoc, h24_16, h24_0, h24_8, h16_0, h16_8]
    all_goals (repeat constructor <;> rfl)
  · intro i
    cases i <;> x86_norm [Copy32.effect]
  · x86_norm [Copy32.effect]

end P256.Proofs.Sec1.SquareRoot.Prepare.InputCopy
