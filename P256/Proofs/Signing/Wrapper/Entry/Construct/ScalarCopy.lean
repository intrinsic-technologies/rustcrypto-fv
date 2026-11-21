import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovLoad.Triple
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

namespace P256.Proofs.Signing.Wrapper.Entry.Construct.ScalarCopy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def bytes : List UInt8 :=
  [72, 139, 68, 36, 24, 72, 137, 68, 36, 88, 72, 139, 68, 36, 16, 72, 137, 68, 36, 80, 72, 139, 4, 36, 72, 139, 76, 36, 8, 72, 137, 76, 36, 72, 72, 137, 68, 36, 64]

theorem run [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip)
    (offset : Nat) (bound : offset + 39 < 118431) :
    AdvanceTriple boundary (Copy32.Pre (Extracted.textAddress + BitVec.ofNat 64 offset)
      (fun s => (Operand.reg 4 : Operand 64).read s + 0) (fun s => (Operand.reg 4 : Operand 64).read s + 64))
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes)
      (Effect.post (Copy32.effect (Extracted.textAddress + BitVec.ofNat 64 offset + 39) (fun s => (Operand.reg 4 : Operand 64).read s + 0) (fun s => (Operand.reg 4 : Operand 64).read s + 64))) := by
  have next (i : Nat) (hi : i ≤ 39) :
      Extracted.textAddress + BitVec.ofNat 64 offset + BitVec.ofNat 64 i ≠ boundary.rip := by
    have h := boundary_ne_program hout (inProgram_of_textOffset (offset+i) (by omega))
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using h
  advance_begin (mov_r64_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    x86_norm
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 24 (by simp)
  case next =>
    intro _ _
    exact next 5 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (Extracted.textAddress + BitVec.ofNat 64 offset + 5) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 24 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) (offset + 5) 5 (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 24 (by simp) (offset + 0) 39 (by omega)
    · x86_norm
      simpa only [BitVec.add_assoc] using next 10 (by decide)
  advance_then (mov_r64_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset + 10) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 16 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using next 15 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (Extracted.textAddress + BitVec.ofNat 64 offset + 15) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 16 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) (offset + 15) 5 (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 16 (by simp) (offset + 0) 39 (by omega)
    · x86_norm
      simpa only [BitVec.add_assoc] using next 20 (by decide)
  advance_then (mov_r64_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset + 20) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 0 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using next 24 (by decide)
  advance_then (mov_r64_m64_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset + 24) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.readable 8 (by simp)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · x86_norm
      simpa only [BitVec.add_assoc] using next 29 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (Extracted.textAddress + BitVec.ofNat 64 offset + 29) 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 8 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) (offset + 29) 5 (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 8 (by simp) (offset + 0) 39 (by omega)
    · x86_norm
      simpa only [BitVec.add_assoc] using next 34 (by decide)
  advance_then (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any (Extracted.textAddress + BitVec.ofNat 64 offset + 34) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case mid =>
    intro s t hP hH hO
    refine ⟨P256.Proofs.Common.Instructions.CrossPageStore.Pre.of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.writable 0 (by simp)
    · x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) (offset + 34) 5 (by omega)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.ofNat_add, BitVec.reduceAdd, BitVec.add_zero, Extracted.textAddress, bytes, List.length_cons, List.length_nil, Nat.reduceAdd] using hP.codeApart 0 (by simp) (offset + 0) 39 (by omega)
    · x86_norm
      simpa only [BitVec.add_assoc] using next 39 (by decide)
  apply AdvanceTriple.block_end
  intro s t hP hH
  have hread (mem : Ram) (i j : Nat) (v : BitVec 64) (hi : i + 8 ≤ 32) (hj : j + 8 ≤ 32) :
      memLoad (memStore mem (((Operand.reg 4 : Operand 64).read s + 64) + BitVec.ofNat 64 i) v)
        (((Operand.reg 4 : Operand 64).read s + 0) + BitVec.ofNat 64 j) 64 =
      memLoad mem (((Operand.reg 4 : Operand 64).read s + 0) + BitVec.ofNat 64 j) 64 := by
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

end P256.Proofs.Signing.Wrapper.Entry.Construct.ScalarCopy
