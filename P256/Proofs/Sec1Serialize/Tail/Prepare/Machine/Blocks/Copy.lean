import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Frame
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Blocks.Immediate

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec.Program P256.Spec.Program.Routines X86 X86.Machine X86.UserProcess X86Proofs

def prepareCopyBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x70, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8b,
   0x44, 0x24, 0x68, 0x48, 0x89, 0x44, 0x24, 0x20, 0x48, 0x8b, 0x44, 0x24,
   0x58, 0x48, 0x8b, 0x4c, 0x24, 0x60, 0x48, 0x89, 0x4c, 0x24, 0x18, 0x48,
   0x89, 0x44, 0x24, 0x10, 0xb0, 0x4]

def prepareCopyEffect (s : RamState) : Effect :=
  { rip := 0x111071
    writes := [
      ⟨(.mem (rspOf s + 40) : Operand 64), (Operand.mem (rspOf s + 112) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 32) : Operand 64), (Operand.mem (rspOf s + 104) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (Operand.mem (rspOf s + 96) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), (Operand.mem (rspOf s + 96) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), (Operand.mem (rspOf s + 88) : Operand 64).read s⟩,
      ⟨(.reg 0 : Operand 64), mergeGPR 8 (4 : BitVec 8)
        ((Operand.mem (rspOf s + 88) : Operand 64).read s)⟩] }

set_option maxHeartbeats 1600000 in
theorem prepare_copy [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (EncodingPre 0x111047 42 0 264)
      (codeRange 0x111047 prepareCopyBytes) (Effect.post prepareCopyEffect) := by
  have next (i : Nat) (hi : i < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 i ≠ boundary.rip :=
    boundary_ne_program hOutside (inProgram_of_textOffset i hi)
  have h1 := next 0x1104c (by decide)
  have h2 := next 0x11051 (by decide)
  have h3 := next 0x11056 (by decide)
  have h4 := next 0x1105b (by decide)
  have h5 := next 0x11060 (by decide)
  have h6 := next 0x11065 (by decide)
  have h7 := next 0x1106a (by decide)
  have h8 := next 0x1106f (by decide)
  have h9 := next 0x11071 (by decide)
  unfold prepareCopyBytes
  advance_begin mov_r64_m64_effect_step 0x111047 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x11104c 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_r64_m64_effect_step 0x111051 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x111056 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_r64_m64_effect_step 0x11105b 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_r64_m64_effect_step 0x111060 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x111065 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x11106a 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then prepare_mov_al_imm8_effect_step 0x11106f 4
  advance_finish [prepareCopyEffect]
  all_goals try (first
    | exact codeRange_mem_of_drop (p := 0x111047) (all := prepareCopyBytes) 5 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111047) (all := prepareCopyBytes) 10 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111047) (all := prepareCopyBytes) 15 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111047) (all := prepareCopyBytes) 20 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111047) (all := prepareCopyBytes) 25 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111047) (all := prepareCopyBytes) 30 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111047) (all := prepareCopyBytes) 35 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111047) (all := prepareCopyBytes) 40 (by decide +kernel))
  all_goals (
    intro s s' hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.writable _ (by decide +kernel)
      · x86_norm
        first
        | exact hP.apart _ (by decide +kernel) 5 5 (by decide)
        | exact hP.apart _ (by decide +kernel) 15 5 (by decide)
        | exact hP.apart _ (by decide +kernel) 30 5 (by decide)
        | exact hP.apart _ (by decide +kernel) 35 5 (by decide)
    · x86_avoid
      exact hP.apart _ (by decide +kernel) 0 42 (by decide)
    · x86_norm
      assumption)

end P256.Proofs.Sec1Serialize.Prepare
