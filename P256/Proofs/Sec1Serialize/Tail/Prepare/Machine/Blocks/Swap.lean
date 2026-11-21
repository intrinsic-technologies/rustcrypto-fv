import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Frame
import P256.Proofs.Common.Instructions.Bswap
import P256.Proofs.Program.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (bswap64 bswap_r64_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec.Program P256.Spec.Program.Routines X86 X86.Machine X86.UserProcess X86Proofs

def prepareSwapBytes : List UInt8 :=
  [0x48,0x0f,0xca,0x48,0x89,0xfd,0x48,0x89,0x54,0x24,0x58,
   0x48,0x0f,0xc8,0x48,0x89,0x44,0x24,0x60,0x49,0x0f,0xcb,
   0x4c,0x89,0x5c,0x24,0x68,0x49,0x0f,0xcd,0x49,0x0f,0xcc,
   0x49,0x0f,0xcf,0x48,0x0f,0xce,0x48,0x89,0x74,0x24,0x70,0x48,0x0f,0xcb]

def prepareSwapEffect (s : RamState) : Effect :=
  { rip := 0x11100b
    writes := [
      ⟨(.reg 2 : Operand 64), bswap64 ((Operand.reg 2 : Operand 64).read s)⟩,
      ⟨(.reg 5 : Operand 64), (Operand.reg 7 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 88) : Operand 64), bswap64 ((Operand.reg 2 : Operand 64).read s)⟩,
      ⟨(.reg 0 : Operand 64), bswap64 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 96) : Operand 64), bswap64 ((Operand.reg 0 : Operand 64).read s)⟩,
      ⟨(.reg 11 : Operand 64), bswap64 ((Operand.reg 11 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 104) : Operand 64), bswap64 ((Operand.reg 11 : Operand 64).read s)⟩,
      ⟨(.reg 13 : Operand 64), bswap64 ((Operand.reg 13 : Operand 64).read s)⟩,
      ⟨(.reg 12 : Operand 64), bswap64 ((Operand.reg 12 : Operand 64).read s)⟩,
      ⟨(.reg 15 : Operand 64), bswap64 ((Operand.reg 15 : Operand 64).read s)⟩,
      ⟨(.reg 6 : Operand 64), bswap64 ((Operand.reg 6 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 112) : Operand 64), bswap64 ((Operand.reg 6 : Operand 64).read s)⟩,
      ⟨(.reg 3 : Operand 64), bswap64 ((Operand.reg 3 : Operand 64).read s)⟩] }

set_option maxHeartbeats 1600000 in
theorem prepare_swap [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (EncodingPre 0x110fdc 47 0 264)
      (codeRange 0x110fdc prepareSwapBytes) (Effect.post prepareSwapEffect) := by
  have next (i : Nat) (hi : i < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 i ≠ boundary.rip :=
    boundary_ne_program hOutside (inProgram_of_textOffset i hi)
  have h1 := next 0x10fdf (by decide)
  have h2 := next 0x10fe2 (by decide)
  have h3 := next 0x10fe7 (by decide)
  have h4 := next 0x10fea (by decide)
  have h5 := next 0x10fef (by decide)
  have h6 := next 0x10ff2 (by decide)
  have h7 := next 0x10ff7 (by decide)
  have h8 := next 0x10ffa (by decide)
  have h9 := next 0x10ffd (by decide)
  have h10 := next 0x11000 (by decide)
  have h11 := next 0x11003 (by decide)
  have h12 := next 0x11008 (by decide)
  have h13 := next 0x1100b (by decide)
  unfold prepareSwapBytes
  advance_begin bswap_r64_effect_step 0x110fdc 2
  advance_then mov_r64_r64_effect_step 0x110fdf 0x48 0xfd (by simp [RexWPrefix]) rfl
  advance_then mov_m64_r64_effect_step 0x110fe2 0x48 (by simp [RexWPrefix]) 2
    (.sib 4 none 0 (.d8 88)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then bswap_r64_effect_step 0x110fe7 0
  advance_then mov_m64_r64_effect_step 0x110fea 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 96)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then bswap_r64_effect_step 0x110fef 11
  advance_then mov_m64_r64_effect_step 0x110ff2 0x4c (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d8 104)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then bswap_r64_effect_step 0x110ff7 13
  advance_then bswap_r64_effect_step 0x110ffa 12
  advance_then bswap_r64_effect_step 0x110ffd 15
  advance_then bswap_r64_effect_step 0x111000 6
  advance_then mov_m64_r64_effect_step 0x111003 0x48 (by simp [RexWPrefix]) 6
    (.sib 4 none 0 (.d8 112)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then bswap_r64_effect_step 0x111008 3
  advance_finish [prepareSwapEffect]
  all_goals try (first
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 3 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 6 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 11 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 14 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 19 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 22 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 27 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 30 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 33 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 36 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 39 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x110fdc) (all := prepareSwapBytes) 44 (by decide +kernel))
  all_goals (
    intro s s' hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.writable _ (by decide +kernel)
      · x86_norm
        first
        | exact hP.apart _ (by decide +kernel) 6 5 (by decide)
        | exact hP.apart _ (by decide +kernel) 14 5 (by decide)
        | exact hP.apart _ (by decide +kernel) 22 5 (by decide)
        | exact hP.apart _ (by decide +kernel) 39 5 (by decide)
    · x86_avoid
      exact hP.apart _ (by decide +kernel) 0 47 (by decide)
    · x86_norm
      assumption)

end P256.Proofs.Sec1Serialize.Prepare
