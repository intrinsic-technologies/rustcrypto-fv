import P256.Proofs.Verifying.Core.Reduce.BlockPre
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] decR64Effect decSpec
attribute [local x86_local] dec_local

def thirdBytes : List UInt8 :=
  [0x48,0x8b,0x6e,0x10,0x49,0xff,0xcf,0x49,0xc1,0xef,0x3f,0x49,0x1,0xef,0x48,0x89,0xe9,0x48,0xf7,0xd1,0x4c,0x9,0xf9,0x48,0xc1,0xe9,0x3f,0x48,0x89,0x4c,0x24,0x8,0x31,0xc9,0x48,0x2b,0x4c,0x24,0x8]

def thirdEffect (s : RamState) : Effect :=
  let a := (Operand.mem (((Operand.reg 6 : Operand 64).read s) + 16) : Operand 64).read s
  let r := ((((Operand.reg 15 : Operand 64).read s) - 1) >>> 63) + a
  let b := (~~~a ||| r) >>> 63
  { rip := 0x1131c0
    writes := [⟨(Operand.reg 5 : Operand 64), a⟩,
      ⟨(Operand.reg 15 : Operand 64), r⟩,
      ⟨(Operand.reg 1 : Operand 64), -b⟩,
      ⟨(Operand.mem (stackPtr s + 8) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem third_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x113199) (codeRange 0x113199 thirdBytes)
      (Effect.post thirdEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x113199 0x48 (by simp [RexWPrefix]) 5 (.base 6 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 0 4)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    change MemReadable s (((Operand.reg 6 : Operand 64).read s) + BitVec.ofNat 64 16) 8
    exact hP.input 16 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1319d (by decide))
  advance_then (dec_r64_effect_step 0x11319d 0x49 0xcf  (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 4 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131a0 (by decide))
  advance_then (shr_r64_imm8_effect_step 0x1131a0 0x49 0xef 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 7 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131a4 (by decide))
  advance_then (add_r64_r64_effect_step 0x1131a4 0x49 0xef  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 11 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131a7 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1131a7 0x48 0xe9  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 14 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131aa (by decide))
  advance_then (not_r64_effect_step 0x1131aa 0x48 0xd1  (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 17 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131ad (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x1131ad 0x4c 0xf9  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 20 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131b0 (by decide))
  advance_then (shr_r64_imm8_effect_step 0x1131b0 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 23 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131b4 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1131b4 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 27 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.writable 8 (by decide))
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x131b4 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x13199 39 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131b9 (by decide))
  advance_then (xor_r32_r32_effect_step 0x1131b9 0xc9 rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 32 2)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131bb (by decide))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x1131bb 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113199 thirdBytes 34 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.writable 8 (by decide)).readable
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131c0 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [thirdEffect]
  · x86_norm [thirdEffect]
    simp [gprNumber, modrmRm, shiftCount, Operand.read_reg64, BitVec.add_comm, gprIndex, BitVec.zero_sub, rexB]
    all_goals (simp only [BitVec.add_comm])
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [thirdEffect]

end P256.Proofs.Verifying.Core.Reduce
