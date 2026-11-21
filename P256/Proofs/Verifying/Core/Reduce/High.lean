import P256.Proofs.Verifying.Core.Reduce.BlockPre
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] decR64Effect decSpec
attribute [local x86_local] dec_local

def highBytes : List UInt8 :=
  [0x48,0x8b,0x5e,0x18,0x48,0xc1,0xf9,0x3f,0x49,0xbe,0x0,0x0,0x0,0x0,0x1,0x0,0x0,0x0,0x49,0x1,0xde,0x49,0x1,0xce,0x48,0x89,0xd9,0x48,0xf7,0xd1,0x4c,0x9,0xf1,0x48,0xc1,0xe9,0x3f,0x48,0x89,0x4c,0x24,0x8,0x48,0x2b,0x7c,0x24,0x8,0x48,0xc1,0xef,0x3f]

def highEffect (s : RamState) : Effect :=
  let a := (Operand.mem (((Operand.reg 6 : Operand 64).read s) + 24) : Operand 64).read s
  let r := 0x100000000 + a + (((Operand.reg 1 : Operand 64).read s)).sshiftRight 63
  let b := (~~~a ||| r) >>> 63
  { rip := 0x1131f3
    writes := [⟨(Operand.reg 3 : Operand 64), a⟩,
      ⟨(Operand.reg 14 : Operand 64), r⟩,
      ⟨(Operand.reg 1 : Operand 64), b⟩,
      ⟨(Operand.reg 7 : Operand 64), (((Operand.reg 7 : Operand 64).read s) - b) >>> 63⟩,
      ⟨(Operand.mem (stackPtr s + 8) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem high_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x1131c0) (codeRange 0x1131c0 highBytes)
      (Effect.post highEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x1131c0 0x48 (by simp [RexWPrefix]) 3 (.base 6 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 0 4)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    change MemReadable s (((Operand.reg 6 : Operand 64).read s) + BitVec.ofNat 64 24) 8
    exact hP.input 24 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x131c4 (by decide))
  advance_then (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x1131c4 0x48 0xf9 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 4 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131c8 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x1131c8 0x49 0xbe (by simp [RexWPrefix]) (by decide) 0x100000000)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 8 10)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131d2 (by decide))
  advance_then (add_r64_r64_effect_step 0x1131d2 0x49 0xde  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 18 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131d5 (by decide))
  advance_then (add_r64_r64_effect_step 0x1131d5 0x49 0xce  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 21 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131d8 (by decide))
  advance_then (mov_r64_r64_effect_step 0x1131d8 0x48 0xd9  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 24 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131db (by decide))
  advance_then (not_r64_effect_step 0x1131db 0x48 0xd1  (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 27 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131de (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x1131de 0x4c 0xf1  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 30 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131e1 (by decide))
  advance_then (shr_r64_imm8_effect_step 0x1131e1 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 33 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131e5 (by decide))
  advance_then (mov_m64_r64_effect_step 0x1131e5 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 37 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.writable 8 (by decide))
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x131e5 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x131c0 51 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131ea (by decide))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x1131ea 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 42 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.writable 8 (by decide)).readable
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131ef (by decide))
  advance_then (shr_r64_imm8_effect_step 0x1131ef 0x48 0xef 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x1131c0 highBytes 47 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x131f3 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [highEffect]
  · x86_norm [highEffect]
    simp [gprNumber, modrmRm, shiftCount, Operand.read_reg64, BitVec.add_comm, gprIndex, rexB, rexR]
    all_goals (simp only [BitVec.add_comm])
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [highEffect]

end P256.Proofs.Verifying.Core.Reduce
