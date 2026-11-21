import P256.Proofs.Verifying.Core.Reduce.BlockPre
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] decR64Effect decSpec
attribute [local x86_local] dec_local

def lowBytes : List UInt8 :=
  [0x48,0x8b,0x6,0x48,0x89,0x44,0x24,0x18,0x48,0xb9,0xaf,0xda,0x9c,0x3,0x3d,0x35,0x46,0xc,0x48,0x1,0xc1,0x48,0x89,0x4c,0x24,0x10,0x48,0xf7,0xd0,0x48,0x9,0xc8,0x48,0xc1,0xe8,0x3f,0x48,0x89,0x44,0x24,0x8,0x48,0x8d,0x44,0x24,0x8,0x31,0xc9,0x48,0x2b,0x4c,0x24,0x8,0x31,0xff]

def lowEffect (s : RamState) : Effect :=
  let a := (Operand.mem (((Operand.reg 6 : Operand 64).read s)) : Operand 64).read s
  let r := 0x0c46353d039cdaaf + a
  let b := (~~~a ||| r) >>> 63
  { rip := 0x11316a
    writes := [⟨(Operand.reg 0 : Operand 64), stackPtr s + 8⟩,
      ⟨(Operand.reg 1 : Operand 64), -b⟩,
      ⟨(Operand.reg 7 : Operand 64), 0⟩,
      ⟨(Operand.mem (stackPtr s + 24) : Operand 64), a⟩,
      ⟨(Operand.mem (stackPtr s + 16) : Operand 64), r⟩,
      ⟨(Operand.mem (stackPtr s + 8) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem low_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x113133) (codeRange 0x113133 lowBytes)
      (Effect.post lowEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x113133 0x48 (by simp [RexWPrefix]) 0 (.base 6 .none) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 0 3)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    change MemReadable s (((Operand.reg 6 : Operand 64).read s) + BitVec.ofNat 64 0) 8
    exact hP.input 0 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x13136 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113136 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 3 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.writable 24 (by decide))
    · x86_norm
      exact hP.apart 24 8 (by decide) 0x13136 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 24 8 (by decide) 0x13133 55 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1313b (by decide))
  advance_then (mov_r64_imm64_effect_step 0x11313b 0x48 0xb9 (by simp [RexWPrefix]) (by decide) 0xc46353d039cdaaf)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 8 10)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13145 (by decide))
  advance_then (add_r64_r64_effect_step 0x113145 0x48 0xc1  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 18 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13148 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113148 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 21 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.writable 16 (by decide))
    · x86_norm
      exact hP.apart 16 8 (by decide) 0x13148 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 16 8 (by decide) 0x13133 55 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1314d (by decide))
  advance_then (not_r64_effect_step 0x11314d 0x48 0xd0  (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 26 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13150 (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113150 0x48 0xc8  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 29 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13153 (by decide))
  advance_then (shr_r64_imm8_effect_step 0x113153 0x48 0xe8 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 32 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13157 (by decide))
  advance_then (mov_m64_r64_effect_step 0x113157 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 36 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.writable 8 (by decide))
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x13157 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x13133 55 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1315c (by decide))
  advance_then (lea_r64_effect_step 0x11315c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 41 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13161 (by decide))
  advance_then (xor_r32_r32_effect_step 0x113161 0xc9 rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 46 2)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13163 (by decide))
  advance_then (P256.Proofs.Common.Field.Instructions.sub_r64_m64_effect_step 0x113163 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 48 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.writable 8 (by decide)).readable
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13168 (by decide))
  advance_then (xor_r32_r32_effect_step 0x113168 0xff rfl)
  try (case sub => exact codeRange_slice_subset 0x113133 lowBytes 53 2)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1316a (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [lowEffect]
  · x86_norm [lowEffect]
    simp [gprNumber, modrmRm, shiftCount, Operand.read_reg64, BitVec.add_comm, gprIndex, modrmReg, BitVec.zero_sub]
    all_goals (simp only [BitVec.add_comm])
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [lowEffect]

end P256.Proofs.Verifying.Core.Reduce
