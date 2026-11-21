import P256.Proofs.Verifying.Core.Reduce.BlockPre
import P256.Proofs.Common.Field.Operations.Add.Machine.ForgetFlags

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Core.Reduce

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

attribute [local x86_compose] decR64Effect decSpec
attribute [local x86_local] dec_local

def secondBytes : List UInt8 :=
  [0x4c,0x8b,0x66,0x8,0x48,0xc1,0xf9,0x3f,0x49,0xbd,0x7c,0x61,0xe8,0x58,0x52,0x5,0x19,0x43,0x4d,0x1,0xe5,0x49,0x1,0xcd,0x4c,0x89,0xe1,0x48,0xf7,0xd1,0x4c,0x9,0xe9,0x48,0xc1,0xe9,0x3f,0x48,0x89,0x4c,0x24,0x8,0x4c,0x8b,0x7c,0x24,0x8]

def secondEffect (s : RamState) : Effect :=
  let a := (Operand.mem (((Operand.reg 6 : Operand 64).read s) + 8) : Operand 64).read s
  let r := 0x4319055258e8617c + a + (((Operand.reg 1 : Operand 64).read s)).sshiftRight 63
  let b := (~~~a ||| r) >>> 63
  { rip := 0x113199
    writes := [⟨(Operand.reg 12 : Operand 64), a⟩,
      ⟨(Operand.reg 13 : Operand 64), r⟩,
      ⟨(Operand.reg 1 : Operand 64), b⟩,
      ⟨(Operand.reg 15 : Operand 64), b⟩,
      ⟨(Operand.mem (stackPtr s + 8) : Operand 64), b⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

set_option maxHeartbeats 800000 in
theorem second_correct [Bindings] (boundary : ReturnBoundary)
    (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (BlockPre 0x11316a) (codeRange 0x11316a secondBytes)
      (Effect.post secondEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x11316a 0x4c (by simp [RexWPrefix]) 4 (.base 6 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 0 4)
  case pre =>
    intro s hP
    refine ⟨hP.rip, ?_⟩
    change MemReadable s (((Operand.reg 6 : Operand 64).read s) + BitVec.ofNat 64 8) 8
    exact hP.input 8 (by decide)
  case next =>
    intro s hP
    exact boundary_ne_program hout (inProgram_of_textOffset 0x1316e (by decide))
  advance_then (P256.Proofs.Common.Instructions.sar_r64_imm8_effect_step 0x11316e 0x48 0xf9 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 4 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13172 (by decide))
  advance_then (mov_r64_imm64_effect_step 0x113172 0x49 0xbd (by simp [RexWPrefix]) (by decide) 0x4319055258e8617c)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 8 10)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1317c (by decide))
  advance_then (add_r64_r64_effect_step 0x11317c 0x4d 0xe5  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 18 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1317f (by decide))
  advance_then (add_r64_r64_effect_step 0x11317f 0x49 0xcd  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 21 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13182 (by decide))
  advance_then (mov_r64_r64_effect_step 0x113182 0x4c 0xe1  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 24 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13185 (by decide))
  advance_then (not_r64_effect_step 0x113185 0x48 0xd1  (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 27 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13188 (by decide))
  advance_then (P256.Proofs.Common.Field.FieldNeg.Instructions.or_r64_r64_effect_step 0x113188 0x4c 0xe9  (by simp [RexWPrefix]) rfl)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 30 3)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1318b (by decide))
  advance_then (shr_r64_imm8_effect_step 0x11318b 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 33 4)
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x1318f (by decide))
  advance_then (mov_m64_r64_effect_step 0x11318f 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 37 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.writable 8 (by decide))
    · x86_norm
      exact hP.apart 8 8 (by decide) 0x1318f 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.apart 8 8 (by decide) 0x1316a 47 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13194 (by decide))
  advance_then (mov_r64_m64_effect_step 0x113194 0x4c (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl)
  try (case sub => exact codeRange_slice_subset 0x11316a secondBytes 42 5)
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact (hP.writable 8 (by decide)).readable
    · x86_avoid
    · exact boundary_ne_program hout (inProgram_of_textOffset 0x13199 (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [secondEffect]
  · x86_norm [secondEffect]
    simp [gprNumber, modrmRm, shiftCount, Operand.read_reg64, BitVec.add_comm, gprIndex, rexB]
    all_goals (simp only [BitVec.add_comm])
  · intro i
    cases i <;> exact .inl rfl
  · x86_norm [secondEffect]

end P256.Proofs.Verifying.Core.Reduce
