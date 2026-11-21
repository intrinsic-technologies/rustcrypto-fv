import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
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
import P256.Proofs.Common.Encoding.Parser.ByteStore

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure FinalZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fd75
  writable : ∀ (i : BitVec 64) (n : Nat), (i,n) ∈ [(288,1),(248,8),(240,8),(232,8),(224,8)] →
    MemWritable s ((Operand.reg 4 : Operand 64).read s+i) n
  codeApart : ∀ (i : BitVec 64) (n : Nat), (i,n) ∈ [(288,1),(248,8),(240,8),(232,8),(224,8)] →
    ∀ offset len : Nat, offset+len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s+i) n (Extracted.textAddress+BitVec.ofNat 64 offset) len

def finalZeroBytes : List UInt8 :=
  [0x40, 0x88, 0xac, 0x24, 0x20, 0x1, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xf8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xf0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xe8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0xe0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0]

def finalZeroEffect (s : RamState) : Effect :=
  { rip := 0x10fdad
    writes := [⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+288) : Operand 8),
      (Operand.reg 5 : Operand 8).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+224) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+232) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+240) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+248) : Operand 64),0⟩] }

set_option maxHeartbeats 800000 in
theorem final_zero_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary FinalZeroPre (codeRange 0x10fd75 finalZeroBytes)
      (Effect.post finalZeroEffect) := by
  advance_begin (mov_m8_r8_effect_step 0x10fd75 0x40 (by simp [RexPrefix]) 5
    (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 288 1 (by simp),h.codeApart 288 1 (by simp) 0xfd75 8 (by decide)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfd7d (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 288 1 (by simp) 0xfd75 56 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10fd7d 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 248)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fd75 finalZeroBytes 8 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 248 8 (by simp)
    · x86_norm
      exact hP.codeApart 248 8 (by simp) 0xfd7d 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 248 8 (by simp) 0xfd75 56 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd89 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10fd89 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 240)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fd75 finalZeroBytes 20 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 240 8 (by simp)
    · x86_norm
      exact hP.codeApart 240 8 (by simp) 0xfd89 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 240 8 (by simp) 0xfd75 56 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd95 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10fd95 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 232)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fd75 finalZeroBytes 32 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 232 8 (by simp)
    · x86_norm
      exact hP.codeApart 232 8 (by simp) 0xfd95 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 232 8 (by simp) 0xfd75 56 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfda1 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10fda1 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 224)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fd75 finalZeroBytes 44 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 224 8 (by simp)
    · x86_norm
      exact hP.codeApart 224 8 (by simp) 0xfda1 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 224 8 (by simp) 0xfd75 56 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfdad (by decide))
  advance_finish [finalZeroEffect]

end P256.Proofs.Sec1.Decompress.Input
