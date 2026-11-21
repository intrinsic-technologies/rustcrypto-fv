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

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Common.Instructions (mov_m8_r8_legacy_effect_step)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ZeroPre (s : RamState) : Prop where
  rip : s.RIP = 0x10fcfc
  writable : ∀ (i : BitVec 64) (n : Nat), (i,n) ∈ [(32,1),(104,8),(96,8),(88,8),(80,8)] →
    MemWritable s ((Operand.reg 4 : Operand 64).read s+i) n
  codeApart : ∀ (i : BitVec 64) (n : Nat), (i,n) ∈ [(32,1),(104,8),(96,8),(88,8),(80,8)] →
    ∀ offset len : Nat, offset+len ≤ 118431 →
    RangeApart ((Operand.reg 4 : Operand 64).read s+i) n (Extracted.textAddress+BitVec.ofNat 64 offset) len

def zeroBytes : List UInt8 :=
  [0x88, 0x44, 0x24, 0x20, 0x48, 0xc7, 0x44, 0x24, 0x68, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x60, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x58, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x50, 0x0, 0x0, 0x0, 0x0]

def zeroEffect (s : RamState) : Effect :=
  { rip := 0x10fd24
    writes := [⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+32) : Operand 8),
      (Operand.reg 0 : Operand 8).read s⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+80) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+88) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+96) : Operand 64),0⟩,
      ⟨(Operand.mem ((Operand.reg 4 : Operand 64).read s+104) : Operand 64),0⟩] }

theorem zero_correct_code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10fcfc zeroBytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xfcfc zeroBytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 800000 in
theorem zero_correct [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary ZeroPre (codeRange 0x10fcfc zeroBytes)
      (Effect.post zeroEffect) := by
  advance_begin (mov_m8_r8_legacy_effect_step 0x10fcfc 0 (by decide)
    (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s h
    exact ⟨h.rip,h.writable 32 1 (by simp),h.codeApart 32 1 (by simp) 0xfcfc 4 (by decide)⟩
  case next =>
    intro s h
    exact boundary_ne_program hout (inProgram_of_textOffset 0xfd00 (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    exact h.codeApart 32 1 (by simp) 0xfcfc 40 (by decide)
  advance_then (mov_m64_imm32_effect_step 0x10fd00 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fcfc zeroBytes 4 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 104 8 (by simp)
    · x86_norm
      exact hP.codeApart 104 8 (by simp) 0xfd00 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 104 8 (by simp) 0xfcfc 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd09 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10fd09 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 96)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fcfc zeroBytes 13 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 96 8 (by simp)
    · x86_norm
      exact hP.codeApart 96 8 (by simp) 0xfd09 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 96 8 (by simp) 0xfcfc 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd12 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10fd12 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 88)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fcfc zeroBytes 22 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 88 8 (by simp)
    · x86_norm
      exact hP.codeApart 88 8 (by simp) 0xfd12 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 88 8 (by simp) 0xfcfc 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd1b (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10fd1b 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 80)) (by decide +kernel) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10fcfc zeroBytes 31 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 80 8 (by simp)
    · x86_norm
      exact hP.codeApart 80 8 (by simp) 0xfd1b 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 80 8 (by simp) 0xfcfc 40 (by decide)
    · exact boundary_ne_program hout (inProgram_of_textOffset 0xfd24 (by decide))
  advance_finish [zeroEffect]

end P256.Proofs.Sec1.Decompress.Input
