import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
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

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks.ZeroMachine

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x1028fe
  writable : ∀ i ∈ ([64,72,80,88,96,104,112] : List (BitVec 64)), MemWritable s (rspOf s + i) 8
  codeApart : ∀ i ∈ ([64,72,80,88,96,104,112] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48,0xc7,0x44,0x24,0x40,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x48,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x50,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x58,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x60,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x68,0x0,0x0,0x0,0x0,0x48,0xc7,0x44,0x24,0x70,0x0,0x0,0x0,0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10293d
    writes := [⟨(.mem (rspOf s + 64) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 72) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 80) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 88) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 96) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 104) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 112) : Operand 64), 0⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x1028fe bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x28fe bytes (by decide +kernel) (by decide +kernel)

 theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x1028fe bytes) (Effect.post effect) := by
  advance_begin (mov_m64_imm32_effect_step 0x1028fe 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 64)) (by decide) rfl rfl 0)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value,
        rspOf, Operand.read, BitVec.add_zero] using h.writable 64 (by simp)
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.tail, rspOf, Operand.read,
        AddrMode.reg64, Disp.value, Disp.bytes, BitVec.add_zero,
        Extracted.textAddress] using h.codeApart 64 (by simp) 0x28fe 9 (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa [rspOf, Operand.read, Extracted.textAddress, bytes] using
      h.codeApart 64 (by simp) 0x28fe 63 (by decide)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0x2907 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x102907 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 72)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1028fe bytes 9 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 72 (by simp)
    · x86_norm
      exact hP.codeApart 72 (by simp) 0x2907 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 72 (by simp) 0x28fe 63 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2910 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x102910 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1028fe bytes 18 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 80 (by simp)
    · x86_norm
      exact hP.codeApart 80 (by simp) 0x2910 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 80 (by simp) 0x28fe 63 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2919 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x102919 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 88)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1028fe bytes 27 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 88 (by simp)
    · x86_norm
      exact hP.codeApart 88 (by simp) 0x2919 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 88 (by simp) 0x28fe 63 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2922 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x102922 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1028fe bytes 36 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 96 (by simp)
    · x86_norm
      exact hP.codeApart 96 (by simp) 0x2922 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 96 (by simp) 0x28fe 63 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x292b (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10292b 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1028fe bytes 45 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 104 (by simp)
    · x86_norm
      exact hP.codeApart 104 (by simp) 0x292b 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 104 (by simp) 0x28fe 63 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x2934 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x102934 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x1028fe bytes 54 9
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 112 (by simp)
    · x86_norm
      exact hP.codeApart 112 (by simp) 0x2934 9 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 112 (by simp) 0x28fe 63 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x293d (by decide))
  advance_finish [effect, BitVec.add_zero]

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks.ZeroMachine
