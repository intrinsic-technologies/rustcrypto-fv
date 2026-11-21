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

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.ZeroMachine

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d7f5
  writable : ∀ i ∈ ([128,136,144,152,160,168,176] : List (BitVec 64)), MemWritable s (rspOf s + i) 8
  codeApart : ∀ i ∈ ([128,136,144,152,160,168,176] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 118431 →
    RangeApart (rspOf s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48,0xc7,0x84,0x24,0x80,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0x88,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0x90,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0x98,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0xa0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0xa8,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x48,0xc7,0x84,0x24,0xb0,0x0,0x0,0x0,0x0,0x0,0x0,0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x10d849
    writes := [⟨(.mem (rspOf s + 128) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 136) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 144) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 152) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 160) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 168) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 176) : Operand 64), 0⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10d7f5 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd7f5 bytes (by decide +kernel) (by decide +kernel)

 theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d7f5 bytes) (Effect.post effect) := by
  advance_begin (mov_m64_imm32_effect_step 0x10d7f5 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 128)) (by decide) rfl rfl 0)
  case pre =>
    intro s h
    refine ⟨h.rip, ?_, ?_⟩
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value,
        rspOf, Operand.read, BitVec.add_zero] using h.writable 128 (by simp)
    · simpa [storeAddrAt, AddrMode.addr, AddrMode.tail, rspOf, Operand.read,
        AddrMode.reg64, Disp.value, Disp.bytes, BitVec.add_zero,
        Extracted.textAddress] using h.codeApart 128 (by simp) 0xd7f5 12 (by decide)
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm
    simpa [rspOf, Operand.read, Extracted.textAddress, bytes] using
      h.codeApart 128 (by simp) 0xd7f5 84 (by decide)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd801 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10d801 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 136)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d7f5 bytes 12 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 136 (by simp)
    · x86_norm
      exact hP.codeApart 136 (by simp) 0xd801 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 136 (by simp) 0xd7f5 84 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd80d (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10d80d 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 144)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d7f5 bytes 24 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 144 (by simp)
    · x86_norm
      exact hP.codeApart 144 (by simp) 0xd80d 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 144 (by simp) 0xd7f5 84 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd819 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10d819 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 152)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d7f5 bytes 36 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 152 (by simp)
    · x86_norm
      exact hP.codeApart 152 (by simp) 0xd819 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 152 (by simp) 0xd7f5 84 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd825 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10d825 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 160)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d7f5 bytes 48 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 160 (by simp)
    · x86_norm
      exact hP.codeApart 160 (by simp) 0xd825 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 160 (by simp) 0xd7f5 84 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd831 (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10d831 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 168)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d7f5 bytes 60 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 168 (by simp)
    · x86_norm
      exact hP.codeApart 168 (by simp) 0xd831 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 168 (by simp) 0xd7f5 84 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd83d (by decide))
  advance_then (mov_m64_imm32_effect_step 0x10d83d 0x48 (by simp [RexWPrefix])
    (.sib 4 none 0 (.d32 176)) (by decide) rfl rfl 0)
  case sub => exact codeRange_slice_subset 0x10d7f5 bytes 72 12
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 176 (by simp)
    · x86_norm
      exact hP.codeApart 176 (by simp) 0xd83d 12 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 176 (by simp) 0xd7f5 84 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd849 (by decide))
  advance_finish [effect, BitVec.add_zero]

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Blocks.ZeroMachine
