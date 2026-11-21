import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Nonce.Update.Absorb.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
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
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Prefix.Head

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

attribute [local x86_compose] cmpR64Imm8Effect

@[local x86_local] theorem cmp_local (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (cmpR64Imm8Effect p dst imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [cmpR64Imm8Effect, h.read_reg]
  · intro s
    simp [cmpR64Imm8Effect, Write.Full, Operand.Full]

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a12f
  readable : MemReadable s (rspOf s + 215) 1
  position : memLoad s.external (rspOf s + 215) 8 = 0
  writable : ∀ offset ∈ ([64,72] : List (BitVec 64)), MemWritable s (rspOf s + offset) 8
  codeApart : ∀ offset ∈ ([64,72] : List (BitVec 64)), ∀ pc len : Nat,
    pc + len ≤ 118431 → RangeApart (rspOf s + offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 :=
  [0x48, 0x8d, 0x73, 0x20, 0x4c, 0x8d, 0xb4, 0x24, 0x98, 0x0, 0x0, 0x0, 0x4c, 0x8d, 0xa4, 0x24, 0xd8, 0x0, 0x0, 0x0, 0x44, 0xf, 0xb6, 0xbc, 0x24, 0xd7, 0x0, 0x0, 0x0, 0x49, 0x83, 0xff, 0x1f, 0x48, 0x89, 0x5c, 0x24, 0x48, 0x48, 0x89, 0x74, 0x24, 0x40]

def effect (s : RamState) : Effect :=
  { rip := 0x10a15a
    writes := [⟨(.reg 6 : Operand 64), (Operand.reg 3 : Operand 64).read s + 32⟩,
      ⟨(.reg 14 : Operand 64), rspOf s + 152⟩,
      ⟨(.reg 12 : Operand 64), rspOf s + 216⟩,
      ⟨(.reg 15 : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 72) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 64) : Operand 64), (Operand.reg 3 : Operand 64).read s + 32⟩]
    flags := some (.ofStatusFlags (cmpSpec (0 : BitVec 64) 31)) }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a12f bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa12f bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a12f bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10a12f 0x48 (by simp [RexWPrefix]) 6 (.base 3 (.d8 32)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa133 (by decide))
  advance_then (lea_r64_effect_step 0x10a133 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 152)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a12f bytes 4 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa13b (by decide))
  advance_then (lea_r64_effect_step 0x10a13b 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a12f bytes 12 8
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa143 (by decide))
  advance_then (movzx_r_m8_rex_effect_step 0x10a143 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (by intro; rfl) 7 (.sib 4 none 0 (.d32 215)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a12f bytes 20 9
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa14c (by decide))
  advance_then (cmp_r64_imm8_effect_step 0x10a14c 0x49 0xff 31 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a12f bytes 29 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa150 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a150 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 72)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a12f bytes 33 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 72 (by simp)
    · x86_norm
      exact hP.codeApart 72 (by simp) 0xa150 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 72 (by simp) 0xa12f 43 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa155 (by decide))
  advance_then (mov_m64_r64_effect_step 0x10a155 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 64)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a12f bytes 38 5
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 64 (by simp)
    · x86_norm
      exact hP.codeApart 64 (by simp) 0xa155 5 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 64 (by simp) 0xa12f 43 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa15a (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have position : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 215) : Operand 8).read s = 0 := hP.position
  simp only [BitVec.ofNat_eq_ofNat] at position
  apply hH.weaken
  · x86_norm [effect, position] <;> rfl
  · x86_norm [effect, position] <;> rfl
  · intro i; cases i <;> x86_norm [effect, position] <;> rw [position] <;> rfl
  · x86_norm [effect, position] <;> rfl

end P256.Proofs.Nonce.Update.Absorb.Prefix.Head
