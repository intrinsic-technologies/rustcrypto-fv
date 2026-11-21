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

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.Head

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
  rip : s.RIP = 0x10a627
  readable : MemReadable s (rspOf s + 383) 1
  position : memLoad s.external (rspOf s + 383) 8 = 0

def bytes : List UInt8 := [0x4c, 0x8d, 0xac, 0x24, 0x80, 0x1, 0x0, 0x0, 0x44, 0xf, 0xb6, 0xbc, 0x24, 0x7f, 0x1, 0x0, 0x0, 0x49, 0x83, 0xff, 0x1f]

def effect (s : RamState) : Effect :=
  { rip := 0x10a63c
    writes := [⟨(.reg 13 : Operand 64), rspOf s + 384⟩,
      ⟨(.reg 15 : Operand 64), 0⟩]
    flags := some (.ofStatusFlags (cmpSpec (0 : BitVec 64) 31)) }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a627 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa627 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a627 bytes) (Effect.post effect) := by
  advance_begin (lea_r64_effect_step 0x10a627 0x4c (by simp [RexWPrefix]) 5 (.sib 4 none 0 (.d32 384)) (by decide +kernel) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa62f (by decide))
  advance_then (movzx_r_m8_rex_effect_step 0x10a62f 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (by intro; rfl) 7 (.sib 4 none 0 (.d32 383)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a627 bytes 8 9
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable
    · exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa638 (by decide))
  advance_then (cmp_r64_imm8_effect_step 0x10a638 0x49 0xff 31 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a627 bytes 17 4
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa63c (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  have position : (Operand.mem ((Operand.reg 4 : Operand 64).read s + 383) : Operand 8).read s = 0 := hP.position
  simp only [BitVec.ofNat_eq_ofNat] at position
  apply hH.weaken
  · x86_norm [effect, position] <;> rfl
  · x86_norm [effect, position] <;> rfl
  · intro i; cases i <;> x86_norm [effect, position] <;> rw [position] <;> rfl
  · x86_norm [effect, position] <;> rfl

end P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.Head
