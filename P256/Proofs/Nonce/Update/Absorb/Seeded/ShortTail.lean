import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Nonce.Update.Absorb.Prefix.TagTail
import P256.Proofs.Common.Instructions.ByteLogic.Register
import P256.Proofs.Common.Encoding.Parser.LengthCheck.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded.ShortTail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteLogic P256.Proofs.Common.Encoding.Parser.LengthCheck

attribute [local x86_local] Prefix.TagHead.store_local
attribute [local x86_compose] cmpR64M64Effect

@[local x86_local] theorem cmp_local (p : BitVec 64) :
    Effect.Local (cmpR64M64Effect p 5 14 (fun s => rspOf s + 80)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h; simp only [cmpR64M64Effect, rspOf, h.read_reg, h.read_mem]
  · intro s; simp [cmpR64M64Effect, Write.Full, Operand.Full]

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a2a9
  readable : MemReadable s (rspOf s + 80) 8
  writable : MemWritable s (rspOf s + 215) 1
  codeApart : ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + 215) 1 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 := [0x41, 0x0, 0xdf, 0x44, 0x88, 0xbc, 0x24, 0xd7, 0x0, 0x0, 0x0, 0x49, 0x83, 0xc6, 0x10, 0x4c, 0x3b, 0x74, 0x24, 0x50]

def sum (s : RamState) : BitVec 8 := (Operand.reg 15 : Operand 8).read s + (Operand.reg 3 : Operand 8).read s

def effect (s : RamState) : Effect :=
  { rip := 0x10a2bd
    writes := [⟨(.reg 15 : Operand 64), mergeGPR 8 (sum s) ((Operand.reg 15 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 215) : Operand 8),sum s⟩,
      ⟨(.reg 14 : Operand 64),(Operand.reg 14 : Operand 64).read s + 16⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 14 : Operand 64).read s + 16)
      (memLoad s.external (rspOf s + 80) 64))) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10a2a9 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa2a9 bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a2a9 bytes) (Effect.post effect) := by
  advance_begin (add_r15b_bl_effect_step 0x10a2a9)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa2ac (by decide))
  advance_then (mov_m8_r8_effect_step 0x10a2ac 0x44 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d32 215)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a2a9 bytes 3 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hP.writable
    · x86_norm; exact hP.codeApart 0xa2ac 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0xa2a9 20 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa2b4 (by decide))
  advance_then (add_r64_imm8_effect_step 0x10a2b4 0x49 0xc6 16 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a2a9 bytes 11 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa2b8 (by decide))⟩
  advance_then (show StepEffect _ _ (cmpR64M64Effect 0x10a2b8 5 14 (fun s => rspOf s + 80)) from
    cmp_r64_m64_effect_step 0x10a2b8 0x4c (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 80)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a2a9 bytes 15 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, Effect.Avoids.of_noMem (by simp [Component.Covers,cmpR64M64Effect,Effect.components]) _, ?_⟩
    · x86_norm; exact hP.readable
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa2bd (by decide))
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect,sum]
  · x86_norm [effect,sum]
    exact .inr rfl
  · intro i; cases i <;> x86_norm [effect,sum] <;> rfl
  · x86_norm [effect,sum]

end P256.Proofs.Nonce.Update.Absorb.Seeded.ShortTail
