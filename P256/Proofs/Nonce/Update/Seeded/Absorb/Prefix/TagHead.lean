import P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.Head
import P256.Proofs.Nonce.UpdateValue.Absorb.OrByte
import P256.Proofs.Common.Instructions.MovzxByte
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Encoding.Parser.ByteStore

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.TagHead

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.Nonce.UpdateValue.Absorb.OrByte
open P256.Proofs.Common.Instructions.MovzxByte
open P256.Proofs.Common.Instructions.ByteOps.ByteOps

attribute [local x86_compose] orR8Imm8Effect cmpAlImm8Effect

@[local x86_local] theorem cmp_local (p : BitVec 64) (imm : BitVec 8) :
    Effect.Local (cmpAlImm8Effect p imm) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [cmpAlImm8Effect, h.read_reg]
  · intro s
    simp [cmpAlImm8Effect, Write.Full, Operand.Full]

@[local x86_local] theorem store_local (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) :
    Effect.Local (storeEffect p len (storeAddrAt p am len)
      (fun s => (Operand.reg src : Operand 8).read s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, storeAddrAt, AddrMode.addr_obs h, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10a665
  position : (Operand.reg 15#5 : Operand 64).read s = 0#64
  writable : MemWritable s (rspOf s + 383) 1
  codeApart : ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + 383) 1 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 := [0x41, 0x80, 0xcf, 0x20, 0x44, 0x88, 0xbc, 0x24, 0x7f, 0x1, 0x0, 0x0, 0x41, 0xf, 0xb6, 0xc7, 0x3c, 0x3f]

def effect (s : RamState) : Effect :=
  { rip := 0x10a677
    writes := [⟨(.reg 15 : Operand 64),32⟩,
      ⟨(.mem (rspOf s + 383) : Operand 8),32⟩,
      ⟨(.reg 0 : Operand 64),32⟩]
    flags := some (.ofStatusFlags (cmpSpec (32 : BitVec 8) 63)) }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10a665 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xa665 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10a665 bytes) (Effect.post effect) := by
  advance_begin (show StepEffect _ _ (orR8Imm8Effect 0x10a665 4 15 32) from or_r8_imm8_effect_step 0x10a665 0x41 0xcf 32 (by simp [RexPrefix]) rfl rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xa669 (by decide))
  advance_then (P256.Proofs.Common.Instructions.mov_m8_r8_effect_step 0x10a669 0x44 (by simp [RexPrefix]) 7
    (.sib 4 none 0 (.d32 383)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10a665 bytes 4 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable
    · x86_norm
      exact hP.codeApart 0xa669 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0xa665 18 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xa671 (by decide))
  advance_then (show StepEffect _ _ (movzxR32R8Effect 0x10a671 4 0 15) from movzx_r32_r8_rex_effect_step 0x10a671 0x41 0xc7 (by simp [RexNoWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10a665 bytes 12 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, movzxR32R8Effect, Effect.components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa675 (by decide))⟩
  advance_then (cmp_al_imm8_effect_step 0x10a675 63)
  case sub => exact codeRange_slice_subset 0x10a665 bytes 16 2
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers, cmpAlImm8Effect, Effect.components]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xa677 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  have position8 : (Operand.reg 15#5 : Operand 8).read s = 0#8 := by
    change ((Operand.reg 15#5 : Operand 64).read s).setWidth 8 = 0#8
    rw [hP.position]
    rfl
  apply hH.weaken
  · x86_norm [effect, hP.position, position8]
  · x86_norm [effect, hP.position, position8, mergeGPR]
  · intro i; cases i <;> x86_norm [effect, hP.position, position8, mergeGPR]
  · x86_norm [effect, hP.position, position8]

end P256.Proofs.Nonce.Update.Seeded.Absorb.Prefix.TagHead
