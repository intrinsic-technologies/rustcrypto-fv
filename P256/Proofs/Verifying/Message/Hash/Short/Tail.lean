import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Program.Code
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Encoding.Parser.ByteStore
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Instructions.ByteLogic.Register
import X86Proofs.Instructions.Cmp.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Short.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.ByteLogic

@[local x86_local] theorem store_local (p : BitVec 64) (len : Nat) (src : BitVec 5)
    (am : AddrMode) :
    Effect.Local (storeEffect p len (storeAddrAt p am len)
      (fun s => (Operand.reg src : Operand 8).read s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, storeAddrAt, AddrMode.addr_obs h, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x10d627
  writable : MemWritable s (rspOf s + 535) 1
  codeApart : ∀ pc len : Nat, pc + len ≤ 118431 →
    RangeApart (rspOf s + 535) 1 (Extracted.textAddress + BitVec.ofNat 64 pc) len

def bytes : List UInt8 :=
  [0x41,0x0,0xdf,0x44,0x88,0xbc,0x24,0x17,0x2,0x0,0x0,0x49,0x83,0xc5,0x10,0x4d,0x39,0xe5]

def sum (s : RamState) : BitVec 8 := (Operand.reg 15 : Operand 8).read s + (Operand.reg 3 : Operand 8).read s

def effect (s : RamState) : Effect :=
  { rip := 0x10d639
    writes := [⟨(.reg 15 : Operand 64), mergeGPR 8 (sum s) ((Operand.reg 15 : Operand 64).read s)⟩,
      ⟨(.mem (rspOf s + 535) : Operand 8),sum s⟩,
      ⟨(.reg 13 : Operand 64),(Operand.reg 13 : Operand 64).read s + 16⟩]
    flags := some (.ofStatusFlags (cmpSpec ((Operand.reg 13 : Operand 64).read s + 16)
      ((Operand.reg 12 : Operand 64).read s))) }

theorem code {s : RamState} (loaded : ProgramLoaded s) : CodeIn (codeRange 0x10d627 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xd627 bytes (by decide) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x10d627 bytes) (Effect.post effect) := by
  advance_begin (add_r8_r8_rex_effect_step 0x10d627 0x41 0xdf (by simp [RexPrefix]) rfl)
  case next => exact fun _ _ => boundary_ne_program outside (inProgram_of_textOffset 0xd62a (by decide))
  advance_then (mov_m8_r8_effect_step 0x10d62a 0x44 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d32 535)) (by decide) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d627 bytes 3 8
  case mid =>
    intro s t hP hH hO
    refine ⟨StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
    · x86_norm; exact hP.writable
    · x86_norm; exact hP.codeApart 0xd62a 8 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0xd627 18 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0xd632 (by decide))
  advance_then (add_r64_imm8_effect_step 0x10d632 0x49 0xc5 16 (by simp [RexWPrefix]) rfl rfl)
  case sub => exact codeRange_slice_subset 0x10d627 bytes 11 4
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd636 (by decide))⟩
  advance_then (cmp_r64_r64_effect_step 0x10d636 0x4d 0xe5 (by simp [RexWPrefix]) rfl)
  case sub => exact codeRange_slice_subset 0x10d627 bytes 15 3
  case mid =>
    intro s t hP hH hO
    exact ⟨hH.rip_of (by x86_norm),
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      boundary_ne_program outside (inProgram_of_textOffset 0xd639 (by decide))⟩
  apply AdvanceTriple.block_end
  intro s t hP hH
  apply hH.weaken
  · x86_norm [effect,sum]
  · x86_norm [effect,sum]
    exact ⟨.inl rfl, .inr (.inl rfl), .inr rfl⟩
  · intro i; cases i <;> x86_norm [effect,sum] <;> rfl
  · x86_norm [effect,sum]

end P256.Proofs.Verifying.Message.Hash.Short.Tail
