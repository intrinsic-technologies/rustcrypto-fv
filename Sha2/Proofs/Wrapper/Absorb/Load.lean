import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper.Variant
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

namespace Sha2.Proofs.Wrapper.Absorb.Load

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

structure Pre (s : RamState) (v : Variant := .sha256) : Prop where
  rip : s.RIP = (v.pc 0xcd)
  stackPointer : MemReadable s (rspOf s + 176) 8
  stackLength : MemReadable s (rspOf s + 184) 8
  pointer : MemReadable s (memLoad s.external (rspOf s + 176) 64 + (s.regValue .r14 <<< (3 : Nat))) 8
  length : MemReadable s (memLoad s.external (rspOf s + 184) 64 + (s.regValue .r14 <<< (3 : Nat))) 8
  tail : MemReadable s (rspOf s + 255) 1

def bytes : List UInt8 :=
  [0x48,0x8b,0x84,0x24,0xb0,0,0,0,0x4e,0x8b,0x2c,0xf0,
   0x48,0x8b,0x84,0x24,0xb8,0,0,0,0x4a,0x8b,0x1c,0xf0,
   0x44,0x0f,0xb6,0xa4,0x24,0xff,0,0,0]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0xee)
    writes := [
      ⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 184) 64⟩,
      ⟨(.reg 13 : Operand 64), memLoad s.external
        (memLoad s.external (rspOf s + 176) 64 + (s.regValue .r14 <<< (3 : Nat))) 64⟩,
      ⟨(.reg 3 : Operand 64), memLoad s.external
        (memLoad s.external (rspOf s + 184) 64 + (s.regValue .r14 <<< (3 : Nat))) 64⟩,
      ⟨(.reg 12 : Operand 64), (memLoad s.external (rspOf s + 255) 8).setWidth 64⟩] }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0xcd) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0xcd) bytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre s v) (codeRange (v.pc 0xcd) bytes) (Effect.post (fun s => effect s v)) := by
  advance_begin (mov_r64_m64_effect_step (v.pc 0xcd) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
  case pre =>
    intro s hp
    exact ⟨hp.rip, hp.stackPointer⟩
  case next =>
    intro _ _
    change v.pc 0xcd + BitVec.ofNat 64 8 ≠ boundary.rip
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xd5 < 1024))
  advance_then (mov_r64_m64_effect_step (v.pc 0xd5) 0x4e (by simp [RexWPrefix]) 5
    (.sib 0 (some 14) 3 .none) (by decide +kernel) rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0xcd 8]
    exact codeRange_slice_subset (v.pc 0xcd) bytes 8 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by simp only [Variant.pc_add]) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0xd5 + BitVec.ofNat 64 4 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xd9 < 1024))⟩
    x86_norm
    simp only [BitVec.add_zero]
    exact hp.pointer
  advance_then (mov_r64_m64_effect_step (v.pc 0xd9) 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0xcd 12]
    exact codeRange_slice_subset (v.pc 0xcd) bytes 12 8
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by simp only [Variant.pc_add]) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0xd9 + BitVec.ofNat 64 8 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xe1 < 1024))⟩
    x86_norm
    exact hp.stackLength
  advance_then (mov_r64_m64_effect_step (v.pc 0xe1) 0x4a (by simp [RexWPrefix]) 3
    (.sib 0 (some 14) 3 .none) (by decide +kernel) rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0xcd 20]
    exact codeRange_slice_subset (v.pc 0xcd) bytes 20 4
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by simp only [Variant.pc_add]) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0xe1 + BitVec.ofNat 64 4 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xe5 < 1024))⟩
    x86_norm
    simp only [BitVec.add_zero]
    exact hp.length
  advance_then (movzx_r_m8_rex_effect_step (v.pc 0xe5) 0x44 (by simp [RexPrefix]) 32
    (Or.inr rfl) (by intro seg; rfl) 4 (.sib 4 none 0 (.d32 255)) (by decide +kernel) rfl rfl)
  case sub =>
    rw [← Variant.pc_add v 0xcd 24]
    exact codeRange_slice_subset (v.pc 0xcd) bytes 24 9
  case mid =>
    intro s t hp hh ho
    refine ⟨LoadPre.of_holds hh (ho true) (by simp only [Variant.pc_add]) (by x86_addr_obs) ?_,
      Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0xe5 + BitVec.ofNat 64 9 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0xee < 1024))⟩
    x86_norm
    exact hp.tail
  advance_finish [Variant.pc_add, effect, BitVec.add_zero]

end Sha2.Proofs.Wrapper.Absorb.Load
