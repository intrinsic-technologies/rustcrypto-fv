import Hkdf.Proofs.Standard.Memory
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Update

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field

structure LoadPre (s : RamState) : Prop where
  rip : s.RIP = 0x101649
  pointerSlot : MemReadable s (rspOf s + 104) 8
  lengthSlot : MemReadable s (rspOf s + 112) 8
  pointerEntry : MemReadable s
    (memLoad s.external (rspOf s + 104) 64 + (s.regValue .r14 <<< (3 : Nat))) 8
  lengthEntry : MemReadable s
    (memLoad s.external (rspOf s + 112) 64 + (s.regValue .r14 <<< (3 : Nat))) 8
  tailSlot : MemReadable s (rspOf s + 183) 1

def loadBytes : List UInt8 :=
  [0x48,0x8b,0x44,0x24,0x68,0x4e,0x8b,0x2c,0xf0,0x48,0x8b,0x44,0x24,0x70,
    0x4a,0x8b,0x1c,0xf0,0x44,0x0f,0xb6,0xbc,0x24,0xb7,0,0,0]

def loadEffect (s : RamState) : Effect :=
  { rip := 0x101664
    writes := [
      ⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + 112) 64⟩,
      ⟨(.reg 13 : Operand 64), memLoad s.external
        (memLoad s.external (rspOf s + 104) 64 + (s.regValue .r14 <<< (3 : Nat))) 64⟩,
      ⟨(.reg 3 : Operand 64), memLoad s.external
        (memLoad s.external (rspOf s + 112) 64 + (s.regValue .r14 <<< (3 : Nat))) 64⟩,
      ⟨(.reg 15 : Operand 64), (memLoad s.external (rspOf s + 183) 8).setWidth 64⟩] }

set_option maxHeartbeats 800000 in
theorem load_run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary LoadPre (codeRange 0x101649 loadBytes) (Effect.post loadEffect) := by
  advance_begin (mov_r64_m64_effect_step 0x101649 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 104)) (by decide +kernel) rfl rfl)
  case pre => intro s h; exact ⟨h.rip, h.pointerSlot⟩
  case next => exact fun _ _ ↦ boundary_ne_program outside (inProgram_of_textOffset 0x164e (by decide))
  advance_then (mov_r64_m64_effect_step 0x10164e 0x4e (by simp [RexWPrefix]) 5
    (.sib 0 (some 14) 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101649 loadBytes 5 4
  case mid =>
    intro s t hp hh ho
    refine ⟨X86Proofs.LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      by x86_avoid, boundary_ne_program outside (inProgram_of_textOffset 0x1652 (by decide))⟩
    x86_norm
    simp only [BitVec.add_zero]
    exact hp.pointerEntry
  advance_then (mov_r64_m64_effect_step 0x101652 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 112)) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101649 loadBytes 9 5
  case mid =>
    intro s t hp hh ho
    refine ⟨X86Proofs.LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      by x86_avoid, boundary_ne_program outside (inProgram_of_textOffset 0x1657 (by decide))⟩
    x86_norm
    exact hp.lengthSlot
  advance_then (mov_r64_m64_effect_step 0x101657 0x4a (by simp [RexWPrefix]) 3
    (.sib 0 (some 14) 3 .none) (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101649 loadBytes 14 4
  case mid =>
    intro s t hp hh ho
    refine ⟨X86Proofs.LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      by x86_avoid, boundary_ne_program outside (inProgram_of_textOffset 0x165b (by decide))⟩
    x86_norm
    simp only [BitVec.add_zero]
    exact hp.lengthEntry
  advance_then (movzx_r_m8_rex_effect_step 0x10165b 0x44 (by simp [RexPrefix]) 32
    (.inr rfl) (by intro seg; rfl) 7 (.sib 4 none 0 (.d32 183))
    (by decide +kernel) rfl rfl)
  case sub => exact codeRange_slice_subset 0x101649 loadBytes 18 9
  case mid =>
    intro s t hp hh ho
    refine ⟨X86Proofs.LoadPre.of_holds hh (ho true) (by x86_norm) (by x86_addr_obs) ?_,
      by x86_avoid, boundary_ne_program outside (inProgram_of_textOffset 0x1664 (by decide))⟩
    x86_norm
    exact hp.tailSlot
  advance_finish [loadEffect, BitVec.add_zero]

end Hkdf.Proofs.Standard.Update
