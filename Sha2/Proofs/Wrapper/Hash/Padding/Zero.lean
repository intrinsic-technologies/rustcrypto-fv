import Sha2.Proofs.Wrapper.Variant
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
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

namespace Sha2.Proofs.Wrapper.Hash.Padding.Zero

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

structure Pre (s : RamState) (v : Variant := .sha256) : Prop where
  rip : s.RIP = (v.pc 0x276)
  writable : ∀ i ∈ ([0,8,16,24,32,40,48] : List (BitVec 64)), MemWritable s (rspOf s + i) 8
  codeApart : ∀ i ∈ ([0,8,16,24,32,40,48] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 71757 →
    RangeApart (rspOf s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48, 0xc7, 0x4, 0x24, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x8, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x10, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x18, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x20, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x28, 0x0, 0x0, 0x0, 0x0, 0x48, 0xc7, 0x44, 0x24, 0x30, 0x0, 0x0, 0x0, 0x0]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0x2b4)
    writes := [⟨(.mem (rspOf s + 0) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 8) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 16) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 24) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 32) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 40) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 48) : Operand 64), 0⟩] }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x276) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x276) bytes (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

local macro "padding_zero_run" "(" v:term "," boundary:term "," outside:term ")" : tactic =>
  `(tactic| (
    advance_begin (mov_m64_imm32_effect_step (($v).pc 0x276) 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 .none) (by decide) rfl rfl 0)
    case pre =>
      intro s h
      refine ⟨h.rip, ?_, ?_⟩
      · simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value,
          rspOf, Operand.read, BitVec.add_zero] using h.writable 0 (by simp)
      · simpa [storeAddrAt, AddrMode.addr, AddrMode.tail, rspOf, Operand.read,
          AddrMode.reg64, Disp.value, Disp.bytes, BitVec.add_zero,
          Extracted.textAddress, Variant.pc] using h.codeApart 0 (by simp) (($v).textOffset + 0x276) 8 (by decide)
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      simpa [rspOf, Operand.read, Extracted.textAddress, Variant.pc, bytes] using
        h.codeApart 0 (by simp) (($v).textOffset + 0x276) 62 (by decide)
    case next =>
      intro _ _
      change ($v).pc 0x276 + BitVec.ofNat 64 8 ≠ ($boundary).rip
      rw [Variant.pc_add]
      exact boundary_ne_program $outside (Variant.pc_inProgram $v (by decide : 0x27e < 1024))
    advance_then (mov_m64_imm32_effect_step (($v).pc 0x27e) 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl 0)
    case sub =>
      rw [← Variant.pc_add $v 0x276 8]
      exact codeRange_slice_subset (($v).pc 0x276) bytes 8 9
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 8 (by simp)
      · x86_norm
        exact hP.codeApart 8 (by simp) (($v).textOffset + 0x27e) 9 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 8 (by simp) (($v).textOffset + 0x276) 62 (by decide)
      · change ($v).pc 0x27e + BitVec.ofNat 64 9 ≠ ($boundary).rip
        rw [Variant.pc_add]
        exact boundary_ne_program $outside (Variant.pc_inProgram $v (by decide : 0x287 < 1024))
    advance_then (mov_m64_imm32_effect_step (($v).pc 0x287) 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl 0)
    case sub =>
      rw [← Variant.pc_add $v 0x276 17]
      exact codeRange_slice_subset (($v).pc 0x276) bytes 17 9
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 16 (by simp)
      · x86_norm
        exact hP.codeApart 16 (by simp) (($v).textOffset + 0x287) 9 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 16 (by simp) (($v).textOffset + 0x276) 62 (by decide)
      · change ($v).pc 0x287 + BitVec.ofNat 64 9 ≠ ($boundary).rip
        rw [Variant.pc_add]
        exact boundary_ne_program $outside (Variant.pc_inProgram $v (by decide : 0x290 < 1024))
    advance_then (mov_m64_imm32_effect_step (($v).pc 0x290) 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 24)) (by decide) rfl rfl 0)
    case sub =>
      rw [← Variant.pc_add $v 0x276 26]
      exact codeRange_slice_subset (($v).pc 0x276) bytes 26 9
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 24 (by simp)
      · x86_norm
        exact hP.codeApart 24 (by simp) (($v).textOffset + 0x290) 9 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 24 (by simp) (($v).textOffset + 0x276) 62 (by decide)
      · change ($v).pc 0x290 + BitVec.ofNat 64 9 ≠ ($boundary).rip
        rw [Variant.pc_add]
        exact boundary_ne_program $outside (Variant.pc_inProgram $v (by decide : 0x299 < 1024))
    advance_then (mov_m64_imm32_effect_step (($v).pc 0x299) 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 32)) (by decide) rfl rfl 0)
    case sub =>
      rw [← Variant.pc_add $v 0x276 35]
      exact codeRange_slice_subset (($v).pc 0x276) bytes 35 9
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 32 (by simp)
      · x86_norm
        exact hP.codeApart 32 (by simp) (($v).textOffset + 0x299) 9 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 32 (by simp) (($v).textOffset + 0x276) 62 (by decide)
      · change ($v).pc 0x299 + BitVec.ofNat 64 9 ≠ ($boundary).rip
        rw [Variant.pc_add]
        exact boundary_ne_program $outside (Variant.pc_inProgram $v (by decide : 0x2a2 < 1024))
    advance_then (mov_m64_imm32_effect_step (($v).pc 0x2a2) 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 40)) (by decide) rfl rfl 0)
    case sub =>
      rw [← Variant.pc_add $v 0x276 44]
      exact codeRange_slice_subset (($v).pc 0x276) bytes 44 9
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 40 (by simp)
      · x86_norm
        exact hP.codeApart 40 (by simp) (($v).textOffset + 0x2a2) 9 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 40 (by simp) (($v).textOffset + 0x276) 62 (by decide)
      · change ($v).pc 0x2a2 + BitVec.ofNat 64 9 ≠ ($boundary).rip
        rw [Variant.pc_add]
        exact boundary_ne_program $outside (Variant.pc_inProgram $v (by decide : 0x2ab < 1024))
    advance_then (mov_m64_imm32_effect_step (($v).pc 0x2ab) 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 (.d8 48)) (by decide) rfl rfl 0)
    case sub =>
      rw [← Variant.pc_add $v 0x276 53]
      exact codeRange_slice_subset (($v).pc 0x276) bytes 53 9
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm
        exact hP.writable 48 (by simp)
      · x86_norm
        exact hP.codeApart 48 (by simp) (($v).textOffset + 0x2ab) 9 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm
        exact hP.codeApart 48 (by simp) (($v).textOffset + 0x276) 62 (by decide)
      · change ($v).pc 0x2ab + BitVec.ofNat 64 9 ≠ ($boundary).rip
        rw [Variant.pc_add]
        exact boundary_ne_program $outside (Variant.pc_inProgram $v (by decide : 0x2b4 < 1024))
    advance_finish [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, BitVec.reduceAdd, effect, BitVec.add_zero]
  ))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre s v) (codeRange (v.pc 0x276) bytes) (Effect.post (fun s => effect s v)) := by
  cases v with
  | sha224 => padding_zero_run (Variant.sha224, boundary, outside)
  | sha256 => padding_zero_run (Variant.sha256, boundary, outside)

end Sha2.Proofs.Wrapper.Hash.Padding.Zero
