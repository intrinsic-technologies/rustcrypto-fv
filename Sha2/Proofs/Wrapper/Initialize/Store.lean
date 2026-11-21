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

namespace Sha2.Proofs.Wrapper.Initialize.Store

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

attribute [local x86_compose] movM8Imm8Effect

@[local x86_local] theorem byteStore_local (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) :
    Effect.Local (movM8Imm8Effect p am imm) := by
  apply Sha2.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [movM8Imm8Effect, storeEffect, storeAddrAt, AddrMode.addr_obs h]
  · intro s
    simp [movM8Imm8Effect, storeEffect, Write.Full, Operand.Full]

structure Pre (s : RamState) (v : Variant := .sha256) : Prop where
  rip : s.RIP = (v.pc 0x29)
  writable : ∀ slot ∈ ([(256,8),(264,8),(272,8),(280,8),(288,8),(255,1)] : List (Nat × Nat)),
    MemWritable s (rspOf s + BitVec.ofNat 64 slot.1) slot.2
  codeApart : ∀ slot ∈ ([(256,8),(264,8),(272,8),(280,8),(288,8),(255,1)] : List (Nat × Nat)),
    ∀ offset len : Nat, offset + len ≤ 71757 →
    RangeApart (rspOf s + BitVec.ofNat 64 slot.1) slot.2
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes (v : Variant := .sha256) : List UInt8 :=
  match v with
  | .sha224 => [0x48, 0xb8, 0xa7, 0x8f, 0xf9, 0x64, 0xa4, 0x4f, 0xfa, 0xbe, 0x48, 0x89, 0x84, 0x24, 0x18, 0x1, 0x0, 0x0, 0x48, 0xb8, 0x31, 0xb, 0xc0, 0xff, 0x11, 0x15, 0x58, 0x68, 0x48, 0x89, 0x84, 0x24, 0x10, 0x1, 0x0, 0x0, 0x48, 0xb8, 0x17, 0xdd, 0x70, 0x30, 0x39, 0x59, 0xe, 0xf7, 0x48, 0x89, 0x84, 0x24, 0x8, 0x1, 0x0, 0x0, 0x48, 0xb8, 0xd8, 0x9e, 0x5, 0xc1, 0x7, 0xd5, 0x7c, 0x36, 0x48, 0x89, 0x84, 0x24, 0x0, 0x1, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x20, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0xff, 0x0, 0x0, 0x0, 0x0]
  | .sha256 =>  [0x48, 0xb8, 0xab, 0xd9, 0x83, 0x1f, 0x19, 0xcd, 0xe0, 0x5b, 0x48, 0x89, 0x84, 0x24, 0x18, 0x1, 0x0, 0x0, 0x48, 0xb8, 0x7f, 0x52, 0xe, 0x51, 0x8c, 0x68, 0x5, 0x9b, 0x48, 0x89, 0x84, 0x24, 0x10, 0x1, 0x0, 0x0, 0x48, 0xb8, 0x72, 0xf3, 0x6e, 0x3c, 0x3a, 0xf5, 0x4f, 0xa5, 0x48, 0x89, 0x84, 0x24, 0x8, 0x1, 0x0, 0x0, 0x48, 0xb8, 0x67, 0xe6, 0x9, 0x6a, 0x85, 0xae, 0x67, 0xbb, 0x48, 0x89, 0x84, 0x24, 0x0, 0x1, 0x0, 0x0, 0x48, 0xc7, 0x84, 0x24, 0x20, 0x1, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0xc6, 0x84, 0x24, 0xff, 0x0, 0x0, 0x0, 0x0]

def initialWords (v : Variant := .sha256) : List (BitVec 64) :=
  match v with
  | .sha224 => [0x367cd507c1059ed8, 0xf70e59393070dd17, 0x68581511ffc00b31, 0xbefa4fa464f98fa7]
  | .sha256 => [0xbb67ae856a09e667, 0xa54ff53a3c6ef372, 0x9b05688c510e527f, 0x5be0cd191f83d9ab]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0x85)
    writes := [
      ⟨(.reg 0 : Operand 64), (initialWords v)[0]!⟩,
      ⟨(.mem (rspOf s + 280) : Operand 64), (initialWords v)[3]!⟩,
      ⟨(.mem (rspOf s + 272) : Operand 64), (initialWords v)[2]!⟩,
      ⟨(.mem (rspOf s + 264) : Operand 64), (initialWords v)[1]!⟩,
      ⟨(.mem (rspOf s + 256) : Operand 64), (initialWords v)[0]!⟩,
      ⟨(.mem (rspOf s + 288) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + 255) : Operand 8), 0⟩] }

 theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x29) (bytes v)) s :=
  programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x29) (bytes v)
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

local macro "runStore" "(" variant:term ")" "(" outside:term ")" : tactic =>
  `(tactic| (
    advance_begin (mov_r64_imm64_effect_step (($variant).pc 0x29) 0x48 0xb8 (by simp [RexWPrefix]) (by decide) (initialWords $variant)[3]!)
    case next => exact fun _ _ => boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x33) (by decide))
    advance_then (mov_m64_r64_effect_step (($variant).pc 0x33) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 280)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset (($variant).pc 0x29) (bytes $variant) 10 8
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.writable (280,8) (by simp)
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (280,8) (by simp) (($variant).textOffset + 0x33) 8 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (280,8) (by simp) (($variant).textOffset + 0x29) 92 (by decide)
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x3b) (by decide))
    advance_then (mov_r64_imm64_effect_step (($variant).pc 0x3b) 0x48 0xb8 (by simp [RexWPrefix]) (by decide) (initialWords $variant)[2]!)
    case sub => exact codeRange_slice_subset (($variant).pc 0x29) (bytes $variant) 18 10
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x45) (by decide))
    advance_then (mov_m64_r64_effect_step (($variant).pc 0x45) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 272)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset (($variant).pc 0x29) (bytes $variant) 28 8
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.writable (272,8) (by simp)
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (272,8) (by simp) (($variant).textOffset + 0x45) 8 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (272,8) (by simp) (($variant).textOffset + 0x29) 92 (by decide)
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x4d) (by decide))
    advance_then (mov_r64_imm64_effect_step (($variant).pc 0x4d) 0x48 0xb8 (by simp [RexWPrefix]) (by decide) (initialWords $variant)[1]!)
    case sub => exact codeRange_slice_subset (($variant).pc 0x29) (bytes $variant) 36 10
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x57) (by decide))
    advance_then (mov_m64_r64_effect_step (($variant).pc 0x57) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 264)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset (($variant).pc 0x29) (bytes $variant) 46 8
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.writable (264,8) (by simp)
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (264,8) (by simp) (($variant).textOffset + 0x57) 8 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (264,8) (by simp) (($variant).textOffset + 0x29) 92 (by decide)
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x5f) (by decide))
    advance_then (mov_r64_imm64_effect_step (($variant).pc 0x5f) 0x48 0xb8 (by simp [RexWPrefix]) (by decide) (initialWords $variant)[0]!)
    case sub => exact codeRange_slice_subset (($variant).pc 0x29) (bytes $variant) 54 10
    case mid =>
      intro s t hP hH hO
      refine ⟨hH.rip_of (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Component.Covers]
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x69) (by decide))
    advance_then (mov_m64_r64_effect_step (($variant).pc 0x69) 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 256)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset (($variant).pc 0x29) (bytes $variant) 64 8
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.writable (256,8) (by simp)
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (256,8) (by simp) (($variant).textOffset + 0x69) 8 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (256,8) (by simp) (($variant).textOffset + 0x29) 92 (by decide)
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x71) (by decide))
    advance_then (mov_m64_imm32_effect_step (($variant).pc 0x71) 0x48 (by simp [RexWPrefix]) (.sib 4 none 0 (.d32 288)) (by decide +kernel) rfl rfl 0)
    case sub => exact codeRange_slice_subset (($variant).pc 0x29) (bytes $variant) 72 12
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.writable (288,8) (by simp)
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (288,8) (by simp) (($variant).textOffset + 0x71) 12 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (288,8) (by simp) (($variant).textOffset + 0x29) 92 (by decide)
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x7d) (by decide))
    advance_then (mov_m8_imm8_effect_step (($variant).pc 0x7d) (.sib 4 none 0 (.d32 255)) (by decide +kernel) rfl rfl 0)
    case sub => exact codeRange_slice_subset (($variant).pc 0x29) (bytes $variant) 84 8
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.writable (255,1) (by simp)
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (255,1) (by simp) (($variant).textOffset + 0x7d) 8 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart (255,1) (by simp) (($variant).textOffset + 0x29) 92 (by decide)
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x85) (by decide))
    advance_finish [effect, Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
  ))

set_option maxHeartbeats 1000000 in
theorem run {v : Variant} [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre s v) (codeRange (v.pc 0x29) (bytes v)) (Effect.post (fun s => effect s v)) := by
  cases v with
  | sha224 => runStore (Variant.sha224) (outside)
  | sha256 => runStore (Variant.sha256) (outside)

end Sha2.Proofs.Wrapper.Initialize.Store
