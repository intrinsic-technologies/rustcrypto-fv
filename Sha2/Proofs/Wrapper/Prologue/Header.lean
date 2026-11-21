import Sha2.Proofs.Wrapper.Variant
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

namespace Sha2.Proofs.Wrapper.Prologue.Header

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

structure Pre (s : RamState) (v : Variant := .sha256) : Prop where
  rip : s.RIP = (v.pc 0x11)
  writable : ∀ slot ∈ ([168,184,176] : List Nat), MemWritable s (rspOf s + BitVec.ofNat 64 slot) 8
  codeApart : ∀ slot ∈ ([168,184,176] : List Nat),
    ∀ offset len : Nat, offset + len ≤ 71757 →
    RangeApart (rspOf s + BitVec.ofNat 64 slot) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len

def bytes : List UInt8 :=
  [0x48, 0x89, 0x8c, 0x24, 0xa8, 0x0, 0x0, 0x0, 0x48, 0x89, 0x94, 0x24, 0xb8, 0x0, 0x0, 0x0, 0x48, 0x89, 0xbc, 0x24, 0xb0, 0x0, 0x0, 0x0]

def effect (s : RamState) (v : Variant := .sha256) : Effect :=
  { rip := (v.pc 0x29)
    writes := [
      ⟨(.mem (rspOf s + 168) : Operand 64), (.reg 1 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 184) : Operand 64), (.reg 2 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 176) : Operand 64), (.reg 7 : Operand 64).read s⟩] }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x11) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x11) bytes
    (by cases v <;> decide +kernel) (by cases v <;> decide +kernel)

local macro "runHeader" "(" variant:term ")" "(" outside:term ")" : tactic =>
  `(tactic| (
    advance_begin (mov_m64_r64_effect_step (($variant).pc 0x11) 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d32 168)) (by decide +kernel) rfl rfl)
    case pre =>
      intro s h
      exact ⟨h.rip, h.writable 168 (by simp), h.codeApart 168 (by simp) (($variant).textOffset + 0x11) 8 (by decide)⟩
    case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
      exact h.codeApart 168 (by simp) (($variant).textOffset + 0x11) 24 (by decide)
    case next => exact fun _ _ => boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x19) (by decide))
    advance_then (mov_m64_r64_effect_step (($variant).pc 0x19) 0x48 (by simp [RexWPrefix]) 2
      (.sib 4 none 0 (.d32 184)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset (($variant).pc 0x11) bytes 8 8
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.writable 184 (by simp)
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart 184 (by simp) (($variant).textOffset + 0x19) 8 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart 184 (by simp) (($variant).textOffset + 0x11) 24 (by decide)
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x21) (by decide))
    advance_then (mov_m64_r64_effect_step (($variant).pc 0x21) 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl)
    case sub => exact codeRange_slice_subset (($variant).pc 0x11) bytes 16 8
    case mid =>
      intro s t hP hH hO
      refine ⟨StorePre.of_holds hH (hO true) (by x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.writable 176 (by simp)
      · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart 176 (by simp) (($variant).textOffset + 0x21) 8 (by decide)
      · apply Effect.Local.avoids (by x86_local) (hO true)
        apply Effect.avoids_codeRange
        x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc]
        exact hP.codeApart 176 (by simp) (($variant).textOffset + 0x11) 24 (by decide)
      · exact boundary_ne_program $outside (inProgram_of_textOffset (($variant).textOffset + 0x29) (by decide))
    apply Sha2.Proofs.Common.Field.AdvanceTriple.block_end
    intro s t _ h
    apply h.weaken
    · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, effect]
    · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, effect]
      exact ⟨by congr 2 <;> decide +kernel, by congr 2 <;> decide +kernel, by congr 2 <;> decide +kernel⟩
    · intro i
      cases i <;> x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, effect]
    · x86_norm [Variant.pc, BitVec.ofNat_add, BitVec.add_assoc, effect]
  ))

theorem run {v : Variant} [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => Pre s v) (codeRange (v.pc 0x11) bytes) (Effect.post (fun s => effect s v)) := by
  cases v with
  | sha224 => runHeader (Variant.sha224) (outside)
  | sha256 => runHeader (Variant.sha256) (outside)

end Sha2.Proofs.Wrapper.Prologue.Header
