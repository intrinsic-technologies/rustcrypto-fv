import Sha2.Proofs.Wrapper512.Absorb.State
import Sha2.Proofs.Common.SHA256.Blocks.Absorb.Instruction
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper512.Variant
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

namespace Sha2.Proofs.Wrapper512.Absorb.Prepare

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.SHA256.Absorb.Blocks

attribute [local x86_compose] readReg

def registerBytes (tail length rest : BitVec 4) : List UInt8 :=
  encodeMovR32Imm32 2 128 ++ encodeSubR64R64 2 tail ++
    encodeMovR64R64 rest length ++ encodeSubR64R64 rest 2

def registerEffect (p : BitVec 64) (tail length rest : BitVec 4) (s : RamState) : Effect :=
  { rip := p + 14
    writes := [⟨(.reg 2 : Operand 64), 128 - readReg s tail⟩,
      ⟨(.reg (rest.setWidth 5) : Operand 64), readReg s length - (128 - readReg s tail)⟩]
    flags := some (.ofStatusFlags (subSpec (readReg s length) (128 - readReg s tail)).2) }

set_option maxHeartbeats 1000000 in
theorem run_registers [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (tail length rest : BitVec 4)
    (ht : tail.setWidth 5 ≠ 2#5) (hl : length.setWidth 5 ≠ 2#5)
    (hr : rest.setWidth 5 ≠ 2#5)
    (outside : ¬ InProgram boundary.rip)
    (inside : BlockInProgram p 14) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (registerBytes tail length rest))
      (Effect.post (registerEffect p tail length rest)) := by
  advance_reloc_begin (constant_step p 2 128)
    next (boundary_ne_program outside (inside 5 (by omega)))
  try (case sub => exact codeRange_mem_of_take (by rfl))
  try (case full => intro s _; x86_norm [ht, hl, hr, Ne.symm ht, Ne.symm hl, Ne.symm hr])
  try x86_norm [ht, hl, hr, Ne.symm ht, Ne.symm hl, Ne.symm hr]
  advance_reloc_then (subtract_step (p + 5) 2 tail)
    next (boundary_ne_program outside (inside 8 (by omega)))
  try (case sub => exact codeRange_mem_of_drop 5 (by rfl))
  try (case full => intro s _; x86_norm [ht, hl, hr, Ne.symm ht, Ne.symm hl, Ne.symm hr])
  try x86_norm [ht, hl, hr, Ne.symm ht, Ne.symm hl, Ne.symm hr]
  advance_reloc_then (move_step (p + 8) rest length)
    next (boundary_ne_program outside (inside 11 (by omega)))
  try (case sub => exact codeRange_mem_of_drop 8 (by rfl))
  try (case full => intro s _; x86_norm [ht, hl, hr, Ne.symm ht, Ne.symm hl, Ne.symm hr])
  try x86_norm [ht, hl, hr, Ne.symm ht, Ne.symm hl, Ne.symm hr]
  advance_reloc_then (subtract_step (p + 11) rest 2)
    next (boundary_ne_program outside (inside 14 (by omega)))
  try (case sub => exact codeRange_mem_of_drop 11 (by rfl))
  try (case full => intro s _; x86_norm [ht, hl, hr, Ne.symm ht, Ne.symm hl, Ne.symm hr])
  try x86_norm [ht, hl, hr, Ne.symm ht, Ne.symm hl, Ne.symm hr]
  advance_finish [registerEffect, registerBytes, encodeMovR32Imm32, encodeSubR64R64,
    encodeMovR64R64, ht, hl, hr, Ne.symm ht, Ne.symm hl, Ne.symm hr]

def bytes : List UInt8 :=
  [0xba,0x80,0,0,0,0x4c,0x29,0xe2,0x48,0x89,0xdd,0x48,0x29,0xd5]

def effect (v : Variant) (s : RamState) : Effect :=
  { rip := (v.pc 0x146)
    writes := [⟨(.reg 2 : Operand 64), 128 - s.regValue .r12⟩,
      ⟨(.reg 5 : Operand 64), s.regValue .rbx - (128 - s.regValue .r12)⟩]
    flags := some (.ofStatusFlags (subSpec (s.regValue .rbx) (128 - s.regValue .r12)).2) }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x138) bytes) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x138) bytes
  · cases v <;> decide +kernel
  · cases v <;> decide +kernel

set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (v.pc 0x138))
      (codeRange (v.pc 0x138) bytes) (Effect.post (effect v)) := by
  have inside : BlockInProgram (v.pc 0x138) 14 := by
    intro offset bound
    rw [Variant.pc_add]
    exact Variant.pc_inProgram v (by omega)
  have effects : registerEffect (v.pc 0x138) 12 3 5 = effect v := by
    funext s
    simp only [registerEffect, effect]
    rw [show v.pc 0x138 + 14 = v.pc 0x146 from Variant.pc_add v 0x138 14]
    rfl
  have h := run_registers boundary (v.pc 0x138) 12 3 5
    (by decide) (by decide) (by decide) outside inside
  rw [effects] at h
  exact h

end Sha2.Proofs.Wrapper512.Absorb.Prepare

namespace Sha2.Proofs.Wrapper512.Absorb.Prepare
open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb.Blocks

def formBytes (v : Variant) (form : Form) : List UInt8 :=
  registerBytes (BitVec.ofNat 4 (v.traversal form).tailReg)
    (BitVec.ofNat 4 (v.traversal form).lengthReg) ((v.restRegister form).setWidth 4)

theorem form_bytes (v : Variant) (form : Form) (table : form ≠ .digest) :
    Extracted.textBytes.toListFrom (v.textOffset form + v.loadedOffset form)
      (formBytes v form).length = formBytes v form := by
  cases form with
  | slices => cases v <;> decide +kernel
  | digest => exact (table rfl).elim
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second => revert second; cases v <;> decide +kernel
  | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel

end Sha2.Proofs.Wrapper512.Absorb.Prepare

namespace Sha2.Proofs.Wrapper512.Absorb.Prepare
open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

theorem code_form {v : Variant} {form : Form} {s : RamState}
    (table : form ≠ .digest) (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (v.loadedOffset form) form) (formBytes v form)) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + v.loadedOffset form) (formBytes v form)
  · cases form with
    | slices => cases v <;> decide +kernel
    | digest => exact (table rfl).elim
    | reset stage => revert stage; cases v <;> decide +kernel
    | finalizeIntoReset second => revert second; cases v <;> decide +kernel
    | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel
  · exact form_bytes v form table

end Sha2.Proofs.Wrapper512.Absorb.Prepare

namespace Sha2.Proofs.Wrapper512.Absorb.Prepare
open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Instructions Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

theorem run_form [Bindings] {v : Variant} {form : Form}
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (v.loadedOffset form) form)
      (codeRange (v.pc (v.loadedOffset form) form) (formBytes v form))
      (Effect.post (registerEffect (v.pc (v.loadedOffset form) form)
        (BitVec.ofNat 4 (v.traversal form).tailReg)
        (BitVec.ofNat 4 (v.traversal form).lengthReg)
        ((v.restRegister form).setWidth 4))) := by
  have limits : v.textOffset form + v.loadedOffset form + 14 < 71757 := by
    cases form with
    | slices | digest => cases v <;> decide +kernel
    | reset stage => revert stage; cases v <;> decide +kernel
    | finalizeIntoReset second => revert second; cases v <;> decide +kernel
    | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel
  refine run_registers boundary _ _ _ _ ?_ ?_ ?_ outside ?_
  · cases form with
    | slices | digest => cases v <;> decide +kernel
    | reset stage => revert stage; cases v <;> decide +kernel
    | finalizeIntoReset second => revert second; cases v <;> decide +kernel
    | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel
  · cases form with
    | slices | digest => cases v <;> decide +kernel
    | reset stage => revert stage; cases v <;> decide +kernel
    | finalizeIntoReset second => revert second; cases v <;> decide +kernel
    | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel
  · cases form with
    | slices | digest => cases v <;> decide +kernel
    | reset stage => revert stage; cases v <;> decide +kernel
    | finalizeIntoReset second => revert second; cases v <;> decide +kernel
    | traitFinalizeIntoReset second => revert second; cases v <;> decide +kernel
  · intro offset bound
    rw [Variant.pc_add v (v.loadedOffset form) offset form]
    apply inProgram_of_textOffset
    omega

end Sha2.Proofs.Wrapper512.Absorb.Prepare
