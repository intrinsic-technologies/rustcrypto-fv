import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper512.ResetLayout
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
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Setup

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def bytes (disp : BitVec 32 := 368) (rex : UInt8 := 0x4c) (modrm : UInt8 := 0xee) : List UInt8 :=
  [0x48,0x8d,0xbc,0x24] ++ immBytes 32 disp ++ [rex,0x89,modrm]

def effectAt (p : BitVec 64) (disp : BitVec 32) (s : RamState)
    (rex : UInt8 := 0x4c) (modrm : UInt8 := 0xee) : Effect :=
  { rip := p + 11
    writes := [⟨(.reg 7 : Operand 64), rspOf s + disp.signExtend 64⟩,
      ⟨(.reg (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) : Operand 64),
        if gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm) = 7 then
          rspOf s + disp.signExtend 64 else
          (.reg (gprNumber 0 (rexR rex.toBitVec) (modrmReg modrm)) : Operand 64).read s⟩] }

def effect (variant : Variant) (s : RamState) : Effect :=
  { rip := variant.pc 0x1c5
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 368⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r13⟩] }

theorem code {variant : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (variant.pc 0x1ba) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (variant.textOffset + 0x1ba) bytes
    (by cases variant <;> decide +kernel) (by cases variant <;> decide +kernel)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem run_at [Bindings] (p : BitVec 64) (disp : BitVec 32)
    (boundary : ReturnBoundary) (rex modrm : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (encoding : (rex = 0x4c ∧ modrm = 0xee) ∨ (rex = 0x4c ∧ modrm = 0xf6) ∨
      (rex = 0x48 ∧ modrm = 0xee) ∨ (rex = 0x49 ∧ modrm = 0xf6) ∨
      (rex = 0x49 ∧ modrm = 0xf5))
    (nextBoundary : p + 8 ≠ boundary.rip) (last : p + 11 ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (bytes disp rex modrm)) (Effect.post (fun s => effectAt p disp s rex modrm)) := by
  advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 disp)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    simp only [AddrMode.modrm, AddrMode.mod, AddrMode.rm, AddrMode.tail, Disp.mod, Disp.bytes]
    change ∀ x ∈ codeRange p ([0x48,0x8d,0xbc,0x24] ++ immBytes 32 disp), x ∈ codeRange p (bytes disp rex modrm)
    simpa [bytes, immBytes, List.take_append] using codeRange_slice_subset p (bytes disp rex modrm) 0 8
  advance_then (mov_r64_r64_effect_step (p + 8) rex modrm hrex hmod)
  case sub => exact codeRange_slice_subset p (bytes disp rex modrm) 8 3
  rcases encoding with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals advance_finish [effectAt, BitVec.add_assoc, BitVec.add_zero]

theorem run [Bindings] {variant : Variant} (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (variant.pc 0x1ba))
      (codeRange (variant.pc 0x1ba) bytes) (Effect.post (effect variant)) := by
  have nextBoundary : variant.pc 0x1ba + 8 ≠ boundary.rip := by
    change variant.pc 0x1ba + BitVec.ofNat 64 8 ≠ boundary.rip
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram variant (by decide : 0x1c2 < 1024))
  have last : variant.pc 0x1ba + 11 ≠ boundary.rip := by
    change variant.pc 0x1ba + BitVec.ofNat 64 11 ≠ boundary.rip
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram variant (by decide : 0x1c5 < 1024))
  have same : effect variant = fun s => effectAt (variant.pc 0x1ba) 368 s := by
    funext s
    change { rip := variant.pc 0x1c5, writes := _ : Effect } =
      { rip := variant.pc 0x1ba + BitVec.ofNat 64 11, writes := _ : Effect }
    rw [Variant.pc_add]
    rfl
  rw [same]
  exact run_at (variant.pc 0x1ba) 368 boundary 0x4c 0xee
    (by simp [RexWPrefix]) rfl (Or.inl ⟨rfl,rfl⟩) nextBoundary last

def moveRex (form : Form) : UInt8 :=
  match form with
  | .reset stage => if stage.val == 0 then 0x4c else 0x49
  | .finalizeIntoReset second => if second then 0x49 else 0x4c
  | .traitFinalizeIntoReset second => if second then 0x4c else 0x48
  | _ => 0x4c

def moveModrm (form : Form) : UInt8 :=
  match form with
  | .reset _ => 0xf6
  | .finalizeIntoReset true => 0xf5
  | _ => 0xee

def offset (v : Variant) (form : Form) : Nat := (v.traversal form).blocksCall - 11

def displacement (form : Form) : BitVec 32 :=
  BitVec.ofNat 32 (form.frameBytes - form.activeMemory.hash)

set_option maxRecDepth 2048 in
theorem code_form {v : Variant} {form : Form} {s : RamState}
    (loaded : ProgramLoaded s) (nonDigest : form ≠ .digest) :
    CodeIn (codeRange (v.pc (offset v form) form)
      (bytes (displacement form) (moveRex form) (moveModrm form))) s := by
  exact programText_slice (programLoaded_codeIn loaded) (v.textOffset form + offset v form) _
    (by cases v <;> cases form <;> first | contradiction | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)) (by cases v <;> cases form <;> first | contradiction | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel))

set_option maxRecDepth 2048 in
theorem run_form [Bindings] (v : Variant) (form : Form)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) (nonDigest : form ≠ .digest) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (offset v form) form)
      (codeRange (v.pc (offset v form) form) (bytes (displacement form) (moveRex form) (moveModrm form)))
      (Effect.post (fun s => effectAt (v.pc (offset v form) form) (displacement form) s
        (moveRex form) (moveModrm form))) := by
  apply run_at
  · unfold RexWPrefix
    cases v <;> cases form <;> first | contradiction | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)
  · cases v <;> cases form <;> first | contradiction | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)
  · cases v <;> cases form <;> first | contradiction | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)
  · change v.pc (offset v form) form + BitVec.ofNat 64 8 ≠ boundary.rip
    rw [Variant.pc_add v _ _ form]
    apply boundary_ne_program outside
    apply inProgram_of_textOffset
    cases v <;> cases form <;> first | contradiction | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)
  · change v.pc (offset v form) form + BitVec.ofNat 64 11 ≠ boundary.rip
    rw [Variant.pc_add v _ _ form]
    apply boundary_ne_program outside
    apply inProgram_of_textOffset
    cases v <;> cases form <;> first | contradiction | decide +kernel | (rename_i b; cases b <;> decide +kernel) | (rename_i k; have h : k = (0 : Fin 3) ∨ k = 1 ∨ k = 2 := (by omega); rcases h with rfl | rfl | rfl <;> decide +kernel)

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Setup
