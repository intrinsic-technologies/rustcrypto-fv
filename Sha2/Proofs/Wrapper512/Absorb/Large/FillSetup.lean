import Sha2.Proofs.Wrapper512.Absorb.Copy
import Sha2.Proofs.Wrapper512.Absorb.Large.Finish
import Sha2.Proofs.Common.EffectCompose.AddImmediate
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
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.FillSetup

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def bytesAt (encoding : Fin 7) (truncated : Bool := false) : List UInt8 :=
  match encoding.val with
  | 0 => [0x4a,0x8d,0x1c,0x2a,0x4a,0x8d,0x3c,0x24,0x48,0x81,0xc7,0xf0,0x0,0x0,0x0,0x4c,0x89,0xee]
  | 1 => [0x49,0x8d,0x2c,0x16,0x4a,0x8d,0x3c,0x2c,0x4c,0x89,0xf6]
  | 2 => [0x4c,0x8d,0x34,0x16,0x4a,0x8d,0x3c,0x2c]
  | 3 => [0x4a,0x8d,0x2c,0x2a,0x4a,0x8d,0x3c,(if truncated then 0x24 else 0x3c),0x48,0x83,0xc7,0x10,0x4c,0x89,0xee]
  | 4 => [0x4c,0x8d,0x2c,0x16,(if truncated then 0x48 else 0x4a),0x8d,0x3c,(if truncated then 0x1c else 0x3c),0x48,0x83,0xc7,0x10]
  | 5 => [0x4c,0x8d,0x34,0x2a,0x48,0x8d,0x3c,0x1c,0x48,0x83,0xc7,0x20,0x48,0x89,0xee]
  | _ => [0x4e,0x8d,0x24,0x2a,0x48,0x8d,0x3c,0x1c,0x48,0x83,0xc7,0x20,0x4c,0x89,0xee]

def effectAt (p : BitVec 64) (encoding : Fin 7) (s : RamState) (truncated : Bool := false) : Effect :=
  match encoding.val with
  | 0 =>
    { rip := p + 18
      writes := [⟨(.reg 3 : Operand 64), (.reg 2 : Operand 64).read s + (.reg 13 : Operand 64).read s⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + (.reg 12 : Operand 64).read s + 240⟩,
        ⟨(.reg 6 : Operand 64), (.reg 13 : Operand 64).read s⟩]
      flags := some (.ofStatusFlags (addSpec (rspOf s + (.reg 12 : Operand 64).read s) 240).2) }
  | 1 =>
    { rip := p + 11
      writes := [⟨(.reg 5 : Operand 64), (.reg 14 : Operand 64).read s + (.reg 2 : Operand 64).read s⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + (.reg 13 : Operand 64).read s⟩,
        ⟨(.reg 6 : Operand 64), (.reg 14 : Operand 64).read s⟩] }
  | 2 =>
    { rip := p + 8
      writes := [⟨(.reg 14 : Operand 64), (.reg 6 : Operand 64).read s + (.reg 2 : Operand 64).read s⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + (.reg 13 : Operand 64).read s⟩] }
  | 3 =>
    { rip := p + 15
      writes := [⟨(.reg 5 : Operand 64), (.reg 2 : Operand 64).read s + (.reg 13 : Operand 64).read s⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + (.reg (if truncated then 12 else 15) : Operand 64).read s + 16⟩,
        ⟨(.reg 6 : Operand 64), (.reg 13 : Operand 64).read s⟩]
      flags := some (.ofStatusFlags (addSpec (rspOf s + (.reg (if truncated then 12 else 15) : Operand 64).read s) 16).2) }
  | 4 =>
    { rip := p + 12
      writes := [⟨(.reg 13 : Operand 64), (.reg 6 : Operand 64).read s + (.reg 2 : Operand 64).read s⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + (.reg (if truncated then 3 else 15) : Operand 64).read s + 16⟩]
      flags := some (.ofStatusFlags (addSpec (rspOf s + (.reg (if truncated then 3 else 15) : Operand 64).read s) 16).2) }
  | 5 =>
    { rip := p + 15
      writes := [⟨(.reg 14 : Operand 64), (.reg 2 : Operand 64).read s + (.reg 5 : Operand 64).read s⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + (.reg 3 : Operand 64).read s + 32⟩,
        ⟨(.reg 6 : Operand 64), (.reg 5 : Operand 64).read s⟩]
      flags := some (.ofStatusFlags (addSpec (rspOf s + (.reg 3 : Operand 64).read s) 32).2) }
  | _ =>
    { rip := p + 15
      writes := [⟨(.reg 12 : Operand 64), (.reg 2 : Operand 64).read s + (.reg 13 : Operand 64).read s⟩,
        ⟨(.reg 7 : Operand 64), rspOf s + (.reg 3 : Operand 64).read s + 32⟩,
        ⟨(.reg 6 : Operand 64), (.reg 13 : Operand 64).read s⟩]
      flags := some (.ofStatusFlags (addSpec (rspOf s + (.reg 3 : Operand 64).read s) 32).2) }

set_option maxHeartbeats 2000000 in
theorem run_at [Bindings] (p : BitVec 64) (encoding : Fin 7)
    (boundary : ReturnBoundary)
    (away : ∀ n : Nat, n ≤ 18 → p + BitVec.ofNat 64 n ≠ boundary.rip)
    (truncated : Bool := false) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (bytesAt encoding truncated)) (Effect.post (fun s => effectAt p encoding s truncated)) := by
  have cases : encoding = 0 ∨ encoding = 1 ∨ encoding = 2 ∨ encoding = 3 ∨
      encoding = 4 ∨ encoding = 5 ∨ encoding = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · cases truncated <;> (
    advance_begin (lea_r64_effect_step p 0x4a (by simp [RexWPrefix]) 3 (.sib 2 (some 13) 0 .none) (by decide +kernel) rfl rfl)
    case «next» => exact fun _ _ => away 4 (by omega)
    advance_then (lea_r64_effect_step (p + 4) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 12) 0 .none) (by decide +kernel) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 8 (by omega)
    advance_then (add_r64_imm32_effect_step (p + 8) 0x48 0xc7 240 (by simp [RexWPrefix]) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 15 (by omega)
    advance_then (mov_r64_r64_effect_step (p + 15) 0x4c 0xee (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 18 (by omega)
    advance_finish [effectAt, (show (0 : Fin 7).val = 0 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero])
  · cases truncated <;> (
    advance_begin (lea_r64_effect_step p 0x49 (by simp [RexWPrefix]) 5 (.sib 14 (some 2) 0 .none) (by decide +kernel) rfl rfl)
    case «next» => exact fun _ _ => away 4 (by omega)
    advance_then (lea_r64_effect_step (p + 4) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 13) 0 .none) (by decide +kernel) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 8 (by omega)
    advance_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 11 (by omega)
    advance_finish [effectAt, (show (1 : Fin 7).val = 1 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero])
  · cases truncated <;> (
    advance_begin (lea_r64_effect_step p 0x4c (by simp [RexWPrefix]) 14 (.sib 6 (some 2) 0 .none) (by decide +kernel) rfl rfl)
    case «next» => exact fun _ _ => away 4 (by omega)
    advance_then (lea_r64_effect_step (p + 4) 0x4a (by simp [RexWPrefix]) 7 (.sib 4 (some 13) 0 .none) (by decide +kernel) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 8 (by omega)
    advance_finish [effectAt, (show (2 : Fin 7).val = 2 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero])
  · let tailReg : BitVec 4 := if truncated then 12 else 15
    let tailRex : UInt8 := 0x4a
    cases truncated <;> (
    advance_begin (lea_r64_effect_step p 0x4a (by simp [RexWPrefix]) 5 (.sib 2 (some 13) 0 .none) (by decide +kernel) rfl rfl)
    case «next» => exact fun _ _ => away 4 (by omega)
    advance_then (lea_r64_effect_step (p + 4) tailRex (by simp [RexWPrefix, tailRex]) 7 (.sib 4 (some tailReg) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 8 (by omega)
    advance_then (add_r64_imm8_effect_step (p + 8) 0x48 0xc7 16 (by simp [RexWPrefix]) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 12 (by omega)
    advance_then (mov_r64_r64_effect_step (p + 12) 0x4c 0xee (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 15 (by omega)
    advance_finish [effectAt, (show (3 : Fin 7).val = 3 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero, tailReg, tailRex]
    all_goals (dsimp only [tailReg, tailRex]; first | x86_sub | x86_full))
  · let tailReg : BitVec 4 := if truncated then 3 else 15
    let tailRex : UInt8 := if truncated then 0x48 else 0x4a
    cases truncated <;> (
    advance_begin (lea_r64_effect_step p 0x4c (by simp [RexWPrefix]) 13 (.sib 6 (some 2) 0 .none) (by decide +kernel) rfl rfl)
    case «next» => exact fun _ _ => away 4 (by omega)
    advance_then (lea_r64_effect_step (p + 4) tailRex (by simp [RexWPrefix, tailRex]) 7 (.sib 4 (some tailReg) 0 .none) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 8 (by omega)
    advance_then (add_r64_imm8_effect_step (p + 8) 0x48 0xc7 16 (by simp [RexWPrefix]) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 12 (by omega)
    advance_finish [effectAt, (show (4 : Fin 7).val = 4 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero, tailReg, tailRex]
    all_goals (dsimp only [tailReg, tailRex]; first | x86_sub | x86_full))
  · cases truncated <;> (
    advance_begin (lea_r64_effect_step p 0x4c (by simp [RexWPrefix]) 14 (.sib 2 (some 5) 0 .none) (by decide +kernel) rfl rfl)
    case «next» => exact fun _ _ => away 4 (by omega)
    advance_then (lea_r64_effect_step (p + 4) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 (some 3) 0 .none) (by decide +kernel) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 8 (by omega)
    advance_then (add_r64_imm8_effect_step (p + 8) 0x48 0xc7 32 (by simp [RexWPrefix]) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 12 (by omega)
    advance_then (mov_r64_r64_effect_step (p + 12) 0x48 0xee (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 15 (by omega)
    advance_finish [effectAt, (show (5 : Fin 7).val = 5 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero])
  · cases truncated <;> (
    advance_begin (lea_r64_effect_step p 0x4e (by simp [RexWPrefix]) 12 (.sib 2 (some 13) 0 .none) (by decide +kernel) rfl rfl)
    case «next» => exact fun _ _ => away 4 (by omega)
    advance_then (lea_r64_effect_step (p + 4) 0x48 (by simp [RexWPrefix]) 7 (.sib 4 (some 3) 0 .none) (by decide +kernel) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 8 (by omega)
    advance_then (add_r64_imm8_effect_step (p + 8) 0x48 0xc7 32 (by simp [RexWPrefix]) rfl rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 12 (by omega)
    advance_then (mov_r64_r64_effect_step (p + 12) 0x4c 0xee (by simp [RexWPrefix]) rfl)
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
      x86_norm
      exact away 15 (by omega)
    advance_finish [effectAt, (show (6 : Fin 7).val = 6 from rfl), BitVec.add_assoc, BitVec.add_zero, BitVec.shiftLeft_zero])

def bytes : List UInt8 :=
  [0x4a,0x8d,0x1c,0x2a,0x4a,0x8d,0x3c,0x24,0x48,0x81,0xc7,0xf0,0x0,0x0,0x0,0x4c,0x89,0xee]

def effect (v : Variant) (s : RamState) : Effect :=
  { rip := (v.pc 0x163)
    writes := [⟨(.reg 3 : Operand 64), ((Operand.reg 2 : Operand 64).read s) + ((Operand.reg 13 : Operand 64).read s)⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + ((Operand.reg 12 : Operand 64).read s) + 240⟩,
      ⟨(.reg 6 : Operand 64), ((Operand.reg 13 : Operand 64).read s)⟩]
    flags := some (.ofStatusFlags (addSpec (rspOf s + ((Operand.reg 12 : Operand 64).read s)) 240).2) }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x151) bytes) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x151) bytes
  · cases v <;> decide +kernel
  · cases v <;> decide +kernel

theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (v.pc 0x151))
      (codeRange (v.pc 0x151) bytes) (Effect.post (effect v)) := by
  have same : effect v = effectAt (v.pc 0x151) 0 := by
    funext s
    change { rip := v.pc 0x163, writes := _, flags := _ : Effect } =
      { rip := v.pc 0x151 + BitVec.ofNat 64 18, writes := _, flags := _ : Effect }
    rw [Variant.pc_add]
  rw [same]
  exact run_at (v.pc 0x151) 0 boundary (by
    intro n hn
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram v (by omega)))

end Sha2.Proofs.Wrapper512.Absorb.Large.FillSetup


namespace Sha2.Proofs.Wrapper512.Absorb.Large.FillSetup
open Sha2.Spec.Program
def formEncoding : Form → Fin 7
  | .slices | .digest => 0
  | .reset stage => if stage.val = 0 then 1 else 2
  | .finalizeIntoReset false => 3
  | .finalizeIntoReset true => 4
  | .traitFinalizeIntoReset false => 5
  | .traitFinalizeIntoReset true => 6

def isTruncated : Variant → Bool
  | .sha512_224 | .sha512_256 => true
  | _ => false

def startOffset (v : Variant) (form : Form) : Nat :=
  Copy.Site.fill.relativeOffset form v - (bytesAt (formEncoding form) (isTruncated v)).length

theorem code_facts (v : Variant) (form : Form) (h : form ≠ .digest) :
    Sha2.Spec.Program.Extracted.textBytes.toListFrom
      (v.textOffset form + startOffset v form)
      (bytesAt (formEncoding form) (isTruncated v)).length =
      bytesAt (formEncoding form) (isTruncated v) := by
  cases v <;> cases form with
  | digest => exact False.elim (h rfl)
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | slices => decide +kernel
open X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Field (AdvanceTriple)

theorem start_bound (v : Variant) (form : Form) :
    v.textOffset form + startOffset v form + 18 < 71757 := by
  cases v <;> cases form with
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | _ => decide +kernel

theorem run_form [Bindings] (v : Variant) (form : Form)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (startOffset v form) form)
      (codeRange (v.pc (startOffset v form) form) (bytesAt (formEncoding form) (isTruncated v)))
      (Effect.post (fun s => effectAt (v.pc (startOffset v form) form)
        (formEncoding form) s (isTruncated v))) := by
  apply run_at
  intro n hn
  rw [Variant.pc_add v (startOffset v form) n form]
  apply boundary_ne_program outside
  apply inProgram_of_textOffset
  have bound := start_bound v form
  omega

def formComponents (v : Variant) (form : Form) : List Component :=
  [.reg (finishSourceRegister v form), .reg 7, .reg 6, .flags, .rip]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem form_result (v : Variant) (form : Form) (nonDigest : form ≠ .digest)
    {s t : RamState}
    (h : (effectAt (v.pc (startOffset v form) form) (formEncoding form) s
      (isTruncated v)).Holds s t) :
    (.reg (finishSourceRegister v form) : Operand 64).read t =
      s.regValue .rdx + v.sourceValue form s ∧
    t.regValue .rdi = rspOf s + v.tailValue form s +
      BitVec.ofNat 64 (form.frameBytes - form.activeMemory.buffer) ∧
    t.regValue .rsi = v.sourceValue form s ∧
    AgreesExcept (formComponents v form) s t := by
  have writes := h.writes
  have frame := h.agrees
  cases v <;> cases form
  all_goals first | exact (nonDigest rfl).elim | skip
  all_goals first
    | (rename_i stage
       have hc : stage = (0 : Fin 3) ∨ stage = 1 ∨ stage = 2 := by omega
       rcases hc with rfl | rfl | rfl)
    | (rename_i second; cases second)
    | skip
  all_goals
    dsimp [effectAt, formEncoding, isTruncated, (show (0 : Fin 7).val = 0 from rfl), (show (1 : Fin 7).val = 1 from rfl), (show (2 : Fin 7).val = 2 from rfl), (show (3 : Fin 7).val = 3 from rfl), (show (4 : Fin 7).val = 4 from rfl), (show (5 : Fin 7).val = 5 from rfl), (show (6 : Fin 7).val = 6 from rfl), Write.AllHold] at writes
    refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | exact writes.1
    | exact writes.1.trans (BitVec.add_comm _ _)
    | exact writes.2.1
    | exact writes.2.2
    | exact writes.2
    | (simpa only [BitVec.add_zero] using writes.2)
    | (simpa only [BitVec.add_zero] using writes.2.1)
    | (have di : t.regValue .rdi = _ := writes.2.1
       rw [di]
       change _ = _ + (0#64)
       rw [BitVec.add_zero]
       rfl)
    | (have di : t.regValue .rdi = _ := writes.2
       rw [di]
       change _ = _ + (0#64)
       rw [BitVec.add_zero]
       rfl)
    | exact frame.read (n:=64) (r:=6) (by simp [effectAt, formEncoding, isTruncated, (show (3 : Fin 7).val = 3 from rfl), (show (4 : Fin 7).val = 4 from rfl), (show (5 : Fin 7).val = 5 from rfl), (show (6 : Fin 7).val = 6 from rfl), Effect.components])
    | (apply frame.mono; simp [effectAt, formEncoding, isTruncated,
        formComponents, finishSourceRegister, Variant.traversal,
        ResetLayout.reset, ResetLayout.finalizeIntoReset, ResetLayout.traitFinalizeIntoReset,
        (show (3 : Fin 7).val = 3 from rfl), (show (4 : Fin 7).val = 4 from rfl), (show (5 : Fin 7).val = 5 from rfl), (show (6 : Fin 7).val = 6 from rfl), Effect.components])

end Sha2.Proofs.Wrapper512.Absorb.Large.FillSetup
