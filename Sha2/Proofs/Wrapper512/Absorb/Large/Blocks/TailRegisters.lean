import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.Select
import Sha2.Proofs.Wrapper512.Absorb.TailLength
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

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.TailRegisters

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

attribute [local x86_compose] andR32Imm8Effect

@[local x86_local] theorem and32_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) :
    Effect.Local (andR32Imm8Effect p len dst imm) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [andR32Imm8Effect, h.read_reg]
  · intro s
    simp [andR32Imm8Effect, Write.Full, Operand.Full]

def bytesAt (encoding : Fin 6) : List UInt8 :=
  match encoding.val with
  | 0 => [0x48,0x89,0xe8,0x48,0xb9,0x80,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x48,0x21,0xc8,0x83,0xe5,0x7f,0x49,0x1,0xc5]
  | 1 => [0x48,0x89,0xd8,0x48,0xb9,0x80,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x48,0x21,0xc8,0x83,0xe3,0x7f,0x49,0x1,0xc6]
  | 2 => [0x48,0x89,0xe8,0x48,0xb9,0x80,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x48,0x21,0xc8,0x83,0xe5,0x7f,0x48,0x1,0xc6]
  | 3 => [0x48,0x89,0xd8,0x48,0xb9,0x80,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x48,0x21,0xc8,0x83,0xe3,0x7f,0x49,0x1,0xc5]
  | 4 => [0x4c,0x89,0xe0,0x48,0xb9,0x80,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x48,0x21,0xc8,0x41,0x83,0xe4,0x7f,0x48,0x1,0xc5]
  | _ => [0x4c,0x89,0xf0,0x48,0xb9,0x80,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x48,0x21,0xc8,0x41,0x83,0xe6,0x7f,0x49,0x1,0xc5]

def registersAt (encoding : Fin 6) : BitVec 5 × BitVec 5 :=
  match encoding.val with
  | 0 => (5, 13)
  | 1 => (3, 14)
  | 2 => (5, 6)
  | 3 => (3, 13)
  | 4 => (12, 5)
  | _ => (14, 13)

def effectAt (p : BitVec 64) (encoding : Fin 6) (s : RamState) : Effect :=
  let rest := (registersAt encoding).1
  let source := (registersAt encoding).2
  let count := (Operand.reg rest : Operand 64).read s
  { rip := p + BitVec.ofNat 64 (bytesAt encoding).length
    writes := [⟨(.reg 0 : Operand 64), 0x7fffffffffffff80 &&& count⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffff80⟩,
      ⟨(.reg rest : Operand 64), ((count).setWidth 32 &&& 127).setWidth 64⟩,
      ⟨(.reg source : Operand 64), (Operand.reg source : Operand 64).read s + (0x7fffffffffffff80 &&& count)⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

macro "tail_register_steps" p:term:max away:term:max mr:term:max mm:term:max astep:term:max ar:term:max aa:term:max last:term:max total:term:max : tactic => `(tactic| (
  advance_begin (mov_r64_r64_effect_step $p $mr $mm (by simp [RexWPrefix]) rfl)
  case «next» => exact fun _ _ => $away 3 (by omega)
  advance_then (mov_r64_imm64_effect_step ($p + 3) 0x48 0xb9 (by simp [RexWPrefix]) (by decide) 0x7fffffffffffff80)
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    x86_norm
    exact $away 13 (by omega)
  advance_then (and_r64_r64_effect_step ($p + 13) 0x48 0xc8 (by simp [RexWPrefix]) rfl)
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    x86_norm
    exact $away 16 (by omega)
  advance_then $astep
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    x86_norm
    exact $away $last (by omega)
  advance_then (add_r64_r64_effect_step ($p + $last) $ar $aa (by simp [RexWPrefix]) rfl)
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    x86_norm
    exact $away $total (by omega)
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effectAt, registersAt, bytesAt, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, BitVec.and_comm]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [effectAt, registersAt, bytesAt, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, BitVec.and_comm]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; cases i <;> exact Or.inl rfl
  · x86_norm [effectAt, registersAt, bytesAt]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem run_at [Bindings] (p : BitVec 64) (encoding : Fin 6) (boundary : ReturnBoundary)
    (away : ∀ n : Nat, n ≤ 23 → p + BitVec.ofNat 64 n ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (bytesAt encoding)) (Effect.post (effectAt p encoding)) := by
  have cases : encoding = 0 ∨ encoding = 1 ∨ encoding = 2 ∨ encoding = 3 ∨ encoding = 4 ∨ encoding = 5 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  · tail_register_steps p away 0x48 0xe8 (and_r32_imm8_effect_step (p + 16) 0xe5 127 rfl rfl) 0x49 0xc5 19 22
  · tail_register_steps p away 0x48 0xd8 (and_r32_imm8_effect_step (p + 16) 0xe3 127 rfl rfl) 0x49 0xc6 19 22
  · tail_register_steps p away 0x48 0xe8 (and_r32_imm8_effect_step (p + 16) 0xe5 127 rfl rfl) 0x48 0xc6 19 22
  · tail_register_steps p away 0x48 0xd8 (and_r32_imm8_effect_step (p + 16) 0xe3 127 rfl rfl) 0x49 0xc5 19 22
  · tail_register_steps p away 0x4c 0xe0 (and_r32_imm8_rex_effect_step (p + 16) 0x41 0xe4 127 (by simp [RexNoWPrefix]) rfl rfl) 0x48 0xc5 20 23
  · tail_register_steps p away 0x4c 0xf0 (and_r32_imm8_rex_effect_step (p + 16) 0x41 0xe6 127 (by simp [RexNoWPrefix]) rfl rfl) 0x49 0xc5 20 23

def bytes : List UInt8 :=
  [0x48,0x89,0xe8,0x48,0xb9,0x80,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,
   0x48,0x21,0xc8,0x83,0xe5,0x7f,0x49,0x01,0xc5]

def effect (variant : Variant) (s : RamState) : Effect :=
  { rip := (variant.pc 0x1e0)
    writes := [⟨(.reg 0 : Operand 64), 0x7fffffffffffff80 &&& s.regValue .rbp⟩,
      ⟨(.reg 1 : Operand 64), 0x7fffffffffffff80⟩,
      ⟨(.reg 5 : Operand 64), ((s.regValue .rbp).setWidth 32 &&& 127).setWidth 64⟩,
      ⟨(.reg 13 : Operand 64), s.regValue .r13 + (0x7fffffffffffff80 &&& s.regValue .rbp)⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {variant : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (variant.pc 0x1ca) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (variant.textOffset + 0x1ca) bytes
    (by cases variant <;> decide +kernel) (by cases variant <;> decide +kernel)

theorem run [Bindings] {variant : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (variant.pc 0x1ca))
      (codeRange (variant.pc 0x1ca) bytes) (Effect.post (effect variant)) := by
  have same : effect variant = effectAt (variant.pc 0x1ca) 0 := by
    funext s
    simp only [effect, effectAt, registersAt, bytesAt]
    rw [Variant.pc_add]
    rfl
  rw [same]
  exact run_at (variant.pc 0x1ca) 0 boundary (by
    intro n hn
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram variant (by omega)))

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.TailRegisters

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512

def tailRegisterEncoding (form : Form) : Fin 6 :=
  match form with
  | .slices | .digest => 0
  | .reset stage => if stage.val = 0 then 1 else 2
  | .finalizeIntoReset second => if second then 2 else 3
  | .traitFinalizeIntoReset second => if second then 5 else 4


theorem tailRegister_bytes (v : Variant) (form : Form) (hd : form ≠ .digest) :
    Extracted.textBytes.toListFrom (v.textOffset form + tailOffset v form)
      (TailRegisters.bytesAt (tailRegisterEncoding form)).length =
      TailRegisters.bytesAt (tailRegisterEncoding form) := by
  cases form with
  | slices => cases v <;> decide +kernel
  | digest => contradiction
  | reset stage =>
    have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals cases v <;> decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> cases v <;> decide +kernel


theorem tailRegister_bounds (v : Variant) (form : Form) :
    v.textOffset form + tailOffset v form + 23 < 71757 := by
  cases form with
  | slices | digest => cases v <;> decide +kernel
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    revert second; cases v <;> decide +kernel


theorem tailRegister_code {v : Variant} {form : Form} {s : RamState}
    (loaded : ProgramLoaded s) (hd : form ≠ .digest) :
    CodeIn (codeRange (v.pc (tailOffset v form) form)
      (TailRegisters.bytesAt (tailRegisterEncoding form))) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + tailOffset v form)
  · have bound := tailRegister_bounds v form
    have size : (TailRegisters.bytesAt (tailRegisterEncoding form)).length ≤ 23 := by
      generalize tailRegisterEncoding form = e
      revert e
      decide +kernel
    omega
  · exact tailRegister_bytes v form hd


theorem tailRegister_effect (v : Variant) (form : Form) (p : BitVec 64) (s : RamState) :
    TailRegisters.effectAt p (tailRegisterEncoding form) s =
    { rip := p + BitVec.ofNat 64 (TailRegisters.bytesAt (tailRegisterEncoding form)).length
      writes := [⟨(.reg 0 : Operand 64), 0x7fffffffffffff80 &&& (.reg (v.restRegister form) : Operand 64).read s⟩,
        ⟨(.reg 1 : Operand 64), 0x7fffffffffffff80⟩,
        ⟨(.reg (v.restRegister form) : Operand 64),
          (((.reg (v.restRegister form) : Operand 64).read s).setWidth 32 &&& 127).setWidth 64⟩,
        ⟨(.reg (BitVec.ofNat 5 (v.traversal form).dataReg) : Operand 64),
          v.sourceValue form s + (0x7fffffffffffff80 &&& (.reg (v.restRegister form) : Operand 64).read s)⟩]
      flags := some ⟨none,none,none,none,none,none⟩ } := by
  cases form with
  | slices | digest => cases v <;> rfl
  | reset stage =>
    have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals cases v <;> rfl
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> cases v <;> rfl


theorem tailRegister_keeps_rsp (v : Variant) (form : Form) :
    v.restRegister form ≠ 4 ∧ BitVec.ofNat 5 (v.traversal form).dataReg ≠ 4 := by
  cases form with
  | slices | digest => cases v <;> decide +kernel
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    revert second; cases v <;> decide +kernel

theorem tail_register_end (v : Variant) (form : Form) (hd : form ≠ .digest) :
    v.pc (tailOffset v form) form +
      BitVec.ofNat 64 (TailRegisters.bytesAt (tailRegisterEncoding form)).length =
      Absorb.lengthPC v true form := by
  cases v <;> cases form with
  | slices => decide +kernel
  | digest => contradiction
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel


end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
