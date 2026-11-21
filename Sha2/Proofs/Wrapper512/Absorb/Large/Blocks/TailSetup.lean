import Sha2.Proofs.Wrapper512.Absorb.Copy
import Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.State
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
import X86Proofs.Instructions.Add.Generated.Imm32.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.TailSetup

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def bytesAt (encoding : Fin 8) : List UInt8 :=
  match encoding.val with
  | 0 => [0x48,0x8d,0xbc,0x24,0xf0,0x0,0x0,0x0,0x4c,0x89,0xee,0x48,0x89,0xea]
  | 1 => [0x48,0x89,0xe7,0x4c,0x89,0xf6,0x48,0x89,0xda]
  | 2 => [0x48,0x89,0xdf,0x48,0x89,0xea]
  | 3 => [0x48,0x89,0xe7,0x48,0x89,0xea]
  | 4 => [0x48,0x8d,0x7c,0x24,0x10,0x4c,0x89,0xee,0x48,0x89,0xda]
  | 5 => [0x48,0x8d,0x7c,0x24,0x10,0x48,0x89,0xea]
  | 6 => [0x48,0x89,0xdf,0x48,0x89,0xee,0x4c,0x89,0xe2]
  | _ => [0x48,0x89,0xdf,0x4c,0x89,0xee,0x4c,0x89,0xf2]

def effectAt (p : BitVec 64) (encoding : Fin 8) (s : RamState) : Effect :=
  match encoding.val with
  | 0 =>
    { rip := p + 14
      writes := [⟨(.reg 7 : Operand 64), rspOf s + 240⟩,
        ⟨(.reg 6 : Operand 64), (.reg 13 : Operand 64).read s⟩,
        ⟨(.reg 2 : Operand 64), (.reg 5 : Operand 64).read s⟩] }
  | 1 =>
    { rip := p + 9
      writes := [⟨(.reg 7 : Operand 64), rspOf s⟩,
        ⟨(.reg 6 : Operand 64), (.reg 14 : Operand 64).read s⟩,
        ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s⟩] }
  | 2 =>
    { rip := p + 6
      writes := [⟨(.reg 7 : Operand 64), s.regValue .rbx⟩,
        ⟨(.reg 2 : Operand 64), (.reg 5 : Operand 64).read s⟩] }
  | 3 =>
    { rip := p + 6
      writes := [⟨(.reg 7 : Operand 64), rspOf s⟩,
        ⟨(.reg 2 : Operand 64), (.reg 5 : Operand 64).read s⟩] }
  | 4 =>
    { rip := p + 11
      writes := [⟨(.reg 7 : Operand 64), rspOf s + 16⟩,
        ⟨(.reg 6 : Operand 64), (.reg 13 : Operand 64).read s⟩,
        ⟨(.reg 2 : Operand 64), (.reg 3 : Operand 64).read s⟩] }
  | 5 =>
    { rip := p + 8
      writes := [⟨(.reg 7 : Operand 64), rspOf s + 16⟩,
        ⟨(.reg 2 : Operand 64), (.reg 5 : Operand 64).read s⟩] }
  | 6 =>
    { rip := p + 9
      writes := [⟨(.reg 7 : Operand 64), s.regValue .rbx⟩,
        ⟨(.reg 6 : Operand 64), (.reg 5 : Operand 64).read s⟩,
        ⟨(.reg 2 : Operand 64), (.reg 12 : Operand 64).read s⟩] }
  | _ =>
    { rip := p + 9
      writes := [⟨(.reg 7 : Operand 64), s.regValue .rbx⟩,
        ⟨(.reg 6 : Operand 64), (.reg 13 : Operand 64).read s⟩,
        ⟨(.reg 2 : Operand 64), (.reg 14 : Operand 64).read s⟩] }

macro "tail_setup_steps" _p:term:max value:term:max away:term:max firstStep:term:max firstLen:term:max
    "[" middle:tacticSeq "]" lastStep:term:max total:term:max : tactic => `(tactic| (
  advance_begin $firstStep
  case «next» => exact fun _ _ => $away $firstLen (by omega)
  ($middle)
  advance_then $lastStep
  case mid =>
    intro s t hp hh ho
    refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
    x86_norm
    exact $away $total (by omega)
  have valueEq := $value
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effectAt, valueEq, BitVec.add_zero]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · x86_norm [effectAt, valueEq, BitVec.add_zero]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]
  · intro i; exact Or.inr rfl
  · x86_norm [effectAt, valueEq]
    all_goals solve_by_elim (maxDepth := 30) only [And.intro, Or.inl, Or.inr, Eq.refl]))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem run_at [Bindings] (p : BitVec 64) (encoding : Fin 8) (boundary : ReturnBoundary)
    (away : ∀ n : Nat, n ≤ 14 → p + BitVec.ofNat 64 n ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (bytesAt encoding)) (Effect.post (effectAt p encoding)) := by
  have cases : encoding = 0 ∨ encoding = 1 ∨ encoding = 2 ∨ encoding = 3 ∨
      encoding = 4 ∨ encoding = 5 ∨ encoding = 6 ∨ encoding = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · tail_setup_steps p (show (0 : Fin 8).val = 0 from rfl) away (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d32 240)) (by decide +kernel) rfl rfl) 8 [
      advance_then (mov_r64_r64_effect_step (p + 8) 0x4c 0xee (by simp [RexWPrefix]) rfl)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact away 11 (by omega)
    ] (mov_r64_r64_effect_step (p + 11) 0x48 0xea (by simp [RexWPrefix]) rfl) 14
  · tail_setup_steps p (show (1 : Fin 8).val = 1 from rfl) away (mov_r64_r64_effect_step p 0x48 0xe7 (by simp [RexWPrefix]) rfl) 3 [
      advance_then (mov_r64_r64_effect_step (p + 3) 0x4c 0xf6 (by simp [RexWPrefix]) rfl)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact away 6 (by omega)
    ] (mov_r64_r64_effect_step (p + 6) 0x48 0xda (by simp [RexWPrefix]) rfl) 9
  · tail_setup_steps p (show (2 : Fin 8).val = 2 from rfl) away (mov_r64_r64_effect_step p 0x48 0xdf (by simp [RexWPrefix]) rfl) 3 [
      skip
    ] (mov_r64_r64_effect_step (p + 3) 0x48 0xea (by simp [RexWPrefix]) rfl) 6
  · tail_setup_steps p (show (3 : Fin 8).val = 3 from rfl) away (mov_r64_r64_effect_step p 0x48 0xe7 (by simp [RexWPrefix]) rfl) 3 [
      skip
    ] (mov_r64_r64_effect_step (p + 3) 0x48 0xea (by simp [RexWPrefix]) rfl) 6
  · tail_setup_steps p (show (4 : Fin 8).val = 4 from rfl) away (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl) 5 [
      advance_then (mov_r64_r64_effect_step (p + 5) 0x4c 0xee (by simp [RexWPrefix]) rfl)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact away 8 (by omega)
    ] (mov_r64_r64_effect_step (p + 8) 0x48 0xda (by simp [RexWPrefix]) rfl) 11
  · tail_setup_steps p (show (5 : Fin 8).val = 5 from rfl) away (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 7 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl) 5 [
      skip
    ] (mov_r64_r64_effect_step (p + 5) 0x48 0xea (by simp [RexWPrefix]) rfl) 8
  · tail_setup_steps p (show (6 : Fin 8).val = 6 from rfl) away (mov_r64_r64_effect_step p 0x48 0xdf (by simp [RexWPrefix]) rfl) 3 [
      advance_then (mov_r64_r64_effect_step (p + 3) 0x48 0xee (by simp [RexWPrefix]) rfl)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact away 6 (by omega)
    ] (mov_r64_r64_effect_step (p + 6) 0x4c 0xe2 (by simp [RexWPrefix]) rfl) 9
  · tail_setup_steps p (show (7 : Fin 8).val = 7 from rfl) away (mov_r64_r64_effect_step p 0x48 0xdf (by simp [RexWPrefix]) rfl) 3 [
      advance_then (mov_r64_r64_effect_step (p + 3) 0x4c 0xee (by simp [RexWPrefix]) rfl)
      case mid =>
        intro s t hp hh ho
        refine ⟨hh.rip_of (by x86_norm), Effect.Avoids.of_noMem (by simp [Component.Covers]) _, ?_⟩
        x86_norm
        exact away 6 (by omega)
    ] (mov_r64_r64_effect_step (p + 6) 0x4c 0xf2 (by simp [RexWPrefix]) rfl) 9

def targetBytes (second : Bool) (displacement : BitVec 32) : List UInt8 :=
  [if second then 0x48 else 0x4c, 0x8d, 0x2d] ++ immBytes 32 displacement

def targetEffect (p : BitVec 64) (second : Bool) (displacement : BitVec 32)
    (_s : RamState) : Effect :=
  { rip := p + 7
    writes := [⟨(.reg (if second then 5 else 13) : Operand 64),
      p + 7 + displacement.signExtend 64⟩] }

theorem target_run [Bindings] (p : BitVec 64) (second : Bool) (displacement : BitVec 32)
    (boundary : ReturnBoundary) (away : p + 7 ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = p)
      (codeRange p (targetBytes second displacement))
      (Effect.post (targetEffect p second displacement)) := by
  have modrm : (AddrMode.rip displacement).modrm 5 = 0x2d := by
    change UInt8.ofBitVec (0#2 ++ 5#3 ++ 5#3) = 0x2d
    decide +kernel
  cases second
  · advance_begin (lea_r64_effect_step p 0x4c (by simp [RexWPrefix]) 5
      (.rip displacement) (by trivial) rfl rfl)
    case sub =>
      intro a h
      simpa only [targetBytes, Bool.false_eq_true, ↓reduceIte, modrm, AddrMode.tail, List.cons_append, List.nil_append] using h
    advance_finish [targetEffect]
  · advance_begin (lea_r64_effect_step p 0x48 (by simp [RexWPrefix]) 5
      (.rip displacement) (by trivial) rfl rfl)
    case sub =>
      intro a h
      simpa only [targetBytes, Bool.false_eq_true, ↓reduceIte, modrm, AddrMode.tail, List.cons_append, List.nil_append] using h
    advance_finish [targetEffect]

def bytes : List UInt8 :=
  [0x48,0x8d,0xbc,0x24,0xf0,0x0,0x0,0x0,0x4c,0x89,0xee,0x48,0x89,0xea]

def effect (variant : Variant) (s : RamState) : Effect :=
  { rip := (variant.pc 0x1f6)
    writes := [⟨(.reg 7 : Operand 64), rspOf s + 240⟩,
      ⟨(.reg 6 : Operand 64), s.regValue .r13⟩,
      ⟨(.reg 2 : Operand 64), s.regValue .rbp⟩] }

theorem code {variant : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (variant.pc 0x1e8) bytes) s :=
  programText_slice (programLoaded_codeIn loaded) (variant.textOffset + 0x1e8) bytes
    (by cases variant <;> decide +kernel) (by cases variant <;> decide +kernel)

theorem run [Bindings] {variant : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (variant.pc 0x1e8))
      (codeRange (variant.pc 0x1e8) bytes) (Effect.post (effect variant)) := by
  have same : effect variant = effectAt (variant.pc 0x1e8) 0 := by
    funext s
    dsimp only [effect, effectAt]
    change { rip := variant.pc 0x1f6, writes := _ : Effect } =
      { rip := variant.pc 0x1e8 + BitVec.ofNat 64 14, writes := _ : Effect }
    rw [Variant.pc_add]
    rfl
  rw [same]
  exact run_at (variant.pc 0x1e8) 0 boundary (by
    intro n hn
    rw [Variant.pc_add]
    exact boundary_ne_program outside (Variant.pc_inProgram variant (by omega)))

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks.TailSetup

namespace Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512

def tailSetupEncoding (form : Form) : Fin 8 :=
  match form with
  | .slices | .digest => 0
  | .reset stage => if stage.val = 0 then 1 else if stage.val = 1 then 2 else 3
  | .finalizeIntoReset second => if second then 5 else 4
  | .traitFinalizeIntoReset second => if second then 7 else 6


def tailSetupOffset (v : Variant) (form : Form) : Nat :=
  Copy.Site.tail.relativeOffset form v -
    (match form with | .traitFinalizeIntoReset _ => 7 | _ => 0) -
    (TailSetup.bytesAt (tailSetupEncoding form)).length


theorem tailSetup_bytes (v : Variant) (form : Form) (hd : form ≠ .digest) :
    Extracted.textBytes.toListFrom (v.textOffset form + tailSetupOffset v form)
      (TailSetup.bytesAt (tailSetupEncoding form)).length =
      TailSetup.bytesAt (tailSetupEncoding form) := by
  cases form with
  | slices => cases v <;> decide +kernel
  | digest => contradiction
  | reset stage =>
    have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals cases v <;> decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    cases second <;> cases v <;> decide +kernel



theorem tailSetup_bounds (v : Variant) (form : Form) :
    v.textOffset form + tailSetupOffset v form + 14 < 71757 := by
  cases form with
  | slices | digest => cases v <;> decide +kernel
  | reset stage => revert stage; cases v <;> decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second =>
    revert second; cases v <;> decide +kernel


theorem tailSetup_code {v : Variant} {form : Form} {s : RamState}
    (loaded : ProgramLoaded s) (hd : form ≠ .digest) :
    CodeIn (codeRange (v.pc (tailSetupOffset v form) form)
      (TailSetup.bytesAt (tailSetupEncoding form))) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset form + tailSetupOffset v form)
  · have bound := tailSetup_bounds v form
    have size : (TailSetup.bytesAt (tailSetupEncoding form)).length ≤ 14 := by
      generalize tailSetupEncoding form = e
      revert e
      decide +kernel
    omega
  · exact tailSetup_bytes v form hd


theorem tailSetup_frame {p : BitVec 64} {e : Fin 8} {s t : RamState}
    (h : (TailSetup.effectAt p e s).Holds s t) :
    AgreesExcept [.rip, .reg 2, .reg 6, .reg 7] s t := by
  apply h.agrees.mono
  rcases e with ⟨value, bound⟩
  have cases : value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 3 ∨ value = 4 ∨ value = 5 ∨ value = 6 ∨ value = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [TailSetup.effectAt, Effect.components]


def tailSetupTargetRegister (form : Form) : BitVec 5 :=
  match form with
  | .traitFinalizeIntoReset second => if second then 5 else 13
  | _ => 2


def tailSetupComponents (form : Form) : List Component :=
  [.rip, .reg 2, .reg 6, .reg 7, .reg (tailSetupTargetRegister form)]


theorem tailSetup_arguments {v : Variant} {form : Form} {p : BitVec 64} {initial s t : RamState}
    (h : (TailSetup.effectAt p (tailSetupEncoding form) s).Holds s t)
    (hd : form ≠ .digest)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes)
    (buffer : form = .reset 1 → s.regValue .rbx = bufferPointer initial form)
    (active : ∀ second, form = .traitFinalizeIntoReset second →
      s.regValue .rbx = bufferPointer initial form form.activeMemory) :
    t.regValue .rdi = bufferPointer initial form form.activeMemory ∧
    t.regValue .rsi = v.sourceValue form s ∧
    t.regValue .rdx = (.reg (v.restRegister form) : Operand 64).read s := by
  have source : t.regValue .rsi = v.sourceValue form s := by
    cases form with
    | digest => contradiction
    | slices => cases v <;> exact h.writes.2.1
    | reset stage =>
      have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      rcases cases with rfl | rfl | rfl
      all_goals cases v
      all_goals first
      | exact h.writes.2.1
      | exact h.agrees.read (n := 64) (r := 6) (by change Component.reg 6 ∉ [.reg 7, .reg 2, .rip]; decide)
    | finalizeIntoReset second | traitFinalizeIntoReset second =>
      cases second <;> cases v
      all_goals first
      | exact h.writes.2.1
      | exact h.agrees.read (n := 64) (r := 6) (by change Component.reg 6 ∉ [.reg 7, .reg 2, .rip]; decide)
  have length : t.regValue .rdx = (.reg (v.restRegister form) : Operand 64).read s := by
    cases form with
    | digest => contradiction
    | slices => cases v <;> exact h.writes.2.2
    | reset stage =>
      have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      rcases cases with rfl | rfl | rfl
      all_goals cases v
      all_goals first | exact h.writes.2.2 | exact h.writes.2
    | finalizeIntoReset second | traitFinalizeIntoReset second =>
      cases second <;> cases v
      all_goals first | exact h.writes.2.2 | exact h.writes.2
  refine ⟨?_, source, length⟩
  cases form with
  | digest => contradiction
  | slices =>
    have value : t.regValue .rdi = stackPtr s + 240 := h.writes.1
    rw [value, rsp]
    simp only [bufferPointer, Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  | reset stage =>
    have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    rcases cases with rfl | rfl | rfl
    · exact h.writes.1.trans rsp
    · exact h.writes.1.trans (buffer rfl)
    · exact h.writes.1.trans rsp
  | finalizeIntoReset second =>
    have value : t.regValue .rdi = stackPtr s + 16 := by cases second <;> exact h.writes.1
    rw [value, rsp]
    simp only [bufferPointer, Form.activeMemory, Form.bufferedMemory, ResetLayout.finalizeMemory,
      Form.frameBytes, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  | traitFinalizeIntoReset second =>
    have value : t.regValue .rdi = s.regValue .rbx := by cases second <;> exact h.writes.1
    exact value.trans (active second rfl)




theorem tail_length_end (v : Variant) (form : Form) (hd : form ≠ .digest) :
    Absorb.lengthPC v true form + BitVec.ofNat 64 (Absorb.lengthSize true form) =
      v.pc (tailSetupOffset v form) form := by
  cases v <;> cases form with
  | slices => decide +kernel
  | digest => contradiction
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel

theorem tailSetup_rip {p : BitVec 64} {e : Fin 8} {s t : RamState}
    (h : (TailSetup.effectAt p e s).Holds s t) :
    t.RIP = p + BitVec.ofNat 64 (TailSetup.bytesAt e).length := by
  have cases : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact h.rip

def tailTargetDisplacement (v : Variant) (second : Bool) : BitVec 32 :=
  BitVec.ofNat 32 (0xdd60 - (v.textOffset (.traitFinalizeIntoReset second) +
    tailSetupOffset v (.traitFinalizeIntoReset second) + 16))

theorem tailSetup_nontrait_end (v : Variant) (form : Form)
    (hd : form ≠ .digest) (hf : form ≠ .traitFinalizeIntoReset false)
    (ht : form ≠ .traitFinalizeIntoReset true) :
    v.pc (tailSetupOffset v form) form +
      BitVec.ofNat 64 (TailSetup.bytesAt (tailSetupEncoding form)).length =
      v.pc (Copy.Site.tail.relativeOffset form v) form := by
  cases v <;> cases form with
  | slices => decide +kernel
  | digest => contradiction
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second => revert second; decide +kernel
  | traitFinalizeIntoReset second => cases second <;> contradiction

theorem tailSetup_target_registers (v : Variant) (form : Form) (r : BitVec 5)
    (h : Copy.Site.tail.register v form = some r) : r ≠ 2 ∧ r ≠ 6 ∧ r ≠ 7 := by
  cases form with
  | slices | digest => simp [Copy.Site.register] at h
  | reset stage =>
    have cases : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    rcases cases with rfl | rfl | rfl
    all_goals simp [Copy.Site.register] at h
    subst r
    decide
  | finalizeIntoReset second =>
    cases second
    · simp [Copy.Site.register] at h
    · cases v <;> simp [Copy.Site.register] at h <;> subst r <;> decide
  | traitFinalizeIntoReset second => cases second <;> simp [Copy.Site.register] at h <;> subst r <;> decide

theorem tailTarget_code {v : Variant} {second : Bool} {s : RamState}
    (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (tailSetupOffset v (.traitFinalizeIntoReset second) + 9)
      (.traitFinalizeIntoReset second)) (TailSetup.targetBytes second (tailTargetDisplacement v second))) s := by
  apply programText_slice (programLoaded_codeIn loaded)
    (v.textOffset (.traitFinalizeIntoReset second) + (tailSetupOffset v (.traitFinalizeIntoReset second) + 9))
  · cases v <;> cases second <;> decide +kernel
  · cases v <;> cases second <;> decide +kernel

set_option maxHeartbeats 800000 in
theorem tail_setup [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} (ctx : Context v initial inputs form)
    (input : Preserved v initial s form)
    (rip : s.RIP = v.pc (tailSetupOffset v form) form) (hd : form ≠ .digest)
    (saved : form = .traitFinalizeIntoReset false →
      memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx)
    (buffer : form = .reset 1 → s.regValue .rbx = bufferPointer initial form)
    (active : ∀ second, form = .traitFinalizeIntoReset second →
      s.regValue .rbx = bufferPointer initial form form.activeMemory)
    (target : ∀ r, Copy.Site.tail.register v form = some r →
      form ≠ .traitFinalizeIntoReset false → form ≠ .traitFinalizeIntoReset true →
      (Operand.reg r : Operand 64).read s = 0x10dd60) :
    ∃ t, Preserved v initial t form ∧
      t.RIP = v.pc (Copy.Site.tail.relativeOffset form v) form ∧
      t.regValue .rdi = bufferPointer initial form form.activeMemory ∧
      t.regValue .rsi = v.sourceValue form s ∧
      t.regValue .rdx = (Operand.reg (v.restRegister form) : Operand 64).read s ∧
      (∀ r, Copy.Site.tail.register v form = some r →
        (Operand.reg r : Operand 64).read t = 0x10dd60) ∧
      AgreesExcept (tailSetupComponents form) s t ∧
      (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      MemoryWriteFrame s t #v[Stack.region initial (v.routine form).minStackBytes] := by
  have outside := (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
  obtain ⟨fuel,u,run,ready,_,effect⟩ := TailSetup.run_at
    (v.pc (tailSetupOffset v form) form) (tailSetupEncoding form) (returnBoundary initial)
    (by
      intro n hn
      rw [Variant.pc_add v _ _ form]
      apply boundary_ne_program outside
      apply inProgram_of_textOffset
      have := tailSetup_bounds v form
      omega) s (supportedMachine_readyToStep input.machine) (tailSetup_code input.loaded hd) rip
  have frame := tailSetup_frame effect
  have preserved := preserved_of_agrees ctx input run ready frame
    (by simp [LocalWrites, Component.Covers]) (by simp) (by simp)
    (by intro h; exact (hd h).elim) (fun h => .inr (saved h))
  have args := tailSetup_arguments (v := v) effect hd input.rsp buffer active
  have ripU := tailSetup_rip effect
  by_cases trait : ∃ second, form = .traitFinalizeIntoReset second
  · obtain ⟨second,rfl⟩ := trait
    have ripTarget : u.RIP = v.pc (tailSetupOffset v (.traitFinalizeIntoReset second) + 9)
        (.traitFinalizeIntoReset second) := by
      rw [ripU]
      cases second <;> exact Variant.pc_add v _ 9 _
    obtain ⟨fuelT,t,runT,readyT,_,effectT⟩ := TailSetup.target_run
      (v.pc (tailSetupOffset v (.traitFinalizeIntoReset second) + 9) (.traitFinalizeIntoReset second))
      second (tailTargetDisplacement v second) (returnBoundary initial)
      (by
        apply boundary_ne_program outside
        have nextEq :
            v.pc (tailSetupOffset v (.traitFinalizeIntoReset second) + 9) (.traitFinalizeIntoReset second) + (7 : BitVec 64) =
            v.pc (tailSetupOffset v (.traitFinalizeIntoReset second) + 16) (.traitFinalizeIntoReset second) := by
          cases v <;> cases second <;> decide +kernel
        rw [nextEq]
        apply inProgram_of_textOffset
        cases v <;> cases second <;> decide +kernel)
      u ready (tailTarget_code preserved.loaded) ripTarget
    have frameT : AgreesExcept [.rip, .reg (if second then 5 else 13)] u t := by
      exact effectT.agrees.mono (by simp [TailSetup.targetEffect, Effect.components])
    have memoryU : u.external = s.external := frame.external (by simp [Component.Covers])
    have preservedT := preserved_of_agrees ctx preserved runT readyT frameT
      (by simp [LocalWrites, Component.Covers])
      (by cases second <;> simp) (by simp)
      (by intro h; contradiction)
      (fun h => .inr (by rw [memoryU]; exact saved h))
    have targetValue :
        v.pc (tailSetupOffset v (.traitFinalizeIntoReset second) + 9) (.traitFinalizeIntoReset second) + 7 +
          (tailTargetDisplacement v second).signExtend 64 = 0x10dd60 := by
      cases v <;> cases second <;> decide +kernel
    have targetRip : t.RIP = v.pc (Copy.Site.tail.relativeOffset (.traitFinalizeIntoReset second) v)
        (.traitFinalizeIntoReset second) := by
      rw [effectT.rip]
      change v.pc (tailSetupOffset v (.traitFinalizeIntoReset second) + 9) (.traitFinalizeIntoReset second) + 7 = _
      cases v <;> cases second <;> decide +kernel
    refine ⟨t,preservedT,targetRip,?_,?_,?_,?_,?_,⟨_,run.trans runT⟩,?_⟩
    · exact (frameT.read (n := 64) (r := 7) (by cases second <;> simp)).trans args.1
    · exact (frameT.read (n := 64) (r := 6) (by cases second <;> simp)).trans args.2.1
    · exact (frameT.read (n := 64) (r := 2) (by cases second <;> simp)).trans args.2.2
    · intro r hr
      have value := effectT.writes
      change (Operand.reg (if second then 5 else 13) : Operand 64).read t = _ at value
      rw [targetValue] at value
      cases second <;> simp only [Copy.Site.register, Option.some.injEq] at hr
      all_goals subst r
      all_goals exact value
    · exact (frame.trans frameT).mono (by
        cases second <;> simp [tailSetupComponents, tailSetupTargetRegister])
    · intro a ha
      rw [frameT.external (by simp [Component.Covers]), memoryU]
  · have hf : form ≠ .traitFinalizeIntoReset false := fun h => trait ⟨false,h⟩
    have ht : form ≠ .traitFinalizeIntoReset true := fun h => trait ⟨true,h⟩
    refine ⟨u,preserved,ripU.trans (tailSetup_nontrait_end v form hd hf ht),
      args.1,args.2.1,args.2.2,?_,?_,⟨_,run⟩,?_⟩
    · intro r hr
      have kept := tailSetup_target_registers v form r hr
      exact (frame.read (n := 64) (r := r) (by
        intro member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with impossible | h | h | h
        · cases impossible
        · exact kept.1 (Component.reg.inj h)
        · exact kept.2.1 (Component.reg.inj h)
        · exact kept.2.2 (Component.reg.inj h))).trans
        (target r hr hf ht)
    · exact frame.mono (by simp [tailSetupComponents])
    · intro a ha
      rw [frame.external (by simp [Component.Covers])]

end Sha2.Proofs.Wrapper512.Absorb.Large.Blocks
