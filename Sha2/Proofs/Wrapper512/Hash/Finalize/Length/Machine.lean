import Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Shld
import Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Movzx
import Sha2.Proofs.Wrapper.Hash.Padding.Length
import Sha2.Proofs.Wrapper512.Hash.Finalize.State
import Sha2.Proofs.Common.Instructions.ShiftLeft.Word32Rex

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Machine

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions
open Sha2.Proofs.Common.Instructions.Or (orR64R64Effect or_r64_r64_effect_step)
open Sha2.Proofs.Common.Instructions.ShiftLeft

attribute [local x86_compose] shlR32Effect shlR64Effect encodeBswapR64 Shld.effect Movzx.movzxEaxR13bEffect
attribute [local x86_local] Sha2.Proofs.Wrapper.Hash.Padding.Length.shift64_local
  Sha2.Proofs.Wrapper.Hash.Padding.Length.shift32_local

@[local x86_local] theorem shld_local (p : BitVec 64) (dst src : BitVec 5) :
    Effect.Local (Shld.effect p dst src) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Shld.effect, h.read_reg]
  · intro s
    simp [Shld.effect, Write.Full, Operand.Full]

@[local x86_local] theorem movzx_local (p : BitVec 64) (form : Form := .slices) :
    Effect.Local (Movzx.movzxEaxR13bEffect p form) := by
  apply Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [Movzx.movzxEaxR13bEffect, h.read_reg]
  · intro s
    simp [Movzx.movzxEaxR13bEffect, Write.Full, Operand.Full]

abbrev reg (r : Syntax.Reg) : BitVec 5 := BitVec.ofNat 5 r.fin.val

abbrev bytes (form : Form := .slices) (v : Variant := .sha384) : List UInt8 :=
  let high := (highCountRegister v form).fin.val
  let count := (lowCountRegister v form).fin.val
  let low := (lowLengthRegister v form).fin.val
  (if countsShifted form then [] else
    [0x4d,0x0f,0xa4,UInt8.ofNat (0xc0 + (count % 8)*8 + high%8),0x0a,
     0x49,0xc1,UInt8.ofNat (0xe0 + count%8),0x0a,
     (if form = .digest then 0x40 else 0x41),0x0f,0xb6,0xc5]) ++
  (if low < 8 then [] else [0x41]) ++
  [0xc1,UInt8.ofNat (0xe0 + low%8),3,
   (if low < 8 then 0x4c else 0x4d),0x09,UInt8.ofNat (0xc0 + (count%8)*8 + low%8),
   (if low < 8 then 0x48 else 0x49),0x0f,UInt8.ofNat (0xc8 + low%8),
   0x49,0x0f,UInt8.ofNat (0xc8 + high%8)]

def effect (v : Variant) (form : Form := .slices) (s : RamState) : Effect :=
  { rip := v.pc (storeOffset v form) form
    writes := if countsShifted form then
      [⟨(.reg (reg (lowLengthRegister v form)) : Operand 64), bswap64
        ((((.reg (reg (lowLengthRegister v form)) : Operand 32).read s <<< 3).setWidth 64) |||
          (.reg (reg (lowCountRegister v form)) : Operand 64).read s)⟩,
       ⟨(.reg (reg (highCountRegister v form)) : Operand 64),
         bswap64 ((.reg (reg (highCountRegister v form)) : Operand 64).read s)⟩]
    else
      [⟨(.reg (reg (highCountRegister v form)) : Operand 64),
        bswap64 (Shld.result ((.reg (reg (highCountRegister v form)) : Operand 64).read s)
          ((.reg (reg (lowCountRegister v form)) : Operand 64).read s))⟩,
       ⟨(.reg (reg (lowCountRegister v form)) : Operand 64),
         (.reg (reg (lowCountRegister v form)) : Operand 64).read s <<< 10⟩,
       ⟨(.reg (reg (lowLengthRegister v form)) : Operand 64), bswap64
         (((((.reg (reg (tailRegister v form)) : Operand 64).read s).setWidth 8).setWidth 32 <<< 3).setWidth 64 |||
           ((.reg (reg (lowCountRegister v form)) : Operand 64).read s <<< 10))⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code_local {v : Variant} {form : Form} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc (lengthOffset v form) form) (bytes form v)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset form + lengthOffset v form) (bytes form v)
  all_goals
    cases form with
    | slices => cases v <;> decide +kernel
    | digest => cases v <;> decide +kernel
    | reset stage =>
      have h : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      rcases h with rfl | rfl | rfl <;> cases v <;> decide +kernel
    | finalizeIntoReset second => cases second <;> cases v <;> decide +kernel
    | traitFinalizeIntoReset second => cases second <;> cases v <;> decide +kernel

macro "length_step" v:term:max f:term:max b:term:max o:term:max start:num off:num len:num step:term:max firstStep:num : tactic => do
  let pc := Lean.quote (start.getNat + off.getNat)
  let next := Lean.quote (start.getNat + off.getNat + len.getNat)
  let begin ← if firstStep.getNat == 1 then `(tactic| advance_begin $step) else `(tactic| advance_then $step)
  let bridge ← if firstStep.getNat == 1 then `(tactic|
    case «next» =>
      intro _ _
      change ($v).pc $pc $f + BitVec.ofNat 64 $len ≠ ($b).rip
      rw [Variant.pc_add (form := $f)]
      exact boundary_ne_program $o (inProgram_of_textOffset (($v).textOffset $f + $next) (by decide +kernel)))
    else `(tactic|
    case mid =>
      intro s t hp hh ho
      refine ⟨hh.rip_of (by x86_norm [Variant.pc_add (form := $f)]), Effect.Avoids.of_noMem ?_ _, ?_⟩
      · simp [Effect.forgetFlags, shlR32Effect, shlR64Effect, Shld.effect,
          Movzx.movzxEaxR13bEffect, orR64R64Effect, bswapR64Effect,
          Effect.components, Write.component, Operand.component, Component.Covers]
      · change ($v).pc $pc $f + BitVec.ofNat 64 $len ≠ ($b).rip
        rw [Variant.pc_add (form := $f)]
        exact boundary_ne_program $o (inProgram_of_textOffset (($v).textOffset $f + $next) (by decide +kernel)))
  `(tactic|
    ($begin
     try case sub =>
       have hpc := Variant.pc_add $v $start $off $f
       simp only [Nat.reduceAdd] at hpc
       rw [← hpc]
       exact codeRange_slice_subset (($v).pc $start $f) (bytes $f $v) $off $len
     $bridge))

macro "length_execute" v:term:max f:term:max b:term:max o:term:max start:num high:num count:num low:num mode:num : tactic => do
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  let mut off := 0
  let mut first := true
  let add := fun (off len : Nat) (step : Lean.TSyntax `term) (first : Bool) => do
    let off := Lean.quote off
    let len := Lean.quote len
    let fst := Lean.quote (if first then 1 else 0)
    `(tactic| length_step $v $f $b $o $start $off $len $step $fst)
  if mode.getNat != 0 then
    let m := Lean.quote (0xc0 + count.getNat % 8 * 8 + high.getNat % 8)
    let pc := Lean.quote start.getNat
    let st ← `(show StepEffect _ _ (Shld.effect (($v).pc $pc $f) $high $count) from
      Shld.effect_step (($v).pc $pc $f) 0x4d $m (by simp [RexWPrefix]) (by rfl))
    steps := steps.push (← add off 5 st first)
    off := 5; first := false
    let pc := Lean.quote (start.getNat + off)
    let m := Lean.quote (0xe0 + count.getNat % 8)
    let st ← `(StepEffect.forgetFlags (h := (show StepEffect _ _ (shlR64Effect (($v).pc $pc $f) 4 $count 10) from
      shl_r64_imm8_effect_step (($v).pc $pc $f) 0x49 $m 10 (by simp [RexWPrefix]) rfl rfl)))
    steps := steps.push (← add off 4 st first)
    off := 9
    let pc := Lean.quote (start.getNat + off)
    let mf ← if mode.getNat == 2 then `(Form.digest) else `(Form.slices)
    let st ← `(Movzx.movzx_eax_r13b_effect_step (form := $mf) (($v).pc $pc $f))
    steps := steps.push (← add off 4 st first)
    off := 13
  let pc := Lean.quote (start.getNat + off)
  let m := Lean.quote (0xe0 + low.getNat % 8)
  let len := if low.getNat < 8 then 3 else 4
  let st ← if low.getNat < 8 then
      `(StepEffect.forgetFlags (h := (show StepEffect _ _ (shlR32Effect (($v).pc $pc $f) 3 $low 3) from
        shl_r32_imm8_effect_step (($v).pc $pc $f) $m 3 rfl rfl)))
    else
      `(StepEffect.forgetFlags (h := (show StepEffect _ _ (shlR32Effect (($v).pc $pc $f) 4 $low 3) from
        shl_r32_imm8_rex_effect_step (($v).pc $pc $f) 0x41 $m 3 (by simp [RexNoWPrefix]) rfl rfl)))
  steps := steps.push (← add off len st first)
  off := off + len
  let pc := Lean.quote (start.getNat + off)
  let rex := Lean.quote (if low.getNat < 8 then 0x4c else 0x4d)
  let m := Lean.quote (0xc0 + count.getNat % 8 * 8 + low.getNat % 8)
  let st ← `(StepEffect.forgetFlags (h := (show StepEffect _ _ (orR64R64Effect (($v).pc $pc $f) $low $count) from
    or_r64_r64_effect_step (($v).pc $pc $f) $rex $m (by simp [RexWPrefix]) rfl)))
  steps := steps.push (← add off 3 st false)
  off := off + 3
  for r in #[low, high] do
    let pc := Lean.quote (start.getNat + off)
    let st ← `(bswap_r64_effect_step (($v).pc $pc $f) $r)
    steps := steps.push (← add off 3 st false)
    off := off + 3
  `(tactic|
    ($steps:tactic*
     advance_finish [effect, countsShifted, lowLengthRegister, highCountRegister,
       lowCountRegister, tailRegister, reg, Syntax.Reg.fin, storeOffset, Variant.pc_add (form := $f),
       BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
       show BitVec.ofNat 5 (15 : Fin 16).val = 15 from rfl,
       show BitVec.ofNat 5 (12 : Fin 16).val = 12 from rfl,
       show BitVec.ofNat 5 (13 : Fin 16).val = 13 from rfl,
       show BitVec.ofNat 5 (14 : Fin 16).val = 14 from rfl,
       show BitVec.ofNat 5 (5 : Fin 16).val = 5 from rfl]
     all_goals simp only [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
     all_goals exact ⟨rfl, rfl, rfl⟩))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem run_slices [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (lengthOffset v Form.slices) Form.slices)
      (codeRange (v.pc (lengthOffset v Form.slices) Form.slices) (bytes Form.slices v)) (Effect.post (effect v Form.slices)) := by
  cases v
  · length_execute Variant.sha384 Form.slices boundary outside 810 15 12 0 1
  · length_execute Variant.sha512 Form.slices boundary outside 810 15 12 0 1
  · length_execute Variant.sha512_224 Form.slices boundary outside 810 15 12 0 1
  · length_execute Variant.sha512_256 Form.slices boundary outside 810 15 12 0 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem run_digest [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (lengthOffset v Form.digest) Form.digest)
      (codeRange (v.pc (lengthOffset v Form.digest) Form.digest) (bytes Form.digest v)) (Effect.post (effect v Form.digest)) := by
  cases v
  · length_execute Variant.sha384 Form.digest boundary outside 579 12 13 0 2
  · length_execute Variant.sha512 Form.digest boundary outside 579 12 13 0 2
  · length_execute Variant.sha512_224 Form.digest boundary outside 579 12 13 0 2
  · length_execute Variant.sha512_256 Form.digest boundary outside 579 12 13 0 2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem run_reset_zero [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (lengthOffset v (Form.reset 0)) (Form.reset 0))
      (codeRange (v.pc (lengthOffset v (Form.reset 0)) (Form.reset 0)) (bytes (Form.reset 0) v)) (Effect.post (effect v (Form.reset 0))) := by
  cases v
  · length_execute Variant.sha384 (Form.reset 0) boundary outside 1233 15 14 5 0
  · length_execute Variant.sha512 (Form.reset 0) boundary outside 1233 15 14 5 0
  · length_execute Variant.sha512_224 (Form.reset 0) boundary outside 1233 15 14 5 0
  · length_execute Variant.sha512_256 (Form.reset 0) boundary outside 1233 15 14 5 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem run_reset_one [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (lengthOffset v (Form.reset 1)) (Form.reset 1))
      (codeRange (v.pc (lengthOffset v (Form.reset 1)) (Form.reset 1)) (bytes (Form.reset 1) v)) (Effect.post (effect v (Form.reset 1))) := by
  cases v
  · length_execute Variant.sha384 (Form.reset 1) boundary outside 1233 15 14 5 0
  · length_execute Variant.sha512 (Form.reset 1) boundary outside 1233 15 14 5 0
  · length_execute Variant.sha512_224 (Form.reset 1) boundary outside 1233 15 14 5 0
  · length_execute Variant.sha512_256 (Form.reset 1) boundary outside 1233 15 14 5 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem run_reset_two [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (lengthOffset v (Form.reset 2)) (Form.reset 2))
      (codeRange (v.pc (lengthOffset v (Form.reset 2)) (Form.reset 2)) (bytes (Form.reset 2) v)) (Effect.post (effect v (Form.reset 2))) := by
  cases v
  · length_execute Variant.sha384 (Form.reset 2) boundary outside 2072 15 14 12 0
  · length_execute Variant.sha512 (Form.reset 2) boundary outside 2104 15 14 12 0
  · length_execute Variant.sha512_224 (Form.reset 2) boundary outside 2040 15 14 12 0
  · length_execute Variant.sha512_256 (Form.reset 2) boundary outside 2040 15 14 12 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem run_finalize_first [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (lengthOffset v (Form.finalizeIntoReset false)) (Form.finalizeIntoReset false))
      (codeRange (v.pc (lengthOffset v (Form.finalizeIntoReset false)) (Form.finalizeIntoReset false)) (bytes (Form.finalizeIntoReset false) v)) (Effect.post (effect v (Form.finalizeIntoReset false))) := by
  cases v
  · length_execute Variant.sha384 (Form.finalizeIntoReset false) boundary outside 776 15 14 13 0
  · length_execute Variant.sha512 (Form.finalizeIntoReset false) boundary outside 776 15 14 13 0
  · length_execute Variant.sha512_224 (Form.finalizeIntoReset false) boundary outside 776 12 14 13 0
  · length_execute Variant.sha512_256 (Form.finalizeIntoReset false) boundary outside 776 12 14 13 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem run_finalize_second [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (lengthOffset v (Form.finalizeIntoReset true)) (Form.finalizeIntoReset true))
      (codeRange (v.pc (lengthOffset v (Form.finalizeIntoReset true)) (Form.finalizeIntoReset true)) (bytes (Form.finalizeIntoReset true) v)) (Effect.post (effect v (Form.finalizeIntoReset true))) := by
  cases v
  · length_execute Variant.sha384 (Form.finalizeIntoReset true) boundary outside 1705 15 12 0 1
  · length_execute Variant.sha512 (Form.finalizeIntoReset true) boundary outside 1737 15 12 0 1
  · length_execute Variant.sha512_224 (Form.finalizeIntoReset true) boundary outside 1675 15 12 0 1
  · length_execute Variant.sha512_256 (Form.finalizeIntoReset true) boundary outside 1675 15 12 0 1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem run_trait_first [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (lengthOffset v (Form.traitFinalizeIntoReset false)) (Form.traitFinalizeIntoReset false))
      (codeRange (v.pc (lengthOffset v (Form.traitFinalizeIntoReset false)) (Form.traitFinalizeIntoReset false)) (bytes (Form.traitFinalizeIntoReset false) v)) (Effect.post (effect v (Form.traitFinalizeIntoReset false))) := by
  cases v
  · length_execute Variant.sha384 (Form.traitFinalizeIntoReset false) boundary outside 920 12 15 13 0
  · length_execute Variant.sha512 (Form.traitFinalizeIntoReset false) boundary outside 920 15 14 12 0
  · length_execute Variant.sha512_224 (Form.traitFinalizeIntoReset false) boundary outside 920 12 15 13 0
  · length_execute Variant.sha512_256 (Form.traitFinalizeIntoReset false) boundary outside 920 12 15 13 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem run_trait_second [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (lengthOffset v (Form.traitFinalizeIntoReset true)) (Form.traitFinalizeIntoReset true))
      (codeRange (v.pc (lengthOffset v (Form.traitFinalizeIntoReset true)) (Form.traitFinalizeIntoReset true)) (bytes (Form.traitFinalizeIntoReset true) v)) (Effect.post (effect v (Form.traitFinalizeIntoReset true))) := by
  cases v
  · length_execute Variant.sha384 (Form.traitFinalizeIntoReset true) boundary outside 1860 15 12 0 1
  · length_execute Variant.sha512 (Form.traitFinalizeIntoReset true) boundary outside 1892 15 12 0 1
  · length_execute Variant.sha512_224 (Form.traitFinalizeIntoReset true) boundary outside 1828 15 12 0 1
  · length_execute Variant.sha512_256 (Form.traitFinalizeIntoReset true) boundary outside 1828 15 12 0 1

theorem run_local [Bindings] {v : Variant} {form : Form} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (lengthOffset v form) form)
      (codeRange (v.pc (lengthOffset v form) form) (bytes form v)) (Effect.post (effect v form)) := by
  cases form with
  | slices => exact run_slices boundary outside
  | digest => exact run_digest boundary outside
  | reset stage =>
    have h : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    rcases h with rfl | rfl | rfl
    · exact run_reset_zero boundary outside
    · exact run_reset_one boundary outside
    · exact run_reset_two boundary outside
  | finalizeIntoReset second =>
    cases second
    · exact run_finalize_first boundary outside
    · exact run_finalize_second boundary outside
  | traitFinalizeIntoReset second =>
    cases second
    · exact run_trait_first boundary outside
    · exact run_trait_second boundary outside

theorem code {v : Variant} {form : Form} {s : RamState} (loaded : ProgramLoaded s)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    CodeIn (codeRange (v.pc (if form = .slices then 0x32a else 0x243) form) (bytes form)) s := by
  rcases eligible with rfl | rfl <;> cases v <;> exact code_local loaded

theorem run [Bindings] {v : Variant} {form : Form} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (if form = .slices then 0x32a else 0x243) form)
      (codeRange (v.pc (if form = .slices then 0x32a else 0x243) form) (bytes form)) (Effect.post (effect v form)) := by
  rcases eligible with rfl | rfl <;> cases v <;> exact run_local boundary outside

end Sha2.Proofs.Wrapper512.Hash.Finalize.Length.Machine
