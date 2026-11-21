import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Field.Operations.Run.Compose
import Sha2.Proofs.Common.Machine.Code
import Sha2.Proofs.Wrapper512.Hash.Finalize.State
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

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Store

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

structure Pre (v : Variant) (s : RamState) (form : Form := .slices) : Prop where
  rip : s.RIP = v.pc (storeOffset v form) form
  writable : ∀ i ∈ ([(BitVec.ofNat 64 (form.frameBytes - form.finalMemory.buffer + 112)),(BitVec.ofNat 64 (form.frameBytes - form.finalMemory.buffer + 120))] : List (BitVec 64)), MemWritable s (rspOf s + i) 8
  codeApart : ∀ i ∈ ([(BitVec.ofNat 64 (form.frameBytes - form.finalMemory.buffer + 112)),(BitVec.ofNat 64 (form.frameBytes - form.finalMemory.buffer + 120))] : List (BitVec 64)),
    ∀ offset len : Nat, offset + len ≤ 71757 →
    RangeApart (rspOf s + i) 8 (Extracted.textAddress + BitVec.ofNat 64 offset) len

abbrev bytes (v : Variant) (form : Form := .slices) : List UInt8 :=
  match form with
  | .slices => [0x4c,0x89,0xbc,0x24,0x90,0,0,0,0x48,0x89,0x84,0x24,0x98,0,0,0]
  | .digest => [0x4c,0x89,0x64,0x24,0x70,0x48,0x89,0x44,0x24,0x78]
  | .reset phase =>
    if phase.val = 2 then
      match v with
      | .sha384 => [0x4c,0x89,0x7c,0x24,0x70,0x4c,0x89,0x64,0x24,0x78]
      | .sha512 => [0x4c,0x89,0x7c,0x24,0x70,0x4c,0x89,0x64,0x24,0x78]
      | .sha512_224 => [0x4c,0x89,0x7c,0x24,0x70,0x4c,0x89,0x64,0x24,0x78]
      | .sha512_256 => [0x4c,0x89,0x7c,0x24,0x70,0x4c,0x89,0x64,0x24,0x78]
    else
      match v with
      | .sha384 => [0x4c,0x89,0x7c,0x24,0x70,0x48,0x89,0x6c,0x24,0x78]
      | .sha512 => [0x4c,0x89,0x7c,0x24,0x70,0x48,0x89,0x6c,0x24,0x78]
      | .sha512_224 => [0x4c,0x89,0x7c,0x24,0x70,0x48,0x89,0x6c,0x24,0x78]
      | .sha512_256 => [0x4c,0x89,0x7c,0x24,0x70,0x48,0x89,0x6c,0x24,0x78]
  | .finalizeIntoReset phase =>
    if phase then
      match v with
      | .sha384 => [0x4c,0x89,0xbc,0x24,0x60,0x01,0x00,0x00,0x48,0x89,0x84,0x24,0x68,0x01,0x00,0x00]
      | .sha512 => [0x4c,0x89,0xbc,0x24,0x60,0x01,0x00,0x00,0x48,0x89,0x84,0x24,0x68,0x01,0x00,0x00]
      | .sha512_224 => [0x4c,0x89,0xbc,0x24,0x60,0x01,0x00,0x00,0x48,0x89,0x84,0x24,0x68,0x01,0x00,0x00]
      | .sha512_256 => [0x4c,0x89,0xbc,0x24,0x60,0x01,0x00,0x00,0x48,0x89,0x84,0x24,0x68,0x01,0x00,0x00]
    else
      match v with
      | .sha384 => [0x4c,0x89,0xbc,0x24,0x80,0x00,0x00,0x00,0x4c,0x89,0xac,0x24,0x88,0x00,0x00,0x00]
      | .sha512 => [0x4c,0x89,0xbc,0x24,0x80,0x00,0x00,0x00,0x4c,0x89,0xac,0x24,0x88,0x00,0x00,0x00]
      | .sha512_224 => [0x4c,0x89,0xa4,0x24,0x80,0x00,0x00,0x00,0x4c,0x89,0xac,0x24,0x88,0x00,0x00,0x00]
      | .sha512_256 => [0x4c,0x89,0xa4,0x24,0x80,0x00,0x00,0x00,0x4c,0x89,0xac,0x24,0x88,0x00,0x00,0x00]
  | .traitFinalizeIntoReset phase =>
    if phase then
      match v with
      | .sha384 => [0x4c,0x89,0xbc,0x24,0x90,0x00,0x00,0x00,0x48,0x89,0x84,0x24,0x98,0x00,0x00,0x00]
      | .sha512 => [0x4c,0x89,0xbc,0x24,0x90,0x00,0x00,0x00,0x48,0x89,0x84,0x24,0x98,0x00,0x00,0x00]
      | .sha512_224 => [0x4c,0x89,0xbc,0x24,0x90,0x00,0x00,0x00,0x48,0x89,0x84,0x24,0x98,0x00,0x00,0x00]
      | .sha512_256 => [0x4c,0x89,0xbc,0x24,0x90,0x00,0x00,0x00,0x48,0x89,0x84,0x24,0x98,0x00,0x00,0x00]
    else
      match v with
      | .sha384 => [0x4c,0x89,0xa4,0x24,0x70,0x01,0x00,0x00,0x4c,0x89,0xac,0x24,0x78,0x01,0x00,0x00]
      | .sha512 => [0x4c,0x89,0xbc,0x24,0x70,0x01,0x00,0x00,0x4c,0x89,0xa4,0x24,0x78,0x01,0x00,0x00]
      | .sha512_224 => [0x4c,0x89,0xa4,0x24,0x70,0x01,0x00,0x00,0x4c,0x89,0xac,0x24,0x78,0x01,0x00,0x00]
      | .sha512_256 => [0x4c,0x89,0xa4,0x24,0x70,0x01,0x00,0x00,0x4c,0x89,0xac,0x24,0x78,0x01,0x00,0x00]

def effect (v : Variant) (form : Form := .slices) (s : RamState) : Effect :=
  { rip := v.pc (storeEndOffset v form) form
    writes := [⟨(.mem (rspOf s + (BitVec.ofNat 64 (form.frameBytes - form.finalMemory.buffer + 112))) : Operand 64), s.regValue (highCountRegister v form)⟩,
      ⟨(.mem (rspOf s + (BitVec.ofNat 64 (form.frameBytes - form.finalMemory.buffer + 120))) : Operand 64), s.regValue (lowLengthRegister v form)⟩] }

theorem code {v : Variant} {form : Form} {s : RamState} (loaded : ProgramLoaded s)
 :
    CodeIn (codeRange (v.pc (storeOffset v form) form) (bytes v form)) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset form + (storeOffset v form)) (bytes v form)
  · cases form with
    | reset stage =>
      have h : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      rcases h with rfl | rfl | rfl <;> cases v <;> decide +kernel +revert
    | finalizeIntoReset second | traitFinalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
    | _ => cases v <;> decide +kernel +revert
  · cases form with
    | reset stage =>
      have h : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      rcases h with rfl | rfl | rfl <;> cases v <;> decide +kernel +revert
    | finalizeIntoReset second | traitFinalizeIntoReset second => cases second <;> cases v <;> decide +kernel +revert
    | _ => cases v <;> decide +kernel +revert

macro "store_run" f:term:max v:term:max b:term:max o:term:max
    p:num hi:num lo:num highOff:num lowOff:num width:num rex:num : tactic => do
  let p0 := p.getNat
  let w := width.getNat
  let num (n : Nat) : Lean.TSyntax `term := ⟨Lean.Syntax.mkNumLit (toString n)⟩
  let arg0 := num p0
  let arg1 := num hi.getNat
  let arg2 := num highOff.getNat
  let arg3 ← if w == 8 then `(.d32 $arg2) else `(.d8 $(num highOff.getNat))
  let arg4 := arg2
  let arg5 := arg2
  let arg6 := arg0
  let arg7 := num w
  let arg8 := arg2
  let arg9 := arg0
  let arg10 := num (2*w)
  let arg11 := arg0
  let arg12 := arg7
  let arg13 := num (p0+w)
  let arg14 := arg13
  let arg15 := num lowOff.getNat
  let arg16 ← if w == 8 then `(.d32 $arg15) else `(.d8 $arg15)
  let arg17 := arg0
  let arg18 := arg7
  let arg19 := arg0
  let arg20 := arg7
  let arg21 := arg7
  let arg22 := arg15
  let arg23 := arg15
  let arg24 := arg13
  let arg25 := arg7
  let arg26 := arg15
  let arg27 := arg0
  let arg28 := arg10
  let arg29 := arg13
  let arg30 := arg7
  let arg31 := num (p0+2*w)
  let low := num lo.getNat
  let lowRex := num rex.getNat
  `(tactic|
    first |
      simp only [bytes]
      advance_begin (mov_m64_r64_effect_step (($v).pc $arg0 $f) 0x4c (by simp [RexWPrefix]) $arg1
        (.sib 4 none 0 $arg3) (by decide) rfl rfl)
      case pre =>
        intro s h
        refine ⟨h.rip, ?_, ?_⟩
        · x86_norm
          exact h.writable $arg4 (by simp [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory])
        · x86_norm
          exact h.codeApart $arg5 (by simp [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory]) (($v).textOffset $f + $arg6) $arg7 (by cases ($v) <;> decide)
      case av =>
        intro s h
        apply Effect.avoids_codeRange
        x86_norm
        exact h.codeApart $arg8 (by simp [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory]) (($v).textOffset $f + $arg9) $arg10 (by cases ($v) <;> decide)
      case «next» =>
        intro _ _
        change ($v).pc $arg11 $f + BitVec.ofNat 64 $arg12 ≠ ($b).rip
        rw [(Variant.pc_add (form := $f))]
        exact boundary_ne_program $o (inProgram_of_textOffset (($v).textOffset $f + $arg13) (by cases ($v) <;> decide))
      advance_then (mov_m64_r64_effect_step (($v).pc $arg14 $f) $lowRex (by simp [RexWPrefix]) $low
        (.sib 4 none 0 $arg16) (by decide) rfl rfl)
      case sub =>
        have hpc := Variant.pc_add $v $arg17 $arg18 $f
        simp only [↓reduceIte, reduceCtorEq, Nat.reduceAdd] at hpc ⊢
        rw [← hpc]
        exact codeRange_slice_subset (($v).pc $arg19 $f) (bytes $v $f) $arg20 $arg21
      case mid =>
        intro s t hp hh ho
        refine ⟨StorePre.of_holds hh (ho true) (by x86_norm [(Variant.pc_add (form := $f))]) (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm
          exact hp.writable $arg22 (by simp [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory])
        · x86_norm
          exact hp.codeApart $arg23 (by simp [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory]) (($v).textOffset $f + $arg24) $arg25 (by cases ($v) <;> decide)
        · apply Effect.Local.avoids (by x86_local) (ho true)
          apply Effect.avoids_codeRange
          x86_norm
          exact hp.codeApart $arg26 (by simp [Form.frameBytes, Form.finalMemory, ResetLayout.resetMemory, ResetLayout.finalizeMemory, ResetLayout.cloneMemory]) (($v).textOffset $f + $arg27) $arg28 (by cases ($v) <;> decide)
        · change ($v).pc $arg29 $f + BitVec.ofNat 64 $arg30 ≠ ($b).rip
          rw [(Variant.pc_add (form := $f))]
          exact boundary_ne_program $o (inProgram_of_textOffset (($v).textOffset $f + $arg31) (by cases ($v) <;> decide))
      advance_finish [effect, Variant.pc_add, State.regValue, gprIndex, Operand.read]
  )

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} {form : Form} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip)
 :
    AdvanceTriple boundary (fun s => Pre v s form) (codeRange (v.pc (storeOffset v form) form) (bytes v form)) (Effect.post (effect v form)) := by
  cases form with
  | slices => store_run Form.slices v boundary outside 835 7 0 144 152 8 72
  | digest => store_run Form.digest v boundary outside 604 4 0 112 120 5 72
  | reset stage =>
    have h : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    rcases h with rfl | rfl | rfl <;> cases v
    · store_run (Form.reset 0) Variant.sha384 boundary outside 1245 7 5 112 120 5 72
    · store_run (Form.reset 0) Variant.sha512 boundary outside 1245 7 5 112 120 5 72
    · store_run (Form.reset 0) Variant.sha512_224 boundary outside 1245 7 5 112 120 5 72
    · store_run (Form.reset 0) Variant.sha512_256 boundary outside 1245 7 5 112 120 5 72
    · store_run (Form.reset 1) Variant.sha384 boundary outside 1245 7 5 112 120 5 72
    · store_run (Form.reset 1) Variant.sha512 boundary outside 1245 7 5 112 120 5 72
    · store_run (Form.reset 1) Variant.sha512_224 boundary outside 1245 7 5 112 120 5 72
    · store_run (Form.reset 1) Variant.sha512_256 boundary outside 1245 7 5 112 120 5 72
    · store_run (Form.reset 2) Variant.sha384 boundary outside 2085 7 4 112 120 5 76
    · store_run (Form.reset 2) Variant.sha512 boundary outside 2117 7 4 112 120 5 76
    · store_run (Form.reset 2) Variant.sha512_224 boundary outside 2053 7 4 112 120 5 76
    · store_run (Form.reset 2) Variant.sha512_256 boundary outside 2053 7 4 112 120 5 76
  | finalizeIntoReset second =>
    cases second <;> cases v
    · store_run (Form.finalizeIntoReset false) Variant.sha384 boundary outside 789 7 5 128 136 8 76
    · store_run (Form.finalizeIntoReset false) Variant.sha512 boundary outside 789 7 5 128 136 8 76
    · store_run (Form.finalizeIntoReset false) Variant.sha512_224 boundary outside 789 4 5 128 136 8 76
    · store_run (Form.finalizeIntoReset false) Variant.sha512_256 boundary outside 789 4 5 128 136 8 76
    · store_run (Form.finalizeIntoReset true) Variant.sha384 boundary outside 1730 7 0 352 360 8 72
    · store_run (Form.finalizeIntoReset true) Variant.sha512 boundary outside 1762 7 0 352 360 8 72
    · store_run (Form.finalizeIntoReset true) Variant.sha512_224 boundary outside 1700 7 0 352 360 8 72
    · store_run (Form.finalizeIntoReset true) Variant.sha512_256 boundary outside 1700 7 0 352 360 8 72
  | traitFinalizeIntoReset second =>
    cases second <;> cases v
    · store_run (Form.traitFinalizeIntoReset false) Variant.sha384 boundary outside 933 4 5 368 376 8 76
    · store_run (Form.traitFinalizeIntoReset false) Variant.sha512 boundary outside 933 7 4 368 376 8 76
    · store_run (Form.traitFinalizeIntoReset false) Variant.sha512_224 boundary outside 933 4 5 368 376 8 76
    · store_run (Form.traitFinalizeIntoReset false) Variant.sha512_256 boundary outside 933 4 5 368 376 8 76
    · store_run (Form.traitFinalizeIntoReset true) Variant.sha384 boundary outside 1885 7 0 144 152 8 72
    · store_run (Form.traitFinalizeIntoReset true) Variant.sha512 boundary outside 1917 7 0 144 152 8 72
    · store_run (Form.traitFinalizeIntoReset true) Variant.sha512_224 boundary outside 1853 7 0 144 152 8 72
    · store_run (Form.traitFinalizeIntoReset true) Variant.sha512_256 boundary outside 1853 7 0 144 152 8 72

end Sha2.Proofs.Wrapper512.Hash.Finalize.Store
