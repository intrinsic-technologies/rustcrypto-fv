import Sha2.Proofs.Wrapper512.Absorb.Large.Counter
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

namespace Sha2.Proofs.Wrapper512.Absorb.Large.CompressSetup

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field (AdvanceTriple)
open Sha2.Proofs.Common.Machine

def prefixBytes (offset : BitVec 32) : List UInt8 :=
  [0xba, 1, 0, 0, 0, 0x48, 0x8d, 0xbc] ++
    (AddrMode.sib 4 none 0 (.d32 offset)).tail

def prefixEffect (ip : BitVec 64) (offset : BitVec 32) (s : RamState) : Effect :=
  { rip := ip + 13
    writes := [⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + offset.signExtend 64⟩] }

set_option maxHeartbeats 1000000 in
theorem prefix_run [Bindings] (boundary : ReturnBoundary) (ip : BitVec 64)
    (offset : BitVec 32) (next₁ : ip + 5 ≠ boundary.rip)
    (next₂ : ip + 13 ≠ boundary.rip) (code : CodeMap)
    (sub : ∀ x ∈ codeRange ip (prefixBytes offset), x ∈ code) :
    AdvanceTriple boundary (fun s => s.RIP = ip)
      code (Effect.post (prefixEffect ip offset)) := by
  advance_begin (mov_r32_imm32_effect_step ip 0xba (by decide +kernel) 1)
  case sub =>
    intro x hx
    apply sub x
    apply codeRange_slice_subset ip (prefixBytes offset) 0 5 x
    simpa [prefixBytes, BitVec.add_zero, immBytes, immByte, List.range_succ] using hx
  case av => intro s _; exact Effect.Avoids.of_noMem (by simp [Component.Covers]) _
  advance_then (lea_r64_effect_step (ip + 5) 0x48 (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 offset)) (by simp [AddrMode.Valid]) rfl rfl)
  case sub =>
    intro x hx
    apply sub x
    apply codeRange_slice_subset ip (prefixBytes offset) 5 8 x
    simpa [prefixBytes, AddrMode.tail, Disp.bytes, AddrMode.modrm, AddrMode.mod, AddrMode.rm, Disp.mod, immBytes, List.range_succ] using hx
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of rfl, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by simpa [leaR64Effect, leaLen, AddrMode.tail, Disp.bytes, BitVec.add_assoc] using next₂⟩
  advance_finish [prefixEffect, BitVec.add_assoc, BitVec.add_zero]

def registerBufferBytes (offset : BitVec 32) (saved : Bool) : List UInt8 :=
  prefixBytes offset ++ [0x48, 0x89, if saved then 0xde else 0xe6]

def registerBufferEffect (ip : BitVec 64) (offset : BitVec 32) (saved : Bool)
    (s : RamState) : Effect :=
  { rip := ip + 16
    writes := [⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + offset.signExtend 64⟩,
      ⟨(.reg 6 : Operand 64), s.regValue (if saved then .rbx else .rsp)⟩] }

set_option maxHeartbeats 1000000 in
theorem run_register_buffer [Bindings] (boundary : ReturnBoundary) (ip : BitVec 64)
    (offset : BitVec 32) (saved : Bool)
    (next₁ : ip + 5 ≠ boundary.rip) (next₂ : ip + 13 ≠ boundary.rip)
    (next₃ : ip + 16 ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = ip)
      (codeRange ip (registerBufferBytes offset saved))
      (Effect.post (registerBufferEffect ip offset saved)) := by
  have prefixRun := prefix_run boundary ip offset next₁ next₂
    (codeRange ip (registerBufferBytes offset saved)) (by
      intro x hx
      apply codeRange_slice_subset ip (registerBufferBytes offset saved) 0 13 x
      simpa [registerBufferBytes, prefixBytes, AddrMode.tail, Disp.bytes, immBytes,
        List.range_succ, BitVec.add_zero] using hx)
  cases saved with
  | false =>
    refine AdvanceTriple.block_then ?k
      (mov_r64_r64_effect_step (ip + 13) 0x48 0xe6 (by simp [RexWPrefix]) rfl)
      (by x86_local) ?sub ?full ?mid prefixRun
    case sub =>
      intro x hx
      apply codeRange_slice_subset ip (registerBufferBytes offset false) 13 3 x
      simpa [registerBufferBytes, prefixBytes, AddrMode.tail, Disp.bytes, immBytes,
        List.range_succ] using hx
    case full => intro s _ w hw; simp [prefixEffect] at hw; rcases hw with rfl | rfl <;> rfl
    case mid =>
      intro s t hp hh ho
      exact ⟨hh.rip_of rfl, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by simpa [movR64R64Effect, BitVec.add_assoc] using next₃⟩
    advance_finish [registerBufferEffect, prefixEffect, BitVec.add_assoc]
  | true =>
    refine AdvanceTriple.block_then ?kSaved
      (mov_r64_r64_effect_step (ip + 13) 0x48 0xde (by simp [RexWPrefix]) rfl)
      (by x86_local) ?subSaved ?fullSaved ?midSaved prefixRun
    case subSaved =>
      intro x hx
      apply codeRange_slice_subset ip (registerBufferBytes offset true) 13 3 x
      simpa [registerBufferBytes, prefixBytes, AddrMode.tail, Disp.bytes, immBytes,
        List.range_succ] using hx
    case fullSaved => intro s _ w hw; simp [prefixEffect] at hw; rcases hw with rfl | rfl <;> rfl
    case midSaved =>
      intro s t hp hh ho
      exact ⟨hh.rip_of rfl, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by simpa [movR64R64Effect, BitVec.add_assoc] using next₃⟩
    advance_finish [registerBufferEffect, prefixEffect, BitVec.add_assoc]

def buffer8Bytes (offset : BitVec 32) (buffer : BitVec 8) (saved : Bool) : List UInt8 :=
  prefixBytes offset ++ [0x48, 0x8d, if saved then 0x5c else 0x74, 0x24, ⟨buffer⟩]

def buffer8Effect (ip : BitVec 64) (offset : BitVec 32) (buffer : BitVec 8)
    (saved : Bool) (s : RamState) : Effect :=
  { rip := ip + 18
    writes := [⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + offset.signExtend 64⟩,
      ⟨(.reg (if saved then 3 else 6) : Operand 64), rspOf s + buffer.signExtend 64⟩] }

set_option maxHeartbeats 1000000 in
theorem run_buffer8 [Bindings] (boundary : ReturnBoundary) (ip : BitVec 64)
    (offset : BitVec 32) (buffer : BitVec 8) (saved : Bool)
    (next₁ : ip + 5 ≠ boundary.rip) (next₂ : ip + 13 ≠ boundary.rip)
    (next₃ : ip + 18 ≠ boundary.rip) (code : CodeMap)
    (sub : ∀ x ∈ codeRange ip (buffer8Bytes offset buffer saved), x ∈ code) :
    AdvanceTriple boundary (fun s => s.RIP = ip) code
      (Effect.post (buffer8Effect ip offset buffer saved)) := by
  have prefixRun := prefix_run boundary ip offset next₁ next₂ code (by
    intro x hx
    apply sub x
    apply codeRange_slice_subset ip (buffer8Bytes offset buffer saved) 0 13 x
    simpa [buffer8Bytes, prefixBytes, AddrMode.tail, Disp.bytes, immBytes,
      List.range_succ, BitVec.add_zero] using hx)
  cases saved with
  | false =>
    refine AdvanceTriple.block_then ?kfalse
      (lea_r64_effect_step (ip + 13) 0x48 (by simp [RexWPrefix]) 6
        (.sib 4 none 0 (.d8 buffer)) (by simp [AddrMode.Valid]) rfl rfl)
      (by x86_local) ?subfalse ?fullfalse ?midfalse prefixRun
    case subfalse =>
      intro x hx
      apply sub x
      apply codeRange_slice_subset ip (buffer8Bytes offset buffer false) 13 5 x
      simpa [buffer8Bytes, prefixBytes, AddrMode.tail, Disp.bytes, immBytes,
        List.range_succ, AddrMode.modrm, AddrMode.mod, AddrMode.rm, Disp.mod,
        AddrMode.sibByte, idxLow, regLow, immByte] using hx
    case fullfalse => intro s _ w hw; simp [prefixEffect] at hw; rcases hw with rfl | rfl <;> rfl
    case midfalse =>
      intro s t hp hh ho
      exact ⟨hh.rip_of rfl, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by simpa [leaR64Effect, leaLen, AddrMode.tail, Disp.bytes, BitVec.add_assoc] using next₃⟩
    advance_finish [buffer8Effect, prefixEffect, BitVec.add_assoc, BitVec.add_zero]
  | true =>
    refine AdvanceTriple.block_then ?ktrue
      (lea_r64_effect_step (ip + 13) 0x48 (by simp [RexWPrefix]) 3
        (.sib 4 none 0 (.d8 buffer)) (by simp [AddrMode.Valid]) rfl rfl)
      (by x86_local) ?subtrue ?fulltrue ?midtrue prefixRun
    case subtrue =>
      intro x hx
      apply sub x
      apply codeRange_slice_subset ip (buffer8Bytes offset buffer true) 13 5 x
      simpa [buffer8Bytes, prefixBytes, AddrMode.tail, Disp.bytes, immBytes,
        List.range_succ, AddrMode.modrm, AddrMode.mod, AddrMode.rm, Disp.mod,
        AddrMode.sibByte, idxLow, regLow, immByte] using hx
    case fulltrue => intro s _ w hw; simp [prefixEffect] at hw; rcases hw with rfl | rfl <;> rfl
    case midtrue =>
      intro s t hp hh ho
      exact ⟨hh.rip_of rfl, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
        by simpa [leaR64Effect, leaLen, AddrMode.tail, Disp.bytes, BitVec.add_assoc] using next₃⟩
    advance_finish [buffer8Effect, prefixEffect, BitVec.add_assoc, BitVec.add_zero]

def savedBufferBytes (offset : BitVec 32) (buffer : BitVec 8) : List UInt8 :=
  buffer8Bytes offset buffer true ++ [0x48, 0x89, 0xde]

def savedBufferEffect (ip : BitVec 64) (offset : BitVec 32) (buffer : BitVec 8)
    (s : RamState) : Effect :=
  { rip := ip + 21
    writes := [⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + offset.signExtend 64⟩,
      ⟨(.reg 3 : Operand 64), rspOf s + buffer.signExtend 64⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + buffer.signExtend 64⟩] }

set_option maxHeartbeats 1000000 in
theorem run_saved_buffer [Bindings] (boundary : ReturnBoundary) (ip : BitVec 64)
    (offset : BitVec 32) (buffer : BitVec 8)
    (away : ∀ n : Nat, n ≤ 21 → ip + BitVec.ofNat 64 n ≠ boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = ip)
      (codeRange ip (savedBufferBytes offset buffer))
      (Effect.post (savedBufferEffect ip offset buffer)) := by
  have block := run_buffer8 boundary ip offset buffer true
    (away 5 (by decide)) (away 13 (by decide)) (away 18 (by decide))
    (codeRange ip (savedBufferBytes offset buffer)) (by
      intro x hx
      apply codeRange_slice_subset ip (savedBufferBytes offset buffer) 0 18 x
      simpa [savedBufferBytes, buffer8Bytes, prefixBytes, AddrMode.tail, Disp.bytes,
        immBytes, List.range_succ, BitVec.add_zero] using hx)
  refine AdvanceTriple.block_then ?k
    (mov_r64_r64_effect_step (ip + 18) 0x48 0xde (by simp [RexWPrefix]) rfl)
    (by x86_local) ?sub ?full ?mid block
  case sub =>
    intro x hx
    apply codeRange_slice_subset ip (savedBufferBytes offset buffer) 18 3 x
    simpa [savedBufferBytes, buffer8Bytes, prefixBytes, AddrMode.tail, Disp.bytes,
      immBytes, List.range_succ] using hx
  case full =>
    intro s _ w hw
    simp [buffer8Effect] at hw
    rcases hw with rfl | rfl | rfl <;> rfl
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of rfl, Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by simpa [movR64R64Effect, BitVec.add_assoc] using away 21 (by decide)⟩
  advance_finish [savedBufferEffect, buffer8Effect, BitVec.add_assoc]

def bytes : List UInt8 :=
  [0xba,0x1,0x0,0x0,0x0,0x48,0x8d,0xbc,0x24,0x70,0x1,0x0,0x0,0x48,0x8d,0xb4,0x24,0xf0,0x0,0x0,0x0]

def effect (v : Variant) (s : RamState) : Effect :=
  { rip := (v.pc 0x190)
    writes := [⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), rspOf s + 368⟩,
      ⟨(.reg 6 : Operand 64), rspOf s + 240⟩] }

theorem code {v : Variant} {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (v.pc 0x17b) bytes) s := by
  apply programText_slice (programLoaded_codeIn loaded) (v.textOffset + 0x17b) bytes
  · cases v <;> decide +kernel
  · cases v <;> decide +kernel

set_option maxHeartbeats 1000000 in
theorem run [Bindings] {v : Variant} (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = (v.pc 0x17b))
      (codeRange (v.pc 0x17b) bytes) (Effect.post (effect v)) := by
  have prefixRun := prefix_run boundary (v.pc 0x17b) 368
    (by
      change v.pc 0x17b + BitVec.ofNat 64 5 ≠ _
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x180 < 1024)))
    (by
      change v.pc 0x17b + BitVec.ofNat 64 13 ≠ _
      rw [Variant.pc_add]
      exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x188 < 1024)))
    (codeRange (v.pc 0x17b) bytes)
    (by
      have h : prefixBytes 368 = bytes.take 13 := by decide +kernel
      rw [h]
      simpa only [List.drop_zero, BitVec.add_zero] using
        codeRange_slice_subset (v.pc 0x17b) bytes 0 13)
  refine AdvanceTriple.block_then ?k (lea_r64_effect_step (v.pc 0x188) 0x48
    (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d32 240))
    (by decide +kernel) rfl rfl) (by x86_local) ?sub ?full ?mid prefixRun
  case full => intro s _ w hw; simp [prefixEffect] at hw; rcases hw with rfl | rfl <;> rfl
  case sub =>
    rw [← Variant.pc_add v 0x17b 13]
    exact codeRange_slice_subset (v.pc 0x17b) bytes 13 8
  case mid =>
    intro s t hp hh ho
    exact ⟨hh.rip_of (by change v.pc 0x17b + BitVec.ofNat 64 13 = v.pc 0x188; exact Variant.pc_add v 0x17b 13), Effect.Avoids.of_noMem (by simp [Component.Covers]) _,
      by
        change v.pc 0x188 + BitVec.ofNat 64 8 ≠ boundary.rip
        rw [Variant.pc_add]
        exact boundary_ne_program outside (Variant.pc_inProgram v (by decide : 0x190 < 1024))⟩
  advance_finish [effect, prefixEffect, Variant.pc_add, BitVec.add_zero]

end Sha2.Proofs.Wrapper512.Absorb.Large.CompressSetup

namespace Sha2.Proofs.Wrapper512.Absorb.Large.CompressSetup
open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Field (AdvanceTriple)

def formBytes (form : Form) : List UInt8 :=
  match form with
  | .slices | .digest => bytes
  | .reset stage => registerBufferBytes 128 (stage.val == 1)
  | .finalizeIntoReset _ => buffer8Bytes 144 16 false
  | .traitFinalizeIntoReset _ => savedBufferBytes 160 32

def formEffect (v : Variant) (form : Form) : RamState → Effect :=
  let p := v.pc (Counter.endOffset false v form) form
  match form with
  | .slices | .digest => effect v
  | .reset stage => registerBufferEffect p 128 (stage.val == 1)
  | .finalizeIntoReset _ => buffer8Effect p 144 16 false
  | .traitFinalizeIntoReset _ => savedBufferEffect p 160 32

theorem form_bytes (v : Variant) (form : Form) (h : form ≠ .digest) :
    Extracted.textBytes.toListFrom (v.textOffset form + Counter.endOffset false v form)
      (formBytes form).length = formBytes form := by
  cases v <;> cases form with
  | digest => exact (h rfl).elim
  | slices => decide +kernel
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel

theorem form_bound (v : Variant) (form : Form) :
    v.textOffset form + Counter.endOffset false v form + 21 < 71757 := by
  cases v <;> cases form with
  | reset stage => revert stage; decide +kernel
  | finalizeIntoReset second | traitFinalizeIntoReset second => revert second; decide +kernel
  | _ => decide +kernel

set_option maxHeartbeats 1000000 in
theorem run_form [Bindings] (v : Variant) (form : Form) (h : form ≠ .digest)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (fun s => s.RIP = v.pc (Counter.endOffset false v form) form)
      (codeRange (v.pc (Counter.endOffset false v form) form) (formBytes form))
      (Effect.post (formEffect v form)) := by
  have away (n : Nat) (hn : n ≤ 21) :
      v.pc (Counter.endOffset false v form) form + BitVec.ofNat 64 n ≠ boundary.rip := by
    rw [Variant.pc_add v (Counter.endOffset false v form) n form]
    apply boundary_ne_program outside
    apply inProgram_of_textOffset
    have bound := form_bound v form
    omega
  cases form with
  | digest => exact (h rfl).elim
  | slices => exact run boundary outside
  | reset stage =>
    exact run_register_buffer boundary _ 128 (stage.val == 1)
      (away 5 (by decide)) (away 13 (by decide)) (away 16 (by decide))
  | finalizeIntoReset second =>
    exact run_buffer8 boundary _ 144 16 false
      (away 5 (by decide)) (away 13 (by decide)) (away 18 (by decide)) _
      (fun _ hx => hx)
  | traitFinalizeIntoReset second =>
    exact run_saved_buffer boundary _ 160 32 away

def formComponents (form : Form) : List Component :=
  (match form with | .traitFinalizeIntoReset _ => [.reg 3] | _ => []) ++
    [.reg 2, .reg 7, .reg 6, .rip]

theorem effect_rip (v : Variant) (form : Form) (nonDigest : form ≠ .digest)
    (s : RamState) : (formEffect v form s).rip = v.pc (v.traversal form).fillCall form := by
  cases v <;> cases form
  all_goals first | exact (nonDigest rfl).elim | skip
  all_goals first
    | (rename_i stage
       have hc : stage = (0 : Fin 3) ∨ stage = 1 ∨ stage = 2 := by omega
       rcases hc with rfl | rfl | rfl)
    | (rename_i second; cases second)
    | skip
  all_goals rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem form_result (v : Variant) (form : Form) (nonDigest : form ≠ .digest)
    {initial u w : RamState} (h : (formEffect v form u).Holds u w)
    (rsp : rspOf u = stackPtr initial - BitVec.ofNat 64 form.frameBytes)
    (saved : form = .reset 1 → u.regValue .rbx = bufferPointer initial form) :
    w.RIP = v.pc (v.traversal form).fillCall form ∧
    w.regValue .rdi = hashPointer initial form form.activeMemory ∧
    w.regValue .rsi = bufferPointer initial form form.activeMemory ∧
    w.regValue .rdx = 1 ∧
    AgreesExcept (formComponents form) u w := by
  refine ⟨h.rip.trans (effect_rip v form nonDigest u), ?_⟩
  have hwrites := h.writes
  have hframe := h.agrees
  cases form
  case digest => exact (nonDigest rfl).elim
  case' reset stage =>
    have hc : stage = (0 : Fin 3) ∨ stage = 1 ∨ stage = 2 := by omega
    rcases hc with rfl | rfl | rfl
  case' finalizeIntoReset second => cases second
  case' traitFinalizeIntoReset second => cases second
  all_goals
    dsimp [formEffect, effect, registerBufferEffect, buffer8Effect, savedBufferEffect,
      Write.AllHold] at hwrites
    try rw [rsp] at hwrites
    try rw [show u.regValue .rsp = stackPtr initial - BitVec.ofNat 64 _ from rsp] at hwrites
    try have hs := saved rfl
    try rw [hs] at hwrites
    have di : w.regValue .rdi = _ := hwrites.2.1
    first
    | have si : w.regValue .rsi = _ := hwrites.2.2
    | have si : w.regValue .rsi = _ := hwrites.2.2.2
    refine ⟨?_, ?_, ?_, ?_⟩
  all_goals first
    | exact si
    | (rw [di]; simp only [hashPointer, Form.activeMemory, Form.bufferedMemory,
        ResetLayout.resetMemory, ResetLayout.finalizeMemory,
        BitVec.sub_eq_add_neg, BitVec.add_assoc, Form.frameBytes]; try rfl)
    | (rw [si]; simp only [bufferPointer, Form.activeMemory, Form.bufferedMemory,
        ResetLayout.finalizeMemory,
        BitVec.sub_eq_add_neg, BitVec.add_assoc, Form.frameBytes]; try rfl)
    | exact hwrites.1
    | (apply hframe.mono; simp [formEffect, effect, registerBufferEffect,
        buffer8Effect, savedBufferEffect, Effect.components, formComponents])

end Sha2.Proofs.Wrapper512.Absorb.Large.CompressSetup
