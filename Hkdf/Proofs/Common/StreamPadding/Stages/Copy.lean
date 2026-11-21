import Hkdf.Proofs.Common.StreamPadding.Layout
import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Stages

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field (AdvanceTriple)

def copyStart (v : Variant) (last : Bool) : BitVec 64 :=
  v.pc (if last then .lastHead else .firstHead)

def copyEnd (v : Variant) (last : Bool) : BitVec 64 :=
  v.pc (if last then .lastCall else .firstCall)

def copyLoadAm (v : Variant) (i : Nat) : AddrMode :=
  .sib 4 none 0 (if v.tail + 8*i < 128 then .d8 (BitVec.ofNat 8 (v.tail + 8*i))
    else .d32 (BitVec.ofNat 32 (v.tail + 8*i)))

def copyStoreAm (v : Variant) (i : Nat) : AddrMode :=
  .sib 4 none 0 (match v with
    | .key => .d32 (BitVec.ofNat 32 (v.scratch + 8*i))
    | .hmac | .simpleInner | .simpleOuter => .d8 (BitVec.ofNat 8 (v.scratch + 8*i)))

def copyLoadBytes (v : Variant) (i : Nat) (reg : BitVec 3 := 0) : List UInt8 :=
  [0x48,0x8b,(copyLoadAm v i).modrm reg] ++ (copyLoadAm v i).tail

def copyStoreBytes (v : Variant) (i : Nat) (reg : BitVec 3 := 0)
    (rex : UInt8 := 0x48) : List UInt8 :=
  [rex,0x89,(copyStoreAm v i).modrm reg] ++ (copyStoreAm v i).tail

def copyStoreLen (v : Variant) : Nat := 3 + (copyStoreAm v 0).tail.length

def copyHeadLen (v : Variant) (last : Bool) : Nat :=
  if last then copyStoreLen v else 13

def copyBytes (v : Variant) (last : Bool) : List UInt8 :=
  (if last then copyStoreBytes v 7 (v.lengthIndex.setWidth 3) 0x4c
   else copyLoadBytes v 7 ++ copyStoreBytes v 7) ++
  ([6,5,4,3,2].flatMap fun i => copyLoadBytes v i ++ copyStoreBytes v i) ++
  copyLoadBytes v 0 ++ copyLoadBytes v 1 1 ++
  copyStoreBytes v 1 1 ++ copyStoreBytes v 0 ++
  [0x48,0x8d,(copyStoreAm v 0).modrm 6] ++ (copyStoreAm v 0).tail ++
  [0xba,1,0,0,0,0x4c,0x89,UInt8.ofNat (0xc7 + 8 * (v.hashIndex.setWidth 3).toNat)]

structure CopyPre (v : Variant) (last : Bool) (s : RamState) : Prop where
  rip : s.RIP = copyStart v last
  readable : ∀ i : Nat, i < (if last then 7 else 8) →
    MemReadable s (rspOf s + BitVec.ofNat 64 (v.tail + 8*i)) 8
  writable : ∀ i : Nat, i < 8 →
    MemWritable s (rspOf s + BitVec.ofNat 64 (v.scratch + 8*i)) 8
  codeApart : ∀ i : Nat, i < 8 →
    RangeApart (rspOf s + BitVec.ofNat 64 (v.scratch + 8*i)) 8
      (copyStart v last) (copyBytes v last).length

def copyEffect (v : Variant) (last : Bool) (s : RamState) : Effect :=
  { rip := copyEnd v last
    writes :=
      [⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + BitVec.ofNat 64 v.tail) 64⟩,
       ⟨(.reg 1 : Operand 64), memLoad s.external (rspOf s + BitVec.ofNat 64 (v.tail+8)) 64⟩,
       ⟨(.reg 6 : Operand 64), rspOf s + BitVec.ofNat 64 v.scratch⟩,
       ⟨(.reg 2 : Operand 64), 1⟩,
       ⟨(.reg 7 : Operand 64), s.regValue v.hashReg⟩] ++
      ([0,1,2,3,4,5,6,7] : List Nat).map fun i =>
        ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.scratch+8*i)) : Operand 64),
          if last && i == 7 then s.regValue v.lengthReg
          else memLoad s.external (rspOf s + BitVec.ofNat 64 (v.tail+8*i)) 64⟩ }

theorem copy_code {s : RamState} (loaded : ProgramLoaded s) (v : Variant) (last : Bool) :
    CodeIn (codeRange (copyStart v last) (copyBytes v last)) s := by
  let offset := (copyStart v last).toNat - 0x100000
  have addr : copyStart v last = Extracted.textAddress + BitVec.ofNat 64 offset := by
    cases v <;> cases last <;> decide +kernel
  rw [addr]
  exact programText_slice (programLoaded_codeIn loaded) offset (copyBytes v last)
    (by cases v <;> cases last <;> decide +kernel)
    (by cases v <;> cases last <;> decide +kernel)

attribute [local x86_compose] copyStart copyEnd copyLoadAm copyStoreAm copyHeadLen copyStoreLen
  Variant.pc Variant.tail Variant.scratch Variant.hashReg Variant.hashIndex
  Variant.lengthReg Variant.lengthIndex regIndex

macro "stream_padding_copy_chain " variant:ident ", " control:ident : tactic => do
  let key := variant.getId == `key
  let inner := variant.getId == `simpleInner
  let v ← match variant.getId with
    | `key => `(Variant.key)
    | `hmac => `(Variant.hmac)
    | `simpleInner => `(Variant.simpleInner)
    | `simpleOuter => `(Variant.simpleOuter)
    | _ => Lean.Macro.throwError "unknown stream padding variant"
  let last := control.getId == `last
  let start := if key then (if last then 0x16551 else 0x16482)
    else if variant.getId == `hmac then (if last then 0xdeb0 else 0xddf6)
    else if inner then (if last then 0x17394 else 0x172da)
    else (if last then 0x17632 else 0x17578)
  let lengthReg := Lean.quote (if inner then 5 else 4)
  let hashModrm := Lean.quote (if inner then 0xff else 0xf7)
  let outside := Lean.mkIdent `outside
  let l ← if last then `(true) else `(false)
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  if last then
    steps := steps.push (← `(tactic| advance_begin (mov_m64_r64_effect_step
      (copyStart $v $l) 0x4c (by simp [RexWPrefix]) $lengthReg (copyStoreAm $v 7)
      (by decide +kernel) rfl rfl)))
  else
    steps := steps.push (← `(tactic| advance_begin (mov_r64_m64_effect_step
      (copyStart $v $l) 0x48 (by simp [RexWPrefix]) 0 (copyLoadAm $v 7)
      (by decide +kernel) rfl rfl)))
  let storeLen := if key then 8 else 5
  let total := (if last then storeLen else 13) + 7*(5+storeLen) + storeLen + 8
  let totalT := Lean.quote total
  let mut off := if last then storeLen else if key then 5 else 8
  let mut offset := Lean.quote off
  if last then
    steps := steps.push (← `(tactic| case pre =>
      intro s h
      refine ⟨h.rip, h.writable 7 (by decide), ?_⟩
      intro a ha b hb
      have hh := h.codeApart 7 (by decide) a ha b
      apply hh
      change b < $totalT
      change b < $(Lean.quote storeLen) at hb
      omega))
    steps := steps.push (← `(tactic| case av =>
      intro s h
      apply Effect.avoids_codeRange
      x86_norm
      exact h.codeApart 7 (by decide)))
  else
    steps := steps.push (← `(tactic| case pre =>
      intro s h
      exact ⟨h.rip, h.readable 7 (by decide)⟩))
  let firstNext := Lean.quote (start + off)
  steps := steps.push (← `(tactic| case next =>
    intro s h
    x86_norm
    exact boundary_ne_program $outside (inProgram_of_textOffset $firstNext (by decide))))
  let mut specs : Array (Lean.TSyntax `term × Nat × Nat) := #[]
  if !last then
    specs := specs.push ((← `(7)), 0, 1)
  specs := specs.push ((← `(6)), 0, 0)
  specs := specs.push ((← `(6)), 0, 1)
  specs := specs.push ((← `(5)), 0, 0)
  specs := specs.push ((← `(5)), 0, 1)
  specs := specs.push ((← `(4)), 0, 0)
  specs := specs.push ((← `(4)), 0, 1)
  specs := specs.push ((← `(3)), 0, 0)
  specs := specs.push ((← `(3)), 0, 1)
  specs := specs.push ((← `(2)), 0, 0)
  specs := specs.push ((← `(2)), 0, 1)
  specs := specs.push ((← `(0)), 0, 0)
  specs := specs.push ((← `(1)), 1, 0)
  specs := specs.push ((← `(1)), 1, 1)
  specs := specs.push ((← `(0)), 0, 1)
  for (i, reg, kind) in specs do
    let r := Lean.quote reg
    let p ← `(copyStart $v $l + BitVec.ofNat 64 $offset)
    let n := if kind == 0 then 5 else storeLen
    let len := Lean.quote n
    let nextOff := Lean.quote (start + off + n)
    let step ← if kind == 0 then
      `(tactic| advance_then (mov_r64_m64_effect_step $p 0x48
        (by simp [RexWPrefix]) $r (copyLoadAm $v $i) (by decide +kernel) rfl rfl))
      else `(tactic| advance_then (mov_m64_r64_effect_step $p 0x48
        (by simp [RexWPrefix]) $r (copyStoreAm $v $i) (by decide +kernel) rfl rfl))
    steps := steps.push step
    steps := steps.push (← `(tactic| try (case sub =>
      exact codeRange_slice_subset (copyStart $v $l) (copyBytes $v $l) $offset $len)))
    if kind == 0 then
      steps := steps.push (← `(tactic| case mid =>
        intro s t hP hH hO
        refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm)
          (by x86_addr_obs) ?_, ?_, ?_⟩
        · x86_norm
          exact hP.readable $i (by decide)
        · apply Effect.Avoids.of_noMem
          x86_norm
          simp [Component.Covers]
        · x86_norm
          exact boundary_ne_program $outside (inProgram_of_textOffset $nextOff (by decide))))
    else
      steps := steps.push (← `(tactic| case mid =>
        intro s t hP hH hO
        refine ⟨StorePre.of_holds hH (hO true) (by x86_norm)
          (by x86_addr_obs) ?_ ?_, ?_, ?_⟩
        · x86_norm
          exact hP.writable $i (by decide)
        · x86_norm
          intro a ha b hb
          have separate := hP.codeApart $i (by decide) a ha ($offset+b) (by
            change b < $len at hb
            change $offset + b < $totalT
            omega)
          x86_norm at separate
          simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat,
            ← BitVec.add_assoc, BitVec.reduceAdd] using separate
        · apply Effect.Local.avoids (by x86_local) (hO true)
          apply Effect.avoids_codeRange
          x86_norm
          exact hP.codeApart $i (by decide)
        · x86_norm
          exact boundary_ne_program $outside (inProgram_of_textOffset $nextOff (by decide))))
    off := off + n
    offset := Lean.quote off
  let p ← `(copyStart $v $l + BitVec.ofNat 64 $offset)
  let nextOff := Lean.quote (start + off + storeLen)
  steps := steps.push (← `(tactic| advance_then (lea_r64_effect_step $p
    0x48 (by simp [RexWPrefix]) 6 (copyStoreAm $v 0) (by decide +kernel) rfl rfl)))
  steps := steps.push (← `(tactic| try (case sub =>
    exact codeRange_slice_subset (copyStart $v $l) (copyBytes $v $l) $offset (copyStoreLen $v))))
  steps := steps.push (← `(tactic| case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · x86_norm
      simp [Component.Covers]
    · x86_norm
      exact boundary_ne_program $outside (inProgram_of_textOffset $nextOff (by decide))))
  off := off + storeLen
  offset := Lean.quote off
  let nextOff := Lean.quote (start + off + 5)
  let p ← `(copyStart $v $l + BitVec.ofNat 64 $offset)
  steps := steps.push (← `(tactic| advance_then (mov_r32_imm32_effect_step $p 0xba (by decide) 1)))
  steps := steps.push (← `(tactic| try (case sub =>
    exact codeRange_slice_subset (copyStart $v $l) (copyBytes $v $l) $offset 5)))
  steps := steps.push (← `(tactic| case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · x86_norm
      simp [Component.Covers]
    · x86_norm
      exact boundary_ne_program $outside (inProgram_of_textOffset $nextOff (by decide))))
  off := off + 5
  offset := Lean.quote off
  let nextOff := Lean.quote (start + off + 3)
  let p ← `(copyStart $v $l + BitVec.ofNat 64 $offset)
  steps := steps.push (← `(tactic| advance_then (mov_r64_r64_effect_step $p
    0x4c $hashModrm (by simp [RexWPrefix]) rfl)))
  steps := steps.push (← `(tactic| try (case sub =>
    exact codeRange_slice_subset (copyStart $v $l) (copyBytes $v $l) $offset 3)))
  steps := steps.push (← `(tactic| case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), Effect.Avoids.of_noMem ?_ _, ?_⟩
    · x86_norm
      simp [Component.Covers]
    · x86_norm
      exact boundary_ne_program $outside (inProgram_of_textOffset $nextOff (by decide))))
  steps := steps.push (← `(tactic| advance_finish [copyEffect, List.map_cons, List.map_nil]))
  `(tactic| ($[$steps:tactic]*))

set_option maxHeartbeats 2500000 in
theorem copy_run [Bindings] (v : Variant) (last : Bool)
    (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (CopyPre v last) (codeRange (copyStart v last) (copyBytes v last))
      (Effect.post (copyEffect v last)) := by
  cases v with
  | key => cases last with
    | false => stream_padding_copy_chain key, first
    | true => stream_padding_copy_chain key, last
  | hmac => cases last with
    | false => stream_padding_copy_chain hmac, first
    | true => stream_padding_copy_chain hmac, last
  | simpleInner => cases last with
    | false => stream_padding_copy_chain simpleInner, first
    | true => stream_padding_copy_chain simpleInner, last
  | simpleOuter => cases last with
    | false => stream_padding_copy_chain simpleOuter, first
    | true => stream_padding_copy_chain simpleOuter, last

end Hkdf.Proofs.Common.StreamPadding.Stages
