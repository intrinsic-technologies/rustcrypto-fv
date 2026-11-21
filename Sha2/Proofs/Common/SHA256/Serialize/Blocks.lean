import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Machine.Relocatable
import Sha2.Proofs.Common.SHA256.Compression.Bswap32
import Sha2.Proofs.Common.Instructions.CrossPageStore.Compose
import Sha2.Proofs.Common.Instructions.CrossPageStore.Legacy

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Serialize

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Compression (bswap32)

inductive HashOffset where
  | at64
  | at72
  | at176

def HashOffset.value : HashOffset → Nat
  | .at64 => 64
  | .at72 => 72
  | .at176 => 176

inductive OutputRegister where
  | rbx
  | r13
  | r12
  | r11
  | r10

def OutputRegister.value : OutputRegister → BitVec 5
  | .rbx => 3
  | .r13 => 13
  | .r12 => 12
  | .r11 => 11
  | .r10 => 10

inductive Block where
  | loadSwap (offset : HashOffset) (truncated : Bool := false)
  | store (output : OutputRegister) (truncated : Bool := false)

def bytes : Block → List UInt8
  | .loadSwap .at64 truncated =>
    let full := [0x8b, 0x44, 0x24, 0x40, 0x8b, 0x4c, 0x24, 0x44, 0xf, 0xc8, 0xf, 0xc9, 0x8b, 0x54, 0x24, 0x48, 0xf, 0xca, 0x8b, 0x74, 0x24, 0x4c, 0xf, 0xce, 0x8b, 0x7c, 0x24, 0x50, 0xf, 0xcf, 0x44, 0x8b, 0x44, 0x24, 0x54, 0x41, 0xf, 0xc8, 0x44, 0x8b, 0x4c, 0x24, 0x58, 0x41, 0xf, 0xc9, 0x44, 0x8b, 0x54, 0x24, 0x5c, 0x41, 0xf, 0xca]
    if truncated then full.take 46 else full
  | .loadSwap .at72 truncated =>
    let full := [0x8b, 0x44, 0x24, 0x48, 0x8b, 0x4c, 0x24, 0x4c, 0xf, 0xc8, 0xf, 0xc9, 0x8b, 0x54, 0x24, 0x50, 0xf, 0xca, 0x8b, 0x74, 0x24, 0x54, 0xf, 0xce, 0x8b, 0x7c, 0x24, 0x58, 0xf, 0xcf, 0x44, 0x8b, 0x44, 0x24, 0x5c, 0x41, 0xf, 0xc8, 0x44, 0x8b, 0x4c, 0x24, 0x60, 0x41, 0xf, 0xc9, 0x44, 0x8b, 0x54, 0x24, 0x64, 0x41, 0xf, 0xca]
    if truncated then full.take 46 else full
  | .loadSwap .at176 truncated =>
    let full := [0x8b, 0x84, 0x24, 0xb0, 0x0, 0x0, 0x0, 0x8b, 0x8c, 0x24, 0xb4, 0x0, 0x0, 0x0, 0xf, 0xc8, 0xf, 0xc9, 0x8b, 0x94, 0x24, 0xb8, 0x0, 0x0, 0x0, 0xf, 0xca, 0x8b, 0xb4, 0x24, 0xbc, 0x0, 0x0, 0x0, 0xf, 0xce, 0x8b, 0xbc, 0x24, 0xc0, 0x0, 0x0, 0x0, 0xf, 0xcf, 0x44, 0x8b, 0x84, 0x24, 0xc4, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc8, 0x44, 0x8b, 0x8c, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x41, 0xf, 0xc9, 0x44, 0x8b, 0x94, 0x24, 0xcc, 0x0, 0x0, 0x0, 0x41, 0xf, 0xca]
    if truncated then full.take 67 else full
  | .store .rbx truncated =>
    let full := [0x89, 0x3, 0x89, 0x4b, 0x4, 0x89, 0x53, 0x8, 0x89, 0x73, 0xc, 0x89, 0x7b, 0x10, 0x44, 0x89, 0x43, 0x14, 0x44, 0x89, 0x4b, 0x18, 0x44, 0x89, 0x53, 0x1c]
    if truncated then full.take 22 else full
  | .store .r13 truncated =>
    let full := [0x41, 0x89, 0x45, 0x0, 0x41, 0x89, 0x4d, 0x4, 0x41, 0x89, 0x55, 0x8, 0x41, 0x89, 0x75, 0xc, 0x41, 0x89, 0x7d, 0x10, 0x45, 0x89, 0x45, 0x14, 0x45, 0x89, 0x4d, 0x18, 0x45, 0x89, 0x55, 0x1c]
    if truncated then full.take 28 else full
  | .store .r12 truncated =>
    let full := [0x41, 0x89, 0x4, 0x24, 0x41, 0x89, 0x4c, 0x24, 0x4, 0x41, 0x89, 0x54, 0x24, 0x8, 0x41, 0x89, 0x74, 0x24, 0xc, 0x41, 0x89, 0x7c, 0x24, 0x10, 0x45, 0x89, 0x44, 0x24, 0x14, 0x45, 0x89, 0x4c, 0x24, 0x18, 0x45, 0x89, 0x54, 0x24, 0x1c]
    if truncated then full.take 34 else full
  | .store .r11 truncated =>
    let full := [0x41, 0x89, 0x3, 0x41, 0x89, 0x4b, 0x4, 0x41, 0x89, 0x53, 0x8, 0x41, 0x89, 0x73, 0xc, 0x41, 0x89, 0x7b, 0x10, 0x45, 0x89, 0x43, 0x14, 0x45, 0x89, 0x4b, 0x18, 0x45, 0x89, 0x53, 0x1c]
    if truncated then full.take 27 else full

  | .store .r10 truncated =>
    let full := [0x41, 0x89, 0x2, 0x41, 0x89, 0x4a, 0x4, 0x41, 0x89, 0x52, 0x8, 0x41, 0x89, 0x72, 0xc, 0x41, 0x89, 0x7a, 0x10, 0x45, 0x89, 0x42, 0x14, 0x45, 0x89, 0x4a, 0x18, 0x45, 0x89, 0x52, 0x1c]
    if truncated then full.take 27 else full

structure LoadPre (p : BitVec 64) (offset : HashOffset) (s : RamState) (truncated : Bool := false) : Prop where
  rip : s.RIP = p
  read0 : MemReadable s (rspOf s + BitVec.ofNat 64 (offset.value + 0)) 4
  read1 : MemReadable s (rspOf s + BitVec.ofNat 64 (offset.value + 4)) 4
  read2 : MemReadable s (rspOf s + BitVec.ofNat 64 (offset.value + 8)) 4
  read3 : MemReadable s (rspOf s + BitVec.ofNat 64 (offset.value + 12)) 4
  read4 : MemReadable s (rspOf s + BitVec.ofNat 64 (offset.value + 16)) 4
  read5 : MemReadable s (rspOf s + BitVec.ofNat 64 (offset.value + 20)) 4
  read6 : MemReadable s (rspOf s + BitVec.ofNat 64 (offset.value + 24)) 4
  read7 : if truncated then True else MemReadable s (rspOf s + BitVec.ofNat 64 (offset.value + 28)) 4

structure StorePre (p : BitVec 64) (output : OutputRegister) (s : RamState) (truncated : Bool := false) : Prop where
  rip : s.RIP = p
  write0 : Common.Instructions.CrossPageStore.Writable s ((.reg output.value : Operand 64).read s + 0) 4
  apart0 : RangeApart ((.reg output.value : Operand 64).read s + 0) 4 p (bytes (.store output truncated)).length
  write1 : Common.Instructions.CrossPageStore.Writable s ((.reg output.value : Operand 64).read s + 4) 4
  apart1 : RangeApart ((.reg output.value : Operand 64).read s + 4) 4 p (bytes (.store output truncated)).length
  write2 : Common.Instructions.CrossPageStore.Writable s ((.reg output.value : Operand 64).read s + 8) 4
  apart2 : RangeApart ((.reg output.value : Operand 64).read s + 8) 4 p (bytes (.store output truncated)).length
  write3 : Common.Instructions.CrossPageStore.Writable s ((.reg output.value : Operand 64).read s + 12) 4
  apart3 : RangeApart ((.reg output.value : Operand 64).read s + 12) 4 p (bytes (.store output truncated)).length
  write4 : Common.Instructions.CrossPageStore.Writable s ((.reg output.value : Operand 64).read s + 16) 4
  apart4 : RangeApart ((.reg output.value : Operand 64).read s + 16) 4 p (bytes (.store output truncated)).length
  write5 : Common.Instructions.CrossPageStore.Writable s ((.reg output.value : Operand 64).read s + 20) 4
  apart5 : RangeApart ((.reg output.value : Operand 64).read s + 20) 4 p (bytes (.store output truncated)).length
  write6 : Common.Instructions.CrossPageStore.Writable s ((.reg output.value : Operand 64).read s + 24) 4
  apart6 : RangeApart ((.reg output.value : Operand 64).read s + 24) 4 p (bytes (.store output truncated)).length
  write7 : if truncated then True else Common.Instructions.CrossPageStore.Writable s ((.reg output.value : Operand 64).read s + 28) 4
  apart7 : if truncated then True else RangeApart ((.reg output.value : Operand 64).read s + 28) 4 p (bytes (.store output truncated)).length

def Pre (p : BitVec 64) : Block → RamState → Prop
  | .loadSwap offset truncated => fun s => LoadPre p offset s truncated
  | .store output truncated => fun s => StorePre p output s truncated

def effect (p : BitVec 64) (block : Block) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (bytes block).length
    writes := match block with
      | .loadSwap offset truncated => [
          ⟨(.reg 0 : Operand 64), (bswap32 ((.mem (rspOf s + BitVec.ofNat 64 (offset.value + 0)) : Operand 32).read s)).setWidth 64⟩,
          ⟨(.reg 1 : Operand 64), (bswap32 ((.mem (rspOf s + BitVec.ofNat 64 (offset.value + 4)) : Operand 32).read s)).setWidth 64⟩,
          ⟨(.reg 2 : Operand 64), (bswap32 ((.mem (rspOf s + BitVec.ofNat 64 (offset.value + 8)) : Operand 32).read s)).setWidth 64⟩,
          ⟨(.reg 6 : Operand 64), (bswap32 ((.mem (rspOf s + BitVec.ofNat 64 (offset.value + 12)) : Operand 32).read s)).setWidth 64⟩,
          ⟨(.reg 7 : Operand 64), (bswap32 ((.mem (rspOf s + BitVec.ofNat 64 (offset.value + 16)) : Operand 32).read s)).setWidth 64⟩,
          ⟨(.reg 8 : Operand 64), (bswap32 ((.mem (rspOf s + BitVec.ofNat 64 (offset.value + 20)) : Operand 32).read s)).setWidth 64⟩,
          ⟨(.reg 9 : Operand 64), (bswap32 ((.mem (rspOf s + BitVec.ofNat 64 (offset.value + 24)) : Operand 32).read s)).setWidth 64⟩] ++ (if truncated then [] else [
          ⟨(.reg 10 : Operand 64), (bswap32 ((.mem (rspOf s + BitVec.ofNat 64 (offset.value + 28)) : Operand 32).read s)).setWidth 64⟩])
      | .store output truncated => [
          ⟨(.mem ((.reg output.value : Operand 64).read s + 0) : Operand 32), (.reg 0 : Operand 32).read s⟩,
          ⟨(.mem ((.reg output.value : Operand 64).read s + 4) : Operand 32), (.reg 1 : Operand 32).read s⟩,
          ⟨(.mem ((.reg output.value : Operand 64).read s + 8) : Operand 32), (.reg 2 : Operand 32).read s⟩,
          ⟨(.mem ((.reg output.value : Operand 64).read s + 12) : Operand 32), (.reg 6 : Operand 32).read s⟩,
          ⟨(.mem ((.reg output.value : Operand 64).read s + 16) : Operand 32), (.reg 7 : Operand 32).read s⟩,
          ⟨(.mem ((.reg output.value : Operand 64).read s + 20) : Operand 32), (.reg 8 : Operand 32).read s⟩,
          ⟨(.mem ((.reg output.value : Operand 64).read s + 24) : Operand 32), (.reg 9 : Operand 32).read s⟩] ++ (if truncated then [] else [
          ⟨(.mem ((.reg output.value : Operand 64).read s + 28) : Operand 32), (.reg 10 : Operand 32).read s⟩]) }

attribute [local x86_compose] HashOffset.value OutputRegister.value bytes
  Sha2.Proofs.Common.SHA256.Compression.encodeBswapR32
  BitVec.setWidth_setWidth_of_le BitVec.setWidth_eq gprNumber
attribute [local x86_pre] Common.Instructions.CrossPageStore.storePre_of_holds

macro "sha256_serialize_load_steps " base:num "," count:num "," pc:term "," outside:term "," inside:term : tactic => do
  let mut pos := 0
  let order := [(true, 0), (true, 1), (false, 0), (false, 1)] ++
    (List.range (count.getNat - 2)).flatMap (fun i => [(true, i + 2), (false, i + 2)])
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  for (load, i) in order do
    let reg := [0, 1, 2, 6, 7, 8, 9, 10][i]!
    let disp := base.getNat + 4 * i
    let am ← if disp < 128 then `(AddrMode.sib 4 none 0 (.d8 $(Lean.quote disp)))
      else `(AddrMode.sib 4 none 0 (.d32 $(Lean.quote disp)))
    let addr ← if pos = 0 then pure pc else `($pc + $(Lean.quote pos))
    let step ← if !load then
      `(Common.SHA256.Compression.bswap_r32_effect_step $addr $(Lean.quote reg))
      else if reg < 8 then
        `(Common.Instructions.LegacyLoad.mov_r32_m32_legacy_effect_step
          $addr $(Lean.quote (reg % 8)) $am (by decide) rfl rfl)
      else `(mov_r32_m32_effect_step $addr 0x44 (by simp [RexNoWPrefix])
        $(Lean.quote (reg % 8)) $am (by decide) rfl rfl)
    let len := if load then (if base.getNat < 128 then 4 else 7) + (if i < 5 then 0 else 1)
      else if i < 5 then 2 else 3
    let first := pos = 0
    pos := pos + len
    let hn ← `(boundary_ne_program $outside ($inside $(Lean.quote pos) (by decide)))
    steps := steps.push (← if first then `(tactic| advance_reloc_begin $step next $hn)
      else `(tactic| advance_reloc_then $step next $hn))
  let mut result ← `(tactic| (advance_finish [effect, HashOffset.value, bytes]))
  for step in steps.reverse do
    result ← `(tactic| ($step:tactic; $result:tactic))
  pure result

macro "sha256_serialize_store_steps " output:num "," count:num "," pc:term "," outside:term "," inside:term : tactic => do
  let mut pos := 0
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  for i in List.range count.getNat do
    let reg := [0, 1, 2, 6, 7, 8, 9, 10][i]!
    let dest := output.getNat
    let disp ← if i = 0 && dest != 13 then `(Disp.none) else `(Disp.d8 $(Lean.quote (4 * i)))
    let am ← if dest = 12 then `(AddrMode.sib 12 none 0 $disp)
      else `(AddrMode.base $(Lean.quote dest) $disp)
    let addr ← if pos = 0 then pure pc else `($pc + $(Lean.quote pos))
    let step ← if dest = 3 && reg < 8 then
      `(Common.Instructions.CrossPageStore.mov_m32_r32_legacy_effect_step_any
        $addr $(Lean.quote (reg % 8)) $am (by decide) rfl rfl)
      else
        let rex := 0x40 + (if dest < 8 then 0 else 1) + (if reg < 8 then 0 else 4)
        `(Common.Instructions.CrossPageStore.mov_m32_r32_effect_step_any
          $addr $(Lean.quote rex) (by simp [RexNoWPrefix]) $(Lean.quote (reg % 8))
          $am (by decide) rfl rfl)
    let len := 2 + (if dest = 3 && reg < 8 then 0 else 1) +
      (if dest = 12 then 1 else 0) + (if i = 0 && dest != 13 then 0 else 1)
    let canonical ← if dest = 3 && reg < 8 then
      `(Common.Instructions.CrossPageStore.movM32R32LegacyEffect $addr $(Lean.quote reg) $am)
      else `(movM32R32Effect $addr $(Lean.quote reg) $am)
    let step ← `(show StepEffect _ _ $canonical from $step)
    let first := pos = 0
    pos := pos + len
    let hn ← `(boundary_ne_program $outside ($inside $(Lean.quote pos) (by decide)))
    steps := steps.push (← if first then `(tactic| advance_reloc_begin $step next $hn)
      else `(tactic| advance_reloc_then $step next $hn))
  let mut result ← `(tactic| (advance_finish [effect, OutputRegister.value, bytes]))
  for step in steps.reverse do
    result ← `(tactic| ($step:tactic; $result:tactic))
  pure result

set_option maxHeartbeats 2000000 in
private theorem loadSwap_at64_run [Bindings] (p : BitVec 64) (truncated : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes (.loadSwap .at64 truncated)).length) :
    AdvanceTriple boundary (Pre p (.loadSwap .at64 truncated)) (codeRange p (bytes (.loadSwap .at64 truncated)))
      (Effect.post (effect p (.loadSwap .at64 truncated))) := by
  cases truncated with
  | false => sha256_serialize_load_steps 64, 8, p, outside, inside
  | true => sha256_serialize_load_steps 64, 7, p, outside, inside

set_option maxHeartbeats 2000000 in
private theorem loadSwap_at72_run [Bindings] (p : BitVec 64) (truncated : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes (.loadSwap .at72 truncated)).length) :
    AdvanceTriple boundary (Pre p (.loadSwap .at72 truncated)) (codeRange p (bytes (.loadSwap .at72 truncated)))
      (Effect.post (effect p (.loadSwap .at72 truncated))) := by
  cases truncated with
  | false => sha256_serialize_load_steps 72, 8, p, outside, inside
  | true => sha256_serialize_load_steps 72, 7, p, outside, inside

set_option maxHeartbeats 2000000 in
private theorem loadSwap_at176_run [Bindings] (p : BitVec 64) (truncated : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes (.loadSwap .at176 truncated)).length) :
    AdvanceTriple boundary (Pre p (.loadSwap .at176 truncated)) (codeRange p (bytes (.loadSwap .at176 truncated)))
      (Effect.post (effect p (.loadSwap .at176 truncated))) := by
  cases truncated with
  | false => sha256_serialize_load_steps 176, 8, p, outside, inside
  | true => sha256_serialize_load_steps 176, 7, p, outside, inside

set_option maxHeartbeats 2000000 in
private theorem store_rbx_run [Bindings] (p : BitVec 64) (truncated : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes (.store .rbx truncated)).length) :
    AdvanceTriple boundary (Pre p (.store .rbx truncated)) (codeRange p (bytes (.store .rbx truncated)))
      (Effect.post (effect p (.store .rbx truncated))) := by
  cases truncated with
  | false => sha256_serialize_store_steps 3, 8, p, outside, inside
  | true => sha256_serialize_store_steps 3, 7, p, outside, inside

set_option maxHeartbeats 2000000 in
private theorem store_r13_run [Bindings] (p : BitVec 64) (truncated : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes (.store .r13 truncated)).length) :
    AdvanceTriple boundary (Pre p (.store .r13 truncated)) (codeRange p (bytes (.store .r13 truncated)))
      (Effect.post (effect p (.store .r13 truncated))) := by
  cases truncated with
  | false => sha256_serialize_store_steps 13, 8, p, outside, inside
  | true => sha256_serialize_store_steps 13, 7, p, outside, inside

set_option maxHeartbeats 2000000 in
private theorem store_r12_run [Bindings] (p : BitVec 64) (truncated : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes (.store .r12 truncated)).length) :
    AdvanceTriple boundary (Pre p (.store .r12 truncated)) (codeRange p (bytes (.store .r12 truncated)))
      (Effect.post (effect p (.store .r12 truncated))) := by
  cases truncated with
  | false => sha256_serialize_store_steps 12, 8, p, outside, inside
  | true => sha256_serialize_store_steps 12, 7, p, outside, inside

set_option maxHeartbeats 2000000 in
private theorem store_r11_run [Bindings] (p : BitVec 64) (truncated : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes (.store .r11 truncated)).length) :
    AdvanceTriple boundary (Pre p (.store .r11 truncated)) (codeRange p (bytes (.store .r11 truncated)))
      (Effect.post (effect p (.store .r11 truncated))) := by
  cases truncated with
  | false => sha256_serialize_store_steps 11, 8, p, outside, inside
  | true => sha256_serialize_store_steps 11, 7, p, outside, inside

set_option maxHeartbeats 2000000 in
private theorem store_r10_run [Bindings] (p : BitVec 64) (truncated : Bool) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes (.store .r10 truncated)).length) :
    AdvanceTriple boundary (Pre p (.store .r10 truncated)) (codeRange p (bytes (.store .r10 truncated)))
      (Effect.post (effect p (.store .r10 truncated))) := by
  cases truncated with
  | false => sha256_serialize_store_steps 10, 8, p, outside, inside
  | true => sha256_serialize_store_steps 10, 7, p, outside, inside

theorem run [Bindings] (p : BitVec 64) (block : Block) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p (bytes block).length) :
    AdvanceTriple boundary (Pre p block) (codeRange p (bytes block))
      (Effect.post (effect p block)) := by
  cases block with
  | loadSwap offset truncated =>
    cases offset with
    | at64 => exact loadSwap_at64_run p truncated boundary outside inside
    | at72 => exact loadSwap_at72_run p truncated boundary outside inside
    | at176 => exact loadSwap_at176_run p truncated boundary outside inside
  | store output truncated =>
    cases output with
    | rbx => exact store_rbx_run p truncated boundary outside inside
    | r13 => exact store_r13_run p truncated boundary outside inside
    | r12 => exact store_r12_run p truncated boundary outside inside
    | r11 => exact store_r11_run p truncated boundary outside inside
    | r10 => exact store_r10_run p truncated boundary outside inside

end Sha2.Proofs.Common.SHA256.Serialize
