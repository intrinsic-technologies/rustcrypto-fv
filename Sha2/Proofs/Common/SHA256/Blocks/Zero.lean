import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Machine.Relocatable
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Blocks.Zero

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

inductive Offset where
  | zero
  | eight
  | oneTwelve

def Offset.value : Offset → Nat
  | .zero => 0
  | .eight => 8
  | .oneTwelve => 112

def Offset.length : Offset → Nat
  | .zero => 62
  | .eight => 63
  | .oneTwelve => 78

def bytes (offset : Offset) : List UInt8 :=
  (List.range 7).flatMap fun i =>
    let n := offset.value + 8 * i
    let disp := if n = 0 then Disp.none else if n < 128 then .d8 (BitVec.ofNat 8 n)
      else .d32 (BitVec.ofNat 32 n)
    encodeMovM64Imm32 (.sib 4 none 0 disp) 0

structure Pre (p : BitVec 64) (offset : Offset) (s : RamState) : Prop where
  rip : s.RIP = p
  write0 : MemWritable s (rspOf s + BitVec.ofNat 64 offset.value) 8
  apart0 : RangeApart (rspOf s + BitVec.ofNat 64 offset.value) 8 p offset.length
  write1 : MemWritable s (rspOf s + BitVec.ofNat 64 (offset.value + 8)) 8
  apart1 : RangeApart (rspOf s + BitVec.ofNat 64 (offset.value + 8)) 8 p offset.length
  write2 : MemWritable s (rspOf s + BitVec.ofNat 64 (offset.value + 16)) 8
  apart2 : RangeApart (rspOf s + BitVec.ofNat 64 (offset.value + 16)) 8 p offset.length
  write3 : MemWritable s (rspOf s + BitVec.ofNat 64 (offset.value + 24)) 8
  apart3 : RangeApart (rspOf s + BitVec.ofNat 64 (offset.value + 24)) 8 p offset.length
  write4 : MemWritable s (rspOf s + BitVec.ofNat 64 (offset.value + 32)) 8
  apart4 : RangeApart (rspOf s + BitVec.ofNat 64 (offset.value + 32)) 8 p offset.length
  write5 : MemWritable s (rspOf s + BitVec.ofNat 64 (offset.value + 40)) 8
  apart5 : RangeApart (rspOf s + BitVec.ofNat 64 (offset.value + 40)) 8 p offset.length
  write6 : MemWritable s (rspOf s + BitVec.ofNat 64 (offset.value + 48)) 8
  apart6 : RangeApart (rspOf s + BitVec.ofNat 64 (offset.value + 48)) 8 p offset.length

def effect (p : BitVec 64) (offset : Offset) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 offset.length
    writes := [⟨(.mem (rspOf s + BitVec.ofNat 64 offset.value) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (offset.value + 8)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (offset.value + 16)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (offset.value + 24)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (offset.value + 32)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (offset.value + 40)) : Operand 64), 0⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (offset.value + 48)) : Operand 64), 0⟩] }

attribute [local x86_compose] Offset.value Offset.length

macro "sha256_zero_steps " base:num "," pc:term "," outside:term "," inside:term : tactic => do
  let mut steps : Array (Lean.TSyntax `tactic) := #[]
  let mut pos := 0
  for i in List.range 7 do
    let n := base.getNat + 8 * i
    let disp ← if n = 0 then `(Disp.none)
      else if n < 128 then `(Disp.d8 $(Lean.quote n)) else `(Disp.d32 $(Lean.quote n))
    let addr ← if i = 0 then pure pc else `($pc + $(Lean.quote pos))
    pos := pos + (if n = 0 then 8 else if n < 128 then 9 else 12)
    let step ← `(mov_m64_imm32_effect_step $addr 0x48 (by simp [RexWPrefix])
      (.sib 4 none 0 $disp) (by decide) rfl rfl 0)
    let hn ← `(boundary_ne_program $outside ($inside $(Lean.quote pos) (by decide)))
    let tactic ← if i = 0 then `(tactic| advance_reloc_begin $step next $hn)
      else `(tactic| advance_reloc_then $step next $hn)
    steps := steps.push tactic
  let mut result ← `(tactic| advance_finish [effect, Offset.value, Offset.length, BitVec.add_zero])
  for step in steps.reverse do
    result ← `(tactic| ($step:tactic; $result:tactic))
  pure result

theorem run [Bindings] (p : BitVec 64) (offset : Offset) (boundary : ReturnBoundary)
    (outside : ¬ InProgram boundary.rip) (inside : BlockInProgram p offset.length) :
    AdvanceTriple boundary (Pre p offset) (codeRange p (bytes offset))
      (Effect.post (effect p offset)) := by
  cases offset with
  | zero => sha256_zero_steps 0, p, outside, inside
  | eight => sha256_zero_steps 8, p, outside, inside
  | oneTwelve => sha256_zero_steps 112, p, outside, inside

end Sha2.Proofs.Common.SHA256.Blocks.Zero
