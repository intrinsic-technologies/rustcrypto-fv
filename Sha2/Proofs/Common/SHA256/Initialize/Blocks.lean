import Sha2.Proofs.Common.SHA256.Initialize
import Sha2.Proofs.Common.Machine.Relocatable
import Sha2.Proofs.Common.Instructions.CrossPageStore.Immediate
import X86Proofs.Instructions.Mov.Encode
import X86Proofs.Instructions.MovStore.Encode

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Initialize

variable {v : Sha2.Proofs.Wrapper.Variant}

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

structure Address where
  base : BitVec 4
  disp : Disp

def Address.mode (a : Address) : AddrMode :=
  if regLow a.base = 4 then .sib a.base none 0 a.disp else .base a.base a.disp

def Address.read (a : Address) (s : RamState) : BitVec 64 :=
  (.reg (a.base.setWidth 5) : Operand 64).read s + a.disp.value

def packedWord (i : Fin 4) (v : Sha2.Proofs.Wrapper.Variant := .sha256) : BitVec 64 :=
  (packedWords v)[i.val]!

structure WordStore (v : Sha2.Proofs.Wrapper.Variant := .sha256) where
  index : Fin 4
  register : BitVec 4
  destination : Address
  loadConstant : Bool

def WordStore.bytes (b : WordStore v) : List UInt8 :=
  (if b.loadConstant then encodeMovR64Imm64 b.register (packedWord b.index v) else []) ++
    encodeMovM64R64 b.register b.destination.mode

structure WordStore.Pre (p : BitVec 64) (b : WordStore v) (s : RamState) : Prop where
  rip : s.RIP = p
  valid : b.destination.mode.Valid
  independent : b.loadConstant = true → b.register ≠ b.destination.base
  value : b.loadConstant = false →
    (.reg (b.register.setWidth 5) : Operand 64).read s = packedWord b.index v
  writable : CrossPageStore.Writable s (b.destination.read s) 8
  apart : RangeApart (b.destination.read s) 8 p b.bytes.length

def WordStore.effect (p : BitVec 64) (b : WordStore v) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 b.bytes.length
    writes := (if b.loadConstant then
      [⟨(.reg (b.register.setWidth 5) : Operand 64), packedWord b.index v⟩] else []) ++
      [⟨(.mem (b.destination.read s) : Operand 64), packedWord b.index v⟩] }

def WordStore.Contract [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (b : WordStore v) : Prop :=
  AdvanceTriple boundary (b.Pre p) (codeRange p b.bytes) (Effect.post (b.effect p))

structure Clear where
  counter : Address
  tail : Address

def Clear.bytes (b : Clear) : List UInt8 :=
  encodeMovM64Imm32 b.counter.mode 0 ++
    [0xc6, b.tail.mode.modrm 0] ++ b.tail.mode.tail ++ [0]

structure Clear.Pre (p : BitVec 64) (b : Clear) (s : RamState) : Prop where
  rip : s.RIP = p
  counterValid : b.counter.mode.Valid
  tailValid : b.tail.mode.Valid
  tailRexX : b.tail.mode.rexX = 0
  tailRexB : b.tail.mode.rexB = 0
  counterWritable : CrossPageStore.Writable s (b.counter.read s) 8
  counterApart : RangeApart (b.counter.read s) 8 p b.bytes.length
  tailWritable : MemWritable s (b.tail.read s) 1
  tailApart : RangeApart (b.tail.read s) 1 p b.bytes.length
  separate : RangeApart (b.counter.read s) 8 (b.tail.read s) 1

def Clear.effect (p : BitVec 64) (b : Clear) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 b.bytes.length
    writes := [⟨(.mem (b.counter.read s) : Operand 64), 0⟩,
      ⟨(.mem (b.tail.read s) : Operand 8), 0⟩] }

def Clear.Contract [Bindings] (boundary : ReturnBoundary) (p : BitVec 64)
    (b : Clear) : Prop :=
  AdvanceTriple boundary (b.Pre p) (codeRange p b.bytes) (Effect.post (b.effect p))

end Sha2.Proofs.Common.SHA256.Initialize
