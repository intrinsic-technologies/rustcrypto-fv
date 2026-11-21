import Sha2.Proofs.Common.SHA256.Finalize.Layout
import Sha2.Proofs.Common.SHA256.Blocks.CompressCall
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Finalize

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

def stackMode (offset : Nat) : AddrMode :=
  .sib 4 none 0 (if offset = 0 then .none else if offset < 128 then
    .d8 (BitVec.ofNat 8 offset) else .d32 (BitVec.ofNat 32 offset))

namespace Mark

def bytes (v : Variant) : List UInt8 :=
  (match v with
    | .digest => [0x4d,0x89,0xe7,0x49,0x83,0xf7,0x3f]
    | .reset | .traitFirst => [0x4c,0x89,0xfb,0x48,0x83,0xf3,0x3f]
    | .finalizeFirst => [0x4c,0x89,0xe3,0x48,0x83,0xf3,0x3f]
    | .finalizeLast | .traitLast => [0x4d,0x89,0xfe,0x49,0x83,0xf6,0x3f] : List UInt8) ++
  (match v with
    | .digest => [0x42,0xc6,0x04,0x24,0x80,0x4a,0x8d,0x3c,0x24,0x48,0xff,0xc7]
    | .reset | .traitLast => [0x42,0xc6,0x04,0x3c,0x80,0x4a,0x8d,0x3c,0x3c,0x48,0xff,0xc7]
    | .finalizeFirst => [0x42,0xc6,0x44,0x24,8,0x80,0x4a,0x8d,0x3c,0x24,0x48,0x83,0xc7,9]
    | .finalizeLast | .traitFirst =>
      [0x42,0xc6,0x44,0x3c,112,0x80,0x4a,0x8d,0x3c,0x3c,0x48,0x83,0xc7,113] : List UInt8) ++
  ([0x31,0xf6] : List UInt8) ++
  (match v with
    | .digest => [0x4c,0x89,0xfa]
    | .reset | .finalizeFirst | .traitFirst => [0x48,0x89,0xda]
    | .finalizeLast | .traitLast => [0x4c,0x89,0xf2] : List UInt8)

def address (v : Variant) (s : RamState) : BitVec 64 :=
  rspOf s + BitVec.ofNat 64 v.buffer.value + (.reg v.registers.tail : Operand 64).read s

structure Pre (p : BitVec 64) (v : Variant) (s : RamState) : Prop where
  rip : s.RIP = p
  writable : MemWritable s (address v s) 1
  apart : RangeApart (address v s) 1 p (bytes v).length

def effect (p : BitVec 64) (v : Variant) (s : RamState) : Effect :=
  let count := (.reg v.registers.tail : Operand 64).read s ^^^ 63
  { rip := p + BitVec.ofNat 64 (bytes v).length
    writes := [⟨(.reg v.padReg : Operand 64), count⟩,
      ⟨(.mem (address v s) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), address v s + 1⟩,
      ⟨(.reg 6 : Operand 64), 0⟩, ⟨(.reg 2 : Operand 64), count⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

end Mark

namespace Branch

def comparisonBytes (v : Variant) : List UInt8 :=
  (match v with
    | .digest => [0x49,0x83,0xff,7]
    | .finalizeLast | .traitLast => [0x49,0x83,0xfe,7]
    | _ => [0x48,0x83,0xfb,7] : List UInt8) ++
  (if v = .reset then encodeLeaR64M 3 (stackMode 64) else [])

def bytes (v : Variant) (disp : BitVec 32) : List UInt8 :=
  comparisonBytes v ++ [0x0f,0x87] ++ immBytes 32 disp

def effect (p : BitVec 64) (v : Variant) (disp : BitVec 32) (s : RamState) : Effect :=
  { rip := if ((.reg v.padReg : Operand 64).read s).toNat < 8 then
      p + BitVec.ofNat 64 (bytes v disp).length
    else branchTarget (p + BitVec.ofNat 64 (comparisonBytes v).length) 6 (disp.signExtend 64)
    writes := if v = .reset then [⟨(.reg 3 : Operand 64), rspOf s + 64⟩] else []
    flags := some ⟨none,none,none,none,none,none⟩ }

end Branch

namespace FirstHead

def bytes (v : Variant) : List UInt8 :=
  encodeMovR64M64 0 (stackMode (v.buffer.value + 56)) ++
    encodeMovM64R64 0 (stackMode (v.scratch + 56))

structure Pre (p : BitVec 64) (v : Variant) (s : RamState) : Prop where
  rip : s.RIP = p
  readable : MemReadable s (rspOf s + BitVec.ofNat 64 (v.buffer.value + 56)) 8
  writable : MemWritable s (rspOf s + BitVec.ofNat 64 (v.scratch + 56)) 8
  apart : RangeApart (rspOf s + BitVec.ofNat 64 (v.scratch + 56)) 8 p (bytes v).length

def effect (p : BitVec 64) (v : Variant) (s : RamState) : Effect :=
  let value := memLoad s.external (rspOf s + BitVec.ofNat 64 (v.buffer.value + 56)) 64
  { rip := p + BitVec.ofNat 64 (bytes v).length
    writes := [⟨(.reg 0 : Operand 64), value⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.scratch + 56)) : Operand 64), value⟩] }

end FirstHead

namespace Lower

def bytes (v : Variant) : List UInt8 :=
  ([48,40,32,24,16] : List Nat).flatMap (fun i =>
    encodeMovR64M64 0 (stackMode (v.buffer.value + i)) ++
      encodeMovM64R64 0 (stackMode (v.scratch + i))) ++
    encodeMovR64M64 0 (stackMode v.buffer.value) ++
    encodeMovR64M64 1 (stackMode (v.buffer.value + 8)) ++
    encodeMovM64R64 1 (stackMode (v.scratch + 8)) ++
    encodeMovM64R64 0 (stackMode v.scratch)

structure Pre (p : BitVec 64) (v : Variant) (s : RamState) : Prop where
  rip : s.RIP = p
  separate : RangeApart (rspOf s + BitVec.ofNat 64 v.buffer.value) 56
    (rspOf s + BitVec.ofNat 64 v.scratch) 56
  read0 : MemReadable s (rspOf s + BitVec.ofNat 64 v.buffer.value) 8
  read8 : MemReadable s (rspOf s + BitVec.ofNat 64 (v.buffer.value + 8)) 8
  read16 : MemReadable s (rspOf s + BitVec.ofNat 64 (v.buffer.value + 16)) 8
  read24 : MemReadable s (rspOf s + BitVec.ofNat 64 (v.buffer.value + 24)) 8
  read32 : MemReadable s (rspOf s + BitVec.ofNat 64 (v.buffer.value + 32)) 8
  read40 : MemReadable s (rspOf s + BitVec.ofNat 64 (v.buffer.value + 40)) 8
  read48 : MemReadable s (rspOf s + BitVec.ofNat 64 (v.buffer.value + 48)) 8
  write0 : MemWritable s (rspOf s + BitVec.ofNat 64 v.scratch) 8
  write8 : MemWritable s (rspOf s + BitVec.ofNat 64 (v.scratch + 8)) 8
  write16 : MemWritable s (rspOf s + BitVec.ofNat 64 (v.scratch + 16)) 8
  write24 : MemWritable s (rspOf s + BitVec.ofNat 64 (v.scratch + 24)) 8
  write32 : MemWritable s (rspOf s + BitVec.ofNat 64 (v.scratch + 32)) 8
  write40 : MemWritable s (rspOf s + BitVec.ofNat 64 (v.scratch + 40)) 8
  write48 : MemWritable s (rspOf s + BitVec.ofNat 64 (v.scratch + 48)) 8
  apart0 : RangeApart (rspOf s + BitVec.ofNat 64 v.scratch) 8 p (bytes v).length
  apart8 : RangeApart (rspOf s + BitVec.ofNat 64 (v.scratch + 8)) 8 p (bytes v).length
  apart16 : RangeApart (rspOf s + BitVec.ofNat 64 (v.scratch + 16)) 8 p (bytes v).length
  apart24 : RangeApart (rspOf s + BitVec.ofNat 64 (v.scratch + 24)) 8 p (bytes v).length
  apart32 : RangeApart (rspOf s + BitVec.ofNat 64 (v.scratch + 32)) 8 p (bytes v).length
  apart40 : RangeApart (rspOf s + BitVec.ofNat 64 (v.scratch + 40)) 8 p (bytes v).length
  apart48 : RangeApart (rspOf s + BitVec.ofNat 64 (v.scratch + 48)) 8 p (bytes v).length

def effect (p : BitVec 64) (v : Variant) (s : RamState) : Effect :=
  let word := fun i => memLoad s.external (rspOf s + BitVec.ofNat 64 (v.buffer.value + i)) 64
  { rip := p + BitVec.ofNat 64 (bytes v).length
    writes := [⟨(.reg 0 : Operand 64), word 0⟩, ⟨(.reg 1 : Operand 64), word 8⟩] ++
      ([48,40,32,24,16,8,0] : List Nat).map (fun i =>
        ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.scratch + i)) : Operand 64), word i⟩) }

end Lower

namespace LastHead

def bytes (v : Variant) : List UInt8 :=
  encodeMovM64R64 (v.registers.tail.setWidth 4) (stackMode (v.buffer.value + 56)) ++
    encodeMovM64R64 (v.registers.tail.setWidth 4) (stackMode (v.scratch + 56))

structure Pre (p : BitVec 64) (v : Variant) (s : RamState) : Prop where
  rip : s.RIP = p
  writeSource : MemWritable s (rspOf s + BitVec.ofNat 64 (v.buffer.value + 56)) 8
  writeDestination : MemWritable s (rspOf s + BitVec.ofNat 64 (v.scratch + 56)) 8
  apartSource : RangeApart (rspOf s + BitVec.ofNat 64 (v.buffer.value + 56)) 8 p (bytes v).length
  apartDestination : RangeApart (rspOf s + BitVec.ofNat 64 (v.scratch + 56)) 8 p (bytes v).length

def effect (p : BitVec 64) (v : Variant) (s : RamState) : Effect :=
  let value := (.reg v.registers.tail : Operand 64).read s
  { rip := p + BitVec.ofNat 64 (bytes v).length
    writes := [⟨(.mem (rspOf s + BitVec.ofNat 64 (v.buffer.value + 56)) : Operand 64), value⟩,
      ⟨(.mem (rspOf s + BitVec.ofNat 64 (v.scratch + 56)) : Operand 64), value⟩] }

end LastHead

namespace Setup

def bytes (v : Variant) (last : Bool) : List UInt8 :=
  (if v = .traitFirst then [0x48,0x89,0xe6]
    else encodeLeaR64M 6 (stackMode v.scratch)) ++ [0xba,1,0,0,0] ++
  (match v with
    | .digest => [0x4c,0x89,0xf7]
    | .traitFirst => [0x48,0x89,0xef]
    | .finalizeFirst => if last then
        encodeLeaR64M 3 (stackMode 72) ++ [0x48,0x89,0xdf]
      else encodeLeaR64M 7 (stackMode 72)
    | _ => [0x48,0x89,0xdf])

def effect (p : BitVec 64) (v : Variant) (last : Bool) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 (bytes v last).length
    writes := [⟨(.reg 6 : Operand 64), rspOf s + BitVec.ofNat 64 v.scratch⟩,
      ⟨(.reg 2 : Operand 64), 1⟩,
      ⟨(.reg 7 : Operand 64), if v = .finalizeFirst then rspOf s + 72
        else (.reg v.hashReg : Operand 64).read s⟩] ++
      (if v = .finalizeFirst ∧ last = true then
        [⟨(.reg 3 : Operand 64), rspOf s + 72⟩] else []) }

end Setup

end Sha2.Proofs.Common.SHA256.Finalize
