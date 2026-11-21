import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.MR.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.MovStore.Encode
import Sha2.Proofs.Common.Machine.Relocatable
import Sha2.Proofs.Common.EffectCompose.Memory
import Sha2.Proofs.Common.Instructions.CrossPageStore.Immediate
import Sha2.Proofs.Common.Instructions.ByteStore.Legacy
import Sha2.Proofs.Common.Instructions.AddByte.Effect
import Sha2.Proofs.Common.Instructions.RepMovsq.Memory
import X86Proofs.Instructions.Mov.Encode
import X86Proofs.Instructions.MovLoad.Encode
import X86Proofs.Instructions.Lea.Encode
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Inc.Generated.M.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Blocks

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Instructions

structure Registers where
  source : BitVec 4
  length : BitVec 4
  tail : BitVec 4
  remaining : BitVec 4

def readReg (s : RamState) (r : BitVec 4) : BitVec 64 :=
  (.reg (r.setWidth 5) : Operand 64).read s

inductive Displacement where
  | short (value : BitVec 8)
  | near (value : BitVec 32)

def Displacement.value : Displacement → BitVec 64
  | .short value => value.signExtend 64
  | .near value => value.signExtend 64

inductive Block where
  | loadPair (index source length : BitVec 4) (pointerSlot lengthSlot : Disp)
  | loadTail (tail : BitVec 4) (address : AddrMode)
  | prepare (registers : Registers)
  | test (register : BitVec 4)
  | branch (condition : BitVec 4) (displacement : Displacement)
  | jump (displacement : Displacement)
  | move (destination source : BitVec 4)
  | address (destination : BitVec 4) (source : AddrMode)
  | constant (destination : BitVec 4) (value : BitVec 32)
  | count (remaining : BitVec 4)
  | splitTail (source remaining : BitVec 4)
  | addTail (destination source : BitVec 4)
  | storeTail (source : BitVec 4) (address : AddrMode)
  | clearTail (address : AddrMode)
  | incrementBlocks (address : AddrMode)
  | addBlocks (address : AddrMode)
  | incrementIndex (index : BitVec 4)
  | compareIndex (index count : BitVec 4)
  | clone
  | addImmediate (destination : BitVec 4) (value : BitVec 8)
  | compareIndexStack (index : BitVec 4) (slot : Disp)
  | zero (destination : BitVec 4)
  | spill (source : BitVec 4) (slot : Disp)
  | compareZeroStack (slot : Disp) (value : BitVec 8)

def bytePrefix (register : BitVec 4) (am : AddrMode) : List UInt8 :=
  if register.toNat < 4 ∧ am.rexX = 0 ∧ am.rexB = 0 then []
  else [am.rexByte false register]

def loadBytePrefix (register : BitVec 4) (am : AddrMode) : List UInt8 :=
  if register.toNat < 8 ∧ am.rexX = 0 ∧ am.rexB = 0 then []
  else [am.rexByte false register]

def bytes : Block → List UInt8
  | .loadPair index source length pointerSlot lengthSlot =>
      encodeMovR64M64 0 (.sib 4 none 0 pointerSlot) ++
      encodeMovR64M64 source (.sib 0 (some index) 3 .none) ++
      encodeMovR64M64 0 (.sib 4 none 0 lengthSlot) ++
      encodeMovR64M64 length (.sib 0 (some index) 3 .none)
  | .loadTail tail am => loadBytePrefix tail am ++ [0x0f, 0xb6, am.modrm (regLow tail)] ++ am.tail
  | .prepare r => encodeMovR32Imm32 2 64 ++ encodeSubR64R64 2 r.tail ++
      encodeMovR64R64 r.remaining r.length ++ encodeSubR64R64 r.remaining 2
  | .test r => encodeTestR64R64 r r
  | .branch cc (.short disp) => jccOpcode8 cc :: immBytes 8 disp
  | .branch cc (.near disp) => 0x0f :: jccOpcode32 cc :: immBytes 32 disp
  | .jump (.short disp) => 0xeb :: immBytes 8 disp
  | .jump (.near disp) => 0xe9 :: immBytes 32 disp
  | .move dst src => encodeMovR64R64 dst src
  | .address dst am => encodeLeaR64M dst am
  | .constant dst value => encodeMovR32Imm32 dst value
  | .count rest => encodeMovR64R64 2 rest ++ encodeShrR64Imm8 2 6
  | .splitTail source rest => encodeMovR64R64 0 rest ++
      encodeMovR64Imm64 1 0x7fffffffffffffc0 ++ encodeAndR64R64 0 1 ++
      encodeAndR32Imm8 rest 63 ++ encodeAddR64R64 source 0
  | .addTail dst src =>
      [UInt8.ofNat (0x40 + 4 * (src.toNat / 8) + dst.toNat / 8), 0,
        UInt8.ofNat (0xc0 + 8 * (src.toNat % 8) + dst.toNat % 8)]
  | .storeTail src am => bytePrefix src am ++ [0x88, am.modrm (regLow src)] ++ am.tail
  | .clearTail am => [0xc6, am.modrm 0] ++ am.tail ++ [0]
  | .incrementBlocks am => encodeIncM64 am
  | .addBlocks am => encodeAddM64R64 2 am
  | .incrementIndex index => encodeIncR64 index
  | .compareIndex index count => encodeCmpR64R64 count index
  | .clone => [0xf3, 0x48, 0xa5]
  | .addImmediate dst value => encodeAddR64Imm8 dst value
  | .compareIndexStack index slot => encodeCmpM64R64 index (.sib 4 none 0 slot)
  | .zero dst => encodeXorR32R32 dst dst
  | .spill src slot => encodeMovM64R64 src (.sib 4 none 0 slot)
  | .compareZeroStack slot value => encodeCmpM64Imm8 (.sib 4 none 0 slot) value

structure LoadPairPre (p : BitVec 64) (index source length : BitVec 4)
    (pointerSlot lengthSlot : Disp) (s : RamState) : Prop where
  rip : s.RIP = p
  distinct : [index, source, length, 0, 4].Pairwise (· ≠ ·)
  validPointer : (AddrMode.sib 4 none 0 pointerSlot).Valid
  validLength : (AddrMode.sib 4 none 0 lengthSlot).Valid
  validIndex : (AddrMode.sib 0 (some index) 3 .none).Valid
  pointerSlotRead : MemReadable s (rspOf s + pointerSlot.value) 8
  lengthSlotRead : MemReadable s (rspOf s + lengthSlot.value) 8
  pointerRead : MemReadable s
    (memLoad s.external (rspOf s + pointerSlot.value) 64 + (readReg s index <<< 3)) 8
  lengthRead : MemReadable s
    (memLoad s.external (rspOf s + lengthSlot.value) 64 + (readReg s index <<< 3)) 8

structure LoadTailPre (p : BitVec 64) (r : BitVec 4) (am : AddrMode) (s : RamState) : Prop where
  rip : s.RIP = p
  valid : am.Valid
  readable : MemReadable s (am.addr s (p + BitVec.ofNat 64 (bytes (.loadTail r am)).length)) 1

structure StorePre (p : BitVec 64) (b : Block) (am : AddrMode) (size : Nat)
    (s : RamState) : Prop where
  rip : s.RIP = p
  valid : am.Valid
  writable : CrossPageStore.Writable s
    (am.addr s (p + BitVec.ofNat 64 (bytes b).length)) size
  apart : RangeApart (am.addr s (p + BitVec.ofNat 64 (bytes b).length)) size p (bytes b).length

structure PreparePre (p : BitVec 64) (r : Registers) (s : RamState) : Prop where
  rip : s.RIP = p
  distinct : [r.tail, r.length, r.remaining, 2].Pairwise (· ≠ ·)

structure SplitTailPre (p : BitVec 64) (source rest : BitVec 4) (s : RamState) : Prop where
  rip : s.RIP = p
  distinct : [source, rest, 0, 1].Pairwise (· ≠ ·)

structure StackReadPre (p : BitVec 64) (slot : Disp) (s : RamState) : Prop where
  rip : s.RIP = p
  valid : (AddrMode.sib 4 none 0 slot).Valid
  readable : MemReadable s (rspOf s + slot.value) 8

def Pre (p : BitVec 64) : Block → RamState → Prop
  | .loadPair i src len pointers lengths => LoadPairPre p i src len pointers lengths
  | .loadTail r am => LoadTailPre p r am
  | .prepare r => PreparePre p r
  | .address _ am => fun s => s.RIP = p ∧ am.Valid
  | .splitTail src rest => SplitTailPre p src rest
  | b@(.storeTail _ am) => StorePre p b am 1
  | b@(.clearTail am) => fun s => StorePre p b am 1 s ∧ am.rexX = 0 ∧ am.rexB = 0
  | b@(.incrementBlocks am) => StorePre p b am 8
  | b@(.addBlocks am) => StorePre p b am 8
  | .clone => fun s => RepMovsq.RepMovsqPre p s ∧ (rcx.read s).toNat = 13
  | .compareIndexStack _ slot | .compareZeroStack slot _ => StackReadPre p slot
  | b@(.spill _ slot) => StorePre p b (.sib 4 none 0 slot) 8
  | _ => fun s => s.RIP = p

def effect (p : BitVec 64) (b : Block) (s : RamState) : Effect :=
  let nextPC := p + BitVec.ofNat 64 (bytes b).length
  match b with
  | .loadPair i src len pointers lengths =>
      { rip := nextPC, writes := [
          ⟨(.reg 0 : Operand 64), memLoad s.external (rspOf s + lengths.value) 64⟩,
          ⟨(.reg (src.setWidth 5) : Operand 64), memLoad s.external
            (memLoad s.external (rspOf s + pointers.value) 64 + (readReg s i <<< 3)) 64⟩,
          ⟨(.reg (len.setWidth 5) : Operand 64), memLoad s.external
            (memLoad s.external (rspOf s + lengths.value) 64 + (readReg s i <<< 3)) 64⟩] }
  | .loadTail r am => { rip := nextPC, writes := [
      ⟨(.reg (r.setWidth 5) : Operand 64), (memLoad s.external (am.addr s nextPC) 8).setWidth 64⟩] }
  | .prepare r =>
      { rip := nextPC, writes := [⟨(.reg 2 : Operand 64), 64 - readReg s r.tail⟩,
          ⟨(.reg (r.remaining.setWidth 5) : Operand 64), readReg s r.length - (64 - readReg s r.tail)⟩]
        flags := some (.ofStatusFlags (subSpec (readReg s r.length) (64 - readReg s r.tail)).2) }
  | .test r => testR64R64Effect p (r.setWidth 5) (r.setWidth 5) s
  | .branch cc disp => jccEffect p (bytes b).length cc disp.value s
  | .jump disp => jmpEffect p (bytes b).length disp.value
  | .move dst src => movR64R64Effect p (dst.setWidth 5) (src.setWidth 5) s
  | .address dst am => leaR64Effect p (dst.setWidth 5) am s
  | .constant dst value => movR32Imm32Effect p (bytes b).length (dst.setWidth 5) value s
  | .count rest =>
      { rip := nextPC, writes := [⟨(.reg 2 : Operand 64), readReg s rest >>> 6⟩]
        flags := some (shrFlags (StatusFlags.ofRFLAGS s.RFLAGS) 6 (readReg s rest)) }
  | .splitTail source rest =>
      { rip := nextPC, writes := [
          ⟨(.reg 0 : Operand 64), readReg s rest &&& 0x7fffffffffffffc0⟩,
          ⟨(.reg 1 : Operand 64), 0x7fffffffffffffc0⟩,
          ⟨(.reg (rest.setWidth 5) : Operand 64), ((readReg s rest).setWidth 32 &&& 63).setWidth 64⟩,
          ⟨(.reg (source.setWidth 5) : Operand 64),
            readReg s source + (readReg s rest &&& 0x7fffffffffffffc0)⟩]
        flags := some ⟨none, none, none, none, none, none⟩ }
  | .addTail dst src => AddByte.addR8R8Effect p (dst.setWidth 5) (src.setWidth 5) s
  | .storeTail src am => storeEffect p (bytes b).length (fun u => am.addr u nextPC)
      (fun u => (.reg (src.setWidth 5) : Operand 8).read u) s
  | .clearTail am => storeEffect p (bytes b).length (fun u => am.addr u nextPC)
      (fun _ => (0 : BitVec 8)) s
  | .incrementBlocks am => incMEffect p (bytes b).length 64 am s
  | .addBlocks am => addMREffect p (bytes b).length 64 2 am s
  | .incrementIndex i => incR64Effect p (i.setWidth 5) s
  | .compareIndex i count => cmpR64R64Effect p (count.setWidth 5) (i.setWidth 5) s
  | .clone => repMovsqEffect p s
  | .addImmediate dst value => addR64Imm8Effect p (dst.setWidth 5) value s
  | .compareIndexStack index slot => cmpMREffect p (bytes b).length 64
      (index.setWidth 5) (.sib 4 none 0 slot) s
  | .zero dst => xorR32R32Effect p (bytes b).length (dst.setWidth 5) (dst.setWidth 5) s
  | .spill src slot => storeEffect p (bytes b).length
      (fun u => rspOf u + slot.value) (fun u => readReg u src) s
  | .compareZeroStack slot value => cmpMImm8Effect p (bytes b).length 64 (.sib 4 none 0 slot) value s

def Contract [Bindings] (boundary : ReturnBoundary) (p : BitVec 64) (b : Block) : Prop :=
  AdvanceTriple boundary (Pre p b) (codeRange p (bytes b)) (Effect.post (effect p b))

structure Site where
  pc : BitVec 64
  block : Block

def Site.code (site : Site) : CodeMap := codeRange site.pc (bytes site.block)

def Site.Contract [Bindings] (boundary : ReturnBoundary) (site : Site) : Prop :=
  Blocks.Contract boundary site.pc site.block

end Sha2.Proofs.Common.SHA256.Absorb.Blocks
