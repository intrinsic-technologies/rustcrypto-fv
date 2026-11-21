import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Wrapper512.Absorb.Mathematics

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb.Blocks

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper Sha2.Proofs.Wrapper512 Sha2.Proofs.Wrapper512.Absorb

structure Input [Bindings] (v : Variant) (initial s : RamState) (inputs : Array Program.Input)
    (index consumed : Nat) (form : Form := .slices) : Prop extends Preserved v initial s form where
  remaining : index < inputs.size
  consumedBound : consumed ≤ inputs[index].bytes.size
  aligned : (prefixMessage inputs index ++ inputs[index].bytes.extract 0 consumed).size % 128 = 0
  hashWords : HashStateAt s (hashPointer initial form form.activeMemory)
    (compressBlocks v.initialHash
      (prefixMessage inputs index ++ inputs[index].bytes.extract 0 consumed))
  blockCount : memLoad s.external (blockCountPointer initial form form.activeMemory) 64 = BitVec.ofNat 64
    ((prefixMessage inputs index ++ inputs[index].bytes.extract 0 consumed).size / 128)
  blockCountHigh : memLoad s.external (blockCountHighPointer initial form form.activeMemory) 64 = BitVec.ofNat 64
    (((prefixMessage inputs index ++ inputs[index].bytes.extract 0 consumed).size / 128) / 2^64)
  source : v.sourceValue form s = inputs[index].address + BitVec.ofNat 64 consumed
  length : (.reg (v.restRegister form) : Operand 64).read s = BitVec.ofNat 64 (inputs[index].bytes.size - consumed)
  indexRegister : v.indexValue form s = BitVec.ofNat 64 index
  countRegister : v.countValue form initial s = BitVec.ofNat 64 inputs.size

  outputSaved : form = .traitFinalizeIntoReset false →
    memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx
  bufferRegister : form = .reset 1 →
    s.regValue .rbx = bufferPointer initial form
  memcpyTarget : match form with
    | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
    | .finalizeIntoReset true =>
      s.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
    | _ => True
  activeBufferRegister : ∀ second, form = .traitFinalizeIntoReset second →
    s.regValue .rbx = bufferPointer initial form form.activeMemory

structure Result [Bindings] (v : Variant) (initial s : RamState) (inputs : Array Program.Input)
    (index : Nat) (form : Form := .slices) : Prop
    extends Buffered v initial s (prefixMessage inputs (index + 1)) form form.activeMemory where
  indexRegister : v.indexValue form s = BitVec.ofNat 64 index
  countRegister : v.countValue form initial s = BitVec.ofNat 64 inputs.size

  outputSaved : form = .traitFinalizeIntoReset false →
    memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx
  bufferRegister : form = .reset 1 →
    s.regValue .rbx = bufferPointer initial form
  memcpyTarget : match form with
    | .reset stage => stage.val = 2 → s.regValue .rbx = 0x10dd60
    | .finalizeIntoReset true =>
      s.regValue (if v = .sha384 ∨ v = .sha512 then .rbx else .r12) = 0x10dd60
    | .traitFinalizeIntoReset second =>
      s.regValue (if second then .rbp else .r13) = 0x10dd60
    | _ => True
  activeBufferRegister : ∀ second, form = .traitFinalizeIntoReset second →
    s.regValue .rbx = bufferPointer initial form form.activeMemory

end Sha2.Proofs.Wrapper512.Absorb.Blocks
