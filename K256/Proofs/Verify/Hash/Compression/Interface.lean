import K256.Proofs.Common.Refine.Store
import K256.Proofs.Verify.Hash.Blocks
import K256.Spec.Program

namespace K256.Proofs.Verify.Hash.Compression

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

def StateAt (mem : Ram) (p : BitVec 64) (hash : Array UInt32) : Prop :=
  hash.size = 8 ∧ WordsAt mem p 32 (Vector.ofFn fun i : Fin 8 => hash[i.val]!.toBitVec)

def footprint (sp dst : BitVec 64) : List MemoryRegion :=
  [⟨sp.toNat - 336, 336⟩, ⟨dst.toNat, 32⟩]

structure Call (args : CFG.Values Value Reg.count) (mem : Ram)
    (sp dst src : BitVec 64) (hash : Array UInt32) (input : ByteArray) : Prop where
  rsp : args[4].get 64 = sp
  rdi : args[7].get 64 = dst
  rsi : args[6].get 64 = src
  rdx : args[2].get 64 = BitVec.ofNat 64 (input.size / 64)
  savedWidths : ∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15] → args[i].width = 64
  state : StateAt mem dst hash
  inputBytes : (⟨src.toNat, input.size⟩ : MemoryRegion).HasBytes mem input
  inputReadable : Readable mem src input.size
  hashWritable : Writable Extracted.programImage mem dst 32
  depth : 336 ≤ sp.toNat
  stackWritable : Writable Extracted.programImage mem (sp - 336) 336
  returnReadable : Readable mem sp 8
  returnLow : (memLoad mem sp 64).toNat < 2^32
  hashStack : dst.toNat + 32 ≤ sp.toNat - 336 ∨ sp.toNat + 8 ≤ dst.toNat
  inputStack : src.toNat + input.size ≤ sp.toNat - 336 ∨ sp.toNat ≤ src.toNat

structure Returned (args : CFG.Values Value Reg.count) (mem : Ram)
    (sp dst : BitVec 64) (hash : Array UInt32) (out : Output Value Ram Reg.count) : Prop where
  state : StateAt out.store dst hash
  writes : RamWriteFrame mem out.store (footprint sp dst)
  tag : out.tag = some ⟨64, memLoad mem sp 64⟩
  rsp : out.values[4] = ⟨64, sp + 8⟩
  preserved : ∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
    out.values[i] = args[i]

def hashRegisters : Vector (Fin Reg.count) 8 := #v[3, 14, 0, 9, 8, 10, 2, 1]

structure LoopState (entry : CFG.Values Value Reg.count) (original : Ram)
    (sp dst src : BitVec 64) (count index : Nat) (hash : Array UInt32)
    (args : CFG.Values Value Reg.count) (mem : Ram) : Prop where
  rsp : args[4].get 64 = sp - 336
  rsi : args[6].get 64 = src + BitVec.ofNat 64 (64 * index)
  size : hash.size = 8
  words : ∀ i : Fin 8, args[hashRegisters[i]].get 32 = hash[i.val]!.toBitVec
  writes : RamWriteFrame original mem [⟨sp.toNat - 336, 336⟩]
  destination : memLoad mem ((sp - 336) + 192) 64 = dst
  limit : memLoad mem ((sp - 336) + 200) 64 = src + BitVec.ofNat 64 (64 * count)
  slots : ∀ i : Fin 6,
    memLoad mem (sp - (#v[48, 8, 40, 32, 24, 16] : Vector (BitVec 64) 6)[i]) 64 =
      entry[(#v[3, 5, 12, 13, 14, 15] : Vector (Fin Reg.count) 6)[i]].get 64
  preserved : ∀ i : Fin Reg.count, i.val ∈ [22, 39, 50, 51] → args[i] = entry[i]

end K256.Proofs.Verify.Hash.Compression
