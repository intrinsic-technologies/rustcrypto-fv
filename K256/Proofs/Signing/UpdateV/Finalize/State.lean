import K256.Proofs.Signing.UpdateV.State
import K256.Proofs.Verify.Hash.Padding.Finalize

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash

abbrev Registers := Values Value Reg.count

abbrev Reaches (l : Label) (a : Registers) (m : Ram) (l' : Label) (b : Registers) (n : Ram) :=
  (program.sem (dialect Extracted.programImage)).Reaches ⟨⟨l,a,m⟩,[]⟩ ⟨⟨l',b,n⟩,[]⟩

def padStart (outer : Bool) : Label := if outer then .l107da7 else .l107adb

def padEnd (outer : Bool) : Label := if outer then .l107f2b else .l107c66

def digestState (msg : ByteArray) :=
  Reference.compress (compressBlocks initialHash msg) (Standards.NIST.SHA2.bytesToBits (finalBlock msg))

structure Buffered (m : Ram) (src : BitVec 64) (msg : ByteArray) : Prop where
  bytes : (⟨src.toNat, msg.size % 64⟩ : MemoryRegion).HasBytes m (remainderBytes msg)
  used : memLoad m (src + 63) 8 = BitVec.ofNat 8 (msg.size % 64)
  hash : Compression.StateAt m (src + 64) (compressBlocks initialHash msg)
  count : memLoad m (src + 96) 64 = BitVec.ofNat 64 (msg.size / 64)

def paddingRegion (sp : BitVec 64) : MemoryRegion := ⟨sp.toNat - 344,520⟩

def savedRegs : List Nat := [3,22,39,50,51]

structure Call (a : Registers) (m : Ram) (sp src dst : BitVec 64) : Prop where
  rsp : a[4] = ⟨64,sp⟩
  ctx : a[7] = ⟨64,src⟩
  out : a[6] = ⟨64,dst⟩
  df : a[22] = ⟨1,0⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [5,12,13] → a[i].width = 64
  stack : Writable Extracted.programImage m (sp - 704) 704
  depth : 704 ≤ sp.toNat
  limit : sp.toNat + 8 < 2^32
  ret : Readable m sp 8
  retLow : (memLoad m sp 64).toNat < 2^32
  ctxRead : Readable m src 168
  dstWrite : Writable Extracted.programImage m dst 32
  ctxAbove : sp.toNat + 8 ≤ src.toNat
  dstAbove : sp.toNat + 8 ≤ dst.toNat
  image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2

def scratch (sp : BitVec 64) : MemoryRegion := ⟨sp.toNat - 704,704⟩

structure Prologue (entry b : Registers) (m t : Ram) (sp src dst : BitVec 64) : Prop where
  rsp : b[4] = ⟨64,sp - 360⟩
  df : b[22] = ⟨1,0⟩
  output : b[3] = ⟨64,dst⟩
  input : b[15] = ⟨64,src⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [5,12,13,14] → b[i].width = 64
  kept : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → b[i] = entry[i]
  writes : RamWriteFrame m t [scratch sp]
  slots : ∀ i : Fin 6,
    memLoad t (sp - (#v[48,8,40,32,24,16] : Vector (BitVec 64) 6)[i]) 64 =
      entry[(#v[3,5,12,13,14,15] : Vector (Fin Reg.count) 6)[i]].get 64

end K256.Proofs.Signing.UpdateV.Finalize
