import K256.Proofs.Verify.Hash.Compression.Execution
import K256.Proofs.Verify.Hash.Padding.Finalize
import K256.Proofs.Verify.Hash.Padding.Compression
import K256.Proofs.Verify.LIR.Fn104f20.Part1

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

def regions (sp : BitVec 64) : List MemoryRegion :=
  [⟨sp.toNat - 512, 624⟩, ⟨sp.toNat + 256, 64⟩, ⟨sp.toNat + 488, 104⟩]

structure Frame (sp : BitVec 64) (a b : Values Value Reg.count) (m t : Ram) : Prop where
  rsp : b[4] = ⟨64, sp⟩
  df : b[22] = ⟨1, 0⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [39,50,51] → b[i] = a[i]
  writes : RamWriteFrame m t (regions sp)

structure Buffer (sp : BitVec 64) (msg : ByteArray) (b : Values Value Reg.count) (t : Ram) : Prop where
  widths : ∀ i : Fin Reg.count, i.val ∈ [5,12,13] → b[i].width = 64
  state : Compression.StateAt t (sp + 552) (compressBlocks initialHash msg)
  bytes : (⟨(sp + 488).toNat, msg.size % 64⟩ : MemoryRegion).HasBytes t (remainderBytes msg)
  len : memLoad t (sp + 551) 8 = BitVec.ofNat 8 (msg.size % 64)
  blocks : memLoad t (sp + 584) 64 = BitVec.ofNat 64 (msg.size / 64)

structure Padding (sp : BitVec 64) (msg : ByteArray) (b : Values Value Reg.count) (t : Ram) : Prop where
  widths : ∀ i : Fin Reg.count, i.val ∈ [5,12,13,14] → b[i].width = 64
  state : Compression.StateAt t (sp + 72) (compressBlocks initialHash msg)
  rbx : b[3] = ⟨64, sp + 72⟩
  length : b[15] = ⟨64, bswapSpec (BitVec.ofNat 64 (8 * msg.size))⟩
  bytes : (⟨(sp + 8).toNat, 64⟩ : MemoryRegion).HasBytes t (paddedBuffer msg)

abbrev markTarget (msg : ByteArray) : Label :=
  if msg.size % 64 < 56 then .l1056d8 else .l10561c

end K256.Proofs.Signing.Hash
