import K256.Proofs.Signing.UpdateV.Finalize.State

namespace K256.Proofs.Signing.UpdateV.Finalize

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Verify.Hash Standards.NIST.SHA2

def compressStart (outer : Bool) : Label := if outer then .l107ea9 else .l107be4

structure Marked (outer : Bool) (a : Registers) (m : Ram) (sp : BitVec 64) (msg : ByteArray) : Prop where
  rsp : a[4] = ⟨64,sp⟩
  hashPtr : a[(if outer then 14 else 15 : Fin Reg.count)] = ⟨64,sp+72⟩
  used : a[(if outer then 12 else 13 : Fin Reg.count)] = ⟨64,BitVec.ofNat 64 (msg.size % 64)⟩
  count : a[(if outer then 13 else 5 : Fin Reg.count)] = ⟨64,BitVec.ofNat 64 (msg.size / 64)⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → a[i].width = 64
  hash : Compression.StateAt m (sp+72) (compressBlocks initialHash msg)
  bytes : (⟨(sp+8).toNat,56⟩ : MemoryRegion).HasBytes m (finalPrefix msg)

end K256.Proofs.Signing.UpdateV.Finalize
