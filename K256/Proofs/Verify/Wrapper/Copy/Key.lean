import K256.Proofs.Ecdh.Decode.Repr
import K256.Proofs.Sec1.Parser.Result.Copy
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Verify.Wrapper

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine
  Standards.SECG.ECC

def copiedKey (mem : Ram) (sp : BitVec 64) : Ram :=
  memCopy (memCopy mem (sp + 256) (sp + 16) 88) (sp + 416) (sp + 256) 88

theorem signatureCallKey {mem : Ram} {sp : BitVec 64} {point : Curve.Point}
    (key : Ecdh.Decode.AffinePointAt mem (sp + 16) point) :
    Ecdh.Decode.AffinePointAt (memStore (copiedKey mem sp) (sp - 8) (0x10302c : BitVec 64))
      (sp + 416) point := by
  apply key.of_copy
  intro off width within
  have apart : RangeApart (sp - 8) 8 (sp + 416) 88 :=
    RangeApart.of_offsets (addr_sub sp 8) rfl (by decide)
  rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.right_sub apart within)]
  unfold copiedKey
  rw [Sec1.Parser.Result.memLoad_memCopy _ _ _ (by decide) within,
    Sec1.Parser.Result.memLoad_memCopy _ _ _ (by decide) within]

theorem signatureCallFrame {initial mem : Ram} {sp : BitVec 64} {regions : List MemoryRegion}
    (frame : RamWriteFrame initial mem regions)
    (tmp : InRegions regions (sp + 256) 88) (dst : InRegions regions (sp + 416) 88)
    (slot : InRegions regions (sp - 8) 8) :
    RamWriteFrame initial (memStore (copiedKey mem sp) (sp - 8) (0x10302c : BitVec 64)) regions :=
  ((frame.memStore _ tmp).memStore _ dst).memStore _ slot

end K256.Proofs.Verify.Wrapper
