import K256.Proofs.Signing.UpdateV.State
import K256.Proofs.Sec1.Parser.Result.Copy
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Signing.UpdateV

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.Hash

theorem hasBytes_memCopy_offset {m : Ram} {src dst : BitVec 64} {len off size : Nat}
    {bytes : ByteArray} (bound : len ≤ 2^64) (fits : off + size ≤ len)
    (source : (⟨(src + BitVec.ofNat 64 off).toNat, size⟩ : MemoryRegion).HasBytes m bytes) :
    (⟨(dst + BitVec.ofNat 64 off).toNat, size⟩ : MemoryRegion).HasBytes (memCopy m dst src len) bytes := by
  refine ⟨source.1, fun i => ?_⟩
  have within : off + i.val < len := by have := i.isLt; have h : bytes.size = size := source.1; omega
  have copied := Sec1.Wrapper.Copy.memCopy_getElem?_self m dst src len bound (off + i.val) within
  have byte := source.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc] at byte copied ⊢
  rw [copied]
  simp only [memByte, PhysicalMemory.read, byte, Option.getD_some]

theorem stateAt_memCopy_offset {m : Ram} {src dst : BitVec 64} {len off : Nat}
    {hash : Array UInt32} (bound : len ≤ 2^64) (fits : off + 32 ≤ len)
    (source : Compression.StateAt m (src + BitVec.ofNat 64 off) hash) :
    Compression.StateAt (memCopy m dst src len) (dst + BitVec.ofNat 64 off) hash := by
  refine ⟨source.1, fun i hi => ?_⟩
  have copy := Sec1.Parser.Result.memLoad_memCopy (width := 32) (off := off + 4 * i)
    m dst src bound (by omega)
  simpa only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc] using
    copy.trans (by simpa only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc] using source.2 i hi)

theorem HmacStateAt.memCopy {m : Ram} {src dst : BitVec 64} {key input : ByteArray}
    (h : HmacStateAt m src key input) : HmacStateAt (memCopy m dst src 168) dst key input := by
  constructor
  · simpa only [BitVec.add_zero] using hasBytes_memCopy_offset (dst := dst) (src := src)
      (off := 0) (by decide : 168 ≤ 2^64) (by decide : 0 + 64 ≤ 168)
      (by simpa only [BitVec.add_zero] using h.outer)
  · exact hasBytes_memCopy_offset (len := 168) (off := 64) (by decide) (by omega) h.buffer
  · exact (Sec1.Parser.Result.memLoad_memCopy (off := 127) m dst src (by decide : 168 ≤ 2^64)
      (by decide : 127 + 8/8 ≤ 168)).trans h.used
  · exact stateAt_memCopy_offset (len := 168) (off := 128) (by decide) (by decide) h.hash
  · exact (Sec1.Parser.Result.memLoad_memCopy (off := 160) m dst src (by decide : 168 ≤ 2^64)
      (by decide : 160 + 64/8 ≤ 168)).trans h.count

end K256.Proofs.Signing.UpdateV
