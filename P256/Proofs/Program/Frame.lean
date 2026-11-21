import P256.Proofs.Program.Memory
import X86Proofs.Program.ReadWrite.Store

set_option autoImplicit false

namespace P256.Proofs.Program

open Prelude X86 X86.Machine X86Proofs

theorem frame_read {s t : RamState} {n : Nat} {written : Vector MemoryRegion n}
    (frame : MemoryWriteFrame s t written) {region : MemoryRegion}
    (disjoint : ∀ other ∈ written, region.Disjoint other)
    {address : BitVec 64} (hc : region.Contains address.toNat) :
    t.external[address]? = s.external[address]? := by
  apply frame
  intro other ho ha
  exact disjoint other ho address.toNat hc ha

theorem frame_memLoad {s t : RamState} {n : Nat} {written : Vector MemoryRegion n}
    (frame : MemoryWriteFrame s t written) {region : MemoryRegion}
    (disjoint : ∀ other ∈ written, region.Disjoint other)
    (bounded : region.Bounded) {address : BitVec 64} {width : Nat}
    (hstart : region.start ≤ address.toNat)
    (hend : address.toNat + width / 8 ≤ region.start + region.size) :
    memLoad t.external address width = memLoad s.external address width := by
  apply memLoad_congr
  intro i hi
  have he := frame_read frame disjoint (memoryRegion_contains_add bounded hstart hend hi)
  change (t.external[address + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[address + BitVec.ofNat 64 i]?).getD 0
  rw [he]

theorem frame_hasBytes {s t : RamState} {n : Nat} {written : Vector MemoryRegion n}
    (frame : MemoryWriteFrame s t written) {region : MemoryRegion}
    (disjoint : ∀ other ∈ written, region.Disjoint other)
    (bounded : region.Bounded) {bytes : ByteArray}
    (hbytes : region.HasBytes s.external bytes) : region.HasBytes t.external bytes := by
  refine ⟨hbytes.1, ?_⟩
  intro i
  have hs : bytes.size = region.size := hbytes.1
  have hi := i.isLt
  have hl : region.start + region.size < 2^32 := bounded
  have hc : region.Contains (BitVec.ofNat 64 (region.start + i.val)).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, by omega⟩
  rw [frame_read frame disjoint hc]
  exact hbytes.2 i

end P256.Proofs.Program
