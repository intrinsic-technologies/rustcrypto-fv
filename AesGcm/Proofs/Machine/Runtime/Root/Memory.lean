import AesGcm.Proofs.Machine.Runtime.Contracts

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86Proofs.Refine

theorem hasBytes_of_frame {original mem : Ram} {regions : List MemoryRegion}
    {region : MemoryRegion} {bytes : ByteArray}
    (hframe : RamWriteFrame original mem regions) (hbytes : region.HasBytes original bytes)
    (hbound : region.start + region.size ≤ 2 ^ 64) (hapart : ∀ r ∈ regions, region.Disjoint r) :
    region.HasBytes mem bytes := by
  refine ⟨hbytes.1, fun i => ?_⟩
  have hsize : bytes.size = region.size := hbytes.1
  have ha : (BitVec.ofNat 64 (region.start + i.val)).toNat = region.start + i.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hframe.outside _ ⟨by rw [ha]; omega, ?_⟩]
  · exact hbytes.2 i
  · intro r hr
    have hn := hapart r hr (region.start + i.val)
      (show region.Contains (region.start + i.val) from ⟨by omega, by omega⟩)
    rw [ha]
    simp only [MemoryRegion.Contains] at hn
    omega

end AesGcm.Proofs.Machine.Runtime
