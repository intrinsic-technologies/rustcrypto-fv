import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Store

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open X86.Machine X86Proofs X86Proofs.Refine

theorem setWidth16_memLoad32 (mem : Ram) (a : BitVec 64) :
    (memLoad mem a 32).setWidth 16 = memLoad mem a 16 := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  simpa only [Nat.zero_div, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    (extractLsb'_memLoad mem a (n := 32) 0 16 (by decide) (by decide) (by decide))

end AesGcm.Proofs.Machine.AES16.Encrypt
