import ChaCha20Poly1305.Proofs.Decrypt.Xor

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
open Prelude X86 X86.Machine X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine

theorem readWrite (m : Ram) (a b : BitVec 64) (v : BitVec 8) :
    memLoad (memStore m a v) b 8 = if b = a then v else memLoad m b 8 := by
  split
  · rename_i ha; subst b; exact memLoad_memStore_8 _ _ _
  · rename_i h
    apply memLoad_memStore_of_rangeApart
    intro i hi j hj he
    have ii : i=0 := by omega
    have jj : j=0 := by omega
    subst i; subst j
    apply h; bv_omega

theorem mov3 (a b : BitVec 64) : a+3+b = a+b+3 := by bv_omega
theorem mov64 (a b : BitVec 64) : a+64+b = a+b+64 := by bv_omega

theorem add3sub3 (a : BitVec 64) : a+3-3 = a := by bv_omega
theorem add3sub2 (a : BitVec 64) : a+3-2 = a+1 := by bv_omega
theorem add3sub1 (a : BitVec 64) : a+3-1 = a+2 := by bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Xor
