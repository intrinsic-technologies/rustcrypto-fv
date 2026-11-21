import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Common.Memory

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem input_slice {s : RamState} {input : Input} {region : MemoryRegion} {offset count : Nat}
    (bytes : input.region.HasBytes s.external input.bytes) (bounded : input.region.Bounded)
    (apart : input.region.Disjoint region) (bound : offset+count≤input.bytes.size) :
    let part : MemoryRegion := ⟨(input.address+BitVec.ofNat 64 offset).toNat,count⟩
    part.HasBytes s.external (input.bytes.extract offset (offset+count)) ∧
      part.Bounded ∧ part.Disjoint region := by
  have low : input.address.toNat+input.bytes.size<2^32 := bounded
  have address : (input.address+BitVec.ofNat 64 offset).toNat = input.address.toNat+offset := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)]
  dsimp only
  rw [address]
  refine ⟨hasBytes_extract bytes bound,?_,?_⟩
  · change input.address.toNat+offset+count<2^32
    omega
  · intro a member other
    apply apart a ?_ other
    change input.address.toNat≤a ∧ a<input.address.toNat+input.bytes.size
    change input.address.toNat+offset≤a ∧ a<input.address.toNat+offset+count at member
    omega

end Sha2.Proofs.Common.Memory
