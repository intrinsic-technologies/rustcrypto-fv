import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Field

open P256.Spec.Operations X86 X86.Machine X86Proofs

theorem montgomeryAt_coefficient_b {s : RamState} {address : BitVec 64}
    (allocated : ∀ i < 32, (s.external[address + BitVec.ofNat 64 i]?).isSome)
    (word0 : memLoad s.external address 64 = 0xd89cdf6229c4bddf)
    (word1 : memLoad s.external (address + 8) 64 = 0xacf005cd78843090)
    (word2 : memLoad s.external (address + 16) 64 = 0xe5a220abf7212ed6)
    (word3 : memLoad s.external (address + 24) 64 = 0xdc30061d04874834) :
    MontgomeryAt s address domain.b := by
  apply montgomeryAt_of_memLoad_limbs (by decide +kernel) allocated
  intro j hj
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases casesJ with rfl | rfl | rfl | rfl
  · change memLoad s.external (address + (0 : BitVec 64)) 64 = 0xd89cdf6229c4bddf
    exact (congrArg (fun a => memLoad s.external a 64) (BitVec.add_zero address)).trans word0
  · exact word1
  · exact word2
  · exact word3

end P256.Proofs.Field
