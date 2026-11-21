import P256.Proofs.Projective.Add.Combinations.Setup
import P256.Proofs.Field.Constants

set_option autoImplicit false

namespace P256.Proofs.Projective.Add.Combinations

open P256.Proofs.Field X86 X86.Machine X86Proofs

theorem copy_value {t u : RamState} {src dst : BitVec 64} {x : Nat}
    (input : MontgomeryAt t src x) (allocated : MemReadable u dst 32)
    (h0 : (Operand.mem dst : Operand 64).read u = (Operand.mem src : Operand 64).read t)
    (h8 : (Operand.mem (dst + 8) : Operand 64).read u = (Operand.mem (src + 8) : Operand 64).read t)
    (h16 : (Operand.mem (dst + 16) : Operand 64).read u = (Operand.mem (src + 16) : Operand 64).read t)
    (h24 : (Operand.mem (dst + 24) : Operand 64).read u = (Operand.mem (src + 24) : Operand 64).read t) :
    MontgomeryAt u dst x := by
  change memLoad u.external dst 64 = memLoad t.external src 64 at h0
  apply montgomeryAt_of_memLoad_limbs input.1 allocated.mem
  intro j hj
  have copy : memLoad u.external (dst + BitVec.ofNat 64 (8*j)) 64 =
      memLoad t.external (src + BitVec.ofNat 64 (8*j)) 64 := by
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h0
    · exact h8
    · exact h16
    · exact h24
  exact copy.trans (input.memLoad_limb j hj)

theorem preserve_value {t u : RamState} {cs : List Component} {src : BitVec 64} {x : Nat}
    (input : MontgomeryAt t src x) (agrees : AgreesExcept cs t u)
    (apart : ∀ i < 32, ∀ c ∈ cs, ¬ c.Covers (src + BitVec.ofNat 64 i)) :
    MontgomeryAt u src x :=
  input.of_bytes_eq (fun i hi => agrees.byte (apart i hi))

theorem call_keep {s t u : RamState} {output : Nat}
    (bytes : ∀ offset len : Nat, offset ≤ 632 → len ≤ offset + 8 →
      (offset + 32 ≤ output ∨ output + len ≤ offset) →
      ∀ i < len, u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?)
    {offset value : Nat} (bound : offset ≤ 632) (low : 24 ≤ offset)
    (apart : offset + 32 ≤ output ∨ output + 32 ≤ offset)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value :=
  input.of_bytes_eq (fun i hi => bytes offset 32 bound (by omega) apart i hi)

end P256.Proofs.Projective.Add.Combinations
