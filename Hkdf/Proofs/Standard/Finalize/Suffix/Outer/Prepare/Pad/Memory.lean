import Hkdf.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad

open X86 X86.Machine X86.UserProcess X86Proofs

theorem external_write_mem {n : Nat} (s : RamState) (a : BitVec 64) (v : BitVec n) :
    ((Operand.mem a : Operand n).write s v).external = memStore s.external a v := rfl

theorem external_write_reg (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

theorem external_after (e : Effect) (s : RamState) (b : Bool) :
    (e.after s b).external = (applyWrites s e.writes).external := rfl

theorem memLoad_zero_store (m : Ram) (a b : BitVec 64)
    (h : memLoad m a 64 = 0) : memLoad (memStore m b (0 : BitVec 64)) a 64 = 0 := by
  apply memLoad_eq_of_memByte (by decide)
  intro i hi
  by_cases inside : ∃ j < 8, a + BitVec.ofNat 64 i = b + BitVec.ofNat 64 j
  · obtain ⟨j,hj,he⟩ := inside
    rw [he]
    have byte := memStore_getElem?_self m b (0 : BitVec 64) (by decide) j hj
    simp only [memByte, PhysicalMemory.read, byte, Option.getD_some]
    simp [storedByte]
  · rw [show memByte (memStore m b (0 : BitVec 64)) (a + BitVec.ofNat 64 i) =
        memByte m (a + BitVec.ofNat 64 i) from by
      change ((memStore m b (0 : BitVec 64))[a + BitVec.ofNat 64 i]?).getD 0 =
        (m[a + BitVec.ofNat 64 i]?).getD 0
      rw [memStore_getElem?_of_ne]
      intro j hj he
      exact inside ⟨j,hj,he.symm⟩]
    rw [← storedByte_memLoad m a i hi, h]

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare.Pad
