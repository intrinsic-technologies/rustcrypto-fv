import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Common.Memory

open X86 X86.Machine X86Proofs

theorem allocated_of_loadBytes {memory : Ram} {address : BitVec 64} {count : Nat}
    {value : BitVec 64} (h : loadBytes memory address count = .ok value) :
    ∀ i < count, (memory[address + BitVec.ofNat 64 i]?).isSome := by
  have loop (remaining current shift accumulator : Nat)
      (hl : loadBytes.loop memory address remaining current shift accumulator = .ok value) :
      ∀ i < remaining, (memory[address + BitVec.ofNat 64 (current + i)]?).isSome := by
    induction remaining generalizing current shift accumulator with
    | zero => intro i hi; omega
    | succ remaining ih =>
      rw [loadBytes.loop] at hl
      cases hm : memory[addAddress address current]? with
      | none => simp only [hm] at hl; cases hl
      | some byte =>
        simp only [hm] at hl
        intro i hi
        cases i with
        | zero => simpa only [Nat.add_zero, addAddress, fromNat, hm] using
            (show (memory[addAddress address current]?).isSome by simp only [hm, Option.isSome_some])
        | succ i =>
          simpa only [Nat.add_assoc, Nat.add_comm 1] using
            ih (current + 1) (shift + 8) (accumulator + byte.toNat * 2^shift) hl i (by omega)
  simpa only [Nat.zero_add] using loop count 0 0 0 h

theorem bytes_of_loadBytes64 {memory : Ram} {address : BitVec 64} {value : BitVec 64}
    (hAllocated : ∀ i < 8, (memory[address + BitVec.ofNat 64 i]?).isSome)
    (hLoad : loadBytes memory address 8 = .ok value) :
    Bytes memory address 8 (storedByte value) := by
  have hBytes := Bytes.of_memLoad (n := 64) hAllocated
  have he : memLoad memory address 64 = value := Except.ok.inj (hBytes.loadBytes64.symm.trans hLoad)
  rwa [he] at hBytes

theorem memLoad32_of_loadBytes64 {memory : Ram} {address : BitVec 64} {value : BitVec 64}
    (hAllocated : ∀ i < 8, (memory[address + BitVec.ofNat 64 i]?).isSome)
    (hLoad : loadBytes memory address 8 = .ok value) :
    memLoad memory address 32 = value.setWidth 32 := by
  have hBytes := bytes_of_loadBytes64 hAllocated hLoad
  apply Bytes.memLoad (n := 32) ?_ (by decide) (by decide)
  intro i hi
  have he : storedByte value i = storedByte (value.setWidth 32) i := by
    simp only [storedByte_eq_extract,
      BitVec.extractLsb'_setWidth_of_le (show 8 * i + 8 ≤ 32 by omega)]
  exact (hBytes i (by omega)).trans (congrArg some he)

end P256.Proofs.Common.Memory
