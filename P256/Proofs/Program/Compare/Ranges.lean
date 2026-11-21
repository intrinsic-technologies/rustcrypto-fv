import X86Proofs.Instructions.Movs.RepTriple
namespace P256.Proofs.Program.Compare.Ranges
open X86 X86.Machine X86.UserProcess X86Proofs
theorem memReadable_slice {s : RamState} {address : BitVec 64} {length : Nat}
    (h : MemReadable s address length) (offset count : Nat) (hle : offset + count ≤ length) :
    MemReadable s (address + BitVec.ofNat 64 offset) count := by
  refine ⟨?_, ?_⟩
  · rw [toNat_add_ofNat _ _ (by have := h.low; omega)]
    have := h.low
    omega
  · intro i hi
    rw [add_ofNat_add_ofNat]
    exact h.mem (offset + i) (by omega)

theorem rangeApart_slice_right {a b : BitVec 64} {m n : Nat} (h : RangeApart a m b n)
    (offset count : Nat) (hle : offset + count ≤ n) :
    RangeApart a m (b + BitVec.ofNat 64 offset) count := by
  intro i hi j hj
  rw [add_ofNat_add_ofNat]
  exact h i hi (offset + j) (by omega)

end P256.Proofs.Program.Compare.Ranges
