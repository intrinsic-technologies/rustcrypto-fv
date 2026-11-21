import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper

theorem input_of_word_copies {s t : RamState} {source target : MemoryRegion}
    {bytes : ByteArray} (input : ValidInput s source bytes)
    (size : bytes.size = 32) (bound : target.Bounded) (len : target.size = 32)
    (present : MemReadable t (BitVec.ofNat 64 target.start) 32)
    (words : ∀ j : Fin 4,
      memLoad t.external (BitVec.ofNat 64 target.start + BitVec.ofNat 64 (8*j.val)) 64 =
      memLoad s.external (BitVec.ofNat 64 source.start + BitVec.ofNat 64 (8*j.val)) 64) :
    ValidInput t target bytes := by
  refine ⟨bound, size.trans len.symm, ?_⟩
  intro i
  have hi : i.val < 32 := by have := i.isLt; omega
  let j : Fin 4 := ⟨i.val / 8, by omega⟩
  have ho : i.val % 8 < 8 := Nat.mod_lt _ (by decide)
  have he : 8 * j.val + i.val % 8 = i.val := by dsimp [j]; omega
  have hs : s.external[BitVec.ofNat 64 source.start + BitVec.ofNat 64 (8*j.val) +
      BitVec.ofNat 64 (i.val % 8)]? = some bytes[i.val] := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, he, ← BitVec.ofNat_add]
    exact input.2.2 i
  have ht := copied_byte (a := BitVec.ofNat 64 target.start + BitVec.ofNat 64 (8*j.val))
    (fun o h => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact present.mem _ (by have := j.isLt; omega)) (words j) ho hs
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, he, ← BitVec.ofNat_add] at ht
  exact ht

theorem add_no_carry (a b : BitVec 64) :
    (!(addSpec a b).2.CF) = decide (a.toNat + b.toNat < 2^64) := by
  have ha := a.isLt
  have hb := b.isLt
  by_cases h : a.toNat + b.toNat < 2^64
  · simp [addSpec, BitVec.toNat_add, Nat.mod_eq_of_lt h, h]
  · have hne : (a.toNat + b.toNat) % 2^64 ≠ a.toNat + b.toNat := by omega
    simp [addSpec, BitVec.toNat_add, hne, h]

theorem argument_readable {s : RamState} {i : Nat} {v : BitVec 64}
    (h : StackArgument s i v) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 (8*(i+1))) 8 := by
  have he : BitVec.ofNat 64 (stackArgumentSlot s i).start =
      stackPtr s + BitVec.ofNat 64 (8*(i+1)) := by
    simp only [stackArgumentSlot, BitVec.ofNat_add, BitVec.ofNat_toNat]
    rfl
  have hb : (stackPtr s).toNat + 8*(i+1) + 8 < 2^32 := h.1
  refine ⟨?_, ?_⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · rw [← he]
    exact loadBytes_isSome h.2.2

theorem argument_value {s : RamState} {i : Nat} {v : BitVec 64}
    (h : StackArgument s i v) :
    wd s (stackPtr s + BitVec.ofNat 64 (8*(i+1))) = v := by
  have he : BitVec.ofNat 64 (stackArgumentSlot s i).start =
      stackPtr s + BitVec.ofNat 64 (8*(i+1)) := by
    simp only [stackArgumentSlot, BitVec.ofNat_add, BitVec.ofNat_toNat]
    rfl
  rw [← he]
  exact word64At_memLoad h.2

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
