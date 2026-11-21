import Sha2.Proofs.Wrapper.Initialize.Store
import Sha2.Proofs.Common.SHA256.Words

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Initialize.Store

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA256

theorem initialized_words {v : Variant} {s t : RamState} (h : (effect s v).Holds s t) :
    ∀ j < 4, memLoad t.external (rspOf s + 256 + BitVec.ofNat 64 (8*j)) 64 =
      (initialWords v)[j]! := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read, rspOf] at stores
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simpa only [rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using stores.2.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using stores.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using stores.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using stores.2.1

theorem hash_words {v : Variant} {s t : RamState} (h : (effect s v).Holds s t)
    (read : MemReadable t (rspOf s + 256) 32) :
    HashStateAt t (rspOf s + 256) v.initialHash := by
  refine ⟨v.initialHash_size, ?_⟩
  intro j hj
  have bytes := Bytes.of_memLoad (n := 64) (m := t.external)
    (a := rspOf s + 256 + BitVec.ofNat 64 (8*(j/2))) (by
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact read.mem _ (by omega))
  rw [initialized_words h (j/2) (by omega)] at bytes
  have half := bytes.sub (4*(j%2)) 4 (by omega)
  have address : rspOf s + 256 + BitVec.ofNat 64 (8*(j/2)) +
      BitVec.ofNat 64 (4*(j%2)) = rspOf s + 256 + BitVec.ofNat 64 (4*j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [address] at half
  apply loadBytes32_of_bytes
  apply half.congr
  intro i hi
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  all_goals cases v <;> decide +kernel

theorem tail_length {v : Variant} {s t : RamState} (h : (effect s v).Holds s t)
    (read : MemReadable t (rspOf s + 255) 1) :
    t.external[rspOf s + 255]? = some 0 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read, rspOf] at stores
  have word := stores.2.2.2.2.2.2
  have bytes := Bytes.of_memLoad (n := 8) read.mem
  change memLoad t.external (rspOf s + 255) 8 = 0 at word
  rw [word] at bytes
  have byte := bytes 0 (by decide)
  simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl] using byte

theorem blocks {v : Variant} {s t : RamState} (h : (effect s v).Holds s t) :
    memLoad t.external (rspOf s + 288) 64 = 0 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read, rspOf] at stores
  exact stores.2.2.2.2.2.1

end Sha2.Proofs.Wrapper.Initialize.Store
