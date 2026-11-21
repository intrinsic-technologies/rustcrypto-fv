import P256.Proofs.Nonce.UpdateValue.Prepare.CompressionSetup
import P256.Proofs.Nonce.UpdateValue.Prepare.State
import P256.Proofs.SHA256.Memory.Words

set_option autoImplicit false

namespace P256.Proofs.Nonce.UpdateValue.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem initial_hash_of_words {s : RamState} {a : BitVec 64}
    (allocated : ∀ i < 32, (s.external[a + BitVec.ofNat 64 i]?).isSome)
    (words : ∀ j < 4, memLoad s.external (a + BitVec.ofNat 64 (8*j)) 64 =
      [0xbb67ae856a09e667,0xa54ff53a3c6ef372,0x9b05688c510e527f,0x5be0cd191f83d9ab][j]!) :
    SHA256.HashStateAt s a P256.Proofs.SHA256.initialHash := by
  refine ⟨by decide +kernel, ?_⟩
  intro j hj
  have bytes := Bytes.of_memLoad (n := 64) (m := s.external)
    (a := a + BitVec.ofNat 64 (8*(j/2))) (by
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated _ (by omega))
  rw [words (j/2) (by omega)] at bytes
  have half := bytes.sub (4*(j%2)) 4 (by omega)
  have address : a + BitVec.ofNat 64 (8*(j/2)) + BitVec.ofNat 64 (4*(j%2)) =
      a + BitVec.ofNat 64 (4*j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
    omega
  rw [address] at half
  apply SHA256.loadBytes32_of_bytes
  apply half.congr
  intro i hi
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  all_goals decide +kernel

theorem CompressionSetup.initialized_words {s t : RamState}
    (h : (effect s).Holds s t) :
    ∀ j < 4, memLoad t.external (rspOf s + 168 + BitVec.ofNat 64 (8*j)) 64 =
      [0xbb67ae856a09e667,0xa54ff53a3c6ef372,0x9b05688c510e527f,0x5be0cd191f83d9ab][j]! := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read] at stores
  rcases stores with ⟨_, _, h3, h2, h1, h0, _, _, _, _, _⟩
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      List.getElem!_cons_zero] using h0
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      List.getElem!_cons_succ, List.getElem!_cons_zero] using h1
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      List.getElem!_cons_succ, List.getElem!_cons_zero] using h2
  · simpa only [rspOf, Operand.read, Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      List.getElem!_cons_succ, List.getElem!_cons_zero] using h3

theorem CompressionSetup.hash_words {s t : RamState}
    (h : (effect s).Holds s t) (allocated : MemReadable t (rspOf s + 168) 32) :
    SHA256.HashStateAt t (rspOf s + 168) P256.Proofs.SHA256.initialHash :=
  initial_hash_of_words allocated.mem (initialized_words h)

theorem CompressionSetup.position {s t : RamState}
    (h : (effect s).Holds s t) (allocated : MemReadable t (rspOf s + 167) 1) :
    t.external[rspOf s + 167]? = some 0 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read] at stores
  have stored : memLoad t.external (rspOf s + 167) 8 = 0 := stores.2.2.2.2.2.2.1
  have bytes := Bytes.of_memLoad (n := 8) allocated.mem
  rw [stored] at bytes
  simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl] using
    bytes 0 (by decide)

theorem CompressionSetup.blocks {s t : RamState}
    (h : (effect s).Holds s t) (allocated : MemReadable t (rspOf s + 200) 8) :
    loadBytes t.external (rspOf s + 200) 8 = .ok 1 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read] at stores
  have stored : memLoad t.external (rspOf s + 200) 64 = 1 := stores.2.2.2.2.2.2.2.1
  have bytes := Bytes.of_memLoad (n := 64) allocated.mem
  rw [stored] at bytes
  exact bytes.loadBytes64

end P256.Proofs.Nonce.UpdateValue.Prepare
