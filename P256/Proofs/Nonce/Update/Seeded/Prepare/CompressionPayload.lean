import P256.Proofs.Program.Code
import P256.Proofs.Nonce.Update.Seeded.Prepare.CompressionSetup
import P256.Proofs.Nonce.Update.Seeded.Prepare.State
import P256.Proofs.Nonce.UpdateValue.Prepare.CompressionPayload
import P256.Proofs.SHA256.Memory.Words

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem CompressionSetup.initialized_words {s t : RamState}
    (h : (effect s).Holds s t) :
    ∀ j < 4, memLoad t.external (rspOf s + 320 + BitVec.ofNat 64 (8*j)) 64 =
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
    (h : (effect s).Holds s t) (allocated : MemReadable t (rspOf s + 320) 32) :
    SHA256.HashStateAt t (rspOf s + 320) SHA256.initialHash :=
  UpdateValue.Prepare.initial_hash_of_words allocated.mem (initialized_words h)

theorem CompressionSetup.position {s t : RamState}
    (h : (effect s).Holds s t) (allocated : MemReadable t (rspOf s + 319) 1) :
    t.external[rspOf s + 319]? = some 0 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read] at stores
  have stored : memLoad t.external (rspOf s + 319) 8 = 0 := stores.2.2.2.2.2.2.1
  have bytes := Bytes.of_memLoad (n := 8) allocated.mem
  rw [stored] at bytes
  simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl] using
    bytes 0 (by decide)

theorem CompressionSetup.blocks {s t : RamState}
    (h : (effect s).Holds s t) (allocated : MemReadable t (rspOf s + 352) 8) :
    loadBytes t.external (rspOf s + 352) 8 = .ok 1 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read] at stores
  have stored : memLoad t.external (rspOf s + 352) 64 = 1 := stores.2.2.2.2.2.2.2.1
  have bytes := Bytes.of_memLoad (n := 64) allocated.mem
  rw [stored] at bytes
  exact bytes.loadBytes64

end P256.Proofs.Nonce.Update.Seeded.Prepare
