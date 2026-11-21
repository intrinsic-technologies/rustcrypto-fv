import P256.Proofs.Signing.Wrapper.Hash.Constants
import P256.Proofs.Nonce.UpdateValue.Prepare.CompressionPayload

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem constants_words {s t : RamState} (result : (constantsEffect s).Holds s t) :
    ∀ j < 4, memLoad t.external (stackPtr s + 240 + BitVec.ofNat 64 (8*j)) 64 =
      [0xbb67ae856a09e667,0xa54ff53a3c6ef372,0x9b05688c510e527f,0x5be0cd191f83d9ab][j]! := by
  have stores := result.writes
  simp only [constantsEffect, Write.AllHold, Operand.read] at stores
  obtain ⟨_, h3, h2, h1, h0, _, _⟩ := stores
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      List.getElem!_cons_zero] using h0
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      List.getElem!_cons_succ, List.getElem!_cons_zero] using h1
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      List.getElem!_cons_succ, List.getElem!_cons_zero] using h2
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      List.getElem!_cons_succ, List.getElem!_cons_zero] using h3

theorem constants_state {s t : RamState} (pre : ConstantsPre s)
    (result : (constantsEffect s).Holds s t) :
    HMAC.Sha256StateAt t (stackPtr s + 176) .empty := by
  have alloc (offset len : Nat) (bound : offset + len ≤ 280) (positive : 0 < len) :=
    ((pre.writable offset len bound positive).of_holds result).mem
  have hash := P256.Proofs.Nonce.UpdateValue.Prepare.initial_hash_of_words
    (alloc 240 32 (by decide) (by decide)) (constants_words result)
  have stores := result.writes
  simp only [constantsEffect, Write.AllHold, Operand.read] at stores
  obtain ⟨_, _, _, _, _, count, position⟩ := stores
  have posBytes := Bytes.of_memLoad (n := 8) (alloc 239 1 (by decide) (by decide))
  change Bytes t.external (stackPtr s + 239) 1
    (storedByte (memLoad t.external (stackPtr s + 239) 8)) at posBytes
  rw [position] at posBytes
  have countBytes := Bytes.of_memLoad (n := 64) (alloc 272 8 (by decide) (by decide))
  change Bytes t.external (stackPtr s + 272) 8
    (storedByte (memLoad t.external (stackPtr s + 272) 64)) at countBytes
  rw [count] at countBytes
  refine ⟨⟨rfl, fun i => Fin.elim0 i⟩, ?_, ?_, ?_⟩
  · change t.external[stackPtr s + 176 + 63]? = some 0
    have positionByte := posBytes 0 (by decide)
    change t.external[stackPtr s + 239 + 0]? = some 0 at positionByte
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] using positionByte
  · change SHA256.HashStateAt t (stackPtr s + 176 + 64) SHA256.initialHash
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hash
  · change loadBytes t.external (stackPtr s + 176#64 + 96#64) 8 = .ok (0#64)
    have countWord := countBytes.loadBytes64
    change loadBytes t.external (stackPtr s + 272#64) 8 = .ok (0#64) at countWord
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using countWord

end P256.Proofs.Signing.Wrapper.Hash
