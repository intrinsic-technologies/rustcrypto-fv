import Hkdf.Proofs.Key.Hash.Initialize.Machine
import Hkdf.Proofs.Common.SHA256.Words

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash.Initialize

open Hkdf.Spec Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.SHA256

theorem hashStateAt_initialHash_of_packedWords {t : RamState} {base : BitVec 64}
    (read : MemReadable t base 32)
    (words : ∀ j < 4, memLoad t.external (base + BitVec.ofNat 64 (8*j)) 64 =
      [0xbb67ae856a09e667,0xa54ff53a3c6ef372,0x9b05688c510e527f,0x5be0cd191f83d9ab][j]!) :
    HashStateAt t base Hkdf.Proofs.NIST.SHA256.initialHash := by
  refine ⟨by decide +kernel, ?_⟩
  intro j hj
  have bytes := Bytes.of_memLoad (n := 64) (m := t.external)
    (a := base + BitVec.ofNat 64 (8*(j/2))) (by
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact read.mem _ (by omega))
  rw [words (j/2) (by omega)] at bytes
  have half := bytes.sub (4*(j%2)) 4 (by omega)
  have address : base + BitVec.ofNat 64 (8*(j/2)) +
      BitVec.ofNat 64 (4*(j%2)) = base + BitVec.ofNat 64 (4*j) := by
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
  all_goals decide +kernel


theorem initialized_words {s t : RamState} (h : (effect s).Holds s t) :
    ∀ j < 4, memLoad t.external (rspOf s + 296 + BitVec.ofNat 64 (8*j)) 64 =
      [0xbb67ae856a09e667,0xa54ff53a3c6ef372,0x9b05688c510e527f,0x5be0cd191f83d9ab][j]! := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read, rspOf] at stores
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simpa only [rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, List.getElem!_cons_zero] using stores.2.2.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      List.getElem!_cons_zero, List.getElem!_cons_succ] using stores.2.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      List.getElem!_cons_zero, List.getElem!_cons_succ] using stores.2.2.2.1
  · simpa only [rspOf, Operand.read, BitVec.setWidth_eq, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
      List.getElem!_cons_zero, List.getElem!_cons_succ] using stores.2.2.1

theorem hash_words {s t : RamState} (h : (effect s).Holds s t)
    (read : MemReadable t (rspOf s + 296) 32) :
    HashStateAt t (rspOf s + 296) Hkdf.Proofs.NIST.SHA256.initialHash :=
  hashStateAt_initialHash_of_packedWords read (initialized_words h)

theorem empty_tail {s t : RamState} (h : (effect s).Holds s t)
    (read : MemReadable t (rspOf s + 295) 1) :
    t.external[rspOf s + 295]? = some 0 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read, rspOf] at stores
  have word := stores.2.2.2.2.2.2.1
  have bytes := Bytes.of_memLoad (n := 8) read.mem
  change memLoad t.external (rspOf s + 295) 8 = 0 at word
  rw [word] at bytes
  have byte := bytes 0 (by decide)
  simpa only [BitVec.add_zero, show storedByte (0 : BitVec 8) 0 = 0 from rfl] using byte

theorem count_word {s t : RamState} (h : (effect s).Holds s t) :
    memLoad t.external (rspOf s + 328) 64 = s.regValue .rdx >>> 6 := by
  have stores := h.writes
  simp only [effect, Write.AllHold, Operand.read, rspOf] at stores
  exact stores.2.2.2.2.2.2.2.2.2.1

end Hkdf.Proofs.Key.Hash.Initialize
