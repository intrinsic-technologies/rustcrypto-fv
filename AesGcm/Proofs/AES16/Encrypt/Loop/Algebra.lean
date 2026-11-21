import AesGcm.Proofs.AES16.Encrypt.State

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Standards.NIST.AES Prelude X86 X86.Machine X86Proofs X86Proofs.Refine X86Proofs.Lift
open AesGcm.Proofs.Machine.Runtime Fixslice16

attribute [local irreducible] memLoad memStore

theorem planes_of_words {mem : Ram} {base : BitVec 64} {planes : Planes16}
    (h : WordsAt mem base 16 (Vector.ofFn planes)) :
    (fun p : Fin 8 ↦ memLoad mem (base + BitVec.ofNat 64 (2 * p.val)) 16) = planes := by
  funext p
  simpa only [wordAddr, Nat.reduceDiv, Vector.getElem_ofFn] using h p.val p.isLt

theorem restore_delayed (planes keys : Planes16) :
    (fun p : Fin 8 ↦ if p.val = 7 then delayedPlanes planes keys p ^^^ keys 7
      else delayedPlanes planes keys p) = planes := by
  funext p
  by_cases hp : p.val = 7
  · have he : p = 7 := Fin.ext hp
    subst p
    simp only [delayedPlanes, show (7 : Fin 8).val = 7 from rfl, ite_true, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  · simp only [delayedPlanes, hp, ite_false]

theorem delay_xor (planes keys : Planes16) :
    delayedPlanes (xorPlanes planes keys) keys =
      (fun p : Fin 8 ↦ if p.val = 7 then planes p else planes p ^^^ keys p) := by
  funext p
  by_cases hp : p.val = 7
  · simp only [delayedPlanes, xorPlanes, hp, ite_true, BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_zero]
  · simp only [delayedPlanes, xorPlanes, hp, ite_false]

theorem roundState_add (v : Variant) (key : Vector UInt8 v.keyBytes)
    (input : Standards.NIST.AES.Block) (j k : Nat) (h : 4 * j + k + 1 < v.Nr) :
    xorPlanes (roundMix ⟨(k + 1) % 4, by omega⟩
      (subBytes (roundState v key input (4 * j + k))))
      (expectedKey v key ⟨4 * j + k + 1, by omega⟩) =
      roundState v key input (4 * j + k + 1) := by
  have hm : (4 * j + k + 1) % 4 = (k + 1) % 4 := by omega
  simpa only [hm] using roundState_next v key input (4 * j + k) h

theorem key_address (base : BitVec 64) (j bias off round plane : Nat)
    (h : 2 * bias + off = 16 * round + 2 * plane) :
    base + (BitVec.ofNat 64 (32 * j + bias) <<< 1) + BitVec.ofNat 64 off =
      base + BitVec.ofNat 64 (16 * (4 * j + round) + 2 * plane) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow,
    show BitVec.twoPow 64 1 = BitVec.ofNat 64 2 by decide +kernel,
    ← BitVec.ofNat_mul, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hn : (32 * j + bias) * 2 + off = 16 * (4 * j + round) + 2 * plane := by omega
  rw [hn]

theorem index_succ (j bias : Nat) :
    BitVec.ofNat 64 (32 * j + bias) + 32 = BitVec.ofNat 64 (32 * (j + 1) + bias) := by
  change BitVec.ofNat 64 (32 * j + bias) + BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_add]
  congr 1
  omega

theorem index_eq_of_bound (j last bias : Nat) (hj : j ≤ last)
    (hb : 32 * last + bias < 2 ^ 64) :
    BitVec.ofNat 64 (32 * j + bias) = BitVec.ofNat 64 (32 * last + bias) ↔ j = last := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hb]
  omega

theorem roundKey_read {mem : Ram} {base : BitVec 64} {v : Variant}
    (h : Readable mem base (16 * (v.Nr + 1))) (r : Fin (v.Nr + 1)) :
    Readable mem (base + BitVec.ofNat 64 (16 * r.val)) 16 := by
  apply h.of_offsets rfl (addr_self base)
  simp only [sub_zero_lit, BitVec.toNat_ofNat]
  have hm := Nat.mod_le (16 * r.val) (2 ^ 64)
  have hr := r.isLt
  omega

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
