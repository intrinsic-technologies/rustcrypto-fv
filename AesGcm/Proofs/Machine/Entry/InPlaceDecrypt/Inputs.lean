import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Memory
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Tagged
import AesGcm.Proofs.Machine.Core.Interface

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 400000 in
theorem coreMemory_buffer (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (sealed : ByteArray) (hsize : (args[13].get 64).toNat = sealed.size)
    (hbytes : (span (args[12].get 64) sealed.size).HasBytes mem sealed)
    (hr : Readable mem (args[12].get 64) sealed.size)
    (hstack : Readable mem (args[4].get 64) 40)
    (hroom : 8 ≤ (args[4].get 64).toNat)
    (hlarge : 16 ≤ sealed.size)
    (hapart : Outside [span (args[4].get 64 - 8) 48] (args[12].get 64) sealed.size) :
    Core.BufferIn (coreMemory use256 args mem) (args[4].get 64 + 16)
      (args[12].get 64) (args[12].get 64) (sealed.extract 0 (sealed.size - 16)) := by
  have hf := coreMemory_frame use256 args mem hroom (by have := hstack.low; omega)
  obtain ⟨_, _, hs, hd, hn, _⟩ := coreMemory_loads use256 args mem
  have hcsize : (sealed.extract 0 (sealed.size - 16)).size = sealed.size - 16 := by
    simp only [ByteArray.size_extract]
    omega
  have hl : ((args[13].get 64) - 16).toNat = sealed.size - 16 := by
    rw [BitVec.toNat_sub_of_le]
    · rw [hsize]
      rfl
    · change 16 ≤ (args[13].get 64).toNat
      omega
  refine ⟨?_, hs, ?_, ?_, ?_, ?_, Or.inl rfl⟩
  · apply (hstack.of_frame hf).of_offsets rfl (BitVec.add_zero _).symm
    decide
  · have he : args[4].get 64 + (16 : BitVec 64) + (8 : BitVec 64) = args[4].get 64 + (24 : BitVec 64) := by bv_omega
    rw [he]
    exact hd
  · have he : args[4].get 64 + (16 : BitVec 64) + (16 : BitVec 64) = args[4].get 64 + (32 : BitVec 64) := by bv_omega
    rw [he, hn, hl, hcsize]
  · rw [hcsize]
    exact (hr.of_frame hf).sub (Nat.le_refl _) (by omega)
  · have hc := ciphertext_hasBytes hbytes
    refine ⟨rfl, ?_⟩
    intro i
    have hi : i.val < sealed.size := by have := i.isLt; omega
    have hx : (BitVec.ofNat 64 ((args[12].get 64).toNat + i.val)).toNat =
        (args[12].get 64).toNat + i.val := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have := hr.low
      omega
    have hout : Outside [span (args[4].get 64 - 8) 48]
        (BitVec.ofNat 64 ((args[12].get 64).toNat + i.val)) 1 := by
      refine ⟨by rw [hx]; have := hr.low; omega, ?_⟩
      intro region hregion
      have ha := hapart.2 region hregion
      rw [hx]
      omega
    exact (hf.outside _ hout).trans (hc.2 i)

theorem coreMemory_tag (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (sealed : ByteArray) (hsize : (args[13].get 64).toNat = sealed.size)
    (hbytes : (span (args[12].get 64) sealed.size).HasBytes mem sealed)
    (hr : Readable mem (args[12].get 64) sealed.size)
    (hstack : Readable mem (args[4].get 64) 40)
    (hroom : 8 ≤ (args[4].get 64).toNat) (hlarge : 16 ≤ sealed.size) :
    (span (args[4].get 64) 16).HasBytes (coreMemory use256 args mem)
      ⟨(Vector.ofFn fun i : Fin 16 ↦ sealed[sealed.size - 16 + i.val]'(by omega)).toArray⟩ := by
  have hf := coreMemory_frame use256 args mem hroom (by have := hstack.low; omega)
  have hlen : args[13].get 64 - 16 = BitVec.ofNat 64 (sealed.size - 16) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le]
    · rw [hsize, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hr.low; omega)]
      rfl
    · change 16 ≤ (args[13].get 64).toNat
      omega
  obtain ⟨h0, h8, _⟩ := coreMemory_loads use256 args mem
  apply tag_hasBytes_of_words
    (tag_hasBytes hbytes hlarge (by have := hr.low; omega))
    ((hstack.of_frame hf).sub (Nat.le_refl _) (by omega))
  · rw [← hlen]
    have he : args[12].get 64 + (args[13].get 64 - (16 : BitVec 64)) =
        args[12].get 64 + args[13].get 64 - 16 := by bv_omega
    rw [he]
    exact h0
  · rw [← hlen]
    have he : args[12].get 64 + (args[13].get 64 - (16 : BitVec 64)) + (8 : BitVec 64) =
        args[12].get 64 + args[13].get 64 - 8 := by bv_omega
    rw [he]
    exact h8

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
