import P256.Proofs.Nonce.Update.Absorb.HmacAppend

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem hmacStateAt_copy_used {s t : RamState} {a : BitVec 64} {key input : ByteArray}
    (old : HMAC.HmacStateAt s a key input)
    (copied : ∀ i < 168, i < 64 + input.size % 64 ∨ 127 ≤ i →
      t.external[a + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?) :
    HMAC.HmacStateAt t a key input := by
  have rem : (HMAC.keyPad key 0x36 ++ input).size % 64 = input.size % 64 := by
    rw [ByteArray.size_append,HMAC.keyPad_size]; omega
  refine ⟨hasBytes_copy old.outer (fun i hi => copied i (by omega) (.inl (by omega))),
    hasBytes_copy old.inner.buffer ?_, ?_, SHA256.HashStateAt.copy old.inner.hash ?_,
    loadBytes_ok_copy ?_ old.inner.count⟩
  · intro i hi
    rw [rem] at hi
    have h := copied (64+i) (by omega) (.inl (by omega))
    simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using h
  · have h := copied 127 (by decide) (.inr (by decide))
    have oldPos := old.inner.position
    simp only [BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] at oldPos ⊢
    exact h.trans oldPos
  · intro i hi
    have h := copied (128+i) (by omega) (.inr (by omega))
    simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using h
  · intro i hi
    have h := copied (160+i) (by omega) (.inr (by omega))
    simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using h

end P256.Proofs.Nonce.Update.Absorb
