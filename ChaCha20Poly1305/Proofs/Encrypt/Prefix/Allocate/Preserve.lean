import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Memory

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper

theorem Common.stack_step [Bindings] {initial s t : RamState} {key : Vector UInt8 32}
    {cs : List Component} (h : Common initial s key) (st : EntryStack initial)
    (ht : GTrack cs s t) (df : .df ∉ cs)
    (writes : ∀ c ∈ cs, ∀ a, c.Covers a →
      (stackPtr initial).toNat - 176 ≤ a.toNat ∧ a.toNat < (stackPtr initial).toNat - 136) :
    Common initial t key := by
  have room := st.room
  apply h.step (by omega) st.top ht.agrees df ht.ready ht.code
  · apply ht.agrees.memoryWriteFrame
    intro c hc a ha
    obtain ⟨lo, hi⟩ := writes c hc a ha
    refine ⟨⟨(stackPtr initial).toNat - 176, 176⟩, by simp, ?_⟩
    change _ - 176 ≤ a.toNat ∧ a.toNat < _ - 176 + 176
    omega
  · intro a lo hi
    apply ht.agrees.byte
    intro c hc ha
    have h := writes c hc a ha
    omega

theorem stack_component_bounds {initial : RamState} (st : EntryStack initial)
    {k i : Nat} (hk : 144 ≤ k) (hk' : k ≤ 176) (hi : i < 8) :
    (stackPtr initial).toNat - 176 ≤
        (stackPtr initial - BitVec.ofNat 64 k + BitVec.ofNat 64 i).toNat ∧
      (stackPtr initial - BitVec.ofNat 64 k + BitVec.ofNat 64 i).toNat <
        (stackPtr initial).toNat - 136 := by
  have hr := st.room
  rw [slot_toNat (by omega) st.top (by omega)]
  omega

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
