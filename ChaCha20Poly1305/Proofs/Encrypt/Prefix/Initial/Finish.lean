import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Memory
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Initial.Allocator
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Initial.KeyCopy

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper

theorem initial_common [bindings : Bindings] {initial u v w t : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hs : EntryStack initial) (U : Track initial u)
    (V : GTrack allocatorChanges u v) (W : GTrack (keyCopyChanges initial) v w)
    (T : GTrack [.reg 5, .flags, .rip] w t)
    (saved : ∀ k r, (k, r) ∈ ([(8, 5), (16, 15), (24, 14), (32, 13), (40, 12), (48, 3)] :
      List (Nat × BitVec 5)) → wd u (stackPtr initial - BitVec.ofNat 64 k) = rd initial r)
    (keyInput : ValidInput w ⟨(stackPtr initial).toNat - 80, 32⟩ ⟨key.toArray⟩) :
    Common initial t key := by
  have room := hs.room
  have top := hs.top
  have allAgree := ((U.agrees.trans V.agrees).trans W.agrees).trans T.agrees
  have apart : allocatorStateRegion.Disjoint (Stack.region initial 1168) := by
    have h := hc.separation.1
    change [_, _, allocatorStateRegion, Stack.region initial 1168].Pairwise
      MemoryRegion.Disjoint at h
    exact (List.pairwise_cons.mp h.tail.tail).1 _ (by simp)
  have saveWord (k : Nat) (r : BitVec 5)
      (hk : (k, r) ∈ ([(8, 5), (16, 15), (24, 14), (32, 13), (40, 12), (48, 3)] :
        List (Nat × BitVec 5))) :
      (localWord initial k).Word64At t.external (rd initial r) := by
    have bounds : 8 ≤ k ∧ k ≤ 48 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hk
      rcases hk with h | h | h | h | h | h <;> omega
    have va : wd v (stackPtr initial - BitVec.ofNat 64 k) =
        wd u (stackPtr initial - BitVec.ofNat 64 k) := by
      apply gload V.agrees
      intro c hc i hi
      simp only [allocatorChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact nonmem_not_covers rfl _
        | (rintro ⟨j, hj, he⟩
           apply apart (stackPtr initial - BitVec.ofNat 64 k + BitVec.ofNat 64 i).toNat
           · rw [he]
             change 0x300000 ≤ _ ∧ _ < 0x300000 + 16
             simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
             omega
           · change (stackPtr initial).toNat - 1168 ≤ _ ∧
               _ < (stackPtr initial).toNat - 1168 +
                 ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
             rw [slot_toNat (by omega) top (by omega)]
             omega)
    have wa : wd w (stackPtr initial - BitVec.ofNat 64 k) =
        wd v (stackPtr initial - BitVec.ofNat 64 k) := by
      apply gload W.agrees
      intro c hc i hi
      simp only [keyCopyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals first
        | exact nonmem_not_covers rfl _
        | (apply mem_not_covers <;>
            simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
              BitVec.reduceToNat] <;> omega)
    apply slot_word hs allAgree.grow (by omega) (by omega)
      ((mem_keep T.agrees (by simp [Component.isMem]) _).trans
        (wa.trans (va.trans (saved k r hk)))) rfl
  refine
    { ready := T.ready
      code := T.code
      machine := ⟨T.ready.cpu, SupportedSSE.of_agreesExcept allAgree hm.sse,
        T.ready.memory, T.ready.ready⟩
      direction := allAgree.directionFlagClear
        (by simp [changes, allocatorChanges, keyCopyChanges]) hc.directionFlagUnset
      frame := ?_
      grows := allAgree.grow
      savedRbp := saveWord 8 5 (by simp)
      savedR15 := saveWord 16 15 (by simp)
      savedR14 := saveWord 24 14 (by simp)
      savedR13 := saveWord 32 13 (by simp)
      savedR12 := saveWord 40 12 (by simp)
      savedRbx := saveWord 48 3 (by simp)
      keyBytes := input_preserved keyInput (fun a _ =>
        T.agrees.memory a (by simp [Component.Covers])) }
  intro a ha
  have hu : u.external[a]? = initial.external[a]? := by
    apply U.frame hs a
    intro r hr hrange
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    subst r
    apply ha ⟨(stackPtr initial).toNat - 176, 176⟩ (by simp)
    change (stackPtr initial).toNat - 176 ≤ a.toNat ∧
      a.toNat < (stackPtr initial).toNat - 176 + 176
    change (stackPtr initial).toNat - 112 ≤ a.toNat ∧
      a.toNat < (stackPtr initial).toNat - 112 + 112 at hrange
    omega
  have hv : v.external[a]? = u.external[a]? := by
    apply V.agrees.byte
    intro c hc hcov
    simp only [allocatorChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact nonmem_not_covers rfl _ hcov
      | (obtain ⟨i, hi, rfl⟩ := hcov
         apply ha allocatorStateRegion (by simp)
         change 0x300000 ≤ _ ∧ _ < 0x300000 + 16
         simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat]
         omega)
  have hw : w.external[a]? = v.external[a]? := by
    apply W.agrees.byte
    intro c hc hcov
    simp only [keyCopyChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals first
      | exact nonmem_not_covers rfl _ hcov
      | (obtain ⟨i, hi, rfl⟩ := hcov
         apply ha ⟨(stackPtr initial).toNat - 176, 176⟩ (by simp)
         change (stackPtr initial).toNat - 176 ≤ _ ∧
           _ < (stackPtr initial).toNat - 176 + 176
         simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat,
           BitVec.reduceToNat]
         omega)
  exact (T.agrees.memory a (by simp [Component.Covers])).trans (hw.trans (hv.trans hu))


end ChaCha20Poly1305.Proofs.Encrypt.Prefix
