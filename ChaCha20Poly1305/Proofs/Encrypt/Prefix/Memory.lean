import ChaCha20Poly1305.Proofs.Encrypt.Prefix.State
import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper

theorem input_preserved {s t : RamState} {r : MemoryRegion} {bytes : ByteArray}
    (h : ValidInput s r bytes)
    (he : ∀ a : BitVec 64, r.Contains a.toNat → t.external[a]? = s.external[a]?) :
    ValidInput t r bytes := by
  refine ⟨h.1, h.2.1, fun i => ?_⟩
  rw [he]
  · exact h.2.2 i
  · have hb := h.1
    have hl := h.2.1
    change bytes.size = r.size at hl
    change r.start + r.size < 2^32 at hb
    simp only [MemoryRegion.Contains, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by have := i.isLt; omega)]
    have := i.isLt
    omega

theorem word_preserved {s t : RamState} {r : MemoryRegion} {value : BitVec 64}
    (hb : r.Bounded) (h : r.Word64At s.external value)
    (he : ∀ a : BitVec 64, r.Contains a.toNat → t.external[a]? = s.external[a]?) :
    r.Word64At t.external value := by
  obtain ⟨start, size⟩ := r
  have hz : size = 8 := h.1.symm
  subst size
  have hb : start + 8 < 2^32 := hb
  have hx (i : Nat) (hi : i < 8) :
      t.external[BitVec.ofNat 64 start + BitVec.ofNat 64 i]? =
      s.external[BitVec.ofNat 64 start + BitVec.ofNat 64 i]? := by
    apply he
    simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine word64At_of_memLoad (a := BitVec.ofNat 64 start) ?_ ?_ rfl
  · intro i hi
    rw [hx i hi]
    exact loadBytes_isSome h.2 i hi
  · rw [← word64At_memLoad h]
    apply memLoad_congr
    intro i hi
    change i < 8 at hi
    change (t.external[BitVec.ofNat 64 start + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[BitVec.ofNat 64 start + BitVec.ofNat 64 i]?).getD 0
    rw [hx i hi]

theorem original_input {initial s : RamState} {key : Vector UInt8 32}
    {nonce : Vector UInt8 12} {aad msg bytes : ByteArray} {r : MemoryRegion}
    (hc : ValidCall encrypt initial [key, nonce, aad, msg])
    (hf : MemoryWriteFrame initial s
      #v[heapRegion encrypt initial, allocatorStateRegion, ⟨(stackPtr initial).toNat - 176, 176⟩])
    (hr : r ∈ readRegions encrypt initial [key, nonce, aad, msg])
    (hi : ValidInput initial r bytes) : ValidInput s r bytes := by
  have room : 1168 ≤ (stackPtr initial).toNat := hc.stackAvailable.2.2.1
  apply input_preserved hi
  intro a ha
  apply hf a
  intro w hw hwc
  simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact hc.separation.2.1 _ (by simp [writtenRegions, encrypt]) r hr a.toNat hwc ha
  · exact hc.separation.2.1 _ (by simp [writtenRegions, encrypt]) r hr a.toNat hwc ha
  · apply hc.separation.2.1 (Stack.region initial 1168)
      (by simp [writtenRegions, encrypt]) r hr a.toNat ?_ ha
    change _ - 176 ≤ a.toNat ∧ a.toNat < _ - 176 + 176 at hwc
    change (stackPtr initial).toNat - 1168 ≤ a.toNat ∧
      a.toNat < (stackPtr initial).toNat - 1168 +
        ((stackPtr initial).toNat + 8 - ((stackPtr initial).toNat - 1168))
    omega

theorem Common.step [bindings : Bindings] {initial s t : RamState} {key : Vector UInt8 32}
    {cs : List Component} (h : Common initial s key)
    (room : 176 ≤ (stackPtr initial).toNat) (top : (stackPtr initial).toNat + 8 < 2^32)
    (he : AgreesExcept cs s t) (hd : .df ∉ cs)
    (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t)
    (hf : MemoryWriteFrame s t
      #v[heapRegion encrypt initial, allocatorStateRegion, ⟨(stackPtr initial).toNat - 176, 176⟩])
    (hk : ∀ a : BitVec 64, (stackPtr initial).toNat - 80 ≤ a.toNat →
      a.toNat < (stackPtr initial).toNat → t.external[a]? = s.external[a]?) :
    Common initial t key := by
  have hw {k : Nat} {value : BitVec 64} (hk8 : 8 ≤ k) (hk80 : k ≤ 80)
      (hw : (localWord initial k).Word64At s.external value) :
      (localWord initial k).Word64At t.external value := by
    apply word_preserved (by change _ - k + 8 < 2^32; omega) hw
    intro a ha
    change _ - k ≤ a.toNat ∧ a.toNat < _ - k + 8 at ha
    exact hk a (by omega) (by omega)
  exact
    { ready := hr
      code := hc
      machine := ⟨hr.cpu, SupportedSSE.of_agreesExcept he h.machine.sse, hr.memory, hr.ready⟩
      direction := he.directionFlagClear hd h.direction
      frame := memoryWriteFrame_trans h.frame hf
      grows := fun a ha => he.grow a (h.grows a ha)
      savedRbp := hw (by omega) (by omega) h.savedRbp
      savedR15 := hw (by omega) (by omega) h.savedR15
      savedR14 := hw (by omega) (by omega) h.savedR14
      savedR13 := hw (by omega) (by omega) h.savedR13
      savedR12 := hw (by omega) (by omega) h.savedR12
      savedRbx := hw (by omega) (by omega) h.savedRbx
      keyBytes := input_preserved h.keyBytes (fun a ha => hk a ha.1 (by
        have hlt := ha.2
        change a.toNat < _ - 80 + 32 at hlt
        omega)) }

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
