import Sha3.Proofs.Update.Frame
import Sha3.Proofs.PermutationCall
import Sha3.Proofs.Permutation.Precondition
import Sha3.Proofs.Calls

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem rangeApart_disjoint {a b : BitVec 64} {m n : Nat} (h : RangeApart a m b n) :
    (⟨a.toNat, m⟩ : MemoryRegion).Disjoint ⟨b.toNat, n⟩ := by
  intro x hx hy
  change a.toNat ≤ x ∧ x < a.toNat + m at hx
  change b.toNat ≤ x ∧ x < b.toNat + n at hy
  apply h (x - a.toNat) (by have := hx.1; have := hx.2; omega)
    (x - b.toNat) (by have := hy.1; have := hy.2; omega)
  have ha : a + BitVec.ofNat 64 (x - a.toNat) = BitVec.ofNat 64 x := by
    calc
      a + BitVec.ofNat 64 (x - a.toNat) =
          BitVec.ofNat 64 a.toNat + BitVec.ofNat 64 (x - a.toNat) := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = BitVec.ofNat 64 x := by rw [← BitVec.ofNat_add, Nat.add_sub_of_le hx.1]
  have hb : b + BitVec.ofNat 64 (x - b.toNat) = BitVec.ofNat 64 x := by
    calc
      b + BitVec.ofNat 64 (x - b.toNat) =
          BitVec.ofNat 64 b.toNat + BitVec.ofNat 64 (x - b.toNat) := by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      _ = BitVec.ofNat 64 x := by rw [← BitVec.ofNat_add, Nat.add_sub_of_le hy.1]
  exact ha.trans hb.symm

theorem stackBase_toNat {initial : RamState} (h : Stack.Valid initial stackBytes) :
    (stackBase initial).toNat = (initial.regValue .rsp).toNat - 328 :=
  stack_sub_toNat h.2.2.1 (Nat.le_refl _)

theorem stackBase_low {initial : RamState} (h : Stack.Valid initial stackBytes) :
    (stackBase initial).toNat + 336 < 2 ^ 32 := by
  rw [stackBase_toNat h]
  have hb := h.1
  have hu : 328 ≤ (initial.regValue .rsp).toNat := h.2.2.1
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Bounded,
    userAddressLimit] at hb
  change (initial.regValue .rsp).toNat - 328 + 336 < 2 ^ 32
  change (initial.regValue .rsp).toNat - 328 +
    ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - 328)) < 2 ^ 32 at hb
  omega

theorem CallContext.stackRead [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state) :
    MemReadable initial (stackBase initial) 336 := by
  apply memReadable_of_region hc.stack.1 hc.stack.2.1
  · rw [stackBase_toNat hc.stack]
    exact Nat.le_refl _
  · rw [stackBase_toNat hc.stack]
    have hu : 328 ≤ (initial.regValue .rsp).toNat := hc.stack.2.2.1
    change (initial.regValue .rsp).toNat - 328 + 336 ≤
      (initial.regValue .rsp).toNat - 328 +
        ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - 328))
    omega

def permutationRegions (initial : RamState) : Vector MemoryRegion 2 :=
  #v[⟨(stackBase initial).toNat, 272⟩, ⟨(initial.regValue .rsi).toNat, 200⟩]

theorem permutationRegions_within (initial : RamState) :
    ∀ region ∈ permutationRegions initial, ∀ address, region.Contains address →
      ∃ target ∈ writeRegions initial, target.Contains address := by
  intro region hr address ha
  simp only [permutationRegions, Vector.mem_mk, List.mem_toArray,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change (stackBase initial).toNat ≤ address ∧ address < (stackBase initial).toNat + 272 at ha
    refine ⟨⟨(stackBase initial).toNat, stackBytes⟩, by simp [writeRegions], ?_⟩
    exact ⟨ha.1, by have := ha.2; change address < (stackBase initial).toNat + 328; omega⟩
  · change (initial.regValue .rsi).toNat ≤ address ∧ address < (initial.regValue .rsi).toNat + 200 at ha
    refine ⟨stateRegion initial, by simp [writeRegions], ?_⟩
    exact ⟨ha.1, by have := ha.2; change address < (initial.regValue .rsi).toNat + 201; omega⟩

theorem permutationRegions_saved [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    {j : Nat} (hj : j < 336) (hmin : 272 ≤ j) :
    ∀ region ∈ permutationRegions initial,
      ¬ region.Contains (stackBase initial + BitVec.ofNat 64 j).toNat := by
  have hl := stackBase_low hc.stack
  have hn : (stackBase initial + BitVec.ofNat 64 j).toNat =
      (stackBase initial).toNat + j := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  intro region hr hin
  simp only [permutationRegions, Vector.mem_mk, List.mem_toArray,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change (stackBase initial).toNat ≤ _ ∧ _ < (stackBase initial).toNat + 272 at hin
    rw [hn] at hin
    have := hin.2
    omega
  · change (initial.regValue .rsi).toNat ≤ _ ∧ _ < (initial.regValue .rsi).toNat + 200 at hin
    apply rangeApart_disjoint hc.stateStack _
      ⟨hin.1, by have := hin.2; change _ < (initial.regValue .rsi).toNat + 201; omega⟩
    change (stackBase initial).toNat ≤ _ ∧ _ < (stackBase initial).toNat + 336
    rw [hn]
    exact ⟨by omega, by omega⟩

theorem SavedFrame.of_permutationRegions [Bindings] {v : Variant}
    {initial s t : RamState} {bytes : ByteArray} {state : Incremental.State}
    (hc : CallContext v initial bytes state) (h : SavedFrame initial s)
    (hm : MemoryWriteFrame s t (permutationRegions initial)) : SavedFrame initial t := by
  apply h.of_memoryWriteFrame hm
  · intro region hr i j hj
    have he : frameBase initial + BitVec.ofNat 64 (8 + 8 * i.val) + BitVec.ofNat 64 j =
        stackBase initial + BitVec.ofNat 64 (280 + 8 * i.val + j) := by
      rw [← stackBase_add_272]
      simp only [BitVec.ofNat_add, BitVec.add_assoc]
      congr 1
      simp only [← BitVec.add_assoc]
      congr 2
    rw [he]
    exact permutationRegions_saved hc (by have := i.isLt; omega) (by omega) region hr
  · intro region hr j hj
    rw [← stackBase_add_328]
    have he : stackBase initial + 328 + BitVec.ofNat 64 j =
        stackBase initial + BitVec.ofNat 64 (328 + j) := by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
    rw [he]
    exact permutationRegions_saved hc (by omega) (by omega) region hr

theorem permutationRegions_slot [Bindings] {v : Variant} {initial s t : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    (hm : MemoryWriteFrame s t (permutationRegions initial)) :
    (Operand.mem (frameBase initial) : Operand 64).read t =
      (Operand.mem (frameBase initial) : Operand 64).read s := by
  apply memLoad_congr
  intro j hj
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  apply hm
  rw [← stackBase_add_272]
  have he : stackBase initial + 272 + BitVec.ofNat 64 j =
      stackBase initial + BitVec.ofNat 64 (272 + j) := by
    simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]
  rw [he]
  exact permutationRegions_saved hc (by omega) (by omega)

theorem permutationRegions_cursor [Bindings] {v : Variant} {initial s t : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    (hm : MemoryWriteFrame s t (permutationRegions initial)) :
    cursor (initial.regValue .rsi) t = cursor (initial.regValue .rsi) s := by
  unfold cursor
  congr 1
  change memLoad t.external (initial.regValue .rsi + 200#64) 8 =
    memLoad s.external (initial.regValue .rsi + 200#64) 8
  apply memLoad_congr
  intro j hj
  have hj0 : j = 0 := by omega
  subst j
  simp only [BitVec.add_zero]
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  apply hm
  intro region hr hin
  have hl := hc.stateRead.low
  have hn : (initial.regValue .rsi + 200#64).toNat = (initial.regValue .rsi).toNat + 200 := by
    rw [BitVec.toNat_add]
    change ((initial.regValue .rsi).toNat + 200) % 2 ^ 64 = _
    omega
  simp only [permutationRegions, Vector.mem_mk, List.mem_toArray,
    List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · change (stackBase initial).toNat ≤ _ ∧ _ < (stackBase initial).toNat + 272 at hin
    apply rangeApart_disjoint hc.stateStack (initial.regValue .rsi + 200#64).toNat
    · change (initial.regValue .rsi).toNat ≤ _ ∧ _ < (initial.regValue .rsi).toNat + 201
      rw [hn]
      exact ⟨by omega, by omega⟩
    · exact ⟨hin.1, by have := hin.2; change _ < (stackBase initial).toNat + 336; omega⟩
  · change (initial.regValue .rsi).toNat ≤ _ ∧ _ < (initial.regValue .rsi).toNat + 200 at hin
    rw [hn] at hin
    exact Nat.lt_irrefl _ hin.2

end Sha3.Proofs.Update
