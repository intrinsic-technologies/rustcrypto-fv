import P256.Proofs.Program.SavePair
import P256.Proofs.Program.CallMemory
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def wrapperRegions (routine : Routine) (s : RamState) : Vector MemoryRegion 3 :=
  #v[allocatorStateRegion, randomSourceRegion, callStack routine s]

theorem stack_component_within {routine : Routine} {s : RamState}
    (hs : Stack.Valid s routine.minStackBytes)
    {offset len : Nat} (ho : offset ≤ routine.minStackBytes) (hl : len ≤ offset + 8)
    {address : BitVec 64}
    (hc : (Component.mem (stackPtr s - BitVec.ofNat 64 offset) len).Covers address) :
    (callStack routine s).Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  apply stack_contains_callStack
  apply memoryRegion_contains_add hs.1 (len := len) _ _ hi
  · rw [stack_sub_toNat hs ho]
    change (stackPtr s).toNat - routine.minStackBytes ≤ (stackPtr s).toNat - offset
    omega
  · rw [stack_region_end, stack_sub_toNat hs ho]
    have := (stack_bounds hs).1
    omega

theorem saved_frame {routine : Routine} {s t : RamState} [Bindings]
    {codeOffset : Nat} {locals : BitVec 8} (hs : Stack.Valid s routine.minStackBytes)
    (space : 16 ≤ routine.minStackBytes) (h : SavePair.SavedEntry s t codeOffset locals) : MemoryWriteFrame s t (wrapperRegions routine s) := by
  apply h.agrees.memoryWriteFrame
  intro c hc a hv
  simp only [SavePair.saveComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  all_goals refine ⟨callStack routine s, by simp [wrapperRegions], ?_⟩
  · exact stack_component_within hs (offset := 8) (by omega) (by decide) hv
  · exact stack_component_within hs (offset := 16) (by omega) (by decide) hv

theorem wrapper_frame_loaded {routine : Routine} {s t : RamState} [Bindings]
    {inputs : List ByteArray} {slices : Array Input}
    (hcall : ValidCallWithSlices routine s inputs slices)
    (loaded : ProgramLoaded s) (frame : MemoryWriteFrame s t (wrapperRegions routine s)) :
    ProgramLoaded t := by
  intro a b hf
  rw [frame a]
  · exact loaded a b hf
  · intro region hr hc
    have hm : region ∈ #v[heapRegion routine s, allocatorStateRegion,
        randomSourceRegion, callStack routine s] := by
      simp_all [wrapperRegions]
    exact (hcall.separation.2 region hm).2 a hc (.inl ⟨b, hf⟩)

theorem wrapper_read_disjoint {routine : Routine} {s : RamState} [Bindings]
    {inputs : List ByteArray} {slices : Array Input}
    (hcall : ValidCallWithSlices routine s inputs slices)
    {region : MemoryRegion} (hr : region ∈ readRegions s slices) :
    ∀ written ∈ wrapperRegions routine s, region.Disjoint written := by
  intro written hw
  have hm : written ∈ #v[heapRegion routine s, allocatorStateRegion,
      randomSourceRegion, callStack routine s] := by
    simp_all [wrapperRegions]
  exact (hcall.separation.2 written hm).1 region hr

theorem static_component_within {offset : Nat}
    (ho : offset ∈ ([0,8,16,24,32] : List Nat)) {address : BitVec 64}
    (hc : (Component.mem (0x300000 + BitVec.ofNat 64 offset) 8).Covers address) :
    ∃ region ∈ #v[allocatorStateRegion, randomSourceRegion], region.Contains address.toNat := by
  obtain ⟨i, hi, rfl⟩ := hc
  have hb : offset + 8 ≤ 40 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    omega
  have hn : ((0x300000 : BitVec 64) + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      3145728 + offset + i := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    change ((3145728 + offset % 2^64) % 2^64 + i % 2^64) % 2^64 = _
    omega
  by_cases hx : offset < 24
  · refine ⟨allocatorStateRegion, by simp, ?_⟩
    change 3145728 ≤ _ ∧ _ < 3145728 + 24
    rw [hn]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    constructor <;> omega
  · refine ⟨randomSourceRegion, by simp, ?_⟩
    change 3145752 ≤ _ ∧ _ < 3145752 + 16
    rw [hn]
    constructor <;> omega

theorem stack_sub_apart {s : RamState} {reserve : Nat} (hs : Stack.Valid s reserve)
    {a b na nb : Nat} (ha : a ≤ reserve) (hb : b ≤ reserve)
    (hna : na ≤ a + 8) (hnb : nb ≤ b + 8)
    (hd : b + na ≤ a ∨ a + nb ≤ b) :
    RangeApart (stackPtr s - BitVec.ofNat 64 a) na (stackPtr s - BitVec.ofNat 64 b) nb := by
  have bounds := stack_bounds hs
  intro i hi j hj he
  have hea := stack_sub_toNat hs ha
  have heb := stack_sub_toNat hs hb
  have he' := congrArg BitVec.toNat he
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, hea, heb] at he'
  omega

theorem memLoad_agrees_apart {s t : RamState} {cs : List Component} {address : BitVec 64} {n : Nat}
    (agrees : AgreesExcept cs s t)
    (apart : ∀ a len, Component.mem a len ∈ cs → RangeApart a len address (n/8)) :
    memLoad t.external address n = memLoad s.external address n := by
  apply memLoad_congr
  intro i hi
  have he := agrees.byte (x := address + BitVec.ofNat 64 i) (by
    intro c hc hv
    cases c <;> try exact hv.elim
    rename_i a len
    obtain ⟨j, hj, he⟩ := hv
    exact apart a len hc j hj i hi he.symm)
  change (t.external[address + BitVec.ofNat 64 i]?).getD 0 = _
  rw [he]
  rfl

theorem hasBytes_agrees_apart {s t : RamState} {cs : List Component}
    {address : BitVec 64} {len : Nat} {bytes : ByteArray}
    (agrees : AgreesExcept cs s t)
    (apart : ∀ a n, Component.mem a n ∈ cs → RangeApart a n address len)
    (hb : (MemoryRegion.mk address.toNat len).HasBytes s.external bytes) :
    (MemoryRegion.mk address.toNat len).HasBytes t.external bytes := by
  refine ⟨hb.1, ?_⟩
  intro i
  have hi : i.val < len := by have hsize : bytes.size = len := hb.1; omega
  have hf := agrees.byte (x := address + BitVec.ofNat 64 i.val) (by
    intro c hc hv
    cases c <;> try exact hv.elim
    rename_i a n
    obtain ⟨j, hj, he⟩ := hv
    exact apart a n hc j hj i.val hi he.symm)
  have hbi := hb.2 i
  change t.external[BitVec.ofNat 64 (address.toNat + i.val)]? = _
  change s.external[BitVec.ofNat 64 (address.toNat + i.val)]? = _ at hbi
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hbi ⊢
  exact hf.trans hbi

end P256.Proofs.Program
