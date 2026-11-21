import Sha3.Proofs.Permutation.LoadStore.Load.Basic
import X86Proofs.Program.ReadWrite.Bytes
import Sha3.Proofs.Permutation.LoadStore.FrameBridge

namespace Sha3.Proofs.Permutation.Load

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {copy : Copy}

theorem read_mem_of_agrees {s t : RamState} {cs : List Component} {addr : BitVec 64}
    (h : AgreesExcept cs s t)
    (ha : ∀ i, i < 8 → ∀ c ∈ cs, ¬ c.Covers (addr + BitVec.ofNat 64 i)) :
    (Operand.mem addr : Operand 64).read t = (Operand.mem addr : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  simp only [memByte, PhysicalMemory.read]
  exact congrArg (fun x : Option UInt8 ↦ x.getD 0) (h.byte (ha i hi))

theorem Progress.reg {initial s t : RamState} {v : Values} {p : BitVec 64}
    (hs : Progress initial v p s) {e : Effect} (he : e.Holds s t)
    {r : BitVec 5} {value : BitVec 64} (hr : r ≠ 4)
    (hc : ∀ c ∈ e.components, c ∈ [.reg r, .flags, .rip])
    (hv : (Operand.reg r : Operand 64).read t = value) :
    Progress initial (v.setReg r value) e.rip t := by
  have hg := he.agrees.mono hc
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read t = (Operand.mem a : Operand 64).read s := by
    apply read_mem_of_agrees hg
    intro i hi c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact id
  refine ⟨he.rip, ?_, ?_, ?_, ?_, hm _ |>.trans hs.returnSlot, ?_,
    fun a ha ↦ hg.grow a (hs.grow a ha), (hg.scalarFrame_eq (by simp [x86_compose])).trans hs.rest⟩
  · apply Eq.trans (hg.agree (.reg 4) ?_ rfl) hs.stack
    simpa only [List.mem_cons, List.not_mem_nil, Component.reg.injEq,
      reduceCtorEq, or_false] using Ne.symm hr
  · intro q hq
    by_cases hqr : q = r
    · subst q
      simpa only [Values.setReg, ite_true] using hv
    · simp only [Values.setReg, ite_eq_right hqr]
      apply Eq.trans (hg.read ?_) (hs.registers q hq)
      simpa only [List.mem_cons, List.not_mem_nil, Component.reg.injEq,
        reduceCtorEq, or_false] using hqr
  · intro i value hi
    exact (hm _).trans (hs.slots i value hi)
  · intro i
    exact (hm _).trans (hs.saved i)
  · intro a ha
    apply Eq.trans (hg.byte ?_) (hs.memory a ha)
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact id

theorem Progress.noop {initial s t : RamState} {v : Values} {p : BitVec 64}
    (hs : Progress initial v p s) {e : Effect} (he : e.Holds s t)
    (hc : ∀ c ∈ e.components, c ∈ [.flags, .rip]) : Progress initial v e.rip t := by
  have hg := he.agrees.mono hc
  have hm (a : BitVec 64) :
      (Operand.mem a : Operand 64).read t = (Operand.mem a : Operand 64).read s := by
    apply read_mem_of_agrees hg
    intro i hi c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact id
  refine ⟨he.rip, ?_, ?_, ?_, ?_, hm _ |>.trans hs.returnSlot, ?_,
    fun a ha ↦ hg.grow a (hs.grow a ha), (hg.scalarFrame_eq (by simp [x86_compose])).trans hs.rest⟩
  · exact Eq.trans (hg.agree (.reg 4) (by simp) rfl) hs.stack
  · intro r hr
    exact (hg.read (by simp)).trans (hs.registers r hr)
  · intro i value hi
    exact (hm _).trans (hs.slots i value hi)
  · intro i
    exact (hm _).trans (hs.saved i)
  · intro a ha
    apply Eq.trans (hg.byte ?_) (hs.memory a ha)
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact id

theorem slotAddress_sub (initial : RamState) {i : Nat} (hi : i ≤ 33) :
    slotAddress initial i = initial.regValue .rsp - BitVec.ofNat 64 (264 - 8 * i) := by
  have h : 8 * i ≤ 264 := by omega
  unfold slotAddress frameBase
  rw [← BitVec.ofNat_sub_ofNat_of_le 264 (8 * i) (by omega) h]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  rfl

theorem Pre.slot_frame {initial : RamState} (hp : Pre copy initial)
    (i : Fin 27) {j : Nat} (hj : j < 8) :
    (⟨(frameBase initial).toNat, frameBytes⟩ : MemoryRegion).Contains
      (slotAddress initial i.val + BitVec.ofNat 64 j).toNat := by
  have hn := hp.entry.stack.2.2.1
  change frameBytes ≤ (initial.regValue .rsp).toNat at hn
  have hb : (frameBase initial).toNat = (initial.regValue .rsp).toNat - frameBytes :=
    stack_sub_toNat hn (Nat.le_refl frameBytes)
  have hi := i.isLt
  have hsp := (initial.regValue .rsp).isLt
  simp only [slotAddress, MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat, hb]
  change 264 ≤ (initial.regValue .rsp).toNat at hn
  change _ ≤ _ ∧ _ < _
  simp only [frameBytes]
  omega

theorem slotAddress_apart (initial : RamState) {i j : Fin 27} (hij : i ≠ j) :
    RangeApart (slotAddress initial i.val) 8 (slotAddress initial j.val) 8 := by
  have hi := i.isLt
  have hj := j.isLt
  have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  exact RangeApart.offsets (frameBase initial) (by omega) (by omega) (by omega)

theorem slotAddress_saved_apart (initial : RamState) (i : Fin 27) (j : Fin 6) :
    RangeApart (slotAddress initial i.val) 8
      (frameBase initial + BitVec.ofNat 64 (216 + 8 * j.val)) 8 := by
  have hi := i.isLt
  have hj := j.isLt
  exact RangeApart.offsets (frameBase initial) (by omega) (by omega) (.inl (by omega))

theorem slotAddress_return_apart (initial : RamState) (i : Fin 27) :
    RangeApart (slotAddress initial i.val) 8 (initial.regValue .rsp) 8 := by
  rw [← frameBase_add_frameBytes initial]
  have hi := i.isLt
  exact RangeApart.offsets (frameBase initial) (by omega) (by decide)
    (.inl (by change 8 * i.val + 8 ≤ 264; omega))

theorem Progress.slot {initial s t : RamState} {v : Values} {p : BitVec 64}
    (hs : Progress initial v p s) (hp : Pre copy initial) {e : Effect} (he : e.Holds s t)
    (i : Fin 27) {value : BitVec 64}
    (hc : ∀ c ∈ e.components, c ∈ [.mem (slotAddress initial i.val) 8, .rip])
    (hv : (Operand.mem (slotAddress initial i.val) : Operand 64).read t = value) :
    Progress initial (v.setSlot i value) e.rip t := by
  have hg := he.agrees.mono hc
  have hm (a : BitVec 64) (ha : RangeApart (slotAddress initial i.val) 8 a 8) :
      (Operand.mem a : Operand 64).read t = (Operand.mem a : Operand 64).read s := by
    apply read_mem_of_agrees hg
    intro j hj c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨k, hk, heq⟩ := hcov
      exact ha k hk j hj heq.symm
    · exact hcov
  refine ⟨he.rip, ?_, ?_, ?_, ?_,
    (hm _ (slotAddress_return_apart initial i)).trans hs.returnSlot, ?_,
    fun a ha ↦ hg.grow a (hs.grow a ha), (hg.scalarFrame_eq (by simp [x86_compose])).trans hs.rest⟩
  · exact Eq.trans (hg.agree (.reg 4) (by simp) rfl) hs.stack
  · intro r hr
    exact (hg.read (by simp)).trans (hs.registers r hr)
  · intro j value' hj
    by_cases hji : j = i
    · subst j
      simp only [Values.setSlot, ite_true, Option.some.injEq] at hj
      exact hv.trans hj
    · simp only [Values.setSlot, ite_eq_right hji] at hj
      exact (hm _ (slotAddress_apart initial (Ne.symm hji))).trans (hs.slots j value' hj)
  · intro j
    exact (hm _ (slotAddress_saved_apart initial i j)).trans (hs.saved j)
  · intro a ha
    apply Eq.trans (hg.byte ?_) (hs.memory a ha)
    intro c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hcov
      exact ha ⟨(frameBase initial).toNat, frameBytes⟩ (by simp)
        (heq ▸ hp.slot_frame i hj)
    · exact hcov

theorem Progress.readable {initial s : RamState} {v : Values} {p addr : BitVec 64}
    {n : Nat} (hs : Progress initial v p s) (hr : MemReadable initial addr n) :
    MemReadable s addr n :=
  ⟨hr.low, fun i hi ↦ hs.grow _ (hr.mem i hi)⟩

theorem Progress.input_readable {initial s : RamState} {v : Values} {p : BitVec 64}
    (hs : Progress initial v p s) (hp : Pre copy initial) :
    MemReadable s (initial.regValue .rdi) 200 := hs.readable hp.input

theorem Pre.slot_readable {initial : RamState} (hp : Pre copy initial) (i : Fin 27) :
    MemReadable initial (slotAddress initial i.val) 8 := by
  have hi := i.isLt
  rw [slotAddress_sub initial (by omega)]
  exact hp.entry.readable (by omega) (by change _ ≤ 264; omega)

theorem Progress.slot_readable {initial s : RamState} {v : Values} {p : BitVec 64}
    (hs : Progress initial v p s) (hp : Pre copy initial) (i : Fin 27) :
    MemReadable s (slotAddress initial i.val) 8 := hs.readable (hp.slot_readable i)

theorem Pre.slot_avoid {initial : RamState} (hp : Pre copy initial) (i : Fin 27)
    {j : Nat} (hj : j < 8) :
    ¬ (InProgram (slotAddress initial i.val + BitVec.ofNat 64 j) ∨
      InPageTables (slotAddress initial i.val + BitVec.ofNat 64 j)) := by
  have hi := i.isLt
  rw [slotAddress_sub initial (by omega)]
  exact hp.entry.slot_avoid (by omega) (by change _ ≤ 264; omega) hj

theorem Pre.slot_page {initial : RamState} (hp : Pre copy initial) (i : Fin 27) :
    (slotAddress initial i.val).toNat % 4096 + 8 ≤ 4096 := by
  have hi := i.isLt
  rw [slotAddress_sub initial (by omega)]
  exact hp.entry.page (by change _ ≤ 264; omega) (by omega)

theorem Pre.slot_apart {initial : RamState} (hp : Pre copy initial) (i : Fin 27)
    {p : BitVec 64} {bytes : List UInt8}
    (hc : ∀ x ∈ codeRange p bytes, InProgram x.1) :
    RangeApart (slotAddress initial i.val) 8 p bytes.length := by
  intro j hj k hk heq
  exact hp.slot_avoid i hj (.inl (heq ▸ hc _ (mem_codeRange p bytes k hk)))

theorem Pre.input_lane_readable {initial : RamState} (hp : Pre copy initial) (i : Fin 25) :
    MemReadable initial (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 8 := by
  have hi := i.isLt
  refine ⟨?_, ?_⟩
  · have hl := hp.input.low
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro j hj
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using
      hp.input.mem (8 * i.val + j) (by omega)

theorem Progress.input_lane_readable {initial s : RamState} {v : Values} {p : BitVec 64}
    (hs : Progress initial v p s) (hp : Pre copy initial) (i : Fin 25) :
    MemReadable s (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) 8 :=
  hs.readable (hp.input_lane_readable i)

theorem Progress.input_lane {initial s : RamState} {v : Values} {p : BitVec 64}
    (hs : Progress initial v p s) (hp : Pre copy initial) (i : Fin 25) :
    (Operand.mem (initial.regValue .rdi + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read s =
      memoryLanes (initial.regValue .rdi) initial i := by
  apply read_mem_of_memoryWriteFrame hs.memory
  intro j hj k hk
  have hi := i.isLt
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using
    hp.apart j hj (8 * i.val + k) (by omega)

end Sha3.Proofs.Permutation.Load
