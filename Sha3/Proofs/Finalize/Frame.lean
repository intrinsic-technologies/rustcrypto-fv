import Sha3.Proofs.Finalize.Contract
import Sha3.Proofs.Outcome

namespace Sha3.Proofs.Finalize

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem CallPre.frameRegion {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {s : RamState} (h : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state s) :
    Stack.region s frameBytes = ⟨(frameBase s).toNat, 304⟩ := by
  have hbase : (frameBase s).toNat = (s.regValue .rsp).toNat - 296 :=
    stack_sub_toNat h.stack.2.2.1 (Nat.le_refl frameBytes)
  rw [hbase]
  change (⟨(s.regValue .rsp).toNat - 296,
    (s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 296)⟩ : MemoryRegion) = _
  have hbottom : 296 ≤ (s.regValue .rsp).toNat := h.stack.2.2.1
  have hsize : (s.regValue .rsp).toNat + 8 - ((s.regValue .rsp).toNat - 296) = 304 := by
    omega
  rw [hsize]

theorem CallPre.frameRead {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {s : RamState} (h : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state s) :
    MemReadable s (frameBase s) 304 := by
  have hb := h.stack.1
  have ha := h.stack.2.1
  rw [h.frameRegion] at hb ha
  exact memReadable_of_region hb ha (Nat.le_refl _) (Nat.le_refl _)

theorem CallPre.frameContains {boundary : ReturnBoundary} {v : Variant} {keccak : Bool} {fullState : Bool} {reset : Bool}
    {state : Incremental.State} {s : RamState} (h : CallPre (keccak := keccak) (fullState := fullState) boundary v reset state s)
    {i : Nat} (hi : i < 304) :
    (Stack.region s frameBytes).Contains (frameBase s + BitVec.ofNat 64 i).toNat := by
  have hl := h.frameRead.low
  rw [h.frameRegion]
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> omega

theorem readable_of_grows {s t : RamState} {a : BitVec 64} {n : Nat}
    (hg : ∀ address : BitVec 64, (s.external[address]?).isSome →
      (t.external[address]?).isSome) (h : MemReadable s a n) : MemReadable t a n :=
  ⟨h.low, fun i hi ↦ hg _ (h.mem i hi)⟩

theorem read_of_agrees {s t : RamState} {cs : List Component} {a : BitVec 64} {n : Nat}
    (h : AgreesExcept cs s t)
    (hsafe : ∀ i < n / 8, ∀ c ∈ cs, ¬ c.Covers (a + BitVec.ofNat 64 i)) :
    (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun x : Option UInt8 ↦ x.getD 0) (h.byte (hsafe i hi))

theorem region_contains_byte {a : BitVec 64} {n i : Nat}
    (hlow : a.toNat + n ≤ 2^32) (hi : i < n) :
    (⟨a.toNat, n⟩ : MemoryRegion).Contains (a + BitVec.ofNat 64 i).toNat := by
  simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> omega

theorem region_contains_offset {a x : BitVec 64} {n : Nat}
    (h : (⟨a.toNat, n⟩ : MemoryRegion).Contains x.toNat) :
    ∃ i < n, x = a + BitVec.ofNat 64 i := by
  change a.toNat ≤ x.toNat ∧ x.toNat < a.toNat + n at h
  refine ⟨x.toNat - a.toNat, by obtain ⟨_, hh⟩ := h; omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have ha := h.1
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem SavedFrame.readable {v : Variant} {fullState : Bool} {initial s : RamState}
    (h : SavedFrame (fullState := fullState) v initial s) {a : BitVec 64} {n : Nat}
    (hr : MemReadable initial a n) : MemReadable s a n := readable_of_grows h.grows hr

theorem frame_offset (initial : RamState) {k : Nat} (hk : k ≤ 296) :
    initial.regValue .rsp - BitVec.ofNat 64 k =
      frameBase initial + BitVec.ofNat 64 (296 - k) := by
  have hn : (296 : BitVec 64) = BitVec.ofNat 64 k + BitVec.ofNat 64 (296 - k) := by
    rw [← BitVec.ofNat_add, Nat.add_sub_of_le hk]
    rfl
  rw [frameBase, hn, ← BitVec.sub_sub, BitVec.sub_add_cancel]

end Sha3.Proofs.Finalize
