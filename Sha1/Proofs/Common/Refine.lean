import Prelude.Execution.CallingConvention
import Prelude.Execution.Termination
import Prelude.Memory
import X86Proofs.Instructions.Branch.Cond
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Call.Form
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Jmp.Generated.M.Triple
import X86Proofs.Instructions.Jmp.Generated.R.Triple
import X86Proofs.Program.Compose
import X86Proofs.Program.Entry
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Program.ReadWrite.Stack
import X86Proofs.Program.ReadWrite.Store
import X86Proofs.Program.ReadWrite.WriteFrame
import X86Proofs.Step.Paging
import X86Proofs.Step.Sse

namespace Sha1.Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs Prelude

instance (rex : BitVec 8) : Decidable (RexPrefix rex) := by unfold RexPrefix; infer_instance
instance (rex : BitVec 8) : Decidable (RexWPrefix rex) := by unfold RexWPrefix; infer_instance
instance (rex : BitVec 8) : Decidable (RexNoWPrefix rex) := by unfold RexNoWPrefix; infer_instance

def InRegion (r : MemoryRegion) (a : BitVec 64) (n : Nat) : Prop :=
  r.start ≤ a.toNat ∧ a.toNat + n ≤ r.start + r.size ∧ a.toNat + n ≤ 2 ^ 64

def InRegions (regions : List MemoryRegion) (a : BitVec 64) (n : Nat) : Prop :=
  ∃ r ∈ regions, InRegion r a n

def Outside (regions : List MemoryRegion) (a : BitVec 64) (n : Nat) : Prop :=
  a.toNat + n ≤ 2 ^ 64 ∧ ∀ r ∈ regions, a.toNat + n ≤ r.start ∨ r.start + r.size ≤ a.toNat

def RegionsWithin (small big : List MemoryRegion) : Prop :=
  ∀ r ∈ small, ∃ r' ∈ big, r'.start ≤ r.start ∧ r.start + r.size ≤ r'.start + r'.size

structure RamWriteFrame (original mem : Ram) (regions : List MemoryRegion) : Prop where
  outside : ∀ x : BitVec 64, Outside regions x 1 → mem[x]? = original[x]?
  present : ∀ x : BitVec 64, (original[x]?).isSome → (mem[x]?).isSome

theorem RamWriteFrame.refl (m : Ram) (regions : List MemoryRegion) : RamWriteFrame m m regions :=
  ⟨fun _ _ => rfl, fun _ h => h⟩

private theorem ne_of_inRegion {r : MemoryRegion} {a x : BitVec 64} {n i : Nat}
    (hin : InRegion r a n) (hi : i < n) (hx : x.toNat + 1 ≤ r.start ∨ r.start + r.size ≤ x.toNat) :
    a + BitVec.ofNat 64 i ≠ x := by
  intro he
  have he' := congrArg BitVec.toNat he
  obtain ⟨h1, h2, h3⟩ := hin
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at he'
  rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)] at he'
  omega

theorem RamWriteFrame.memStore {o m : Ram} {regions : List MemoryRegion}
    (h : RamWriteFrame o m regions) {a : BitVec 64} {n : Nat} (v : BitVec n)
    (hin : InRegions regions a (n / 8)) :
    RamWriteFrame o (memStore m a v) regions where
  outside x hx := by
    obtain ⟨r, hr, hin⟩ := hin
    rw [memStore_getElem?_of_ne m a v x fun i hi => ne_of_inRegion hin hi (hx.2 r hr)]
    exact h.outside x hx
  present x hx := memStore_isSome m a v x (h.present x hx)

theorem RamWriteFrame.trans {o m m' : Ram} {regions regions' : List MemoryRegion}
    (h₁ : RamWriteFrame o m regions) (h₂ : RamWriteFrame m m' regions')
    (hw : RegionsWithin regions' regions) : RamWriteFrame o m' regions where
  outside x hx := by
    rw [h₂.outside x ⟨hx.1, fun r hr => ?_⟩, h₁.outside x hx]
    obtain ⟨r', hr', h1, h2⟩ := hw r hr
    rcases hx.2 r' hr' with h | h <;> omega
  present x hx := h₂.present x (h₁.present x hx)

theorem RamWriteFrame.memLoad_eq {o m : Ram} {regions : List MemoryRegion}
    (h : RamWriteFrame o m regions) {a : BitVec 64} {k : Nat} (hout : Outside regions a (k / 8)) :
    memLoad m a k = memLoad o a k := by
  apply memLoad_congr
  intro i hi
  simp only [memByte, PhysicalMemory.read]
  have := a.isLt
  have := hout.1
  have hx : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by have := hout.1; omega)]
  rw [h.outside _ ⟨by omega, fun r hr => by rcases hout.2 r hr with h' | h' <;> omega⟩]

theorem RamWriteFrame.memoryWriteFrame {initial t : RamState} {rs : List MemoryRegion} {n : Nat}
    {regions : Vector MemoryRegion n} (h : RamWriteFrame initial.external t.external rs)
    (hregions : ∀ x, (∀ r ∈ regions, ¬ r.Contains x) → ∀ r ∈ rs, ¬ r.Contains x) :
    MemoryWriteFrame initial t regions := by
  intro a ha
  refine h.outside a ⟨by omega, fun r hr => ?_⟩
  have hc := hregions a.toNat ha r hr
  simp only [MemoryRegion.Contains, not_and, Nat.not_lt] at hc
  omega

end Sha1.Proofs.Refine
