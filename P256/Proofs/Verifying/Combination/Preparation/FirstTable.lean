import P256.Proofs.Verifying.Combination.Preparation.Start
import P256.Proofs.Verifying.Combination.TableInvoke
import P256.Proofs.Verifying.Combination.TableSetup.Left

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Preparation

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame TableSetup
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def firstTableSite : TableCallSite :=
  ⟨0x657f, 0x4a6c, by decide, by decide +kernel, by decide⟩

structure FirstTableOutput [Bindings] (s t : RamState) (p q : Projective) : Prop
    extends FrameState s t 96 8808 6552, CopyRegisters s t 4656 where
  rip : t.RIP = 0x1065d9
  table : Table.TableAt t (stackPtr s - 1584) (Table.oddTable p)
  right : ProjectiveAt t (stackPtr s - 5344) q
  cursor : memLoad t.external (stackPtr s - 6520) 64 = stackPtr s - 6496
  point : memLoad t.external (stackPtr s - 6496) 64 = stackPtr s - 5344
  savedInput : memLoad t.external (stackPtr s - 6544) 64 = s.regValue .rsi
  savedOutput : memLoad t.external (stackPtr s - 6536) 64 = s.regValue .rdi

theorem first_table_of_correct (correct : Table.Correct) [Bindings]
    {s t : RamState} {boundary : ReturnBoundary} {p q : Projective} {u v : Nat}
    (pre : Pre s boundary) (input : FirstTableInput s t p q u v) :
    ∃ fuel w, Advances boundary fuel t w ∧ FirstTableOutput s w p q := by
  obtain ⟨n, a, runA, stateA, ripA, tableA, pointA, regsA, keptA⟩ :=
    table_call_of_correct correct pre input.toFrameState firstTableSite
      (by decide) (by decide) input.rip input.input input.output input.cursor
      input.point input.values.1
  have memoryA (off len : Nat) (ho : off ≤ 6552) (hl : len ≤ off + 8)
      (ha : off + 768 ≤ 4656 ∨ 4656 + len ≤ off)
      (hc : off + 8 ≤ 6496 ∨ 6496 + len ≤ off) :
      ∀ i < len, a.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? :=
    keptA off len ho hl ha hc
  have rightT : ProjectiveAt t (stackPtr s - 5344) q := by
    have address : stackPtr s - 5472 + 128 = stackPtr s - 5344 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    simpa only [address] using input.values.2.2.1
  have rightA := rightT.of_bytes_eq (memoryA 5344 96 (by decide) (by decide)
    (Or.inr (by decide)) (Or.inl (by decide)))
  obtain ⟨m, w, runW, stateW, ripW, tableW, regsW, keptW⟩ :=
    left_table_copies pre stateA ripA tableA
      ((regsA .r15 (by simp)).trans input.original)
      ((regsA .r14 (by simp)).trans input.target)
      ((regsA .rbp (by simp)).trans input.temporary)
  have memoryW (off len : Nat) (ho : off ≤ 6552) (hl : len ≤ off + 8)
      (ha : ∀ dst ∈ [6240,3888,3120,1584], off + 768 ≤ dst ∨ dst + len ≤ off) :
      ∀ i < len, w.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? =
        a.external[stackPtr s - BitVec.ofNat 64 off + BitVec.ofNat 64 i]? :=
    keptW off len ho hl ha
  refine ⟨n+m, w, runA.trans runW, stateW, regsW, ripW, tableW, ?_, ?_, ?_, ?_, ?_⟩
  · exact rightA.of_bytes_eq (memoryW 5344 96 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide))
  · refine Eq.trans ?_ input.cursor
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    exact (memoryW 6520 8 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi).trans
      (memoryA 6520 8 (by decide) (by decide) (Or.inr (by decide)) (Or.inr (by decide)) i hi)
  · have value : memLoad a.external (stackPtr s - 6496) 64 = stackPtr s - 5344 := by
      rw [pointA]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    refine Eq.trans ?_ value
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0)
      (memoryW 6496 8 (by decide) (by decide)
        (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi)
  · refine Eq.trans ?_ input.savedInput
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    exact (memoryW 6544 8 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi).trans
      (memoryA 6544 8 (by decide) (by decide) (Or.inr (by decide)) (Or.inr (by decide)) i hi)
  · refine Eq.trans ?_ input.savedOutput
    apply memLoad_congr
    intro i hi
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    exact (memoryW 6536 8 (by decide) (by decide)
      (by intro dst hd; simp at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide) i hi).trans
      (memoryA 6536 8 (by decide) (by decide) (Or.inr (by decide)) (Or.inr (by decide)) i hi)

end P256.Proofs.Verifying.Combination.Preparation
