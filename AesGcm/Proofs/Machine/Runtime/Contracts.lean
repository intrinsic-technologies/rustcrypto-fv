import AesGcm.Proofs.Copied.X86Proofs.Refine.Frame
import AesGcm.Proofs.Copied.X86Proofs.Lift.Simulation
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Store

namespace AesGcm.Proofs.Machine.Runtime

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine

def span (base : BitVec 64) (length : Nat) : MemoryRegion := ⟨base.toNat, length⟩

def callStack (fr : Activation) : MemoryRegion :=
  ⟨fr.low.toNat, fr.rsp.toNat + 8 - fr.low.toNat⟩

def BlocksIn (mem : Ram) (base : BitVec 64) (blocks : Vector (Vector UInt8 16) 4) : Prop :=
  ∀ (j : Fin 4) (i : Fin 16),
    mem[base + BitVec.ofNat 64 (16 * j.val + i.val)]? = some blocks[j][i]

def GPRsTyped (values : Values Value Reg.count) : Prop :=
  ∀ r : Fin 16,
    (values[r.val]'(by have := r.isLt; change r.val < 53; omega)).width = 64

theorem GPRsTyped.of_updates {before after : Values Value Reg.count}
    (h : GPRsTyped before) (changed : List Nat)
    (computed : ∀ r : Fin 16, r.val ∈ changed →
      (after[r.val]'(by have := r.isLt; change r.val < 53; omega)).width = 64)
    (unchanged : ∀ r : Fin 16, r.val ∉ changed →
      after[r.val]'(by have := r.isLt; change r.val < 53; omega) =
        before[r.val]'(by have := r.isLt; change r.val < 53; omega)) :
    GPRsTyped after := by
  intro r
  by_cases hr : r.val ∈ changed
  · exact computed r hr
  · rw [unchanged r hr]
    exact h r

theorem GPRsTyped.value {values : Values Value Reg.count} (h : GPRsTyped values)
    (r : Fin 16) : values[r.val]'(by have := r.isLt; change r.val < 53; omega) =
      ⟨64, (values[r.val]'(by have := r.isLt; change r.val < 53; omega)).get 64⟩ := by
  have hv := h r
  generalize values[r.val]'(by have := r.isLt; change r.val < 53; omega) = v at *
  cases v with
  | mk width bits =>
    change width = 64 at hv
    subst width
    simp only [Value.get, BitVec.setWidth_eq]

theorem GPRsTyped.locationOf (P : Lifted) (label : P.Label) (s : RamState) :
    GPRsTyped (P.locationOf label s).arguments := by
  intro r
  simp only [Lifted.locationOf, Vector.getElem_ofFn, Reg.ofIndex, r.isLt, ↓reduceIte, Reg.read]

def CallContract (P : Lifted) (code : CodeMap) (label : P.Label) (frame : FrameInfo)
    (footprint : Activation → List MemoryRegion)
    (pre post : Activation → Ram → Prop) : Prop :=
  ∀ (fr : Activation) (loc : P.Location), loc.label = label →
    loc.store = fr.original →
    Atom.All code loc.arguments loc.store (frame.entryAtoms fr) →
    GPRsTyped loc.arguments →
    pre fr loc.store →
    ∃ output : Output Value Ram Reg.count,
      P.program.Exec (dialect code) ⟨loc, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store (frame.doneAtoms fr) ∧
      GPRsTyped output.values ∧
      RamWriteFrame fr.original output.store (fr.region :: footprint fr) ∧
      post fr output.store

end AesGcm.Proofs.Machine.Runtime
