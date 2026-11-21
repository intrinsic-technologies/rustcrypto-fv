import X86Proofs.Instructions.Movs.Execution
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace P256.Proofs.Common.Memory.Fill

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def registerComponents : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 8, .flags, .rip]

def fillComponents (s : RamState) (count : Nat) : List Component :=
  registerComponents ++ [.reg 7, .mem (s.regValue .rdi) count]

structure FillState [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rdi : t.regValue .rdi = s.regValue .rdi + BitVec.ofNat 64 count
  fill : ∀ i < count, t.external[s.regValue .rdi + BitVec.ofNat 64 i]? = some 0
  agrees : AgreesExcept (fillComponents s count) s t

theorem FillState.start [Bindings] {s : RamState} (h : ReadyToStep s) : FillState s s 0 :=
  ⟨h, by simp, by intro i hi; omega, AgreesExcept.refl _ _⟩

theorem FillState.registers [Bindings] {s t u : RamState} {count : Nat}
    (h : FillState s t count) (hr : ReadyToStep u)
    (he : AgreesExcept registerComponents t u) : FillState s u count := by
  refine ⟨hr, ?_, ?_, ?_⟩
  · exact (he.read (n := 64) (r := 7) (by decide)).trans h.rdi
  · intro i hi
    exact (he.byte (by simp [registerComponents, Component.Covers])).trans (h.fill i hi)
  · exact (h.agrees.trans he).mono (by
      intro c hc
      simp only [List.mem_append] at hc
      rcases hc with hc | hc
      · exact hc
      · exact List.mem_append_left _ hc)

theorem FillState.step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {count : Nat} {code : CodeMap} {pre : RamState → Prop} {effect : RamState → Effect}
    (h : FillState s t count) (hi : StepEffect pre code effect) (hc : CodeIn code t)
    (hp : pre t) (hne : (effect t).rip ≠ boundary.rip)
    (hcomp : ∀ c ∈ (effect t).components, c ∈ registerComponents) :
    ∃ u, Advances boundary 1 t u ∧ FillState s u count ∧ (effect t).Holds t u := by
  obtain ⟨u, ha, hr, he⟩ := hi.advances h.ready hc hp hne
  exact ⟨u, ha, h.registers hr (he.agrees.mono hcomp), he⟩

theorem FillState.append [Bindings] {s t u : RamState} {count more : Nat}
    (h : FillState s t count) (hbound : (s.regValue .rdi).toNat + count + more < 2^64)
    (hr : ReadyToStep u)
    (hd : u.regValue .rdi = t.regValue .rdi + BitVec.ofNat 64 more)
    (hz : ∀ i < more, u.external[t.regValue .rdi + BitVec.ofNat 64 i]? = some 0)
    (he : AgreesExcept [.reg 1, .reg 7, .mem (t.regValue .rdi) more, .rip] t u) :
    FillState s u (count + more) := by
  refine ⟨hr, ?_, ?_, ?_⟩
  · rw [hd, h.rdi, add_ofNat_add_ofNat]
  · intro i hi
    by_cases hold : i < count
    · refine (he.byte ?_).trans (h.fill i hold)
      intro c hmem hcover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl <;> try exact hcover
      obtain ⟨j, hj, hjEq⟩ := hcover
      rw [h.rdi, add_ofNat_add_ofNat] at hjEq
      have hn := congrArg BitVec.toNat hjEq
      rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
      omega
    · have hb := hz (i-count) (by omega)
      rw [h.rdi, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega)] at hb
      exact hb
  · refine (h.agrees.trans he).widen ?_ ?_
    · intro c hc hnm
      simp only [fillComponents, registerComponents, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) |
        (rfl | rfl | rfl | rfl) <;> simp_all [Component.isMem]
    · intro a c hc hcover
      refine ⟨.mem (s.regValue .rdi) (count+more), by simp [fillComponents], ?_⟩
      simp only [fillComponents, registerComponents, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)) |
        (rfl | rfl | rfl | rfl) <;> try exact hcover.elim
      · obtain ⟨i, hi, rfl⟩ := hcover
        exact ⟨i, by omega, rfl⟩
      · obtain ⟨i, hi, rfl⟩ := hcover
        exact ⟨count+i, by omega, by rw [h.rdi, add_ofNat_add_ofNat]⟩

end P256.Proofs.Common.Memory.Fill
