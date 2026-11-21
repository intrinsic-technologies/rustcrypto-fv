import X86Proofs.Program.Execution

namespace X86Proofs

open X86 X86.Machine X86.UserProcess

def AdvanceTriple [Bindings] (boundary : ReturnBoundary) (fuel : Nat)
    (pre : RamState → Prop) (code : CodeMap) (post : RamState → RamState → Prop) : Prop :=
  ∀ s, ReadyToStep s → CodeIn code s → pre s →
    ∃ t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn code t ∧ post s t

def ReturnTriple [Bindings] (boundary : ReturnBoundary) (fuel : Nat)
    (pre : RamState → Prop) (code : CodeMap) (post : RamState → RamState → Prop) : Prop :=
  ∀ s, ReadyToStep s → CodeIn code s → pre s →
    ∃ t, Returns boundary fuel s t ∧ post s t

namespace AdvanceTriple

variable [Bindings] {boundary : ReturnBoundary} {m n : Nat}
  {pre pre' mid : RamState → Prop} {code : CodeMap}
  {post post' post₁ post₂ : RamState → RamState → Prop}

theorem refl (boundary : ReturnBoundary) (pre : RamState → Prop) (code : CodeMap) :
    AdvanceTriple boundary 0 pre code Eq := by
  intro s hready hcode _
  exact ⟨s, (advances_zero boundary s s).mpr rfl, hready, hcode, rfl⟩

theorem of_step
    (h : ∀ s, ReadyToStep s → CodeIn code s → pre s → ∃ t,
      Machine.step s = some (.next t) ∧
      (t.RIP ≠ boundary.rip ∨ t.GPR[4] ≠ boundary.rsp) ∧
      ReadyToStep t ∧ CodeIn code t ∧ post s t) :
    AdvanceTriple boundary 1 pre code post := by
  intro s hready hcode hpre
  obtain ⟨t, hstep, hboundary, hready', hcode', hpost⟩ := h s hready hcode hpre
  exact ⟨t, Advances.of_step hstep hboundary, hready', hcode', hpost⟩

theorem of_effect_of_boundary {localCode : CodeMap} {e : RamState → Effect}
    (h : StepEffect pre localCode e) (hsub : ∀ x ∈ localCode, x ∈ code)
    (hav : ∀ s, pre s → (e s).Avoids code)
    (hne : ∀ s t, pre s → (e s).Holds s t →
      t.RIP ≠ boundary.rip ∨ t.GPR[4] ≠ boundary.rsp) :
    AdvanceTriple boundary 1 pre code (Effect.post e) := by
  apply of_step
  intro s hready hcode hpre
  obtain ⟨t, hstep, hready', heffect⟩ := h s hready (hcode.mono hsub) hpre
  exact ⟨t, hstep, hne s t hpre heffect, hready', heffect.codeIn (hav s hpre) hcode,
    heffect⟩

theorem of_effect {localCode : CodeMap} {e : RamState → Effect}
    (h : StepEffect pre localCode e) (hsub : ∀ x ∈ localCode, x ∈ code)
    (hav : ∀ s, pre s → (e s).Avoids code)
    (hne : ∀ s, pre s → (e s).rip ≠ boundary.rip) :
    AdvanceTriple boundary 1 pre code (Effect.post e) := by
  intro s hready hcode hpre
  obtain ⟨t, hrun, hready', heffect⟩ :=
    h.advances hready (hcode.mono hsub) hpre (hne s hpre)
  exact ⟨t, hrun, hready', heffect.codeIn (hav s hpre) hcode, heffect⟩

theorem conseq (h : AdvanceTriple boundary m pre code post)
    (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s t, pre' s → post s t → post' s t) :
    AdvanceTriple boundary m pre' code post' := by
  intro s hready hcode hs
  obtain ⟨t, hrun, hready', hcode', hp⟩ := h s hready hcode (hpre s hs)
  exact ⟨t, hrun, hready', hcode', hpost s t hs hp⟩

theorem seq (h₁ : AdvanceTriple boundary m pre code post₁)
    (h₂ : AdvanceTriple boundary n mid code post₂)
    (hmid : ∀ s t, pre s → post₁ s t → mid t) :
    AdvanceTriple boundary (m + n) pre code
      (fun s u ↦ ∃ t, post₁ s t ∧ post₂ t u) := by
  intro s hready hcode hpre
  obtain ⟨t, hrun₁, hready₁, hcode₁, hpost₁⟩ := h₁ s hready hcode hpre
  obtain ⟨u, hrun₂, hready₂, hcode₂, hpost₂⟩ :=
    h₂ t hready₁ hcode₁ (hmid s t hpre hpost₁)
  exact ⟨u, hrun₁.trans hrun₂, hready₂, hcode₂, t, hpost₁, hpost₂⟩

theorem iterate {invariant : Nat → RamState → Prop} (count fuel : Nat)
    (body : ∀ i, i < count → AdvanceTriple boundary fuel (invariant i) code
      (fun _ t ↦ invariant (i + 1) t)) :
    AdvanceTriple boundary (count * fuel) (invariant 0) code
      (fun _ t ↦ invariant count t) := by
  induction count with
  | zero =>
    simp only [Nat.zero_mul]
    intro s hready hcode hs
    exact ⟨s, (advances_zero boundary s s).mpr rfl, hready, hcode, hs⟩
  | succ count ih =>
    have first := ih (fun i hi ↦ body i (Nat.lt_trans hi (Nat.lt_succ_self count)))
    have last := body count (Nat.lt_succ_self count)
    rw [Nat.succ_mul]
    exact (first.seq last (fun _ _ _ hi ↦ hi)).conseq (fun _ hi ↦ hi)
      (fun _ _ _ ⟨_, _, hi⟩ ↦ hi)

theorem returns (h₁ : AdvanceTriple boundary m pre code post₁)
    (h₂ : ReturnTriple boundary n mid code post₂)
    (hmid : ∀ s t, pre s → post₁ s t → mid t) :
    ReturnTriple boundary (m + n) pre code
      (fun s u ↦ ∃ t, post₁ s t ∧ post₂ t u) := by
  intro s hready hcode hpre
  obtain ⟨t, hrun₁, hready₁, hcode₁, hpost₁⟩ := h₁ s hready hcode hpre
  obtain ⟨u, hrun₂, hpost₂⟩ := h₂ t hready₁ hcode₁ (hmid s t hpre hpost₁)
  exact ⟨u, hrun₁.returns hrun₂, t, hpost₁, hpost₂⟩

end AdvanceTriple

namespace ReturnTriple

variable [Bindings] {boundary : ReturnBoundary} {fuel : Nat}
  {pre pre' : RamState → Prop} {code : CodeMap}
  {post post' : RamState → RamState → Prop}

theorem of_step
    (h : ∀ s, ReadyToStep s → CodeIn code s → pre s → ∃ t,
      Machine.step s = some (.next t) ∧ t.RIP = boundary.rip ∧
      t.GPR[4] = boundary.rsp ∧ post s t) :
    ReturnTriple boundary 1 pre code post := by
  intro s hready hcode hpre
  obtain ⟨t, hstep, hip, hsp, hpost⟩ := h s hready hcode hpre
  exact ⟨t, Returns.of_step hstep hip hsp, hpost⟩

theorem of_effect {localCode : CodeMap} {e : RamState → Effect}
    (h : StepEffect pre localCode e) (hsub : ∀ x ∈ localCode, x ∈ code)
    (hip : ∀ s, pre s → (e s).rip = boundary.rip)
    (hsp : ∀ s t, pre s → (e s).Holds s t → t.GPR[4] = boundary.rsp) :
    ReturnTriple boundary 1 pre code (Effect.post e) := by
  intro s hready hcode hpre
  exact h.returns hready (hcode.mono hsub) hpre (hip s hpre)
    (fun t heffect ↦ hsp s t hpre heffect)

theorem conseq (h : ReturnTriple boundary fuel pre code post)
    (hpre : ∀ s, pre' s → pre s)
    (hpost : ∀ s t, pre' s → post s t → post' s t) :
    ReturnTriple boundary fuel pre' code post' := by
  intro s hready hcode hs
  obtain ⟨t, hrun, hp⟩ := h s hready hcode (hpre s hs)
  exact ⟨t, hrun, hpost s t hs hp⟩

end ReturnTriple

end X86Proofs
