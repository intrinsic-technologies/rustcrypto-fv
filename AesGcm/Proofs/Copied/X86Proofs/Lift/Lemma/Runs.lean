import AesGcm.Proofs.Copied.X86Proofs.Lift.Lockstep

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG

theorem CodeAt.mono {code code' : CodeMap} {a : BitVec 64} (h : CodeAt code a)
    (hsub : ∀ x ∈ code, x ∈ code') : CodeAt code' a :=
  let ⟨b, hb⟩ := h
  ⟨b, hsub _ hb⟩

theorem ReturnOutside.ne {boundary : ReturnBoundary} {code : CodeMap} (h : ReturnOutside boundary code)
    {a : BitVec 64} (ha : CodeAt code a) : a ≠ boundary.rip :=
  let ⟨_, hb⟩ := ha
  h _ hb

theorem ReturnOutside.mono {boundary : ReturnBoundary} {code code' : CodeMap}
    (h : ReturnOutside boundary code') (hsub : ∀ x ∈ code, x ∈ code') : ReturnOutside boundary code :=
  fun x hx => h x (hsub x hx)

theorem codeAt_codeRange {p : BitVec 64} {bytes : List UInt8} (h : 0 < bytes.length) :
    CodeAt (codeRange p bytes) p := by
  have := mem_codeRange p bytes 0 h
  simp only [BitVec.add_zero] at this
  exact ⟨_, this⟩

namespace Runs

variable [Bindings] {code code' : CodeMap} {k m n : Nat} {s t u : RamState}

theorem eq_of_zero (h : Runs code 0 s u) : s = u := by
  cases h
  rfl

theorem mono (h : Runs code k s u) (hsub : ∀ x ∈ code, x ∈ code') : Runs code' k s u := by
  induction h with
  | refl => exact .refl _
  | step hs hin _ ih => exact .step hs (fun hk => (hin hk).mono hsub) ih

theorem single (h : X86.Machine.step s = some (.next t)) : Runs code 1 s t :=
  .step h (fun h0 => absurd rfl h0) (.refl t)

theorem trans (h₁ : Runs code m s t) (hmid : m ≠ 0 → n ≠ 0 → CodeAt code t.RIP)
    (h₂ : Runs code n t u) : Runs code (m + n) s u := by
  induction h₁ with
  | refl => simpa using h₂
  | @step k s t' t hs hin hr ih =>
    rw [Nat.add_right_comm]
    refine .step hs (fun hkn => ?_) (ih (fun hk hn => hmid (Nat.succ_ne_zero _) hn) h₂)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hr.eq_of_zero]
      exact hmid (Nat.succ_ne_zero _) (by omega)
    · exact hin (by omega)

theorem of_loop {inv : Nat → RamState → Prop} {f : RamState → RamState} {p : BitVec 64}
    (hstep : ∀ c s, inv (c + 1) s → X86.Machine.step s = some (.next (f s)))
    (hnext : ∀ c s, inv (c + 2) s → inv (c + 1) (f s))
    (hrip : ∀ c s, inv (c + 2) s → (f s).RIP = s.RIP) (hat : CodeAt code p) :
    ∀ c s, inv (c + 1) s → s.RIP = p → Runs code (c + 1) s (nextStates (c + 1) s) := by
  intro c
  induction c with
  | zero =>
    intro s h _
    rw [nextStates_one, nextState_of_step (hstep 0 s h)]
    exact single (hstep 0 s h)
  | succ c ih =>
    intro s h hp
    rw [nextStates_add (c + 1) 1, nextStates_one, nextState_of_step (hstep _ s h)]
    have hp' : (f s).RIP = p := (hrip c s h).trans hp
    exact .step (hstep _ s h) (fun _ => by rw [hp']; exact hat) (ih (f s) (hnext c s h) hp')

theorem advances {boundary : ReturnBoundary} (h : Runs code k s u)
    (hout : ReturnOutside boundary code)
    (hu : k ≠ 0 → u.RIP ≠ boundary.rip ∨ u.GPR[4] ≠ boundary.rsp) :
    Advances boundary k s u := by
  induction h with
  | refl => exact (advances_zero _ _ _).mpr rfl
  | @step k s t u hs hin hr ih =>
    have hne : t.RIP ≠ boundary.rip ∨ t.GPR[4] ≠ boundary.rsp := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [hr.eq_of_zero]
        exact hu (Nat.succ_ne_zero _)
      · exact .inl (ReturnOutside.ne hout (hin (by omega)))
    rw [Nat.add_comm]
    exact (Advances.of_step hs hne).trans (ih fun hk => hu (Nat.succ_ne_zero _))

theorem returns {boundary : ReturnBoundary} (h : Runs code k s u)
    (hout : ReturnOutside boundary code) (hk : k ≠ 0) (hu : AtBoundary boundary u) :
    Returns boundary k s u := by
  induction h with
  | refl => exact absurd rfl hk
  | @step k s t u hs hin hr ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · obtain rfl := hr.eq_of_zero
      exact Returns.of_step hs hu.1 hu.2
    · have ht : t.RIP ≠ boundary.rip ∨ t.GPR[4] ≠ boundary.rsp :=
        .inl (ReturnOutside.ne hout (hin (by omega)))
      rw [Nat.add_comm]
      exact (Advances.of_step hs ht).returns (ih (by omega) hu)

theorem advances_to_label {blockCode : CodeMap} {boundary : ReturnBoundary} {k : Nat}
    {s u : RamState} (h : Runs blockCode k s u) (hout : ReturnOutside boundary blockCode)
    (hoff : u.RIP ≠ boundary.rip) : Advances boundary k s u :=
  h.advances hout fun _ => .inl hoff

end Runs

theorem StepEffect.runs [Bindings] {pre : RamState → Prop} {code : CodeMap} {e : RamState → Effect}
    (h : StepEffect pre code e) : RunsEffect pre code e := fun s hready hcode hpre =>
  let ⟨s', hstep, hready', hholds⟩ := h s hready hcode hpre
  ⟨1, s', .single hstep, hready', hholds⟩

theorem RunsEffect.of_rep [Bindings] {p : BitVec 64} {ib : List UInt8} {pre : RamState → Prop}
    {e : RamState → Effect} {inv : Nat → RamState → Prop} {f : RamState → RamState}
    (zero : StepEffect (fun s => s.RIP = p ∧ rcx.read s = 0) (codeRange p ib) e)
    (loop : ∀ s, ReadyToStep s → CodeIn (codeRange p ib) s → pre s →
      ReadyToStep (nextStates (max (rcx.read s).toNat 1) s) ∧
        CodeIn (codeRange p ib) (nextStates (max (rcx.read s).toNat 1) s) ∧
        (e s).Holds s (nextStates (max (rcx.read s).toNat 1) s))
    (hrip : ∀ s, pre s → s.RIP = p)
    (start : ∀ s, ReadyToStep s → CodeIn (codeRange p ib) s → pre s →
      rcx.read s = BitVec.ofNat 64 (rcx.read s).toNat → inv (rcx.read s).toNat s)
    (hstep : ∀ c s, inv (c + 1) s → X86.Machine.step s = some (.next (f s)))
    (hnext : ∀ c s, inv (c + 2) s → inv (c + 1) (f s))
    (hnextRip : ∀ c s, inv (c + 2) s → (f s).RIP = s.RIP) (hib : 0 < ib.length) :
    RunsEffect (RepPre p pre) (codeRange p ib) e := by
  intro s h hcode hpre
  by_cases hz : rcx.read s = 0
  · exact StepEffect.runs zero s h hcode ⟨hpre.elim (·.1) (hrip s), hz⟩
  have hpre : pre s := hpre.resolve_left fun h0 => hz h0.2
  obtain ⟨hready, -, hholds⟩ := loop s h hcode hpre
  have hinv := start s h hcode hpre (by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])
  have hn0 : (rcx.read s).toNat ≠ 0 := fun h0 => hz (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  obtain ⟨c, hn⟩ : ∃ c, (rcx.read s).toNat = c + 1 := ⟨(rcx.read s).toNat - 1, by omega⟩
  rw [hn, show max (c + 1) 1 = c + 1 by omega] at hready hholds
  rw [hn] at hinv
  exact ⟨c + 1, _, Runs.of_loop hstep hnext hnextRip (codeAt_codeRange hib) c s hinv (hrip s hpre),
    hready, hholds⟩

end X86Proofs.Lift
