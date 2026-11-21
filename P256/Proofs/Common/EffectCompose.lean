import X86Proofs.Program.Compose

set_option autoImplicit false

register_simp_attr x86_local_on

open X86Proofs

namespace P256.Proofs.Common.EffectCompose

open X86 X86.Machine X86.UserProcess

def FlagsAgree (flags : List StatusFlag) (s t : RamState) : Prop :=
  ∀ i ∈ flags, (StatusFlags.ofRFLAGS s.RFLAGS).get i = (StatusFlags.ofRFLAGS t.RFLAGS).get i

structure Effect.LocalOn (flags : List StatusFlag) (e : RamState → Effect) : Prop where
  rip : ∀ t t', Obs t t' → FlagsAgree flags t t' → (e t).rip = (e t').rip
  writes : ∀ t t', Obs t t' → FlagsAgree flags t t' → (e t).writes = (e t').writes
  flagsSome : ∀ t t', Obs t t' → FlagsAgree flags t t' → (e t).flags.isSome = (e t').flags.isSome
  flag : ∀ t t', Obs t t' → FlagsAgree flags t t' → ∀ i,
    (StatusFlags.ofRFLAGS t.RFLAGS).get i = (StatusFlags.ofRFLAGS t'.RFLAGS).get i →
    (e t).flag t i = (e t').flag t' i
  full : ∀ t, ∀ w ∈ (e t).writes, w.Full

theorem Effect.LocalOn.avoids {flags : List StatusFlag} {e : RamState → Effect}
    (hl : Effect.LocalOn flags e) {t t' : RamState} (ho : Obs t t')
    (hf : FlagsAgree flags t t') {code : CodeMap} (h : (e t).Avoids code) :
    (e t').Avoids code := by
  unfold Effect.Avoids at *
  rw [← Effect.components_eq (hl.writes t t' ho hf) (hl.flagsSome t t' ho hf)]
  exact h

theorem Effect.Holds.knownFlags_after {e : Effect} {s t : RamState} (h : e.Holds s t)
    (flags : List StatusFlag) (known : ∀ i ∈ flags, e.flag s i ≠ none) (b : Bool) :
    FlagsAgree flags (e.after s b) t := by
  intro i hi
  rw [Effect.after_flag]
  have hf := h.flag i
  cases he : e.flag s i with
  | none => exact False.elim (known i hi he)
  | some v =>
    rw [he] at hf
    exact hf.symm

theorem Effect.Holds.seq_on {e₁ e₂ : RamState → Effect} {s s₁ s₂ : RamState}
    (flags : List StatusFlag) (hl : Effect.LocalOn flags e₂)
    (known : ∀ i ∈ flags, (e₁ s).flag s i ≠ none) (hf : ∀ w ∈ (e₁ s).writes, w.Full) (h₁ : (e₁ s).Holds s s₁)
    (h₂ : (e₂ s₁).Holds s₁ s₂) : (Effect.seq e₁ e₂ s).Holds s s₂ := by
  have hobs := h₁.obsAfter hf
  have hflags := (P256.Proofs.Common.EffectCompose.Effect.Holds.knownFlags_after (h := h₁)) flags known
  have hrip := hl.rip _ _ (hobs true) (hflags true)
  have hws := hl.writes _ _ (hobs true) (hflags true)
  have hfs := hl.flagsSome _ _ (hobs true) (hflags true)
  have hfin : Obs (applyWrites ((e₁ s).after s true) (e₂ ((e₁ s).after s true)).writes) s₂ := by
    rw [hws]
    exact h₂.obs (hobs true) (hl.full s₁)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Effect.seq]
    rw [h₂.rip, hrip]
  · rw [Write.allHold_iff]
    simp only [Effect.seq, List.mem_append, List.mem_map]
    rintro w (⟨w₀, hw₀, rfl⟩ | hw)
    · rcases w₀ with @⟨n, dst, v⟩
      by_cases hv : dst.Visible
      · exact (hfin.read dst hv).symm
      · cases dst with
        | fcc m =>
          obtain ⟨hwE, hsh⟩ := List.mem_filter.mp hw₀
          have hsh' : Write.shadowed (e₂ ((e₁ s).after s true)).writes ⟨.fcc m, v⟩ = false := by
            simpa using hsh
          show (Operand.fcc m : Operand n).read s₂ = (Operand.fcc m : Operand n).read _
          apply fcc_read_eq
          intro i hi
          have hnone := Write.not_setsCC_of_shadowed hsh' i
          have hagr : Component.fcc ∉ (e₂ s₁).components := by
            intro hc
            rcases Effect.mem_components.mp hc with ⟨w', hw', hwc⟩ | ⟨-, h'⟩ | h'
            · rw [← hws] at hw'
              have := List.any_eq_false.mp hsh' w' hw'
              rw [hwc] at this
              exact this rfl
            · cases h'
            · cases h'
          have h2 : ccBit i s₂ = ccBit i s₁ := by
            have := h₂.agrees.fcc hagr
            exact congrArg (fun x => x.getLsbD i) this
          rw [h2, Write.ccBit_applyWrites_of_none _ _ hnone]
          exact (Write.cc_applyWrites_holds _ ⟨_, hwE, hi⟩ hf s s₁ h₁.writes).symm
        | _ => exact absurd trivial hv
    · rw [hws] at hw
      exact Write.allHold_iff.mp h₂.writes w hw
  · by_cases hc : ((e₁ s).flags.isNone && (e₂ ((e₁ s).after s true)).flags.isNone) = true
    · simp only [Effect.FlagsHold, Effect.seq, hc, ↓reduceIte]
    · apply Effect.flagsHold_of_flag
      intro i
      rw [Effect.seq_flag]
      simp only [hc]
      let x := (StatusFlags.ofRFLAGS s₁.RFLAGS).get i
      have hx : ∀ b, x = b → (e₂ ((e₁ s).after s b)).flag ((e₁ s).after s b) i =
          (e₂ s₁).flag s₁ i := by
        intro b hb
        apply hl.flag _ _ (hobs b) (hflags b)
        rw [Effect.after_flag]
        have := h₁.flag i
        cases hk : (e₁ s).flag s i with
        | none => simp [← hb, x]
        | some v => rw [hk] at this; simp only [Option.getD_some]; exact this.symm
      exact FlagAllows.pick (hx true) (hx false) (h₂.flag i)
  · apply (h₁.agrees.trans h₂.agrees).mono
    intro c hc
    rw [List.mem_append] at hc
    rw [Effect.mem_components]
    rcases hc with hc | hc
    · rcases Effect.mem_components.mp hc with ⟨w, hw, rfl⟩ | ⟨hs, rfl⟩ | rfl
      · by_cases hsh : Write.shadowed (e₂ ((e₁ s).after s true)).writes w = true
        · obtain ⟨w', hw', he⟩ := Write.shadowed_spec hsh
          exact .inl ⟨w', by simp only [Effect.seq]; exact List.mem_append_right _ hw', he⟩
        · refine .inl ⟨Write.reread (applyWrites ((e₁ s).after s true)
            (e₂ ((e₁ s).after s true)).writes) w, ?_, rfl⟩
          simp only [Effect.seq]
          apply List.mem_append_left
          exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hw, by simpa using hsh⟩)
      · refine .inr (.inl ⟨?_, rfl⟩)
        simp only [Effect.seq]
        split
        · rename_i hc'
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc'
          simp [hc'.1] at hs
        · rfl
      · exact .inr (.inr rfl)
    · rcases Effect.mem_components.mp hc with ⟨w, hw, rfl⟩ | ⟨hs, rfl⟩ | rfl
      · rw [← hws] at hw
        exact .inl ⟨w, by simp only [Effect.seq]; exact List.mem_append_right _ hw, rfl⟩
      · refine .inr (.inl ⟨?_, rfl⟩)
        simp only [Effect.seq]
        split
        · rename_i hc'
          simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc'
          rw [← hfs, hc'.2] at hs
          cases hs
        · rfl
      · exact .inr (.inr rfl)

theorem Effect.LocalOn.of_eq {flags : List StatusFlag} {e : RamState → Effect}
    (same : ∀ t t', Obs t t' → FlagsAgree flags t t' → e t = e t')
    (full : ∀ t, ∀ w ∈ (e t).writes, w.Full) : Effect.LocalOn flags e := by
  refine ⟨fun t t' ho hf => congrArg Effect.rip (same t t' ho hf),
    fun t t' ho hf => congrArg Effect.writes (same t t' ho hf),
    fun t t' ho hf => congrArg (fun x => x.flags.isSome) (same t t' ho hf), ?_, full⟩
  intro t t' ho hf i hi
  rw [same t t' ho hf]
  unfold Effect.flag
  cases (e t').flags <;> simp only [hi]

theorem FlagsAgree.cf {flags : List StatusFlag} {s t : RamState}
    (h : FlagsAgree flags s t) (hi : StatusFlag.CF ∈ flags) :
    s.RFLAGS.extractLsb' 0 1 = t.RFLAGS.extractLsb' 0 1 := by
  have hc : s.RFLAGS.getLsbD 0 = t.RFLAGS.getLsbD 0 := h .CF hi
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he : i = 0 := by omega
  subst he
  simpa only [BitVec.getLsbD_extractLsb', Nat.zero_lt_succ, decide_true, Bool.true_and, Nat.add_zero] using hc

@[x86_compose] theorem Effect.cf_after (e : Effect) (s : RamState) (b : Bool) :
    (e.after s b).RFLAGS.extractLsb' 0 1 = BitVec.ofBool ((e.flag s .CF).getD b) := by
  have hf := e.after_flag s b .CF
  change (e.after s b).RFLAGS.getLsbD 0 = _ at hf
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have he : i = 0 := by omega
  subst he
  simpa only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, Nat.zero_lt_succ,
    decide_true, Bool.true_and, Nat.add_zero] using hf

@[x86_compose] theorem Effect.gpr_after (e : Effect) (s : RamState) (b : Bool) (r : BitVec 5) :
    (e.after s b).GPR[gprIndex r] = (Operand.reg r : Operand 64).read (applyWrites s e.writes) := rfl

theorem Effect.Local.of_eq {e : RamState → Effect}
    (same : ∀ t t', Obs t t' → e t = e t')
    (full : ∀ t, ∀ w ∈ (e t).writes, w.Full) : Effect.Local e := by
  refine ⟨fun t t' ho => congrArg Effect.rip (same t t' ho),
    fun t t' ho => congrArg Effect.writes (same t t' ho),
    fun t t' ho => congrArg (fun x => x.flags.isSome) (same t t' ho), ?_, full⟩
  intro t t' ho i hi
  rw [same t t' ho]
  unfold Effect.flag
  cases (e t').flags <;> simp only [hi]

theorem Effect.Holds.read_after {e : Effect} {s t : RamState} (h : e.Holds s t)
    (hf : ∀ w ∈ e.writes, w.Full) (hcc : Component.fcc ∉ e.components) {n : Nat}
    (op : Operand n) : op.read t = op.read (e.after s true) := by
  by_cases hv : op.Visible
  · exact ((h.obsAfter hf true).read op hv).symm
  · cases op with
    | fcc m =>
      apply fcc_read_eq
      intro i _
      have hnone : ∀ w ∈ e.writes, ¬ w.SetsCC i := by
        intro w hw hs
        apply hcc
        rw [Effect.mem_components]
        refine .inl ⟨w, hw, ?_⟩
        rcases w with @⟨k, dst, v⟩
        cases dst with
        | fcc m' => rfl
        | _ => exact hs.elim
      have hs : ccBit i t = ccBit i s := congrArg (fun x => x.getLsbD i) (h.agrees.fcc hcc)
      rw [hs]
      exact (Write.ccBit_applyWrites_of_none e.writes s hnone).symm
    | _ => exact absurd trivial hv

end P256.Proofs.Common.EffectCompose
