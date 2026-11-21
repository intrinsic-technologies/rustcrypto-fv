import AesGcm.Proofs.Copied.X86Proofs.Lift.Lemma.Reg
import AesGcm.Proofs.Copied.X86Proofs.Lift.IR

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs

@[simp] theorem dialect_eval (code : CodeMap) {n : Nat} (op : Op n) (args : CFG.Values Value n)
    (mem : Ram) : (dialect code).eval op args mem = op.eval code args mem := rfl

theorem Reg.read_of_agreesExcept {cs : List Component} {t t' : RamState} (h : AgreesExcept cs t t')
    {r : Reg} (hr : r.component ∉ cs) : r.read t' = r.read t := by
  cases r with
  | gpr r => simp only [Reg.read, h.read hr]
  | flag f => simp only [Reg.read, h.statusFlags hr]
  | df => simp only [Reg.read, Operand.read_df, h.df hr]
  | xmm r => simp only [Reg.read, h.read_xmm hr]
  | mxcsr => simp only [Reg.read, Operand.read_mxcsr, h.mxcsr hr]
  | fpr r => simp only [Reg.read, Operand.read_fpr, h.fpr hr]
  | fsw => simp only [Reg.read, Operand.read_fsw, h.fsw hr]
  | fcc => simp only [Reg.read, Operand.read_fcc, h.fcc hr]
  | ftw => simp only [Reg.read, Operand.read_ftw, h.ftw hr]
  | fcw => simp only [Reg.read, Operand.read_fcw, h.fcw hr]
  | fpuPtr => simp only [Reg.read, Operand.read_fpuPtr, h.fpuPtr hr]

theorem Reg.ofWrite?_spec {t' : RamState} {w : Write} (hf : w.Full) (hh : w.dst.read t' = w.val)
    {r : Reg} {v : Value} (h : Reg.ofWrite? w = some (r, v)) : r.read t' = v := by
  rcases w with @⟨n, dst, val⟩
  cases dst <;> simp only [Reg.ofWrite?, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp only [Write.Full, Operand.Full] at hf <;> subst hf <;>
    dsimp only at hh <;> simp only [Reg.read] <;> rw [← hh] <;> simp

theorem Reg.ofWrite?_of_component {w : Write} (hf : w.Full) {r : Reg} (hr : r.isFlag = false)
    (hcc : r ≠ .fcc) (hc : w.component = r.component) : ∃ v, Reg.ofWrite? w = some (r, v) := by
  rcases w with @⟨n, dst, val⟩
  cases dst <;> cases r <;>
    simp_all [Write.component, Operand.component, Reg.component, Reg.ofWrite?, Write.Full,
      Operand.Full, Reg.isFlag]

theorem writtenValue_of_holds {t' : RamState} {r : Reg} (hr : r.isFlag = false) (hcc : r ≠ .fcc) :
    ∀ {ws : List Write}, (∀ w ∈ ws, w.dst.read t' = w.val) → (∀ w ∈ ws, w.Full) →
      (∃ w ∈ ws, w.component = r.component) → r.read t' = writtenValue r ws
  | [], _, _, ⟨_, hw, _⟩ => absurd hw List.not_mem_nil
  | w :: ws, hh, hf, hex => by
    unfold writtenValue
    rw [List.findSome?_cons]
    cases ht : Reg.ofWrite? w with
    | none =>
      have hex' : ∃ w' ∈ ws, w'.component = r.component := by
        obtain ⟨w', hw', hc⟩ := hex
        rcases List.mem_cons.mp hw' with rfl | hw'
        · obtain ⟨v, hv⟩ := Reg.ofWrite?_of_component (hf _ List.mem_cons_self) hr hcc hc
          rw [hv] at ht
          cases ht
        · exact ⟨w', hw', hc⟩
      exact writtenValue_of_holds hr hcc (fun w hw => hh w (List.mem_cons_of_mem _ hw))
        (fun w hw => hf w (List.mem_cons_of_mem _ hw)) hex'
    | some rv =>
      obtain ⟨r', v⟩ := rv
      by_cases hr' : r' = r
      · subst hr'
        simp only [↓reduceIte, Option.getD_some]
        exact Reg.ofWrite?_spec (hf _ List.mem_cons_self) (hh _ List.mem_cons_self) ht
      · simp only [hr', ↓reduceIte]
        have hex' : ∃ w' ∈ ws, w'.component = r.component := by
          obtain ⟨w', hw', hc⟩ := hex
          rcases List.mem_cons.mp hw' with rfl | hw'
          · obtain ⟨v', hv⟩ := Reg.ofWrite?_of_component (hf _ List.mem_cons_self) hr hcc hc
            rw [hv] at ht
            cases ht
            exact absurd rfl hr'
          · exact ⟨w', hw', hc⟩
        exact writtenValue_of_holds hr hcc (fun w hw => hh w (List.mem_cons_of_mem _ hw))
          (fun w hw => hf w (List.mem_cons_of_mem _ hw)) hex'

theorem applyWrites_external_isSome (s : RamState) (ws : List Write) (x : BitVec 64)
    (h : (s.external[x]?).isSome) : ((applyWrites s ws).external[x]?).isSome := by
  induction ws generalizing s with
  | nil => exact h
  | cons w ws ih =>
    rw [applyWrites_cons]
    apply ih
    rcases w with @⟨n, dst, val⟩
    cases dst <;> simp only [Write.apply, Operand.write] <;>
      first | exact h | exact memStore_isSome _ _ _ _ h

theorem applyWrites_external_of_not_covers (s : RamState) (ws : List Write) (x : BitVec 64)
    (h : ∀ w ∈ ws, ¬ w.component.Covers x) : (applyWrites s ws).external[x]? = s.external[x]? := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    rw [applyWrites_cons, ih _ fun w' hw' => h w' (List.mem_cons_of_mem _ hw')]
    rcases w with @⟨n, dst, val⟩
    have hw := h _ List.mem_cons_self
    cases dst <;> simp only [Write.apply, Operand.write]
    apply memStore_getElem?_of_ne
    intro i hi he
    exact hw ⟨i, hi, he.symm⟩

theorem external_eq_of_holds {E : Effect} {s t : RamState} (h : E.Holds s t)
    (hf : ∀ w ∈ E.writes, w.Full) (hp : WritesPresent E s.external) :
    t.external = (applyWrites s E.writes).external := by
  have ho : Obs (applyWrites s E.writes) t := h.obs (Obs.refl s) hf
  apply Std.ExtHashMap.ext_getElem?
  intro x
  by_cases hc : ∃ c ∈ E.components, c.Covers x
  · obtain ⟨c, hc, hcx⟩ := hc
    have hs := hp c hc x hcx
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (h.agrees.grow x hs)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (applyWrites_external_isSome s E.writes x hs)
    have hm := ho.mem x
    simp only [memByte, PhysicalMemory.read, ha, hb, Option.getD_some] at hm
    rw [ha, hb, hm]
  · have hnc : ∀ c ∈ E.components, ¬ c.Covers x := fun c hc' hcx => hc ⟨c, hc', hcx⟩
    rw [h.agrees.memory x hnc, applyWrites_external_of_not_covers s E.writes x fun w hw hcx =>
      hnc _ (Effect.mem_components.mpr (.inl ⟨w, hw, rfl⟩)) hcx]

theorem Value.ofBool_inj {a b : Bool} (h : Value.ofBool a = Value.ofBool b) : a = b := by
  cases a <;> cases b <;> first | rfl | (simp [Value.ofBool] at h)

theorem nonFlags_operands (R : List Reg) (F : List StatusFlag) :
    Reg.nonFlags (Reg.operands R F) = Reg.nonFlags R := by
  induction F <;> simp_all [Reg.operands, Reg.nonFlags, List.filter_append, Reg.isFlag]

theorem nonFlags_reads (o : EffectPart) (R : List Reg) (F : List StatusFlag) :
    Reg.nonFlags (o.reads R F) = Reg.nonFlags R := by
  have h (f : StatusFlag) : Reg.nonFlags (Reg.operands R F ++ [.flag f]) = Reg.nonFlags R := by
    rw [← nonFlags_operands R F]
    simp [Reg.nonFlags, List.filter_append, Reg.isFlag]
  cases o <;> simp only [EffectPart.reads] <;> (try split) <;> simp only [h, nonFlags_operands]

theorem mem_operands {R : List Reg} {F : List StatusFlag} {f : StatusFlag} (hf : f ∈ F) :
    Reg.flag f ∈ Reg.operands R F :=
  List.mem_append_right _ (List.mem_map_of_mem hf)

theorem mem_reads_of_param (o : EffectPart) {R : List Reg} {F : List StatusFlag} {f : StatusFlag}
    (hf : f ∈ F) : Reg.flag f ∈ o.reads R F := by
  cases o <;> simp only [EffectPart.reads] <;> (try split) <;>
    first | exact mem_operands hf | exact List.mem_append_left _ (mem_operands hf)

theorem stateOf_obs_of_nonFlags (p : BitVec 64) {R L : List Reg}
    (h : Reg.nonFlags L = Reg.nonFlags R) (t : RamState) :
    Obs (stateOf p (entriesOf R t) t.external) (stateOf p (entriesOf L t) t.external) := by
  have h₀ := stateOf_obs_filter p t.external (entriesOf R t)
  have h₁ := stateOf_obs_filter p t.external (entriesOf L t)
  rw [filter_entriesOf] at h₀ h₁
  rw [h] at h₁
  exact h₀.trans h₁.symm

theorem flagsAgree_stateOf (p : BitVec 64) {R L : List Reg} {F : List StatusFlag}
    (hR : ∀ f ∈ F, Reg.flag f ∈ R) (hL : ∀ f ∈ F, Reg.flag f ∈ L) (t : RamState) :
    FlagsAgree F (stateOf p (entriesOf R t) t.external) (stateOf p (entriesOf L t) t.external) :=
  fun f hf => Value.ofBool_inj
    ((read_stateOf_entriesOf (p := p) (mem := t.external) t (hR f hf)).trans
      (read_stateOf_entriesOf (p := p) (mem := t.external) t (hL f hf)).symm)

theorem EffectPart.value_congr {e : RamState → Effect} {F : List StatusFlag} (hl : LocalWith F e)
    {p : BitVec 64} {R : List Reg} (heff : ReadsOnly p e R) (hclosed : Reg.FlagsClosed R)
    (hF : ∀ f ∈ F, Reg.flag f ∈ R) (o : EffectPart)
    (hsets : o.isFlag = true → R.any Reg.isFlag = false → ∀ s, (e s).flags.isSome = true)
    (t : RamState) :
    o.value (e (stateOf p (entriesOf (o.reads R F) t) t.external))
        (stateOf p (entriesOf (o.reads R F) t) t.external) = o.value (e t) t := by
  have hobs := stateOf_obs_of_nonFlags p (nonFlags_reads o R F) t
  have hparams := flagsAgree_stateOf p hF (fun _ hf => mem_reads_of_param o (R := R) hf) t
  rw [heff t]
  cases o with
  | reg r => simp only [EffectPart.value, hl.writes _ _ hobs hparams]
  | target => simp only [EffectPart.value, hl.rip _ _ hobs hparams]
  | flag f =>
    simp only [EffectPart.value]
    have hmem : ∀ i : StatusFlag, R.any Reg.isFlag = true → Reg.flag i ∈ R := fun i hR =>
      hclosed hR _ (by cases i <;> simp [Reg.flags])

    have hagree : (StatusFlags.ofRFLAGS (stateOf p (entriesOf R t) t.external).RFLAGS).get f =
        (StatusFlags.ofRFLAGS (stateOf p (entriesOf ((EffectPart.flag f).reads R F) t)
          t.external).RFLAGS).get f := by
      cases hR : R.any Reg.isFlag with
      | true =>
        have h₀ := read_stateOf_entriesOf (p := p) (mem := t.external) t (hmem f hR)
        have h₁ := read_stateOf_entriesOf (p := p) (mem := t.external)
          (rs := (EffectPart.flag f).reads R F) (r := .flag f) t (by simp [EffectPart.reads, hR])
        exact Value.ofBool_inj (h₀.trans h₁.symm)
      | false =>

        have hF' : f ∉ F := fun hf => by
          have : R.any Reg.isFlag = true := List.any_eq_true.mpr ⟨_, hF f hf, rfl⟩
          rw [hR] at this
          cases this
        have hn₀ : Reg.flag f ∉ (entriesOf R t).map Prod.fst := by
          rw [map_fst_entriesOf]
          intro hf
          have : R.any Reg.isFlag = true := List.any_eq_true.mpr ⟨_, hf, rfl⟩
          rw [hR] at this
          cases this
        have hn₁ : Reg.flag f ∉ (entriesOf ((EffectPart.flag f).reads R F) t).map Prod.fst := by
          rw [map_fst_entriesOf]
          simp [EffectPart.reads, hR, Reg.operands, Reg.nonFlags, Reg.isFlag, hF']
        exact Value.ofBool_inj ((read_stateOf_not_mem hn₀).trans (read_stateOf_not_mem hn₁).symm)
    have hl' := hl.flag _ _ hobs hparams f hagree
    rw [← hl']
    congr 1
    unfold Effect.flag
    cases hfl : (e (stateOf p (entriesOf R t) t.external)).flags with
    | some fe => rfl
    | none =>
      cases hR : R.any Reg.isFlag with
      | true =>
        have h₀ := read_stateOf_entriesOf (p := p) (mem := t.external) t (hmem f hR)
        exact Value.ofBool_inj h₀
      | false =>
        have := hsets rfl hR (stateOf p (entriesOf R t) t.external)
        rw [hfl] at this
        cases this

theorem EffectPart.value_fresh {e : RamState → Effect} {p : BitVec 64} {R : List Reg}
    {F : List StatusFlag} (heff : ReadsOnly p e R) (hclosed : Reg.FlagsClosed R)
    (hF : ∀ f ∈ F, Reg.flag f ∈ R) (hR : R.any Reg.isFlag = true) {f : StatusFlag}
    (hf : FlagFresh F e f) (t : RamState) :
    (EffectPart.flag f).value (e (stateOf p (entriesOf (Reg.operands R F) t) t.external))
        (stateOf p (entriesOf (Reg.operands R F) t) t.external) =
      (EffectPart.flag f).value (e t) t := by
  have hobs := stateOf_obs_of_nonFlags p (nonFlags_operands R F) t
  simp only [EffectPart.value]
  rw [← hf _ _ hobs (flagsAgree_stateOf p hF (fun _ h => mem_operands (R := R) h) t), heff t]
  unfold Effect.flag
  split
  ·
    have h := read_stateOf_entriesOf (p := p) (mem := t.external) t
      (hclosed hR (.flag f) (by cases f <;> simp [Reg.flags]))
    simp only [Reg.read] at h
    rw [Value.ofBool_inj h]
  · rfl

end X86Proofs.Lift
