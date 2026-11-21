import AesGcm.Proofs.Copied.X86Proofs.Lift.Lockstep
import AesGcm.Proofs.Copied.X86Proofs.Lift.Lemma.Effect
import AesGcm.Proofs.Copied.X86Proofs.Lift.Lemma.Runs

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG

theorem RegMap.has_iff {ρ : RegMap} {i j : Nat} : ρ.has i j = true ↔ (i, j) ∈ ρ := by
  simp only [RegMap.has, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨a, b⟩, h, ha, hb⟩
    rwa [← Nat.eq_of_beq_eq_true ha, ← Nat.eq_of_beq_eq_true hb]
  · exact fun h => ⟨_, h, Nat.beq_refl i, Nat.beq_refl j⟩

theorem EffectPart.eq_ofReg_of_isAt {o : EffectPart} {i : Nat} (h : o.isAt i = true) :
    o = EffectPart.ofReg (Reg.ofIndex i) := by
  cases o with
  | reg r =>
    simp only [EffectPart.isAt, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨htr, hnf⟩, hi⟩ := h
    rw [← Nat.eq_of_beq_eq_true hi, Reg.ofIndex_index htr]
    cases r <;> simp_all [Reg.isFlag, EffectPart.ofReg]
  | flag f =>
    rw [← Nat.eq_of_beq_eq_true h, Reg.ofIndex_index rfl]
    rfl
  | target => cases h

theorem remapOk_spec {ρ : RegMap} {outs : List (EffectPart × Nat)} {cs : List Component}
    {ρ' : RegMap} (h : remapOk ρ outs cs ρ' = true) : RemapOk ρ outs cs ρ' := by
  induction ρ' generalizing ρ with
  | nil => exact fun _ _ h => absurd h List.not_mem_nil
  | cons e ρ' ih =>
    obtain ⟨i, j⟩ := e
    intro i' j' hmem
    simp only [remapOk] at h
    cases hout : outs.any (fun o => o.1.isAt i && o.2.beq j)
    · simp only [hout, Bool.cond_false, Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨hi, hcs⟩, hρ⟩ := h
      split at hρ
      · rename_i i₁ j₁ ρ₁ hdrop
        simp only [Bool.and_eq_true] at hρ
        obtain ⟨⟨hi₁, hj₁⟩, hrest⟩ := hρ
        have hsub : ∀ x ∈ (i₁, j₁) :: ρ₁, x ∈ ρ := fun x hx =>
          (List.dropWhile_suffix _).subset (hdrop ▸ hx)
        rcases List.mem_cons.mp hmem with he | hmem
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          refine .inr ⟨fun hc => ?_, ?_⟩
          · have hany : cs.any (fun c => (Reg.positions c).any (·.beq i')) = true :=
              List.any_eq_true.mpr ⟨_, hc, List.any_eq_true.mpr
                ⟨i', Reg.mem_positions i' (Nat.le_of_ble_eq_true hi), Nat.beq_refl i'⟩⟩
            rw [hany] at hcs
            cases hcs
          · rw [← Nat.eq_of_beq_eq_true hi₁, ← Nat.eq_of_beq_eq_true hj₁]
            exact hsub _ List.mem_cons_self
        · exact (ih hrest i' j' hmem).imp id fun ⟨hc, hm⟩ =>
            ⟨hc, hsub _ (List.mem_cons_of_mem _ hm)⟩
      · cases hρ
    · simp only [hout, Bool.cond_true] at h
      rcases List.mem_cons.mp hmem with he | hmem
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨⟨o, k⟩, ho, hok⟩ := List.any_eq_true.mp hout
        simp only [Bool.and_eq_true] at hok
        left
        rw [← EffectPart.eq_ofReg_of_isAt hok.1, ← Nat.eq_of_beq_eq_true hok.2]
        exact ho
      · exact ih h i' j' hmem

theorem maskLe_spec {m m' : Nat} (h : maskLe m m' = true) (i : Nat) :
    m.testBit i = true → m'.testBit i = true := by
  intro hm
  have := congrArg (·.testBit i) (Nat.eq_of_beq_eq_true h)
  simp only [Nat.testBit_and, hm, Bool.true_and] at this
  exact this

theorem RegMap.testBit_mask {ρ : RegMap} {i : Nat} (h : ρ.mask.testBit i = true) :
    ∃ j, (i, j) ∈ ρ := by
  induction ρ with
  | nil => simp [RegMap.mask] at h
  | cons e ρ ih =>
    simp only [RegMap.mask, List.foldr_cons, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow,
      Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | rfl
    · obtain ⟨j, hj⟩ := ih (by simpa only [RegMap.mask, Nat.one_shiftLeft] using h)
      exact ⟨j, List.mem_cons_of_mem _ hj⟩
    · exact ⟨e.2, List.mem_cons_self⟩

theorem RegMap.getElem_args (ρ : RegMap) (n : Nat) [NeZero n] (i : Nat) (hi : i < Reg.count) :
    (ρ.args n)[i] = Fin.ofNat n ((ρ.lookup i).getD i) := by
  simp [RegMap.args]

theorem At.args {ρ : RegMap} {n : Nat} [NeZero n] {regs : Values Value n} {t : RamState}
    (hat : At ρ regs t) {m : Nat} (h : maskLe m ρ.mask = true) :
    ∀ i (hi : i < Reg.count), Live m i → (regs.select (ρ.args n))[i] = (Reg.ofIndex i).read t := by
  intro i hi hlive
  obtain ⟨j, hj⟩ := RegMap.testBit_mask (maskLe_spec h i hlive)
  obtain ⟨j', hl⟩ := Option.isSome_iff_exists.mp
    (List.lookup_isSome_iff.mpr ⟨_, hj, BEq.rfl⟩ : (ρ.lookup i).isSome)
  obtain ⟨l₁, l₂, hρ, -⟩ := List.lookup_eq_some_iff.mp hl
  obtain ⟨hjn, hval⟩ := hat i j' (by rw [hρ]; exact List.mem_append_right _ List.mem_cons_self)
  simp only [Values.getElem_select, RegMap.getElem_args _ _ _ hi, hl, Option.getD_some]
  rw [← hval]
  exact congrArg (regs[·]) (Fin.ext (Nat.mod_eq_of_lt hjn) : Fin.ofNat n j' = ⟨j', hjn⟩)

theorem mem_entryMap {m i j : Nat} (h : (i, j) ∈ entryMap m) :
    j = i ∧ i < Reg.count ∧ Live m i := by
  simp only [entryMap, List.mem_filterMap, List.mem_range] at h
  obtain ⟨k, hk, he⟩ := h
  split at he
  · cases he
    exact ⟨rfl, hk, by assumption⟩
  · cases he

theorem At.push {ρ : RegMap} {n : Nat} {regs : Values Value n} {t : RamState} (h : At ρ regs t)
    (v : Value) : At ρ (regs.push v) t := by
  intro i j hj
  obtain ⟨hjn, he⟩ := h i j hj
  exact ⟨Nat.lt_succ_of_lt hjn, by rw [Vector.getElem_push_lt hjn]; exact he⟩

theorem operands_entries {ρ : RegMap} {L : List Reg} {n : Nat} {args : Vector (Fin n) L.length}
    (hargs : operandsOk ρ L args = true) {regs : Values Value n} {t : RamState}
    (hat : At ρ regs t) : L.zip (regs.select args).toList = entriesOf L t := by
  simp only [operandsOk, List.all_eq_true, Bool.and_eq_true] at hargs
  apply List.ext_getElem
  · simp [entriesOf]
  · intro j h₁ h₂
    have hj : j < L.length := by simpa [entriesOf] using h₂
    have hmem : (L[j], args[j]) ∈ L.zip args.toList :=
      List.mem_iff_getElem.mpr ⟨j, by simpa using hj, by simp⟩
    obtain ⟨htr, hρ⟩ := hargs _ hmem
    obtain ⟨_, hv⟩ := hat _ _ (RegMap.has_iff.mp hρ)
    simp only [List.getElem_zip, Vector.getElem_toList, Values.getElem_select, entriesOf,
      List.getElem_map]
    rw [Reg.ofIndex_index htr] at hv
    exact Prod.ext rfl hv

theorem state_operands {ρ : RegMap} {L : List Reg} {n : Nat} {args : Vector (Fin n) L.length}
    (hargs : operandsOk ρ L args = true) {regs : Values Value n} {t : RamState}
    (hat : At ρ regs t) (p : BitVec 64) :
    Op.state p L (regs.select args) t.external = stateOf p (entriesOf L t) t.external := by
  simp only [Op.state, operands_entries hargs hat]

theorem applyWrites_external_congr {t t' : RamState} (h : t.external = t'.external) :
    ∀ ws : List Write, (applyWrites t ws).external = (applyWrites t' ws).external
  | [] => h
  | w :: ws => by
    rw [applyWrites_cons, applyWrites_cons]
    apply applyWrites_external_congr
    rcases w with @⟨n, dst, val⟩
    cases dst <;> simp only [Write.apply, Operand.write] <;> rw [h]

theorem Reg.component_ne_rip (r : Reg) : r.component ≠ .rip := by cases r <;> simp [Reg.component]

theorem Reg.component_isMem (r : Reg) : r.component.isMem = false := by
  cases r <;> rfl

theorem Reg.component_ne_flags {r : Reg} (h : r.isFlag = false) : r.component ≠ .flags := by
  cases r <;> simp_all [Reg.component, Reg.isFlag]

theorem carry_congr {a b : StatusFlags} (h : ∀ x ∈ [StatusFlag.CF], a.get x = b.get x) :
    a.CF = b.CF :=
  h .CF (List.mem_singleton_self _)

theorem condHolds_congr (cc : BitVec 4) {a b : StatusFlags}
    (h : ∀ f ∈ condFlags cc, a.get f = b.get f) : condHolds cc a = condHolds cc b := by
  have hlt : cc.toNat < 16 := cc.isLt
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := a
  obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆⟩ := b
  rcases (show cc.toNat = 0 ∨ cc.toNat = 1 ∨ cc.toNat = 2 ∨ cc.toNat = 3 ∨ cc.toNat = 4 ∨
      cc.toNat = 5 ∨ cc.toNat = 6 ∨ cc.toNat = 7 ∨ cc.toNat = 8 ∨ cc.toNat = 9 ∨ cc.toNat = 10 ∨
      cc.toNat = 11 ∨ cc.toNat = 12 ∨ cc.toNat = 13 ∨ cc.toNat = 14 ∨ cc.toNat = 15 by omega) with
    hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc | hc <;>
    simp_all [condHolds, condFlags, StatusFlags.get]

theorem flagsOf_get {fs : List StatusFlag} (hnd : fs.Nodup) (t : RamState) {f : StatusFlag}
    (hf : f ∈ fs) :
    (flagsOf fs (fs.map fun f => (Reg.flag f).read t)).get f = (StatusFlags.ofRFLAGS t.RFLAGS).get f := by
  induction fs with
  | nil => cases hf
  | cons f₀ fs ih =>
    simp only [flagsOf, List.map_cons, List.zip_cons_cons, List.foldr_cons] at ih ⊢
    by_cases h : f = f₀
    · subst h
      rw [StatusFlags.get_set_self]
      simp [Reg.read]
    · rw [StatusFlags.get_set_ne _ h]
      exact ih (List.nodup_cons.mp hnd).2 ((List.mem_cons.mp hf).resolve_left h)

theorem condFlags_nodup (cc : BitVec 4) : (condFlags cc).Nodup := by
  unfold condFlags
  split <;> decide

theorem condOp_operands {ρ : RegMap} {n : Nat} {cc : BitVec 4}
    {args : Vector (Fin n) (condReads cc).length} (hargs : operandsOk ρ (condReads cc) args = true)
    {regs : Values Value n} {t : RamState} (hat : At ρ regs t) :
    (condOp cc (regs.select args)).truth = condHolds cc (StatusFlags.ofRFLAGS t.RFLAGS) := by
  have he := operands_entries hargs hat
  have hvals : (regs.select args).toList = (condFlags cc).map fun f => (Reg.flag f).read t := by
    have h1 := congrArg (List.map Prod.snd) he
    rw [List.map_snd_zip (by simp)] at h1
    rw [h1]
    simp [entriesOf, condReads]
  simp only [condOp, Value.truth_ofBool, hvals]
  exact condHolds_congr cc fun f hf => flagsOf_get (condFlags_nodup cc) t hf

section

variable [Bindings] {code : CodeMap} {n : Nat}

theorem exec_run {ρ ρ' : RegMap} {p : BitVec 64} {ib : List UInt8} {pre : RamState → Prop}
    {e : RamState → Effect} {R : List Reg} {F : List StatusFlag} {cs : List Component}
    {outs : List (EffectPart × Nat)} (spec : InstrSpec p ib pre e R F cs)
    {args : Vector (Fin n) (Reg.operands R F).length}
    (hargs : operandsOk ρ (Reg.operands R F) args = true) (remap : RemapOk ρ outs cs ρ')
    {regs : Values Value n} {t : RamState} (hrip : t.RIP = p) (hat : At ρ regs t)
    (hready : ReadyToStep t) (hsse : Prelude.SupportedSSE Bindings.processor t)
    (hcode : CodeIn code t) (hib : ∀ x ∈ codeRange p ib, x ∈ code)
    (houts : ∀ oj ∈ outs,
      EffectPart.Valid e cs oj.1 ∧ ∃ h : oj.2 < n, regs[oj.2] = oj.1.value (e t) t)
    {v : Value} {mem' : Ram}
    (heval : (Op.exec p pre e (Reg.operands R F)).eval code (regs.select args) t.external =
      some (v, mem')) :
    pre t ∧ ∃ m t', Runs (codeRange p ib) m t t' ∧ ReadyToStep t' ∧ (e t).Holds t t' ∧
      mem' = t'.external ∧ Prelude.SupportedSSE Bindings.processor t' ∧ CodeIn code t' ∧
      At ρ' (regs.push v) t' := by
  have hstate := state_operands hargs hat p
  simp only [Op.eval] at heval
  split at heval
  · rename_i hguard
    obtain ⟨hpre₁, havoid₁, hpresent₁⟩ := hguard
    rw [hstate] at hpre₁ havoid₁ hpresent₁ heval
    cases heval
    have hpre := spec.pre t hrip hpre₁
    obtain ⟨m, t', hrun, hready', hholds⟩ := spec.run t hready (hcode.mono hib) hpre
    have hobs := stateOf_obs_of_nonFlags p (nonFlags_operands R F) t
    have hparams := flagsAgree_stateOf p spec.params (fun _ h => mem_operands (R := R) h) t
    have he : e t = e (stateOf p (entriesOf R t) t.external) := spec.reads t
    have hwrites : (e t).writes =
        (e (stateOf p (entriesOf (Reg.operands R F) t) t.external)).writes := by
      rw [he]; exact spec.isLocal.writes _ _ hobs hparams
    have hsome : (e t).flags.isSome =
        (e (stateOf p (entriesOf (Reg.operands R F) t) t.external)).flags.isSome := by
      rw [he]; exact spec.isLocal.flagsSome _ _ hobs hparams
    have hcomp := Effect.components_eq hwrites hsome
    have havoid : (e t).Avoids code := by
      unfold Effect.Avoids at havoid₁ ⊢
      rw [hcomp]; exact havoid₁
    have hpresent : WritesPresent (e t) t.external := by
      unfold WritesPresent at hpresent₁ ⊢
      rw [hcomp]; exact hpresent₁
    have hfull : ∀ w ∈ (e t).writes, w.Full := spec.isLocal.full t
    refine ⟨hpre, m, t', hrun, hready', hholds, ?_,
      SupportedSSE.of_agreesExcept hholds.agrees hsse, hholds.codeIn havoid hcode, ?_⟩
    · rw [external_eq_of_holds hholds hfull hpresent, hwrites]
      exact applyWrites_external_congr (by simp) _
    · intro i j hj
      rcases remap i j hj with hout | ⟨hnc, hρ⟩
      · obtain ⟨hvalid, hjn, hval⟩ := houts _ hout
        refine ⟨Nat.lt_succ_of_lt hjn, ?_⟩
        rw [Vector.getElem_push_lt hjn, hval]
        cases hr : Reg.ofIndex i with
        | flag f =>
          simp only [hr, EffectPart.ofReg, EffectPart.Valid] at hvalid ⊢
          obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hvalid t)
          have hflag := hholds.flag f
          rw [hb] at hflag
          simp only [EffectPart.value, hb, Option.getD_some, Reg.read]
          rw [show (StatusFlags.ofRFLAGS t'.RFLAGS).get f = b from hflag]
        | _ =>
          simp only [hr, EffectPart.ofReg] at hvalid ⊢
          obtain ⟨hnf, hncc, hcs⟩ := hvalid
          simp only [EffectPart.value]
          refine (writtenValue_of_holds hnf hncc (Write.allHold_iff.mp hholds.writes) hfull ?_).symm
          have hmem := (spec.components t _ (Reg.component_isMem _)).mpr hcs
          rcases Effect.mem_components.mp hmem with h | ⟨-, h⟩ | h
          · exact h
          · exact absurd h (Reg.component_ne_flags hnf)
          · exact absurd h (Reg.component_ne_rip _)
      · obtain ⟨hjn, hval⟩ := hat i j hρ
        refine ⟨Nat.lt_succ_of_lt hjn, ?_⟩
        rw [Vector.getElem_push_lt hjn, hval]
        refine (Reg.read_of_agreesExcept hholds.agrees fun hc => hnc ?_).symm
        exact (spec.components t _ (Reg.component_isMem _)).mp hc
  · cases heval

variable {P : Lifted} {blockCode : CodeMap}

theorem RestInside.push {ρ : RegMap} {e : RamState → Effect} {cs : List Component}
    {outs : List (EffectPart × Nat)} {k : Nat} {p : BitVec 64} {bytes : List UInt8} {m : Nat}
    {op : Op m}
    {args : Vector (Fin n) m} {o : EffectPart} (valid : EffectPart.Valid e cs o)
    (hval : ∀ regs mem t, Start code blockCode ρ p bytes regs mem t →
      (dialect code).eval op (regs.select args) mem = some (o.value (e t) t, mem))
    {tail : Block Op P.Label signature Reg.count (n + 1)}
    (rest : RestInside code P blockCode ρ e cs (outs ++ [(o, n)]) k p bytes tail) :
    RestInside code P blockCode ρ e cs outs k p bytes (.letOp op args tail) where
  run regs mem t start houts hns := by
    have heval : (Block.letOp op args tail : Block Op P.Label signature Reg.count n).eval
        (dialect code) regs mem = tail.eval (dialect code) (regs.push (o.value (e t) t)) mem := by
      simp only [Block.eval, hval regs mem t start]
    rw [heval] at hns ⊢
    refine rest.run _ mem t ⟨start.rip, start.related.push _, start.store, start.ready,
      start.sse, start.codeIn, start.bytesIn, start.blockIn⟩ ?_ hns
    intro oj hoj
    rcases List.mem_append.mp hoj with hoj | hoj
    · obtain ⟨hv, hjn, hj⟩ := houts oj hoj
      exact ⟨hv, Nat.lt_succ_of_lt hjn, by rw [Vector.getElem_push_lt hjn]; exact hj⟩
    · obtain rfl := List.mem_singleton.mp hoj
      exact ⟨valid, Nat.lt_succ_self n, by simp⟩

end

end X86Proofs.Lift
