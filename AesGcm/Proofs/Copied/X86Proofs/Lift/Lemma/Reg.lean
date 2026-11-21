import AesGcm.Proofs.Copied.X86Proofs.Lift.IR

namespace X86Proofs

@[simp] theorem StatusFlags.get_set_self (f : StatusFlags) (i : StatusFlag) (b : Bool) :
    (f.set i b).get i = b := by
  cases i <;> rfl

theorem StatusFlags.get_set_ne (f : StatusFlags) {i j : StatusFlag} (h : i ≠ j) (b : Bool) :
    (f.set j b).get i = f.get i := by
  cases i <;> cases j <;> first | rfl | exact absurd rfl h

end X86Proofs

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs

@[simp] theorem Value.get_mk (n : Nat) (x : BitVec n) : (⟨n, x⟩ : Value).get n = x := by
  simp [Value.get]

@[simp] theorem Value.truth_ofBool (b : Bool) : (Value.ofBool b).truth = b := by
  cases b <;> rfl

theorem Value.eq_bits {w : Nat} {a b : BitVec w} (h : (⟨w, a⟩ : Value) = ⟨w, b⟩) : a = b :=
  eq_of_heq (Value.mk.inj h).2

theorem gprIndex_ne {r r' : BitVec 5} (h : r ≠ r') : gprIndex r ≠ gprIndex r' :=
  fun he => h (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp he))

theorem xmmIndex_ne {r r' : BitVec 5} (h : r ≠ r') : xmmIndex r ≠ xmmIndex r' :=
  fun he => h (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp he))

theorem fprIndex_ne {r r' : BitVec 3} (h : r ≠ r') : fprIndex r ≠ fprIndex r' :=
  fun he => h (BitVec.eq_of_toNat_eq (Fin.mk.inj_iff.mp he))

namespace Reg

theorem ofIndex_index {r : Reg} (h : r.isTracked = true) : ofIndex r.index = r := by
  cases r with
  | gpr r =>
    have hr : r.toNat < 16 := Nat.le_of_ble_eq_true h
    simp only [index, ofIndex, hr, ↓reduceIte, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | flag f => cases f <;> rfl
  | xmm r =>
    have hr : r.toNat < 16 := Nat.le_of_ble_eq_true h
    simp only [index, ofIndex, show ¬ 23 + r.toNat < 16 by omega,
      show ¬ 23 + r.toNat < 22 by omega, show ¬ 23 + r.toNat = 22 by omega,
      show 23 + r.toNat < 39 by omega, ↓reduceIte, Nat.add_sub_cancel_left, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  | fpr r =>
    have hr : r.toNat < 8 := r.isLt
    simp only [index, ofIndex, show ¬ 40 + r.toNat < 16 by omega,
      show ¬ 40 + r.toNat < 22 by omega, show ¬ 40 + r.toNat = 22 by omega,
      show ¬ 40 + r.toNat < 39 by omega, show ¬ 40 + r.toNat = 39 by omega,
      show 40 + r.toNat < 48 by omega, ↓reduceIte, Nat.add_sub_cancel_left, BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  | _ => rfl

theorem mem_positions : ∀ i, i < count → i ∈ positions (ofIndex i).component := by
  decide

theorem read_write_read (r : Reg) (u t : RamState) : r.read (r.write (r.read u) t) = r.read u := by
  cases r with
  | xmm r =>
    simp only [read, write, Value.get_mk]
    rw [Operand.read_write_xmm_self]
  | fcc =>
    simp only [read, write, Value.get_mk, Operand.read_fcc, Operand.write_fcc, fswCC_fswSetCC]
    congr 1
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_and]
  | _ => simp [read, write]

theorem read_write_ne {r r' : Reg} (h : r ≠ r') (v : Value) (t : RamState) :
    r.read (r'.write v t) = r.read t := by
  cases r <;> cases r' <;>
    simp_all [read, write, setFpuPtr, fpuPtrOf, gprIndex, xmmIndex, fprIndex, Vector.getElem_set_ne,
      BitVec.toNat_inj, StatusFlags.get_set_ne, fswCC_fswMerge, eq_comm]

@[simp] theorem write_external (r : Reg) (v : Value) (t : RamState) :
    (r.write v t).external = t.external := by
  cases r <;> simp [write, setFpuPtr]

@[simp] theorem write_RIP (r : Reg) (v : Value) (t : RamState) : (r.write v t).RIP = t.RIP := by
  cases r <;> simp [write, setFpuPtr]

theorem read_df_iff {s : RamState} :
    (ofIndex 22).read s = ⟨1, 0⟩ ↔ Prelude.RFLAGS.DirectionFlagClear s.RFLAGS := by
  show (⟨1, (dfBit s.RFLAGS).setWidth 1⟩ : Value) = ⟨1, 0⟩ ↔ _
  rw [BitVec.setWidth_eq]
  exact ⟨fun h => ⟨Value.eq_bits h⟩, fun h => by rw [show dfBit s.RFLAGS = 0 from h.df]⟩

end Reg

@[simp] theorem stateOf_external (p : BitVec 64) (entries : List (Reg × Value)) (mem : Ram) :
    (stateOf p entries mem).external = mem := by
  induction entries with
  | nil => rfl
  | cons e es ih => simp only [stateOf, List.foldr_cons] at ih ⊢; rw [Reg.write_external, ih]

@[simp] theorem stateOf_RIP (p : BitVec 64) (entries : List (Reg × Value)) (mem : Ram) :
    (stateOf p entries mem).RIP = p := by
  induction entries with
  | nil => rfl
  | cons e es ih => simp only [stateOf, List.foldr_cons] at ih ⊢; rw [Reg.write_RIP, ih]

theorem read_stateOf_not_mem {p : BitVec 64} {mem : Ram} {r : Reg} :
    ∀ {entries : List (Reg × Value)}, r ∉ entries.map Prod.fst →
      r.read (stateOf p entries mem) = r.read (stateOf p [] mem)
  | [], _ => rfl
  | ⟨r', v⟩ :: es, hr => by
    simp only [List.map_cons, List.mem_cons, not_or] at hr
    simp only [stateOf, List.foldr_cons] at *
    rw [Reg.read_write_ne hr.1]
    exact read_stateOf_not_mem hr.2

theorem read_stateOf {u : RamState} {p : BitVec 64} {mem : Ram} {r : Reg} :
    ∀ {entries : List (Reg × Value)}, (∀ e ∈ entries, e.2 = e.1.read u) →
      r ∈ entries.map Prod.fst → r.read (stateOf p entries mem) = r.read u
  | [], _, h => by simp at h
  | e :: es, hent, hr => by
    simp only [stateOf, List.foldr_cons]
    obtain ⟨re, ve⟩ := e
    have hve : ve = re.read u := hent _ List.mem_cons_self
    subst hve
    by_cases hre : r = re
    · subst hre
      exact Reg.read_write_read r u _
    · rw [Reg.read_write_ne hre]
      have hr' : r ∈ es.map Prod.fst := by
        simp only [List.map_cons, List.mem_cons] at hr
        exact hr.resolve_left hre
      exact read_stateOf (fun e he => hent e (List.mem_cons_of_mem _ he)) hr'

theorem entriesOf_holds (rs : List Reg) (s : RamState) : ∀ e ∈ entriesOf rs s, e.2 = e.1.read s := by
  intro e he
  simp only [entriesOf, List.mem_map] at he
  obtain ⟨r, -, rfl⟩ := he
  rfl

theorem map_fst_entriesOf (rs : List Reg) (s : RamState) : (entriesOf rs s).map Prod.fst = rs := by
  simp only [entriesOf, List.map_map]
  exact List.map_id' rs

theorem read_stateOf_entriesOf {p : BitVec 64} {mem : Ram} {rs : List Reg} {r : Reg}
    (s : RamState) (hr : r ∈ rs) : r.read (stateOf p (entriesOf rs s) mem) = r.read s :=
  read_stateOf (entriesOf_holds rs s) ((map_fst_entriesOf rs s).symm ▸ hr)

theorem filter_entriesOf (rs : List Reg) (s : RamState) :
    (entriesOf rs s).filter (fun e => !e.1.isFlag) = entriesOf (Reg.nonFlags rs) s := by
  simp only [entriesOf, Reg.nonFlags, List.filter_map]
  rfl

theorem Reg.write_obs {t t' : RamState} (h : Obs t t') (r : Reg) (v : Value) :
    r.isFlag = false → Obs (r.write v t) (r.write v t') := by
  intro hr
  obtain ⟨hgpr, hmem, hzmm, hrfl, hmx, hfpr, hfsw, hftw, hfcw, hptr, hcs⟩ := h
  simp only [fpuPtrOf] at hptr
  cases r <;> simp only [Reg.isFlag] at hr <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp_all [Reg.write, setFpuPtr, fpuPtrOf, clearStatusFlags_setSlice_df]

theorem Reg.write_flag_obs {t t' : RamState} (h : Obs t t') (f : StatusFlag) (v : Value) :
    Obs ((Reg.flag f).write v t) t' := by
  obtain ⟨hgpr, hmem, hzmm, hrfl, hmx, hfpr, hfsw, hftw, hfcw, hptr, hcs⟩ := h
  refine ⟨hgpr, hmem, hzmm, ?_, hmx, hfpr, hfsw, hftw, hfcw, hptr, hcs⟩
  simp only [Reg.write]
  rw [clearStatusFlags_store]
  exact hrfl

theorem stateOf_obs_filter (p : BitVec 64) (mem : Ram) :
    ∀ entries : List (Reg × Value),
      Obs (stateOf p entries mem) (stateOf p (entries.filter fun e => !e.1.isFlag) mem)
  | [] => Obs.refl _
  | ⟨r, v⟩ :: es => by
    have ih := stateOf_obs_filter p mem es
    cases hr : r.isFlag with
    | true =>
      cases r with
      | flag f =>
        simp only [stateOf, List.foldr_cons, List.filter_cons, hr] at ih ⊢
        exact Reg.write_flag_obs ih f v
      | _ => simp [Reg.isFlag] at hr
    | false =>
      simp only [stateOf, List.foldr_cons, List.filter_cons, hr] at ih ⊢
      exact Reg.write_obs ih r v hr

end X86Proofs.Lift
