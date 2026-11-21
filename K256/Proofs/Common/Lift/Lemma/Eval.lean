import K256.Proofs.Common.Lift.Lemma.Lockstep
import K256.Proofs.Common.Lift.Lemma.Read
import X86Proofs.Instructions.Call.Triple
namespace K256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG

section States

variable {p : BitVec 64} {mem : Ram}

theorem Op.state_RIP (reads : List Reg) {n : Nat} (args : Values Value n) :
    (Op.state p reads args mem).RIP = p :=
  stateOf_RIP _ _ _

theorem Op.state_external (reads : List Reg) {n : Nat} (args : Values Value n) :
    (Op.state p reads args mem).external = mem :=
  stateOf_external _ _ _

end States

theorem read_stateOf_cons (r r' : Reg) (v : Value) (es : List (Reg × Value)) (p : BitVec 64)
    (mem : Ram) :
    r.read (stateOf p ((r', v) :: es) mem) =
      if r = r' then r'.read (r'.write v (stateOf p es mem)) else r.read (stateOf p es mem) := by
  simp only [stateOf, List.foldr_cons]
  split
  · subst r'
    rfl
  · exact Reg.read_write_ne ‹_› v _

theorem Reg.read_write_gpr (r : BitVec 5) (v : Value) (t : RamState) :
    (Reg.gpr r).read ((Reg.gpr r).write v t) = ⟨64, v.get 64⟩ := by
  simp [Reg.read, Reg.write]

theorem Reg.read_write_flag (f : StatusFlag) (v : Value) (t : RamState) :
    (Reg.flag f).read ((Reg.flag f).write v t) = .ofBool v.truth := by
  simp [Reg.read, Reg.write, StatusFlags.ofRFLAGS_store]

theorem Reg.read_write_df (v : Value) (t : RamState) :
    Reg.df.read (Reg.df.write v t) = ⟨1, v.get 1⟩ := by
  simp [Reg.read, Reg.write]

theorem Value.get_mk_setWidth (n m : Nat) (x : BitVec n) : (⟨n, x⟩ : Value).get m = x.setWidth m :=
  rfl

theorem RegMap.args_entryMap (m n : Nat) [NeZero n] : (entryMap m).args n = RegMap.args [] n := by
  apply Vector.ext
  intro i hi
  rw [RegMap.getElem_args _ _ _ hi, RegMap.getElem_args _ _ _ hi]
  cases h : (entryMap m).lookup i with
  | none => rfl
  | some j =>
    obtain ⟨l₁, l₂, hρ, -⟩ := List.lookup_eq_some_iff.mp h
    obtain ⟨rfl, -⟩ := mem_entryMap (m := m) (i := i) (j := j)
      (by rw [hρ]; exact List.mem_append_right _ List.mem_cons_self)
    rfl

section Addr

variable (b i : BitVec 4) (sc : BitVec 2) (v8 : BitVec 8) (v : BitVec 32) (t : RamState)
  (q : BitVec 64)

theorem addr_base_none :
    (AddrMode.base b .none).addr t q = ((Reg.gpr (b.setWidth 5)).read t).get 64 := by
  simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get, Disp.value]
  exact BitVec.add_zero _

theorem addr_base_d8 :
    (AddrMode.base b (.d8 v8)).addr t q =
      ((Reg.gpr (b.setWidth 5)).read t).get 64 + v8.signExtend 64 := by
  simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get, Disp.value]

theorem addr_base_d32 :
    (AddrMode.base b (.d32 v)).addr t q =
      ((Reg.gpr (b.setWidth 5)).read t).get 64 + v.signExtend 64 := by
  simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get, Disp.value]

theorem addr_sib_none :
    (AddrMode.sib b none sc .none).addr t q = ((Reg.gpr (b.setWidth 5)).read t).get 64 := by
  simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get, Disp.value]
  exact BitVec.add_zero _

theorem addr_sib_d8 :
    (AddrMode.sib b none sc (.d8 v8)).addr t q =
      ((Reg.gpr (b.setWidth 5)).read t).get 64 + v8.signExtend 64 := by
  simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get, Disp.value]

theorem addr_sib_d32 :
    (AddrMode.sib b none sc (.d32 v)).addr t q =
      ((Reg.gpr (b.setWidth 5)).read t).get 64 + v.signExtend 64 := by
  simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get, Disp.value]

theorem addr_index_none :
    (AddrMode.sib b (some i) sc .none).addr t q =
      ((Reg.gpr (b.setWidth 5)).read t).get 64 +
        (((Reg.gpr (i.setWidth 5)).read t).get 64 <<< sc.toNat) := by
  simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get, Disp.value]
  exact BitVec.add_zero _

theorem addr_index_d8 :
    (AddrMode.sib b (some i) sc (.d8 v8)).addr t q =
      ((Reg.gpr (b.setWidth 5)).read t).get 64 +
        (((Reg.gpr (i.setWidth 5)).read t).get 64 <<< sc.toNat) + v8.signExtend 64 := by
  simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get, Disp.value]

theorem addr_index_d32 :
    (AddrMode.sib b (some i) sc (.d32 v)).addr t q =
      ((Reg.gpr (b.setWidth 5)).read t).get 64 +
        (((Reg.gpr (i.setWidth 5)).read t).get 64 <<< sc.toNat) + v.signExtend 64 := by
  simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get, Disp.value]

theorem addr_rip : (AddrMode.rip v).addr t q = q + v.signExtend 64 := by
  rw [AddrMode.addr]

theorem addr_abs_none :
    (AddrMode.abs none sc v).addr t q = v.signExtend 64 := by
  rw [AddrMode.addr]

theorem addr_abs_some :
    (AddrMode.abs (some i) sc v).addr t q =
      (((Reg.gpr (i.setWidth 5)).read t).get 64 <<< sc.toNat) + v.signExtend 64 := by
  simp only [AddrMode.addr, AddrMode.reg64, Operand.read_reg_get]

end Addr

theorem add_zero_lit {w : Nat} (x : BitVec w) : x + 0 = x := BitVec.add_zero x

theorem zero_add_lit {w : Nat} (x : BitVec w) : 0 + x = x := BitVec.zero_add x

theorem sub_zero_lit {w : Nat} (x : BitVec w) : x - 0 = x := BitVec.sub_zero x

theorem xor_self_lit {w : Nat} (x : BitVec w) : x ^^^ x = 0 := BitVec.xor_self

theorem sub_self_lit {w : Nat} (x : BitVec w) : x - x = 0 := BitVec.sub_self x

theorem add_add_lit {w : Nat} (x a b c : BitVec w) (h : a + b = c) : x + a + b = x + c := by
  rw [BitVec.add_assoc, h]

theorem sub_add_lit {w : Nat} (x a b c : BitVec w) (h : b - a = c) : x - a + b = x + c := by
  rw [← h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (-a) b]

theorem add_sub_lit {w : Nat} (x a b c : BitVec w) (h : a - b = c) : x + a - b = x + c := by
  rw [← h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem sub_sub_lit {w : Nat} (x a b c : BitVec w) (h : -a - b = c) : x - a - b = x + c := by
  rw [← h, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]

theorem add_eq_sub_of_neg_eq {w : Nat} (x c c' : BitVec w) (h : -c' = c) :
    x + c = x - c' := by
  rw [BitVec.sub_eq_add_neg, h]

theorem sub_eq_add_of_neg_eq {w : Nat} (x c c' : BitVec w) (h : -c' = c) :
    x - c = x + c' := by
  rw [BitVec.sub_eq_add_neg, ← h, BitVec.neg_neg]

theorem ite_ite_none {α : Type} {a b : Prop} [Decidable a] [Decidable b] (x : Option α) :
    (if a then (if b then x else none) else none) = if a ∧ b then x else none := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

theorem and_eq_subst {α : Sort _} {a t : α} (q : α → Prop) : (a = t ∧ q a) = (a = t ∧ q t) :=
  propext ⟨fun ⟨h, hq⟩ => ⟨h, h ▸ hq⟩, fun ⟨h, hq⟩ => ⟨h, h ▸ hq⟩⟩

theorem not_covers_of_isMem {c : Component} (h : c.isMem = false) (x : BitVec 64) :
    ¬ c.Covers x := by
  cases c <;> simp_all [Component.isMem, Component.Covers]

theorem applyWrites_external_of_noMem (t : RamState) {ws : List Write}
    (h : ∀ w ∈ ws, w.component.isMem = false) : (applyWrites t ws).external = t.external :=
  Std.ExtHashMap.ext_getElem? fun x => applyWrites_external_of_not_covers t ws x
    fun w hw => not_covers_of_isMem (h w hw) x

theorem applyWrites_mem_external (t : RamState) (a : BitVec 64) {n : Nat} (v : BitVec n) :
    (applyWrites t [⟨(Operand.mem a : Operand n), v⟩]).external = memStore t.external a v := rfl

theorem applyWrites_pushEffect_external (rip v : RamState → BitVec 64) (t : RamState) :
    (applyWrites t (pushEffect rip v t).writes).external = memStore t.external (pushAddr t) (v t) := by
  simp [pushEffect, applyWrites_cons, applyWrites_nil, Write.apply_mk, Operand.write]

section Guards

variable {code : CodeMap} {p : BitVec 64} {e : RamState → Effect} {t : RamState} {mem : Ram}

theorem avoids_of_noMem (hmem : ∀ c ∈ (e t).components, c.isMem = false) :
    (e t).Avoids code :=
  Effect.Avoids.of_noMem (fun c hc => not_covers_of_isMem (hmem c hc)) code

theorem writesPresent_of_noMem (hmem : ∀ c ∈ (e t).components, c.isMem = false) :
    WritesPresent (e t) mem :=
  fun c hc x hx => absurd hx (not_covers_of_isMem (hmem c hc) x)

theorem guard_rip (hrip : t.RIP = p) (hmem : ∀ c ∈ (e t).components, c.isMem = false) :
    Guard code (fun s => s.RIP = p) e t mem :=
  ⟨hrip, avoids_of_noMem hmem, writesPresent_of_noMem hmem⟩

theorem loadOk_iff {a : BitVec 64} {len : Nat} (hext : t.external = mem) :
    MemReadable t a len ↔ LoadOk mem a len := by
  subst hext
  exact ⟨fun h => ⟨h.low, h.mem⟩, fun h => ⟨h.low, h.present⟩⟩

theorem guard_load_iff {addr : RamState → BitVec 64} {len : Nat} (hrip : t.RIP = p)
    (hext : t.external = mem) (hmem : ∀ c ∈ (e t).components, c.isMem = false) :
    Guard code (LoadPre p addr len) e t mem ↔ LoadOk mem (addr t) len :=
  ⟨fun h => (loadOk_iff hext).mp h.1.read, fun h => ⟨⟨hrip, (loadOk_iff hext).mpr h⟩,
    avoids_of_noMem hmem, writesPresent_of_noMem hmem⟩⟩

theorem guard_ret_iff (hrip : t.RIP = p) (hext : t.external = mem)
    (hmem : ∀ c ∈ (e t).components, c.isMem = false) :
    Guard code (RetPre p) e t mem ↔
      LoadOk mem (stackPtr t) 8 ∧ (memLoad mem (stackPtr t) 64).toNat < 2^32 := by
  have htop : stackTop t = memLoad mem (stackPtr t) 64 := by
    rw [← hext]
    rfl
  rw [htop.symm]
  refine ⟨fun h => ⟨(loadOk_iff hext).mp h.1.1.read, h.1.2⟩, fun h => ⟨⟨⟨hrip,
    (loadOk_iff hext).mpr h.1⟩, h.2⟩, avoids_of_noMem hmem, writesPresent_of_noMem hmem⟩⟩

theorem guard_and {pre q : RamState → Prop} :
    Guard code (fun s => pre s ∧ q s) e t mem ↔ Guard code pre e t mem ∧ q t :=
  ⟨fun ⟨⟨h, hq⟩, ha, hw⟩ => ⟨⟨h, ha, hw⟩, hq⟩, fun ⟨⟨h, ha, hw⟩, hq⟩ => ⟨⟨h, hq⟩, ha, hw⟩⟩

theorem avoids_iff_of_mem {a : BitVec 64} {len : Nat}
    (hmem : (e t).components.filter Component.isMem = [.mem a len]) :
    (e t).Avoids code ↔ ∀ x ∈ code, ∀ i < len, x.1 ≠ a + BitVec.ofNat 64 i := by
  have hin : Component.mem a len ∈ (e t).components :=
    (List.mem_filter.mp (hmem ▸ List.mem_singleton_self _)).1
  have hc : ∀ c ∈ (e t).components, ∀ x, c.Covers x → c = .mem a len := by
    intro c hc x hx
    cases hm : c.isMem
    · exact absurd hx (not_covers_of_isMem hm x)
    · have h := List.mem_filter.mpr ⟨hc, hm⟩
      rw [hmem] at h
      exact List.mem_singleton.mp h
  refine ⟨fun hav x hx i hi he => hav x hx _ hin ⟨i, hi, he⟩, fun h x hx c hcm hcov => ?_⟩
  obtain rfl := hc c hcm _ hcov
  obtain ⟨i, hi, he⟩ := hcov
  exact h x hx i hi he

theorem writesPresent_iff_of_mem {a : BitVec 64} {len : Nat}
    (hmem : (e t).components.filter Component.isMem = [.mem a len]) :
    WritesPresent (e t) mem ↔ ∀ i < len, (mem[a + BitVec.ofNat 64 i]?).isSome := by
  have hin : Component.mem a len ∈ (e t).components :=
    (List.mem_filter.mp (hmem ▸ List.mem_singleton_self _)).1
  refine ⟨fun h i hi => h _ hin _ ⟨i, hi, rfl⟩, fun h c hcm x hcov => ?_⟩
  cases hm : c.isMem
  · exact absurd hcov (not_covers_of_isMem hm x)
  · have hc := List.mem_filter.mpr ⟨hcm, hm⟩
    rw [hmem, List.mem_singleton] at hc
    subst hc
    obtain ⟨i, hi, rfl⟩ := hcov
    exact h i hi

theorem guard_store_iff {codeLen len : Nat} {addr : RamState → BitVec 64} (hrip : t.RIP = p)
    (hext : t.external = mem)
    (hmem : (e t).components.filter Component.isMem = [.mem (addr t) len]) :
    Guard code (StorePre p codeLen addr len) e t mem ↔ StoreOk code mem (addr t) len p codeLen := by
  subst hext
  have hin : Component.mem (addr t) len ∈ (e t).components :=
    (List.mem_filter.mp (hmem ▸ List.mem_singleton_self _)).1
  have hc : ∀ c ∈ (e t).components, ∀ x, c.Covers x → c = .mem (addr t) len := by
    intro c hc x hx
    cases hm : c.isMem
    · exact absurd hx (not_covers_of_isMem hm x)
    · have h := List.mem_filter.mpr ⟨hc, hm⟩
      rw [hmem] at h
      exact List.mem_singleton.mp h
  constructor
  · rintro ⟨⟨-, hw, hap⟩, hav, -⟩
    exact ⟨hw.low, hw.mem, hw.tables, hap, fun x hx i hi he => hav x hx _ hin ⟨i, hi, he⟩⟩
  · intro h
    refine ⟨⟨hrip, ⟨h.low, h.present, h.tables⟩, h.apart⟩, ?_, ?_⟩
    · intro x hx c hcm hcov
      obtain rfl := hc c hcm _ hcov
      obtain ⟨i, hi, he⟩ := hcov
      exact h.notCode x hx i hi he
    · intro c hcm x hcov
      obtain rfl := hc c hcm x hcov
      obtain ⟨i, hi, rfl⟩ := hcov
      exact h.present i hi

end Guards

end K256.Proofs.Lift
