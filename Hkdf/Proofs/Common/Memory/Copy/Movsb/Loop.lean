import Hkdf.Proofs.Common.Memory.Copy.Movsb.Step
import X86Proofs.Program.Effect

namespace Hkdf.Proofs.Common.Memory.Copy.Movsb

open X86Proofs X86 X86.Machine X86.UserProcess

structure ReadyRepMovsbLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xA4]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + count ≤ 2^32
  dstLow : (rdi.read s).toNat + count ≤ 2^32
  srcMem : ∀ i < count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + count ≤ (rsi.read s).toNat
  dstTables : (rdi.read s).toNat + count ≤ 0x1000 ∨ 0x3000 ≤ (rdi.read s).toNat
  dstCode : RangeApart (rdi.read s) count s.RIP 2

theorem ReadyRepMovsbLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : ReadyRepMovsbLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; omega)

theorem ReadyRepMovsbLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    {s : RamState} {count : Nat} (h : ReadyRepMovsbLoop s count)
    (hpos : 0 < count) : X86.Machine.step s = some (.next (repMovsbAfter s)) := by
  have := h.srcLow
  have := h.dstLow
  exact rep_movsb_step hstride s h.ready h.df h.code h.codeLow (h.rcx_ne hpos) (by omega)
    (by omega) (by simpa only [BitVec.add_zero] using h.srcMem 0 hpos) (by simpa only [BitVec.add_zero] using h.dstMem 0 hpos)

theorem ReadyRepMovsbLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : ReadyRepMovsbLoop s (count + 1)) : rcx.read (repMovsbAfter s) = BitVec.ofNat 64 count := by
  rw [repMovsbAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem ReadyRepMovsbLoop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : ReadyRepMovsbLoop s count) (j : Nat) (hj : j < count) :
    (repMovsbAfter s).external[rsi.read s + BitVec.ofNat 64 j]? =
      s.external[rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsbAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem ReadyRepMovsbLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : ReadyRepMovsbLoop s (count + 2)) : ReadyRepMovsbLoop (repMovsbAfter s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hrip : (repMovsbAfter s).RIP = s.RIP := by
    rw [repMovsbAfter_rip s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsbAfter s) = rsi.read s + BitVec.ofNat 64 1 := repMovsbAfter_rsi s
  have hd : rdi.read (repMovsbAfter s) = rdi.read s + BitVec.ofNat 64 1 := repMovsbAfter_rdi s
  have hsn : (rsi.read (repMovsbAfter s)).toNat = (rsi.read s).toNat + 1 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsbAfter s)).toNat = (rdi.read s).toNat + 1 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨ReadyMidRep.repMovsb h.ready (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsbAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (1 + i) (by omega)]
    exact h.srcMem (1 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsbAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (1 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (1 + i) (by omega) j hj

structure RepMovsbDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP 2#64
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 count
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 count
  copy : ∀ i < count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) count, .rip]
    (clearRep s) t

theorem rep_movsb_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (count : Nat) (s : RamState) (h : ReadyRepMovsbLoop s (count + 1)) :
    RepMovsbDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = repMovsbAfter s := nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsbAfter s).Repeat_String_Operation = false := by
      rw [repMovsbAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (ReadyMidRep.repMovsb h.ready (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsbAfter_rip s h.ready.msr, hc]; rfl
    · rw [repMovsbAfter_rcx, hc]
    · exact repMovsbAfter_rsi s
    · exact repMovsbAfter_rdi s
    · intro i hi
      exact repMovsbAfter_copy s i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovsb s
  | succ k ih =>
    have hnext : nextState s = repMovsbAfter s := nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsbAfter s) = rsi.read s + BitVec.ofNat 64 1 := repMovsbAfter_rsi s
    have hd : rdi.read (repMovsbAfter s) = rdi.read s + BitVec.ofNat 64 1 := repMovsbAfter_rdi s
    have hfirst (i : Nat) (hi : i < 1) :
        (repMovsbAfter s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsbAfter_copy s i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsbAfter s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsbAfter s).RIP = s.RIP := by
      rw [repMovsbAfter_rip s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := k + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 1
      ·
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 1) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovsb s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (k + 1 + 1), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨1 + j, by omega, he⟩

structure RepMovsbPre (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + (rcx.read s).toNat ≤ 2^32
  srcMem : ∀ i < (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : (rdi.read s).toNat + (rcx.read s).toNat ≤ 0x1000 ∨ 0x3000 ≤ (rdi.read s).toNat
  dstCode : RangeApart (rdi.read s) (rcx.read s).toNat p 2

def repMovsbEffect (p : BitVec 64) (s : RamState) : Effect where
  rip := p + 2
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 (rcx.read s).toNat⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 (rcx.read s).toNat⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand (8 * (rcx.read s).toNat)),
      (Operand.mem (rsi.read s) : Operand (8 * (rcx.read s).toNat)).read s⟩]

theorem repMovsbEffect_components (p : BitVec 64) (s : RamState) :
    (repMovsbEffect p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) (rcx.read s).toNat, .rip] := by
  simp only [repMovsbEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show 8 * (rcx.read s).toNat / 8 = (rcx.read s).toNat by omega]

theorem repMovsbEffect_avoids {p : BitVec 64} {s : RamState}
    (h : RangeApart (rdi.read s) (rcx.read s).toNat p 2) :
    (repMovsbEffect p s).Avoids (codeRange p [0xF3, 0xA4]) := by
  intro x hx c hc hcov
  rw [repMovsbEffect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
  obtain ⟨i, hi, hxe⟩ := hcov
  obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
  exact h i hi j hj (hxe.symm.trans hxj)

theorem rep_movsb_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xF3, 0xA4]) s) (hpre : RepMovsbPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xF3, 0xA4]) t ∧ (repMovsbEffect p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP [0xF3, 0xA4] := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + 2 ≤ 2^32 := hpre.rip ▸ hcode.low (by simp) (by simp)
  suffices hh : ReadyToStep t ∧ (repMovsbEffect p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsbEffect_avoids hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | k
  ·
    have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repMovsbZeroAfter s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movsb_step_zero s h.midRep hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repMovsbZeroAfter s) :=
      (AgreesExcept.repMovsbZero s).of_clearRep hrep (repMovsbZeroAfter_repeat s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repMovsbZeroAfter_rip s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < 8 * (rcx.read s).toNat := hi
        omega
    · exact hag.mono (by simp [repMovsbEffect_components])
  ·
    have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      omega
    have hready : ReadyRepMovsbLoop s (k + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movsb_loop hstride k s hready
    have ht : t = nextStates (k + 1) s := by
      simp only [t, hn, show max (k + 1) 1 = k + 1 by omega]
    rw [ht]
    have hag := hd.agrees
    rw [clearRep_eq hrep] at hag
    refine ⟨hd.ready, ?_, ?_, trivial, ?_⟩
    · rw [hd.rip, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd.rsiAfter, hn]
      · rw [hd.rdiAfter, hn]
      · exact hd.rcxZero
      · simp only [Operand.read]
        apply memLoad_congr
        intro i hi
        have hi' : i < 8 * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by omega))
    · rw [repMovsbEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_movsb_triple [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) :
    Triple (RepMovsbPre p) (codeRange p [0xF3, 0xA4]) (Effect.post (repMovsbEffect p)) :=
  fun s h hcode hpre => ⟨_, rep_movsb_steps hstride p s h hcode hpre⟩

theorem repMovsbEffect_bytes {p : BitVec 64} {s s' : RamState} (h : (repMovsbEffect p s).Holds s s')
    (i : Nat) (hi : i < (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := 8 * (rcx.read s).toNat) h.writes.2.2.2 i (by omega)

end Hkdf.Proofs.Common.Memory.Copy.Movsb
