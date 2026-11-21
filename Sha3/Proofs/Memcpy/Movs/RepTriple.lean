import X86Proofs.Instructions.Movs.RepTriple
import Sha3.Proofs.Memory
import Sha3.Proofs.Memcpy.Movs.RepStep
import X86Proofs.Program.Effect

namespace X86Proofs

open X86 X86.Machine X86.UserProcess Prelude Sha3.Spec.Program

local macro "movs_omega" b:ident : tactic =>
  `(tactic| first | omega |
    (cases ($b) <;>
      simp_all only [movsBytes, movsLength, Bool.false_eq_true, ite_false, ite_true] <;> omega))

structure ReadyMovsLoop (byte : Bool) [Bindings] (rex : UInt8) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP (movsCode byte rex)
  codeLow : s.RIP.toNat + (movsLength byte) ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + (movsBytes byte) * count ≤ 2^32
  dstLow : (rdi.read s).toNat + (movsBytes byte) * count ≤ 2^32
  dstAlign : (rdi.read s).toNat % (movsBytes byte) = 0
  srcMem : ∀ i < (movsBytes byte) * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < (movsBytes byte) * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + (movsBytes byte) * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + (movsBytes byte) * count ≤ (rsi.read s).toNat
  dstTables : (MemoryRegion.mk (rdi.read s).toNat ((movsBytes byte) * count)).Avoids InPageTables
  dstCode : RangeApart (rdi.read s) ((movsBytes byte) * count) s.RIP (movsLength byte)


theorem ReadyMovsLoop.rcx_ne {byte : Bool} [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyMovsLoop byte rex s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.srcLow; movs_omega byte)

theorem ReadyMovsLoop.step {byte : Bool} [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8}
    (hrex : byte = false → RexWPrefix rex.toBitVec) {s : RamState} {count : Nat} (h : ReadyMovsLoop byte rex s count)
    (hpos : 0 < count) : X86.Machine.step s = some (.next (repMovsAfter byte s)) := by
  have := h.srcLow
  have := h.dstLow
  have := h.dstAlign
  exact rep_movs_step byte hstride s h.ready rex hrex h.df h.code h.codeLow (h.rcx_ne hpos) (by movs_omega byte)
    (by movs_omega byte) (by movs_omega byte) (fun i hi => h.srcMem i (by movs_omega byte)) (fun i hi => h.dstMem i (by movs_omega byte))

theorem ReadyMovsLoop.rcx_after {byte : Bool} [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyMovsLoop byte rex s (count + 1)) : rcx.read (repMovsAfter byte s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem ReadyMovsLoop.source_frame {byte : Bool} [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyMovsLoop byte rex s count) (j : Nat) (hj : j < (movsBytes byte) * count) :
    (repMovsAfter byte s).external[rsi.read s + BitVec.ofNat 64 j]? =
      s.external[rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by movs_omega byte), toNat_add_ofNat _ _ (by movs_omega byte)] at hn
  movs_omega byte

theorem ReadyMovsLoop.after_tables {byte : Bool} [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyMovsLoop byte rex s count) (hpos : 0 < count) :
    IdentityPageTableMemory (repMovsAfter byte s).external := by
  rw [repMovsAfter_external]
  apply Sha3.Proofs.identityPageTableMemory_memStore_of_avoids s _ _
    #v[MemoryRegion.mk (rdi.read s).toNat ((movsBytes byte) * count)] h.ready.clear.memory.tables
  · intro i hi
    refine ⟨MemoryRegion.mk (rdi.read s).toNat ((movsBytes byte) * count), by simp, ?_⟩
    rw [toNat_add_ofNat _ _ (by have := h.dstLow; movs_omega byte)]
    change (rdi.read s).toNat ≤ (rdi.read s).toNat + i ∧
      (rdi.read s).toNat + i < (rdi.read s).toNat + (movsBytes byte) * count
    constructor <;> movs_omega byte
  · intro region hregion
    have he : region = MemoryRegion.mk (rdi.read s).toNat ((movsBytes byte) * count) := by
      simpa using hregion
    rw [he]
    exact h.dstTables

theorem ReadyMovsLoop.next {byte : Bool} [Bindings] {rex : UInt8} {s : RamState} {count : Nat}
    (h : ReadyMovsLoop byte rex s (count + 2)) : ReadyMovsLoop byte rex (repMovsAfter byte s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hal := h.dstAlign
  have hrip : (repMovsAfter byte s).RIP = s.RIP := by
    rw [repMovsAfter_rip byte s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by movs_omega byte) (by movs_omega byte), ↓reduceIte]
  have hs : rsi.read (repMovsAfter byte s) = rsi.read s + BitVec.ofNat 64 (movsBytes byte) := repMovsAfter_rsi byte s
  have hd : rdi.read (repMovsAfter byte s) = rdi.read s + BitVec.ofNat 64 (movsBytes byte) := repMovsAfter_rdi byte s
  have hsn : (rsi.read (repMovsAfter byte s)).toNat = (rsi.read s).toNat + (movsBytes byte) := by
    rw [hs, toNat_add_ofNat _ _ (by movs_omega byte)]
  have hdn : (rdi.read (repMovsAfter byte s)).toNat = (rdi.read s).toNat + (movsBytes byte) := by
    rw [hd, toNat_add_ofNat _ _ (by movs_omega byte)]
  refine ⟨h.ready.repMovs (h.after_tables (by movs_omega byte)), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by movs_omega byte) i (by simpa only [movsCode_length] using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; movs_omega byte
  · rw [hdn]; movs_omega byte
  · rw [hdn]; movs_omega byte
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame ((movsBytes byte) + i) (by movs_omega byte)]
    exact h.srcMem ((movsBytes byte) + i) (by movs_omega byte)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem ((movsBytes byte) + i) (by movs_omega byte))
  · rw [hsn, hdn]; have := h.disjoint; movs_omega byte
  · intro x hx
    apply h.dstTables x
    change (rdi.read (repMovsAfter byte s)).toNat ≤ x.toNat ∧
      x.toNat < (rdi.read (repMovsAfter byte s)).toNat + (movsBytes byte) * (count + 1) at hx
    rw [hdn] at hx
    change (rdi.read s).toNat ≤ x.toNat ∧ x.toNat < (rdi.read s).toNat + (movsBytes byte) * (count + 2)
    constructor <;> movs_omega byte
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode ((movsBytes byte) + i) (by movs_omega byte) j hj

structure MovsDone (byte : Bool) [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 (movsLength byte))
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 ((movsBytes byte) * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 ((movsBytes byte) * count)
  copy : ∀ i < (movsBytes byte) * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) ((movsBytes byte) * count), .rip]
    (clearRep s) t


theorem rep_movs_loop {byte : Bool} [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {rex : UInt8}
    (hrex : byte = false → RexWPrefix rex.toBitVec) (count : Nat) (s : RamState) (h : ReadyMovsLoop byte rex s (count + 1)) :
    MovsDone byte s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = repMovsAfter byte s := nextState_of_step (h.step hstride hrex (by movs_omega byte))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsAfter byte s).Repeat_String_Operation = false := by
      rw [repMovsAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (h.ready.repMovs (h.after_tables (by movs_omega byte))).ready hflag
    · rw [repMovsAfter_rip byte s h.ready.msr, hc]; rfl
    · rw [repMovsAfter_rcx, hc]
    · simpa only [Nat.zero_add, Nat.mul_one] using repMovsAfter_rsi byte s
    · simpa only [Nat.zero_add, Nat.mul_one] using repMovsAfter_rdi byte s
    · intro i hi
      exact repMovsAfter_copy byte s i (by movs_omega byte) (h.srcMem i (by movs_omega byte))
    · rw [← clearRep_eq hflag]
      simpa only [Nat.zero_add, Nat.mul_one] using AgreesExcept.repMovs byte s
  | succ k ih =>
    have hnext : nextState s = repMovsAfter byte s := nextState_of_step (h.step hstride hrex (by movs_omega byte))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsAfter byte s) = rsi.read s + BitVec.ofNat 64 (movsBytes byte) := repMovsAfter_rsi byte s
    have hd : rdi.read (repMovsAfter byte s) = rdi.read s + BitVec.ofNat 64 (movsBytes byte) := repMovsAfter_rdi byte s
    have hfirst (i : Nat) (hi : i < (movsBytes byte)) :
        (repMovsAfter byte s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsAfter_copy byte s i hi (h.srcMem i (by movs_omega byte))
    have ih' := ih (repMovsAfter byte s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsAfter byte s).RIP = s.RIP := by
      rw [repMovsAfter_rip byte s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := k + 1) (by movs_omega byte) (by movs_omega byte), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; movs_omega byte
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; movs_omega byte
    · intro i hi
      by_cases hsmall : i < (movsBytes byte)
      ·
        refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by movs_omega byte), toNat_add_ofNat _ _ (by movs_omega byte)] at hn
        movs_omega byte
      · have hc := ih'.copy (i - (movsBytes byte)) (by movs_omega byte)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by movs_omega byte),
          h.source_frame i (by movs_omega byte)] at hc
        exact hc
    · refine (AgreesExcept.repMovs byte s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) ((movsBytes byte) * (k + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by movs_omega byte, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨(movsBytes byte) + j, by movs_omega byte, he⟩

structure RepMovsPre (byte : Bool) (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  srcLow : (rsi.read s).toNat + (movsBytes byte) * (rcx.read s).toNat ≤ 2^32
  dstLow : (rdi.read s).toNat + (movsBytes byte) * (rcx.read s).toNat ≤ 2^32
  dstAlign : (rdi.read s).toNat % (movsBytes byte) = 0
  srcMem : ∀ i < (movsBytes byte) * (rcx.read s).toNat, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < (movsBytes byte) * (rcx.read s).toNat, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + (movsBytes byte) * (rcx.read s).toNat ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + (movsBytes byte) * (rcx.read s).toNat ≤ (rsi.read s).toNat
  dstTables : (MemoryRegion.mk (rdi.read s).toNat ((movsBytes byte) * (rcx.read s).toNat)).Avoids InPageTables
  dstCode : RangeApart (rdi.read s) ((movsBytes byte) * (rcx.read s).toNat) p (movsLength byte)

def repMovsEffect (byte : Bool) (p : BitVec 64) (s : RamState) : Effect where
  rip := p + BitVec.ofNat 64 (movsLength byte)
  writes := [⟨rsi, rsi.read s + BitVec.ofNat 64 ((movsBytes byte) * (rcx.read s).toNat)⟩,
    ⟨rdi, rdi.read s + BitVec.ofNat 64 ((movsBytes byte) * (rcx.read s).toNat)⟩, ⟨rcx, 0⟩,
    ⟨(Operand.mem (rdi.read s) : Operand ((8 * movsBytes byte) * (rcx.read s).toNat)),
      (Operand.mem (rsi.read s) : Operand ((8 * movsBytes byte) * (rcx.read s).toNat)).read s⟩]

theorem repMovsEffect_components {byte : Bool} (p : BitVec 64) (s : RamState) :
    (repMovsEffect byte p s).components =
      [.reg 6, .reg 7, .reg 1, .mem (rdi.read s) ((movsBytes byte) * (rcx.read s).toNat), .rip] := by
  simp only [repMovsEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append]
  rw [show (8 * movsBytes byte) * (rcx.read s).toNat / 8 = (movsBytes byte) * (rcx.read s).toNat by movs_omega byte]

theorem repMovsEffect_avoids {byte : Bool} {p : BitVec 64} {s : RamState} (rex : UInt8)
    (h : RangeApart (rdi.read s) ((movsBytes byte) * (rcx.read s).toNat) p (movsLength byte)) :
    (repMovsEffect byte p s).Avoids (codeRange p (movsCode byte rex)) := by
  intro x hx c hc hcov
  rw [repMovsEffect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
  obtain ⟨i, hi, hxe⟩ := hcov
  obtain ⟨j, hj, hxj⟩ := exists_of_mem_codeRange hx
  exact h i hi j (by simpa only [movsCode_length] using hj) (hxe.symm.trans hxj)


theorem rep_movs_steps {byte : Bool} [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : byte = false → RexWPrefix rex.toBitVec) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p (movsCode byte rex)) s) (hpre : RepMovsPre byte p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p (movsCode byte rex)) t ∧ (repMovsEffect byte p s).Holds s t := by
  intro t
  have hcodeS : BytesAt s s.RIP (movsCode byte rex) := hpre.rip ▸ hcode.bytesAt
  have hlow : s.RIP.toNat + (movsLength byte) ≤ 2^32 := hpre.rip ▸ (by simpa only [movsCode_length] using hcode.low (by cases byte <;> simp [movsCode]) (by cases byte <;> simp [movsCode]))
  suffices hh : ReadyToStep t ∧ (repMovsEffect byte p s).Holds s t from
    ⟨hh.1, hh.2.codeIn (repMovsEffect_avoids rex hpre.dstCode) hcode, hh.2⟩
  have hrep := h.ready.repeatClear
  rcases hn : (rcx.read s).toNat with _ | k
  ·
    have hz : rcx.read s = 0 := BitVec.eq_of_toNat_eq hn
    have ht : t = repMovsZeroAfter byte s := by
      simp only [t, hn]
      exact nextState_of_step (rep_movs_step_zero byte s h.midRep rex hrex hcodeS hlow hz)
    rw [ht]
    have hag : AgreesExcept [.rip] s (repMovsZeroAfter byte s) :=
      (AgreesExcept.repMovsZero byte s).of_clearRep hrep (repMovsZeroAfter_repeat byte s)
    refine ⟨ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_, ?_, trivial, ?_⟩
    · rw [repMovsZeroAfter_rip byte s h.ready.msr, hpre.rip]; rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hn]; simp
      · rw [hag.read (by simp), hz]
      · apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hi' : i < (8 * movsBytes byte) * (rcx.read s).toNat := hi
        movs_omega byte
    · exact hag.mono (by simp [repMovsEffect_components])
  ·
    have hc : rcx.read s = BitVec.ofNat 64 (k + 1) := by
      apply BitVec.eq_of_toNat_eq
      have := hpre.srcLow
      rw [hn, BitVec.toNat_ofNat]
      movs_omega byte
    have hready : ReadyMovsLoop byte rex s (k + 1) :=
      ⟨h.midRep, hpre.df, hcodeS, hlow, hc, hn ▸ hpre.srcLow, hn ▸ hpre.dstLow, hpre.dstAlign, hn ▸ hpre.srcMem,
        hn ▸ hpre.dstMem, hn ▸ hpre.disjoint, hn ▸ hpre.dstTables, hpre.rip ▸ hn ▸ hpre.dstCode⟩
    have hd := rep_movs_loop hstride hrex k s hready
    have ht : t = nextStates (k + 1) s := by
      simp only [t, hn, show max (k + 1) 1 = k + 1 by movs_omega byte]
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
        have hi' : i < (8 * movsBytes byte) * (rcx.read s).toNat / 8 := hi
        exact memByte_congr (hd.copy i (by movs_omega byte))
    · rw [repMovsEffect_components, hn]
      exact hag.mono (by simp)

theorem rep_movs_triple {byte : Bool} [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (rex : UInt8) (hrex : byte = false → RexWPrefix rex.toBitVec) :
    Triple (RepMovsPre byte p) (codeRange p (movsCode byte rex)) (Effect.post (repMovsEffect byte p)) :=
  fun s h hcode hpre => ⟨_, rep_movs_steps hstride p rex hrex s h hcode hpre⟩

theorem repMovsEffect_bytes {byte : Bool} {p : BitVec 64} {s s' : RamState} (h : (repMovsEffect byte p s).Holds s s')
    (i : Nat) (hi : i < (movsBytes byte) * (rcx.read s).toNat) :
    memByte s'.external (rdi.read s + BitVec.ofNat 64 i) =
      memByte s.external (rsi.read s + BitVec.ofNat 64 i) :=
  memByte_of_memLoad_eq (n := (8 * movsBytes byte) * (rcx.read s).toNat) h.writes.2.2.2 i (by movs_omega byte)


abbrev RepMovsbPre := RepMovsPre true
abbrev repMovsbEffect := repMovsEffect true

theorem rep_movsb_steps [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (p : BitVec 64) (s : RamState) (h : ReadyToStep s)
    (hcode : CodeIn (codeRange p [0xf3, 0xa4]) s) (hpre : RepMovsbPre p s) :
    let t := nextStates (max (rcx.read s).toNat 1) s
    ReadyToStep t ∧ CodeIn (codeRange p [0xf3, 0xa4]) t ∧ (repMovsbEffect p s).Holds s t := by
  exact rep_movs_steps (byte := true) hstride p 0 (by simp) s h hcode hpre

end X86Proofs
