import Sha2.Proofs.Common.Memory.Fill.Stos.After
import X86Proofs.Program.Execution

namespace Sha2.Proofs.Common.Memory.Fill.Stos

open X86Proofs X86 X86.Machine X86.UserProcess

structure StosInstruction [Bindings] (bytes : Nat) (code : List UInt8) : Prop where
  positive : 0 < bytes
  sizeBound : bytes ≤ 8
  codeNonempty : code ≠ []
  codeSmall : code.length ≤ 15
  step : ∀ s, ReadyMidRep s → DirectionFlagClear s.RFLAGS →
    BytesAt s s.RIP code → s.RIP.toNat + code.length ≤ 2^32 → rcx.read s ≠ 0 →
    (rdi.read s).toNat + bytes ≤ 2^32 → (rdi.read s).toNat % bytes = 0 →
    (∀ i < bytes, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome) →
    X86.Machine.step s = some (.next (repStosAfter bytes code.length s))
  zero : ∀ s, ReadyMidRep s → BytesAt s s.RIP code →
    s.RIP.toNat + code.length ≤ 2^32 → rcx.read s = 0 →
    X86.Machine.step s = some (.next (repStosZeroAfter code.length s))

structure ReadyRepStosLoop [Bindings] (bytes : Nat) (code : List UInt8)
    (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  codeAt : BytesAt s s.RIP code
  codeLow : s.RIP.toNat + code.length ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  zero : (Operand.reg 0 : Operand (8 * bytes)).read s = 0
  dstLow : (rdi.read s).toNat + bytes * count ≤ 2^32
  aligned : (rdi.read s).toNat % bytes = 0
  dstMem : ∀ i < bytes * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : (rdi.read s).toNat + bytes * count ≤ 0x1000 ∨ 0x3000 ≤ (rdi.read s).toNat
  dstCode : RangeApart (rdi.read s) (bytes * count) s.RIP code.length

theorem ReadyRepStosLoop.countBound [Bindings] {bytes count : Nat} {code : List UInt8}
    {s : RamState} (h : ReadyRepStosLoop bytes code s count) (hb : 0 < bytes) : count < 2^64 := by
  have hm : count ≤ bytes * count := by simpa using Nat.mul_le_mul_right count hb
  have := h.dstLow
  omega

theorem ReadyRepStosLoop.rcx_ne [Bindings] {bytes count : Nat} {code : List UInt8}
    {s : RamState} (h : ReadyRepStosLoop bytes code s count) (hb : 0 < bytes)
    (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (h.countBound hb)

theorem ReadyRepStosLoop.step [Bindings] {bytes count : Nat} {code : List UInt8}
    {s : RamState} (h : ReadyRepStosLoop bytes code s count) (hs : StosInstruction bytes code)
    (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repStosAfter bytes code.length s)) := by
  have hb : bytes ≤ bytes * count := by simpa using Nat.mul_le_mul_left bytes hpos
  have := h.dstLow
  exact hs.step s h.ready h.df h.codeAt h.codeLow (h.rcx_ne hs.positive hpos)
    (by omega) h.aligned (fun i hi => h.dstMem i (by omega))

theorem ReadyRepStosLoop.rcx_after [Bindings] {bytes count : Nat} {code : List UInt8}
    {s : RamState} (h : ReadyRepStosLoop bytes code s (count + 1)) :
    rcx.read (repStosAfter bytes code.length s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem ReadyRepStosLoop.rip_after [Bindings] {bytes count : Nat} {code : List UInt8}
    {s : RamState} (h : ReadyRepStosLoop bytes code s (count + 2)) (hb : 0 < bytes) :
    (repStosAfter bytes code.length s).RIP = s.RIP := by
  rw [repStosAfter_rip bytes code.length s h.ready.msr, h.counter]
  have hn := h.countBound hb
  simp only [show count + 2 = (count + 1) + 1 from rfl, ofNat_succ_sub_one,
    ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]

theorem ReadyRepStosLoop.next [Bindings] {bytes count : Nat} {code : List UInt8}
    {s : RamState} (h : ReadyRepStosLoop bytes code s (count + 2)) (hb : 0 < bytes) :
    ReadyRepStosLoop bytes code (repStosAfter bytes code.length s) (count + 1) := by
  have hd := h.dstLow
  have ht := h.dstTables
  have hmul : bytes * (count + 2) = bytes + bytes * (count + 1) := by simp only [Nat.mul_succ]; omega
  rw [hmul] at hd ht
  have hrip := h.rip_after hb
  have hdi := repStosAfter_rdi bytes code.length s
  have hdn : (rdi.read (repStosAfter bytes code.length s)).toNat = (rdi.read s).toNat + bytes := by
    rw [hdi, toNat_add_ofNat _ _ (by omega)]
  refine ⟨repStosAfter_ready bytes code.length h.ready (by omega) (by omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repStosAfter_external, memStore_getElem?_of_ne]
    · exact h.codeAt i hi
    · intro j hj he
      exact h.dstCode j (by omega) i hi he
  · rw [hrip]; exact h.codeLow
  · exact ((repStosAfter_agrees bytes code.length s).read (r := 0) (by simp)).trans h.zero
  · rw [hdn]; omega
  · rw [hdn, Nat.add_mod, h.aligned, Nat.mod_self, Nat.zero_add, Nat.zero_mod]
  · intro i hi
    rw [hdi, add_ofNat_add_ofNat, repStosAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (bytes + i) (by omega))
  · rw [hdn]; omega
  · intro i hi j hj
    rw [hdi, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (bytes + i) (by omega) j hj

structure RepStosDone [Bindings] (bytes : Nat) (code : List UInt8)
    (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 code.length)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (bytes * count)
  fill : ∀ i < bytes * count, t.external[rdi.read s + BitVec.ofNat 64 i]? = some 0
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (bytes * count), .rip]
    (clearRep s) t

theorem rep_stos_loop [Bindings] {bytes : Nat} {code : List UInt8}
    (hs : StosInstruction bytes code) (count : Nat) (s : RamState)
    (h : ReadyRepStosLoop bytes code s (count + 1)) :
    RepStosDone bytes code s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext := nextState_of_step (h.step hs (by omega))
    have hd := h.dstLow
    have ht := h.dstTables
    simp only [Nat.zero_add, Nat.mul_one] at hd ht
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by rw [h.counter]; rfl
    have hflag : (repStosAfter bytes code.length s).Repeat_String_Operation = false := by
      rw [repStosAfter_repeat, hc]; rfl
    refine ⟨(repStosAfter_ready bytes code.length h.ready hd ht).ready hflag,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [repStosAfter_rip bytes code.length s h.ready.msr, hc]; rfl
    · rw [repStosAfter_rcx, hc]
    · simpa only [Nat.zero_add, Nat.mul_one] using repStosAfter_rdi bytes code.length s
    · intro i hi
      exact repStosAfter_fill bytes code.length s hs.sizeBound h.zero i (by simpa using hi)
    · rw [← clearRep_eq hflag]
      simpa only [Nat.zero_add, Nat.mul_one] using repStosAfter_agrees bytes code.length s
  | succ k ih =>
    have hnext := nextState_of_step (h.step hs (by omega))
    have hd := h.dstLow
    have hmul : bytes * (k + 1 + 1) = bytes + bytes * (k + 1) := by simp only [Nat.mul_succ]; omega
    rw [hmul] at hd
    have hdi := repStosAfter_rdi bytes code.length s
    have ih' := ih (repStosAfter bytes code.length s) (h.next hs.positive)
    rw [nextStates_succ, hnext]
    have hrip := h.rip_after hs.positive
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_⟩
    · rw [ih'.rdiAfter, hdi, add_ofNat_add_ofNat, hmul]
    · intro i hi
      by_cases hsmall : i < bytes
      · refine (ih'.agrees.byte ?_).trans
          (repStosAfter_fill bytes code.length s hs.sizeBound h.zero i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hdi, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hz := ih'.fill (i - bytes) (by omega)
        rw [hdi, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega)] at hz
        exact hz
    · refine ((repStosAfter_agrees bytes code.length s).trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (bytes * (k + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hdi, add_ofNat_add_ofNat] at he
          exact ⟨bytes + j, by omega, he⟩

end Sha2.Proofs.Common.Memory.Fill.Stos
