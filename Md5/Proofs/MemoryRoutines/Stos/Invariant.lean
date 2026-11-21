import Md5.Proofs.MemoryRoutines.Stos.State

namespace Md5.Proofs.MemoryRoutines.Stos

open X86 X86.Machine X86.UserProcess X86Proofs Md5.Spec.Program

structure ReadyLoop [Bindings] (kind : Kind) (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP kind.code
  codeLow : s.RIP.toNat + kind.code.length ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  dstLow : (rdi.read s).toNat + kind.bytes * count ≤ 2^32
  dstAlign : (rdi.read s).toNat % kind.bytes = 0
  dstMem : ∀ i < kind.bytes * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : ∀ i < kind.bytes * count, ¬ InPageTables (rdi.read s + BitVec.ofNat 64 i)
  dstCode : RangeApart (rdi.read s) (kind.bytes * count) s.RIP kind.code.length

structure Done [Bindings] (kind : Kind) (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 kind.code.length)
  rcxZero : rcx.read t = 0
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (kind.bytes * count)
  fill : ∀ i < kind.bytes * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? =
      some (storedByte ((Operand.reg 0 : Operand (8 * kind.bytes)).read s) (i % kind.bytes))
  agrees : AgreesExcept [.reg 1, .reg 7, .mem (rdi.read s) (kind.bytes * count), .rip]
    (clearRep s) t

structure Pre (kind : Kind) (p : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = p
  df : DirectionFlagClear s.RFLAGS
  dstLow : (rdi.read s).toNat + kind.bytes * (rcx.read s).toNat ≤ 2^32
  dstAlign : rcx.read s ≠ 0 → (rdi.read s).toNat % kind.bytes = 0
  dstMem : ∀ i < kind.bytes * (rcx.read s).toNat,
    (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  dstTables : ∀ i < kind.bytes * (rcx.read s).toNat,
    ¬ InPageTables (rdi.read s + BitVec.ofNat 64 i)
  dstCode : RangeApart (rdi.read s) (kind.bytes * (rcx.read s).toNat) p kind.code.length

theorem ReadyLoop.count_lt [Bindings] {kind : Kind} {s : RamState} {count : Nat}
    (h : ReadyLoop kind s count) : count < 2^64 := by
  have hp := kind.bytes_pos
  have hm : count ≤ kind.bytes * count := Nat.le_mul_of_pos_left count hp
  have := h.dstLow
  omega

theorem ReadyLoop.rcx_ne [Bindings] {kind : Kind} {s : RamState} {count : Nat}
    (h : ReadyLoop kind s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos h.count_lt

theorem ReadyLoop.rcx_after [Bindings] {kind : Kind} {s : RamState} {count : Nat}
    (h : ReadyLoop kind s (count + 1)) :
    rcx.read (repStosAfter kind s) = BitVec.ofNat 64 count := by
  rw [repStosAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem ReadyLoop.next_rip [Bindings] {kind : Kind} {s : RamState} {count : Nat}
    (h : ReadyLoop kind s (count + 2)) : (repStosAfter kind s).RIP = s.RIP := by
  rw [repStosAfter_rip kind s h.ready.msr, h.counter]
  simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega)
    (by have := h.count_lt; omega), ↓reduceIte]

theorem ReadyLoop.next [Bindings] {kind : Kind} {s : RamState} {count : Nat}
    (h : ReadyLoop kind s (count + 2)) : ReadyLoop kind (repStosAfter kind s) (count + 1) := by
  have hb := kind.bytes_pos
  have hdl := h.dstLow
  have hal := h.dstAlign
  have hsize : kind.bytes * (count + 2) = kind.bytes + kind.bytes * (count + 1) := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two]; omega
  have hdn : (rdi.read (repStosAfter kind s)).toNat = (rdi.read s).toNat + kind.bytes := by
    rw [repStosAfter_rdi, toNat_add_ofNat _ _ (by omega)]
  refine ⟨repStosAfter_ready kind h.ready (fun i hi ↦ h.dstTables i (by omega)),
    h.df, ?_, ?_, h.rcx_after, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [h.next_rip, repStosAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i hi he
  · rw [h.next_rip]; exact h.codeLow
  · rw [hdn]; omega
  · rw [hdn, Nat.add_mod, hal, Nat.mod_self, Nat.zero_add, Nat.zero_mod]
  · intro i hi
    rw [repStosAfter_rdi, add_ofNat_add_ofNat, repStosAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (kind.bytes + i) (by omega))
  · intro i hi
    rw [repStosAfter_rdi, add_ofNat_add_ofNat]
    exact h.dstTables (kind.bytes + i) (by omega)
  · intro i hi j hj
    rw [repStosAfter_rdi, add_ofNat_add_ofNat, h.next_rip]
    exact h.dstCode (kind.bytes + i) (by omega) j hj

end Md5.Proofs.MemoryRoutines.Stos
