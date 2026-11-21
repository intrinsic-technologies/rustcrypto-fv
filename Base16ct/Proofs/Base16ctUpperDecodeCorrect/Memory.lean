import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Entry
namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect
open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def decodeLoopEffects (initial : RamState) (capacity : Nat) : List Component :=
  [.reg 0, .reg 3, .reg 5, .reg 6, .reg 8, .reg 10, .reg 11, .flags, .rip,
    .mem (initial.regValue .rcx) capacity]

def decodeCallEffects (initial : RamState) (capacity : Nat) : List Component :=
  [.reg 0, .reg 4, .reg 6, .reg 9, .mem (initial.regValue .rsp - 8#64) 8,
    .mem (initial.regValue .rsp - 16#64) 8] ++
    decodeLoopEffects initial capacity

theorem readOutput_store_next {initial s t : RamState} {count : Nat}
    {bytes : List UInt8} {byte : UInt8}
    (hcount : count < 2^64)
    (hread : readOutput initial s count = .ok bytes)
    (hmem : t.external = memStore s.external
      (initial.regValue .rcx + BitVec.ofNat 64 count) byte.toBitVec) :
    readOutput initial t (count + 1) = .ok (bytes ++ [byte]) := by
  have mapM_eq {α β : Type} {f g : α → Except Fault β} {xs : List α}
      (hh : ∀ a ∈ xs, f a = g a) : xs.mapM f = xs.mapM g := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
      rw [List.mapM_cons, List.mapM_cons, hh a (by simp),
        ih (fun b hb => hh b (by simp only [List.mem_cons]; exact Or.inr hb))]
  have hprefix : readOutput initial t count = readOutput initial s count := by
    unfold readOutput
    apply mapM_eq
    intro j hj
    have hj' := List.mem_range.mp hj
    have hpres : t.external[BitVec.ofNat 64 ((outputRegion initial count).start + j)]? =
        s.external[BitVec.ofNat 64 ((outputRegion initial count).start + j)]? := by
      rw [hmem]
      apply memStore_getElem?_of_ne
      intro i hi heq
      have hz : i = 0 := by omega
      subst i
      simp only [BitVec.add_zero, outputRegion, registerRegion,
        BitVec.ofNat_add, BitVec.ofNat_toNat] at heq
      have hn := add_ofNat_inj (initial.regValue .rcx) (by omega : j < 2^64) hcount heq
      omega
    dsimp only
    rw [hpres]
  have hnew : t.external[BitVec.ofNat 64 ((outputRegion initial count).start + count)]? = some byte := by
    rw [hmem]
    have hh := memStore_getElem?_self s.external
      (initial.regValue .rcx + BitVec.ofNat 64 count) byte.toBitVec (by decide) 0 (by decide)
    simpa [outputRegion, registerRegion, BitVec.ofNat_add, storedByte] using hh
  have hpre : readOutput initial t count = .ok bytes := hprefix.trans hread
  unfold readOutput at hpre ⊢
  simp only [List.range_succ, List.mapM_append]
  simp only [outputRegion, registerRegion] at hpre hnew ⊢
  rw [hpre]
  simp [hnew]
  rfl

theorem region_contains_offset {region : MemoryRegion} (hb : region.Bounded)
    {offset : Nat} (hi : offset < region.size) :
    region.Contains (BitVec.ofNat 64 (region.start + offset)).toNat := by
  have hn : region.start + offset < 2^64 := by
    change region.start + region.size < 2^32 at hb
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  exact ⟨by omega, by omega⟩

theorem loadBytes_eq_of_bytes_eq {m m' : Ram} {address : BitVec 64} {count : Nat}
    (h : ∀ i < count, m'[address + BitVec.ofNat 64 i]? = m[address + BitVec.ofNat 64 i]?) :
    Machine.loadBytes m' address count = Machine.loadBytes m address count := by
  have hloop : ∀ remaining current shift accumulator, current + remaining ≤ count →
      Machine.loadBytes.loop m' address remaining current shift accumulator =
        Machine.loadBytes.loop m address remaining current shift accumulator := by
    intro remaining
    induction remaining with
    | zero => intros; rfl
    | succ remaining ih =>
      intro current shift accumulator hb
      simp only [Machine.loadBytes.loop, Machine.addAddress, Machine.fromNat]
      rw [h current (by omega)]
      cases m[address + BitVec.ofNat 64 current]? with
      | none => rfl
      | some byte => exact ih (current + 1) (shift + 8) _ (by omega)
  exact hloop count 0 0 0 (by omega)

theorem decode_return_stack {routine : Routine} {lengthWritten : Prop} {length : Nat} {initial s : RamState} {input : List UInt8} {capacity : Nat}
    (hv : ValidCall routine initial input capacity lengthWritten)
    (hf : AgreesExcept (decodeCallEffects initial length) initial s)
    (hbudget : 16 ≤ routine.minStackBytes) (hlength : length ≤ capacity) :
    MemReadable s (stackPtr initial) 8 ∧
      memLoad s.external (stackPtr initial) 64 = stackTop initial := by
  have hr := returnSlotReadable hv
  have hrs : MemReadable s (stackPtr initial) 8 :=
    ⟨hr.low, fun i hi => hf.grow _ (hr.mem i hi)⟩
  have hn := hv.stack.2.2.1
  change routine.minStackBytes ≤ (initial.regValue .rsp).toNat at hn
  have hb := hv.stack.1
  change (initial.regValue .rsp).toNat - routine.minStackBytes +
    ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - routine.minStackBytes)) < 2^32 at hb
  have haddr (i : Nat) (hi : i < 8) :
      (stackPtr initial + BitVec.ofNat 64 i).toNat = (initial.regValue .rsp).toNat + i := by
    change (initial.regValue .rsp + BitVec.ofNat 64 i).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      Nat.mod_eq_of_lt (by omega)]
  have hstack (i : Nat) (hi : i < 8) :
      (Stack.region initial routine.minStackBytes).Contains (stackPtr initial + BitVec.ofNat 64 i).toNat := by
    rw [haddr i hi]
    change (initial.regValue .rsp).toNat - routine.minStackBytes ≤ (initial.regValue .rsp).toNat + i ∧
      (initial.regValue .rsp).toNat + i < (initial.regValue .rsp).toNat - routine.minStackBytes +
        ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - routine.minStackBytes))
    omega
  have hbytes : ∀ i < 8, s.external[stackPtr initial + BitVec.ofNat 64 i]? =
      initial.external[stackPtr initial + BitVec.ofNat 64 i]? := by
    intro i hi
    apply hf.byte
    intro c hc hcov
    have hc' : c = .mem (initial.regValue .rsp - 8#64) 8 ∨
        c = .mem (initial.regValue .rsp - 16#64) 8 ∨
        c = .mem (initial.regValue .rcx) length := by
      cases c <;> simp_all [decodeCallEffects, decodeLoopEffects, Component.Covers]
    rcases hc' with rfl | rfl | rfl
    · obtain ⟨j, hj, he⟩ := hcov
      have hsub : (initial.regValue .rsp - 8#64).toNat = (initial.regValue .rsp).toNat - 8 := by
        rw [BitVec.toNat_sub_of_le (by change 8 ≤ (initial.regValue .rsp).toNat; omega)]
        rfl
      have heq := congrArg BitVec.toNat he
      rw [haddr i hi, BitVec.toNat_add, hsub, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : j < 2^64), Nat.mod_eq_of_lt (by omega)] at heq
      omega
    · obtain ⟨j, hj, he⟩ := hcov
      have hsub : (initial.regValue .rsp - 16#64).toNat = (initial.regValue .rsp).toNat - 16 := by
        rw [BitVec.toNat_sub_of_le (by change 16 ≤ (initial.regValue .rsp).toNat; omega)]
        rfl
      have heq := congrArg BitVec.toNat he
      rw [haddr i hi, BitVec.toNat_add, hsub, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : j < 2^64), Nat.mod_eq_of_lt (by omega)] at heq
      omega
    · obtain ⟨j, hj, he⟩ := hcov
      have hout : (outputRegion initial capacity).Contains
          (stackPtr initial + BitVec.ofNat 64 i).toNat := by
        rw [he]
        simpa [outputRegion, registerRegion, BitVec.ofNat_add] using
          (region_contains_offset hv.outputInMemory.2.1 (show j < capacity by omega))
      exact hv.separation.1 (1 : Fin 3) (2 : Fin 3) (by decide) _ hout (hstack i hi)
  have hsload := (Bytes.of_memLoad (n := 64) hrs.mem).loadBytes64
  have hiload := (Bytes.of_memLoad (n := 64) hr.mem).loadBytes64
  have hload := loadBytes_eq_of_bytes_eq hbytes
  rw [hsload, hiload] at hload
  exact ⟨hrs, Except.ok.inj hload⟩

theorem decode_saved_stack_readable {routine : Routine} {lengthWritten : Prop}
    {initial s : RamState} {input : List UInt8} {capacity length offset : Nat}
    (hv : ValidCall routine initial input capacity lengthWritten)
    (hf : AgreesExcept (decodeCallEffects initial length) initial s)
    (hoffset : 8 ≤ offset) (hbudget : offset ≤ routine.minStackBytes) :
    MemReadable s (initial.regValue .rsp - BitVec.ofNat 64 offset) 8 := by
  have hn := hv.stack.2.2.1
  change routine.minStackBytes ≤ (initial.regValue .rsp).toNat at hn
  have hb := hv.stack.1
  change (initial.regValue .rsp).toNat - routine.minStackBytes +
    ((initial.regValue .rsp).toNat + 8 -
      ((initial.regValue .rsp).toNat - routine.minStackBytes)) < 2^32 at hb
  have hoff : offset < 2^64 := by omega
  have haddr : (initial.regValue .rsp - BitVec.ofNat 64 offset).toNat =
      (initial.regValue .rsp).toNat - offset := by
    rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
    · simp only [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff]
      omega
  have hi : MemReadable initial (initial.regValue .rsp - BitVec.ofNat 64 offset) 8 := by
    apply regionReadable hv.stack.1 hv.stack.2.1
    · rw [haddr]
      change (initial.regValue .rsp).toNat - routine.minStackBytes ≤ _
      omega
    · rw [haddr]
      change (initial.regValue .rsp).toNat - offset + 8 ≤
        (initial.regValue .rsp).toNat - routine.minStackBytes +
          ((initial.regValue .rsp).toNat + 8 -
            ((initial.regValue .rsp).toNat - routine.minStackBytes))
      omega
  exact ⟨hi.low, fun i h => hf.grow _ (hi.mem i h)⟩

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
