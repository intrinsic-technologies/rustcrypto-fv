import K256.Proofs.Verify.Core.Lincomb.Loop.State
import K256.Proofs.Verify.Core.Lincomb.Loop.Initialize.Identity
import K256.Proofs.Verify.Core.Lincomb.Recode.Stack
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Generate.Generator.Multiply.Lookup.Memory
import K256.Proofs.Sec1.Wrapper.Copy.Execution

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC
open Generate.Generator.Multiply (identity identity_valid identity_value)
open Generate.Generator.Multiply.Lookup (copyGuard copyStored)

private theorem seedJump {l r : Label} {a b : Registers} {m n : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ = .jump ⟨r,b,n⟩) :
    Reaches l a m r b n := by
  apply Semantics.Reaches.single
  change (program.runBlock _ _).next _ [] = _
  rw [step]
  rfl

set_option maxRecDepth 4096 in
private theorem copyIdentity {a : Registers} {m : Ram} {base : BitVec 64}
    (rsp : a[4].get 64 = base) (df : a[22].get 1 = 0) (positive : a[0].get 64 ≠ 0)
    (copy : RepMovsOk Extracted.programImage m 0 0x202d48 (base + 0x130) 15 8 0x1101f2 3)
    (read : LoadOk (memCopy m (base + 0x130) 0x202d48 120) base 8)
    (back : memLoad (memCopy m (base + 0x130) 0x202d48 120) base 64 = 0) :
    ∃ b, Reaches .l1101de a m .l110202 b (memCopy m (base + 0x130) 0x202d48 120) ∧
      b[8] = ⟨64, 0⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [0,4,5,13,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?_, seedJump ?run, ?_, ?keep⟩
  case run =>
    cfg_eval [rsp, df, BitVec.and_self, testFlags, beq_eq_false_iff_ne.mpr positive]
    simp only [false_or, copy, read, back, ite_true]
    rfl
  · rfl
  case keep =>
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

private def seedSlots (base : BitVec 64) : List MemoryRegion :=
  [⟨base.toNat + 8, 0x50⟩, ⟨base.toNat + 0xd8, 8⟩]

private theorem seedAddress {base : BitVec 64} (low : base.toNat + 0x1d8 ≤ 2^32)
    (off : BitVec 64) (fits : off.toNat ≤ 0x1d8) :
    (base + off).toNat = base.toNat + off.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]

private theorem seedStoreFrame {m n : Ram} {base off : BitVec 64}
    (low : base.toNat + 0x1d8 ≤ 2^32)
    (frame : RamWriteFrame m n (seedSlots base)) (value : BitVec 64)
    (slot : off = 0xd8 ∨ (8 ≤ off.toNat ∧ off.toNat + 8 ≤ 0x58)) :
    RamWriteFrame m (memStore n (base + off) value) (seedSlots base) := by
  apply frame.memStore
  rcases slot with rfl | ⟨start, stop⟩
  · have addr : (base + 0xd8).toNat = base.toNat + 0xd8 := seedAddress low _ (by decide)
    have fits : (base + 0xd8).toNat + 8 ≤ 2^64 := by rw [addr]; omega
    exact ⟨_, .tail _ (.head _), Nat.le_of_eq addr.symm,
      Nat.le_of_eq (congrArg (· + 8) addr), fits⟩
  · refine ⟨_, .head _, ?_, ?_, ?_⟩
    all_goals
      rw [seedAddress low off (by omega)]
      simp only [Nat.reduceDiv]
      omega

private theorem keepSeedWord (m : Ram) (base rd wr : BitVec 64) (value : BitVec 64)
    (sep : (8 : Nat) ≤ (rd - wr).toNat ∧ (8 : Nat) ≤ (wr - rd).toNat) :
    memLoad (memStore m (base + wr) value) (base + rd) 64 = memLoad m (base + rd) 64 := by
  apply memLoad_memStore_of_rangeApart
  exact RangeApart.of_offsets (x := base) (c := wr) (d := rd) rfl rfl sep

set_option maxRecDepth 4096 in
private theorem storeSeed {a : Registers} {m : Ram} {base iterator dataPtr : BitVec 64}
    (rsp : a[4].get 64 = base) (iter : a[15].get 64 = iterator)
    (front : a[13].get 64 = 0) (nextTable : a[14].get 64 = dataPtr)
    (writable : Writable Extracted.programImage m base 0x1d8)
    (readable : Readable m iterator 112) :
    ∃ b n, Reaches .l110202 a m .l110278 b n ∧
      b[9].get 64 = a[0].get 64 ∧
      (∀ i : Fin Reg.count, i.val ∈ [4,5,8,13,14,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m n (seedSlots base) ∧
      memLoad n (base + 0x40) 64 = 0 ∧ memLoad n (base + 0x38) 64 = dataPtr := by
  let n1 := memStore m (base + 0xd8) (memLoad m (iterator + 0x20) 64)
  let n2 := memStore n1 (base + 0x50) (memLoad n1 (iterator + 0x38) 64)
  let n3 := memStore n2 (base + 0x48) (memLoad n2 (iterator + 0x60) 64)
  let n4 := memStore n3 (base + 0x28) (0 : BitVec 64)
  let n5 := memStore n4 (base + 0x8) (memLoad n2 (iterator + 0x50) 64)
  let n6 := memStore n5 (base + 0x40) (0 : BitVec 64)
  let n7 := memStore n6 (base + 0x38) dataPtr
  let n8 := memStore n7 (base + 0x30) (memLoad n1 (iterator + 0x30) 64)
  let n9 := memStore n8 (base + 0x20) (memLoad n3 (iterator + 0x68) 64)
  have load (mem : Ram) (r : Readable mem iterator 112) (off : BitVec 64)
      (fits : (off - 0).toNat + 8 ≤ 112) : LoadOk mem (iterator + off) 8 :=
    LoadOk.of_offsets (x := iterator) r rfl (BitVec.add_zero _).symm fits
  refine ⟨?_, n9, seedJump ?run, ?_, ?keep, ?frame, ?front, ?next⟩
  case run =>
    cfg_eval [rsp, iter, front, nextTable]
    repeat' (
      refine Eq.trans (ite_eq_left ?_) ?_
      first
      | (refine load _ ?_ _ (by decide); repeat' (first | exact readable | apply Readable.memStore))
      | slot_guard using code_l110202)
    rfl
  · rfl
  case keep =>
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  case frame =>
    dsimp only [n9, n8, n7, n6, n5, n4, n3, n2, n1]
    repeat' (refine seedStoreFrame writable.readable.low ?_ _ (by decide))
    exact RamWriteFrame.refl _ _
  case front =>
    dsimp only [n9, n8, n7, n6]
    rw [keepSeedWord _ _ 0x40 0x20 _ (by decide),
      keepSeedWord _ _ 0x40 0x30 _ (by decide),
      keepSeedWord _ _ 0x40 0x38 _ (by decide),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]
  case next =>
    dsimp only [n9, n8, n7]
    rw [keepSeedWord _ _ 0x38 0x20 _ (by decide),
      keepSeedWord _ _ 0x38 0x30 _ (by decide),
      memLoad_memStore_same _ _ _ (by decide) (by decide)]

theorem seedRounds {a b : Registers} {m n : Ram} {sp dst iterator dataPtr : BitVec 64}
    {bases : Fin 4 → Curve.Point} {ds : Fin 4 → List Int} {k : Nat}
    (entry : RoutineEntry a m sp 0x478) (saved : SavedFrame a m sp dst b n)
    (count : (b[0].get 64).toNat = k+1) (front : b[13].get 64 = 0)
    (nextTable : b[14].get 64 = dataPtr) (last : b[5] = ⟨64, dataPtr + 0x1340⟩)
    (iter : b[15].get 64 = iterator) (back : memLoad n (baseSp sp) 64 = 0)
    (read : Readable m iterator 112) (empty : suffix bases ds (k+1) = .infinity) :
    ∃ c t, Reaches .l1101de b n .l110278 c t ∧
      RoundState a m sp dst dataPtr bases ds (k+1) c t := by
  let base := baseSp sp
  let dest := base + 0x130
  let copied := memCopy n dest 0x202d48 120
  let area : MemoryRegion := ⟨base.toNat + 0x130, 120⟩
  have spRoom := entry.room
  have stack : Writable Extracted.programImage n base 0x1d8 :=
    (Recode.stackSlot entry (by decide) (by decide)).of_frame saved.frame
  have low := stack.readable.low
  have addr (off : BitVec 64) (fit : off.toNat ≤ 0x1d8) :
      (base + off).toNat = base.toNat + off.toNat := seedAddress low off fit
  have bottom : base.toNat = sp.toNat - 0x1d8 := by
    apply Recode.subNat
    change 0x1d8 ≤ sp.toNat
    omega
  have destNat : dest.toNat = base.toNat + 0x130 := addr _ (by decide)
  have write : Writable Extracted.programImage n dest 120 := by
    apply stack.sub <;> rw [destNat] <;> omega
  have scratchRegion (off len : Nat) (fits : off + len ≤ 0x1d8) :
      ∃ s ∈ [scratch sp 0x478], s.start ≤ base.toNat + off ∧
        base.toNat + off + len ≤ s.start + s.size := by
    refine ⟨_, .head _, ?_⟩
    change sp.toNat - 0x478 ≤ base.toNat + off ∧
      base.toNat + off + len ≤ sp.toNat - 0x478 + 0x478
    rw [bottom]
    omega
  have copyFrame : RamWriteFrame n copied [area] := by
    apply Sec1.Wrapper.Copy.memCopy_frame (RamWriteFrame.refl _ _)
    exact ⟨area, .head _, Nat.le_of_eq destNat.symm,
      Nat.le_of_eq (congrArg (· + 120) destNat), by rw [destNat]; omega⟩
  have copiedFrame : RamWriteFrame m copied [scratch sp 0x478] := by
    apply saved.frame.trans copyFrame
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact scratchRegion 0x130 120 (by decide)
  have loaded := Recode.imageFromFrame entry saved.frame
  obtain ⟨source, apart⟩ := identitySource loaded write
  have guard : RepMovsOk Extracted.programImage n 0 0x202d48 dest 15 8 0x1101f2 3 :=
    copyGuard source (Recode.storeGuard (off := 0x14) write code_l1101de (by decide)) apart
  have afterCopy := stack.of_frame copyFrame
  have headRead : LoadOk copied base 8 :=
    LoadOk.of_region afterCopy.readable (Nat.le_refl _) (by omega)
  have nonoverlap (off : BitVec 64) (len start size : Nat)
      (fits : off.toNat + len ≤ 0x1d8)
      (sep : off.toNat + len ≤ start ∨ start + size ≤ off.toNat) :
      (base + off).toNat + len ≤ base.toNat + start ∨
        base.toNat + start + size ≤ (base + off).toNat := by
    rw [addr off (by omega)]
    omega
  have copyOutside (off : BitVec 64) (len : Nat) (fits : off.toNat + len ≤ 0x1d8)
      (sep : off.toNat + len ≤ 0x130 ∨ 0x1a8 ≤ off.toNat) :
      Outside [area] (base + off) len := by
    refine ⟨by rw [addr off (by omega)]; omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    exact nonoverlap off len 0x130 120 fits sep
  have headWord : memLoad copied base 64 = 0 := by
    have h := copyFrame.memLoad_eq (k := 64) (copyOutside 0 8 (by decide) (by decide))
    rw [show base + (0 : BitVec 64) = base from BitVec.add_zero base] at h
    exact h.trans back
  have rsp : b[4].get 64 = base := congrArg (Value.get 64) saved.rsp
  have df : b[22].get 1 = 0 := congrArg (Value.get 1) ((saved.control 22 (by decide)).trans entry.df)
  have positive : b[0].get 64 ≠ 0 := by
    intro zero
    rw [zero] at count
    change 0 = k+1 at count
    omega
  obtain ⟨mid, first, backReg, keep⟩ := copyIdentity rsp df positive guard headRead headWord
  have get (i : Fin Reg.count) (hi : i.val ∈ [0,4,5,13,14,15,22,39,50,51]) :
      mid[i].get 64 = b[i].get 64 := congrArg (Value.get 64) (keep i hi)
  obtain ⟨c, t, second, newCount, kept, writes, savedFront, savedNext⟩ :=
    storeSeed (base := base) ((get 4 (by decide)).trans rsp) ((get 15 (by decide)).trans iter)
      ((get 13 (by decide)).trans front) ((get 14 (by decide)).trans nextTable)
      afterCopy (read.of_frame copiedFrame)
  have keepReg (i : Fin Reg.count) (h : i.val ∈ [4,5,13,14,22,39,50,51]) : c[i] = b[i] :=
    (kept i ((by decide : ∀ i : Fin Reg.count, i.val ∈ [4,5,13,14,22,39,50,51] →
      i.val ∈ [4,5,8,13,14,22,39,50,51]) i h)).trans
      (keep i ((by decide : ∀ i : Fin Reg.count, i.val ∈ [4,5,13,14,22,39,50,51] →
        i.val ∈ [0,4,5,13,14,15,22,39,50,51]) i h))
  have storeOutside (off : BitVec 64) (len : Nat) (fits : off.toNat + len ≤ 0x1d8)
      (slots : off.toNat + len ≤ 8 ∨ 0x58 ≤ off.toNat)
      (wide : off.toNat + len ≤ 0xd8 ∨ 0xe0 ≤ off.toNat) :
      Outside (seedSlots base) (base + off) len := by
    refine ⟨by rw [addr off (by omega)]; omega, fun r hr => ?_⟩
    simp only [seedSlots, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact nonoverlap off len 8 0x50 fits slots
    · exact nonoverlap off len 0xd8 8 fits wide
  have frame : RamWriteFrame m t [scratch sp 0x478] := by
    apply copiedFrame.trans writes
    intro r hr
    simp only [seedSlots, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact scratchRegion 8 0x50 (by decide)
    · exact scratchRegion 0xd8 8 (by decide)
  have same (off : BitVec 64) (fits : off.toNat + 8 ≤ 0x1d8)
      (cp : off.toNat + 8 ≤ 0x130 ∨ 0x1a8 ≤ off.toNat)
      (slots : off.toNat + 8 ≤ 8 ∨ 0x58 ≤ off.toNat)
      (wide : off.toNat + 8 ≤ 0xd8 ∨ 0xe0 ≤ off.toNat) :
      memLoad t (base + off) 64 = memLoad n (base + off) 64 :=
    (writes.memLoad_eq (k := 64) (storeOutside off 8 fits slots wide)).trans
      (copyFrame.memLoad_eq (k := 64) (copyOutside off 8 fits cp))
  have sameSaved (off : BitVec 64) (lower : 8 ≤ off.toNat) (upper : off.toNat ≤ 48) :
      memLoad t (sp - off) 64 = memLoad n (sp - off) 64 := by
    rw [show sp - off = base + (0x1d8 - off) by dsimp only [base, baseSp]; bv_omega]
    have offset : ((0x1d8 : BitVec 64) - off).toNat = 0x1d8 - off.toNat :=
      Recode.subNat (by change off.toNat ≤ 0x1d8; omega)
    apply same <;> rw [offset] <;> omega
  have point : identity.Stored t dest :=
    (copyStored (identityImage loaded)).of_frame writes
      (storeOutside 0x130 120 (by decide) (by decide) (by decide))
  have counter : b[0].get 64 = BitVec.ofNat 64 (k+1) := by
    apply BitVec.eq_of_toNat_eq
    rw [count, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    rw [← count]
    exact (b[0].get 64).isLt
  refine ⟨c, t, first.trans second, {
    toSavedFrame := ?_
    counter := newCount.trans ((get 0 (by decide)).trans counter)
    front := (congrArg (Value.get 64) (keepReg 13 (by decide))).trans front
    nextTable := (congrArg (Value.get 64) (keepReg 14 (by decide))).trans nextTable
    tableEnd := (keepReg 5 (by decide)).trans last
    back := (kept 8 (by decide)).trans backReg
    savedFront := savedFront
    savedNext := savedNext
    savedBack := ?_
    point := ⟨identity, point, identity_valid, identity_value.trans empty.symm⟩
    inactive := fun _ => empty }⟩
  · refine ⟨(keepReg 4 (by decide)).trans saved.rsp,
      (same 0xd0 (by decide) (by decide) (by decide) (by decide)).trans saved.dest,
      (sameSaved 48 (by decide) (by decide)).trans saved.rbx,
      (sameSaved 40 (by decide) (by decide)).trans saved.r12,
      (sameSaved 32 (by decide) (by decide)).trans saved.r13,
      (sameSaved 24 (by decide) (by decide)).trans saved.r14,
      (sameSaved 16 (by decide) (by decide)).trans saved.r15,
      (sameSaved 8 (by decide) (by decide)).trans saved.rbp, ?_, frame⟩
    intro i h
    exact (keepReg i ((by decide : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] →
      i.val ∈ [4,5,13,14,22,39,50,51]) i h)).trans (saved.control i h)
  · have h := same 0 (by decide) (by decide) (by decide) (by decide)
    rw [show base + (0 : BitVec 64) = base from BitVec.add_zero base] at h
    exact h.trans back

end K256.Proofs.Verify.Core.Lincomb.Loop
