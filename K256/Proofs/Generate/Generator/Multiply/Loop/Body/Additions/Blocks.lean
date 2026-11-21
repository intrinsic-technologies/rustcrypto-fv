import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Additions.Call

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem windowLookupBlock (first : Bool) {fr : Activation} {initial a : Registers} {m : Ram} {d k : Nat}
    (entry : CoreEntry fr initial d) (bound : k < 32) (s : RoundState fr d k (lookupSite first) a m)
    (table : a[12].get 64 = roundSp fr + tableOffset first) (zero : a[14].get 64 = 0)
    (ptr : first = false → a[13].get 64 = digitPointer fr k)
    (dst : first = false → a[5].get 64 = roundSp fr + 0x1d0) :
    ∃ b, WindowCall fr (lookupSite first) .l11c510 (lookupResume first) (lookupTag first) a b m ∧
      b[7].get 64 = roundSp fr + 0x1d0 ∧ b[6].get 64 = roundSp fr + tableOffset first ∧
      (b[2].get 64).setWidth 8 = BitVec.ofInt 8 (windowIndex first d k) ∧
      b[5].get 64 = roundSp fr + 0x1d0 ∧ b[12].get 64 = roundSp fr + 0x490 ∧
      b[13].get 64 = digitPointer fr k ∧ b[14].get 64 = 0 ∧ b[15] = a[15] := by
  have atoms := s.atoms
  have layout : Fn11c880.frameAt (lookupSite first) fr = Fn11c880.frameAt .l11d7d0 fr := by
    cases first <;> rfl
  rw [layout] at atoms
  simp only [Fn11c880.frameAt, Fn11c880.frameAtG2, Atom.All, Atom.Holds] at atoms
  have rsp : a[4].get 64 = roundSp fr := congrArg (Value.get 64) atoms.1
  have stack := atoms.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have slot : Writable Extracted.programImage m (roundSp fr - 8) 8 := by
    dsimp only [roundSp]
    slot_state region
  have digits := entry.digitWrite.readable.of_frame s.memory.frame
  have digitOk (i : Nat) (hi : i < 66) : LoadOk m (fr.r9 + BitVec.ofNat 64 i) 1 := by
    refine LoadOk.of_offsets (c := BitVec.ofNat 64 i) (d := 0) digits rfl (addr_self _) ?_
    have subZero : BitVec.ofNat 64 i - 0 = BitVec.ofNat 64 i := BitVec.sub_zero _
    rw [subZero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega)]
    omega
  have leftAddr : digitPointer fr k - 33 = fr.r9 + BitVec.ofNat 64 k := by
    simp only [digitPointer, BitVec.ofNat_add]
    bv_omega
  have rightAddr : digitPointer fr k = (fr.r9 + 33) + BitVec.ofNat 64 k := by
    simp only [digitPointer, BitVec.ofNat_add]
    bv_omega
  cases first
  · have ptr := ptr rfl
    have dst := dst rfl
    have digit := (congrArg (fun addr => memLoad m addr 8) rightAddr).trans
      (windowDigit (base := fr.r9 + 33) (x := (secondComponent d).natAbs) (i := k)
        s.memory.secondDigits bound)
    have read : LoadOk m (digitPointer fr k) 1 := by
      rw [rightAddr, BitVec.add_assoc, show (33 : BitVec 64) = BitVec.ofNat 64 33 from rfl, ← BitVec.ofNat_add]
      exact digitOk (33+k) (by omega)
    have push : StoreOk Extracted.programImage m (roundSp fr - 8) 8 0x11f696 5 := by
      slot_guard using code_l11f68a
    refine ⟨?lookupSecond, ⟨?run, ?widths, ?saved, ?rsp, ?control⟩,
      ?di, ?si, ?byte, ?bp, ?r12, ?r13, ?r14, ?r15⟩
    case run =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l11f68a,a,m⟩ =
        .call ⟨.l11c510,?lookupSecond,memStore m (roundSp fr - 8) (0x11f69b : BitVec 64)⟩ (callFrame .l11f69b 0x11f69b)
      arithmetic_segment using code_l11f68a [rsp, table, ptr, zero, dst, read, push]
    case widths =>
      rintro ⟨i, hi⟩ hm
      have w := s.widths ⟨i, hi⟩ hm
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
    case saved =>
      rintro ⟨i, hi⟩ hm
      have w := s.saved ⟨i, hi⟩ hm
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> exact w
    case rsp => rfl
    case control =>
      rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> rfl
    case di => rfl
    case si => rfl
    case byte =>
      change ((memLoad m (digitPointer fr k) 8).setWidth 64).setWidth 8 = _
      refine (BitVec.setWidth_setWidth_of_le _ (by decide)).trans ?_
      simpa only [BitVec.setWidth_eq, windowIndex, windowComponent, Bool.false_eq_true, ↓reduceIte] using digit
    case bp => exact dst
    case r12 => exact table
    case r13 => exact ptr
    case r14 => exact zero
    case r15 => rfl
  · have ptrValue : memLoad m (roundSp fr + 0xf0) 64 = digitPointer fr k := by
      change memLoad m (fr.rsp - 0xcb8 + 0xf0) 64 = _
      rw [show fr.rsp - 0xcb8 + 0xf0 = fr.rsp - 0xbc8 by bv_omega]
      exact s.pointer
    have readPtr : LoadOk m (roundSp fr + 0xf0) 8 := by
      dsimp only [roundSp]
      slot_guard using code_l11f64e
    have digit := windowDigit (base := fr.r9) (x := (firstComponent d).natAbs) (i := k)
      s.memory.firstDigits bound
    have read := digitOk k (by omega)
    have push : StoreOk Extracted.programImage m (roundSp fr - 8) 8 0x11f672 5 := by
      slot_guard using code_l11f64e
    refine ⟨?lookupFirst, ⟨?run, ?widths, ?saved, ?rsp, ?control⟩,
      ?di, ?si, ?byte, ?bp, ?r12, ?r13, ?r14, ?r15⟩
    case run =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l11f64e,a,m⟩ =
        .call ⟨.l11c510,?lookupFirst,memStore m (roundSp fr - 8) (0x11f677 : BitVec 64)⟩ (callFrame .l11f677 0x11f677)
      arithmetic_segment using code_l11f64e [rsp, table, zero, readPtr, ptrValue, leftAddr, read, push]
    case widths =>
      rintro ⟨i, hi⟩ hm
      have w := s.widths ⟨i, hi⟩ hm
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
    case saved =>
      rintro ⟨i, hi⟩ hm
      have w := s.saved ⟨i, hi⟩ hm
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
    case rsp => rfl
    case control =>
      rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> rfl
    case di => rfl
    case si => rfl
    case byte =>
      change ((memLoad m (fr.r9 + BitVec.ofNat 64 k) 8).setWidth 64).setWidth 8 = _
      refine (BitVec.setWidth_setWidth_of_le _ (by decide)).trans ?_
      simpa only [BitVec.setWidth_eq, windowIndex, windowComponent, ↓reduceIte] using digit
    case bp => rfl
    case r12 => rfl
    case r13 => rfl
    case r14 => exact zero
    case r15 => rfl

theorem windowAdditionBlock (first : Bool) {fr : Activation} {a : Registers} {m : Ram} {d k : Nat}
    (s : RoundState fr d k (lookupResume first) a m)
    (dst : a[5].get 64 = roundSp fr + 0x1d0) (acc : first = false → a[15].get 64 = roundSp fr + 0x128) :
    ∃ b, WindowCall fr (lookupResume first) .l10a410 (additionResume first) (additionTag first) a b m ∧
      b[7].get 64 = roundSp fr + 0x128 ∧ b[6].get 64 = roundSp fr + 0x1d0 ∧
      b[15].get 64 = roundSp fr + 0x128 ∧
      ∀ j : Fin Reg.count, j.val ∈ [5,12,13,14] → b[j] = a[j] := by
  have atoms := s.atoms
  have layout : Fn11c880.frameAt (lookupResume first) fr = Fn11c880.frameAt .l11d7d0 fr := by
    cases first <;> rfl
  rw [layout] at atoms
  simp only [Fn11c880.frameAt, Fn11c880.frameAtG2, Atom.All, Atom.Holds] at atoms
  have rsp : a[4].get 64 = roundSp fr := congrArg (Value.get 64) atoms.1
  have stack := atoms.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have slot : Writable Extracted.programImage m (roundSp fr - 8) 8 := by
    dsimp only [roundSp]
    slot_state region
  cases first
  · have acc := acc rfl
    have push : StoreOk Extracted.programImage m (roundSp fr - 8) 8 0x11f6a1 5 := by
      slot_guard using code_l11f69b
    refine ⟨?b, ⟨?run, ?widths, ?saved, ?rsp, ?control⟩, ?di, ?si, ?r15, ?regs⟩
    case run =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l11f69b,a,m⟩ =
        .call ⟨.l10a410,?b,memStore m (roundSp fr - 8) (0x11f6a6 : BitVec 64)⟩ (callFrame .l11f6a6 0x11f6a6)
      arithmetic_segment using code_l11f69b [rsp, dst, acc, push]
    case widths =>
      rintro ⟨i, hi⟩ hm
      have w := s.widths ⟨i, hi⟩ hm
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
    case saved =>
      rintro ⟨i, hi⟩ hm
      have w := s.saved ⟨i, hi⟩ hm
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> exact w
    case rsp => rfl
    case control =>
      rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> rfl
    case di => rfl
    case si => rfl
    case r15 => exact acc
    case regs =>
      rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> rfl
  · have push : StoreOk Extracted.programImage m (roundSp fr - 8) 8 0x11f685 5 := by
      slot_guard using code_l11f677
    refine ⟨?bTrue, ⟨?run, ?widths, ?saved, ?rsp, ?control⟩, ?di, ?si, ?r15, ?regs⟩
    case run =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l11f677,a,m⟩ =
        .call ⟨.l10a410,?bTrue,memStore m (roundSp fr - 8) (0x11f68a : BitVec 64)⟩ (callFrame .l11f68a 0x11f68a)
      arithmetic_segment using code_l11f677 [rsp, dst, push]
    case widths =>
      rintro ⟨i, hi⟩ hm
      have w := s.widths ⟨i, hi⟩ hm
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
    case saved =>
      rintro ⟨i, hi⟩ hm
      have w := s.saved ⟨i, hi⟩ hm
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
    case rsp => rfl
    case control =>
      rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> rfl
    case di => rfl
    case si => rfl
    case r15 => rfl
    case regs =>
      rintro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Generate.Generator.Multiply
