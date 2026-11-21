import K256.Proofs.Generate.Generator.Multiply.Radix.State

namespace K256.Proofs.Generate.Generator.Multiply.Radix

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Generate.LIR

private theorem digitCarry (x pos : Nat) (small : pos < 32) :
    pending x pos - ((pending x pos + 8) &&& 0xf0) = byte x pos ∧
      (pending x pos + 8).sshiftRight 4 + BitVec.ofNat 8 (nibble x (pos + 1)) =
        pending x (pos + 1) := by
  have finite : ∀ k : Fin 17,
      (BitVec.ofNat 8 k.val) - ((BitVec.ofNat 8 k.val + 8) &&& 0xf0) =
        BitVec.ofInt 8 ((k.val : Int) - 16 * (((k.val + 8) / 16 : Nat) : Int)) ∧
      (BitVec.ofNat 8 k.val + 8).sshiftRight 4 = BitVec.ofNat 8 ((k.val + 8) / 16) :=
    by decide +kernel
  have hn : nibble x pos < 16 := Nat.mod_lt _ (by decide)
  have hc := Generate.Curve.radixCarry_le_one x pos
  have hk : nibble x pos + Generate.Curve.radixCarry x pos < 17 := by omega
  obtain ⟨hd, hq⟩ := finite ⟨_, hk⟩
  simp only [pending, byte, show pos ≠ 32 by omega, ↓reduceIte,
    Generate.Curve.radixDigit_remaining, Generate.Curve.radixCarry]
  unfold nibble at hd hq ⊢
  refine ⟨hd, ?_⟩
  rw [hq, ← BitVec.ofNat_add, Nat.add_comm]
  rfl

set_option maxHeartbeats 800000 in
theorem carryPair {code : CodeMap} (included : ∀ a ∈ fnCode, a ∈ code)
    {fr : Activation} {initial m : Ram} {a : regs} {x pos : Nat} (_bound : x < 2^128)
    (small : pos + 2 ≤ 32) (s : LoopState code fr initial m a x pos) :
    ∃ b n, Path code .l11ac00 a m (loopLabel (pos + 2)) b n ∧
      LoopState code fr initial n b x (pos + 2) := by
  have atoms := s.atoms
  simp only [Fn11aa40.frameAt, Fn11aa40.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, ax, bx, bp, r9, r12, r13, r14, r15, mx, ftw, fcw,
    rd, ret, retLow, win, room, alignment⟩ := atoms
  let q := fr.rsp - 33
  have spBits : a[4].get 64 = q := congrArg (Value.get 64) sp
  have index := s.index
  have current := s.current
  change Writable code m q 33 at win
  have low := win.readable.low
  have enter : (a[1].get 64).setWidth 8 = pending x pos :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans current
  have lowAdd (w : BitVec 64) : (w + 8).setWidth 8 = w.setWidth 8 + 8 := by bv_omega
  have offset0 : q + BitVec.ofNat 64 (pos + 2) - 2 = q + BitVec.ofNat 64 pos := by
    rw [BitVec.ofNat_add]
    bv_omega
  have offset1 : q + BitVec.ofNat 64 (pos + 2) - 1 = q + BitVec.ofNat 64 (pos + 1) := by
    rw [BitVec.ofNat_add, BitVec.ofNat_add]
    bv_omega
  have addrNat (i : Nat) (hi : i < 33) :
      (q + BitVec.ofNat 64 i).toNat = q.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have nat0 := addrNat pos (by omega)
  have nat1 := addrNat (pos + 1) (by omega)
  have nat2 := addrNat (pos + 2) (by omega)
  have frame := s.frame
  change RamWriteFrame initial m [⟨q.toNat, 33⟩] at frame
  obtain ⟨digit0, carry0⟩ := digitCarry x pos (by omega)
  obtain ⟨digit1, carry1⟩ := digitCarry x (pos + 1) (by omega)
  let m1 := memStore m (q + BitVec.ofNat 64 pos) (byte x pos)
  let m2 := memStore m1 (q + BitVec.ofNat 64 (pos + 1)) (byte x (pos + 1))
  let m3 := memStore m2 (q + BitVec.ofNat 64 (pos + 2)) (pending x (pos + 2))
  have stk := s.stack
  change WordsAt m q 8 (Vector.ofFn fun i : Fin 33 => stackByte x pos i.val) at stk
  have low64 : q.toNat + 8 / 8 * 33 ≤ 2 ^ 64 := by
    change q.toNat + 33 ≤ _
    omega
  have stk1 := stk.write_set (j := pos) (by omega) (byte x pos)
    (by decide) (by decide) (by decide) low64
  have m1Eq : memStore m (q + BitVec.ofNat 64 pos) (byte x pos) = m1 := rfl
  simp only [wordAddr, Nat.reduceDiv, Nat.one_mul, m1Eq] at stk1
  have stk2 := stk1.write_set (j := pos + 1) (by omega) (byte x (pos + 1))
    (by decide) (by decide) (by decide) low64
  have m2Eq : memStore m1 (q + BitVec.ofNat 64 (pos + 1)) (byte x (pos + 1)) = m2 := rfl
  simp only [wordAddr, Nat.reduceDiv, Nat.one_mul, m2Eq] at stk2
  have stk3 := stk2.write_set (j := pos + 2) (by omega) (pending x (pos + 2))
    (by decide) (by decide) (by decide) low64
  have m3Eq : memStore m2 (q + BitVec.ofNat 64 (pos + 2)) (pending x (pos + 2)) = m3 := rfl
  simp only [wordAddr, Nat.reduceDiv, Nat.one_mul, m3Eq] at stk3
  have load1 : memLoad m1 (q + BitVec.ofNat 64 (pos + 1)) 8 =
      BitVec.ofNat 8 (nibble x (pos + 1)) := by
    simpa only [Vector.getElem_set, show pos ≠ pos + 1 by omega, ↓reduceIte,
      Vector.getElem_ofFn, wordAddr, Nat.reduceDiv, Nat.one_mul, stackByte,
      show ¬pos + 1 < pos by omega, show pos + 1 ≠ pos by omega]
      using stk1 (pos + 1) (by omega)
  have load2 : memLoad m2 (q + BitVec.ofNat 64 (pos + 2)) 8 =
      BitVec.ofNat 8 (nibble x (pos + 2)) := by
    simpa only [Vector.getElem_set, show pos + 1 ≠ pos + 2 by omega,
      show pos ≠ pos + 2 by omega, ↓reduceIte, Vector.getElem_ofFn,
      wordAddr, Nat.reduceDiv, Nat.one_mul, stackByte,
      show ¬pos + 2 < pos by omega, show pos + 2 ≠ pos by omega]
      using stk2 (pos + 2) (by omega)
  have inc := fun v hv => included v (code_l11ac00 v hv)
  have win1 : Writable code m1 q 33 := by
    dsimp only [m1]
    slot_state region
  have win2 : Writable code m2 q 33 := by
    dsimp only [m2]
    slot_state region
  have wrote : RamWriteFrame m m3 [⟨q.toNat, 33⟩] := by
    dsimp only [m3, m2, m1]
    slot_state region
  have nextIndex : BitVec.ofNat 64 (pos + 2) + 2 = BitVec.ofNat 64 (pos + 2 + 2) := by
    exact (BitVec.ofNat_add (n := 64) (pos + 2) 2).symm
  have compare : BitVec.ofNat 64 (pos + 2 + 2) = 34 ↔ pos + 2 = 32 := by
    rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change pos + 2 + 2 = 34 ↔ pos + 2 = 32
    omega
  have branch (v : regs) :
      (if (!(cmpSpec (BitVec.ofNat 64 (pos + 2 + 2)) 34).ZF) = true then
        Transfer.jump (signature := signature) (results := Reg.count) ⟨.l11ac00, v, m3⟩
      else .jump ⟨.l11ac3d, v, m3⟩) = .jump ⟨loopLabel (pos + 2), v, m3⟩ := by
    simp only [cmpSpec_ZF, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, compare, ite_not, loopLabel]
    split <;> rename_i h <;> first | rw [ite_eq_left h] | rw [ite_eq_right h]
  refine ⟨?nextRegs, m3, ?path, ?state⟩
  case path =>
    have run : program.runBlock (dialect code) ⟨.l11ac00, a, m⟩ =
        .jump ⟨loopLabel (pos + 2), ?nextRegs, m3⟩ := by
      generate_block [spBits, index, offset0, offset1]
      simp only [setWidth_mergeGPR8, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
        lowAdd, enter, digit0, m1Eq, load1, carry0, digit1, m2Eq, load2, carry1, m3Eq]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using inc)
      simp only [nextIndex]
      exact branch _
    apply Semantics.Reaches.single
    change program.step _ _ = _
    simp only [Program.step, run, Transfer.next]
  case state =>
    refine ⟨?atoms, ?widths, ?index, ?current, ?stack, ?frame⟩
    case atoms =>
      have spNat : q.toNat + 33 = fr.rsp.toNat := by
        dsimp only [q]
        rw [BitVec.toNat_sub_of_le (by change 33 ≤ fr.rsp.toNat; omega)]
        change fr.rsp.toNat - 33 + 33 = fr.rsp.toNat
        omega
      have retOutside : Outside [⟨q.toNat, 33⟩] fr.rsp 8 := by
        refine ⟨by have := rd.low; omega, ?_⟩
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact Or.inr (Nat.le_of_eq spNat)
      have win3 : Writable code m3 q 33 := by slot_state region
      exact ⟨sp, df, ax, bx, bp, r9, r12, r13, r14, r15, mx, ftw, fcw,
        rd.of_frame wrote, (wrote.memLoad_eq retOutside).trans ret, retLow, win3, room, alignment⟩
    case widths =>
      intro ⟨i, hi⟩ hm
      have w := s.widths ⟨i, hi⟩ hm
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
    case index => rfl
    case current =>
      change (mergeGPR 8 (pending x (pos + 2)) _).setWidth 8 = _
      exact setWidth_mergeGPR8 _ _
    case stack =>
      intro i hi
      rw [stk3 i hi]
      simp only [Vector.getElem_set, Vector.getElem_ofFn, stackByte]
      by_cases h₂ : pos + 2 = i
      · subst i
        simp
      by_cases h₁ : pos + 1 = i
      · subst i
        simp [show pos + 1 < pos + 2 by omega]
      by_cases h₀ : pos = i
      · subst i
        simp [show pos < pos + 2 by omega]
      by_cases h : i < pos
      · simp [h, h₂, h₁, h₀, show i < pos + 2 by omega]
      · simp [h, h₂, h₁, h₀, show i ≠ pos by omega,
          show ¬i < pos + 2 by omega, show i ≠ pos + 2 by omega]
    case frame =>
      apply frame.trans wrote
      exact fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩

end K256.Proofs.Generate.Generator.Multiply.Radix
