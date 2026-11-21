import K256.Proofs.Signing.SecretDecode.Nonzero.Equal
import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Signing.SecretDecode

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private def compareMemory (m : Ram) (p : BitVec 64) (w : Nat → BitVec 64) : Ram :=
  let m := memStore m (p + 40) (w 0)
  let m := memStore m (p + 48) (w 1)
  let m := memStore m (p + 56) (w 2)
  let m := memStore m (p + 64) (w 3)
  let m := memStore m (p + 24) (0 : BitVec 64)
  let m := memStore m (p + 16) (0 : BitVec 64)
  let m := memStore m (p + 8) (0 : BitVec 64)
  let m := memStore m p (0 : BitVec 64)
  memStore m (p - 8) (0x106f3b : BitVec 64)

set_option maxHeartbeats 1000000 in
private theorem compareCallBlock {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (h : Frame .l106eed fr a m) (limbs : Limbs fr a) :
    let p := fr.rsp - 120
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l106eed, a, m⟩ =
      .call ⟨.l127f50, b, compareMemory m p (word fr)⟩ (Verify.resumeAt .l106f3b 0x106f3b) ∧
      b[4] = ⟨64, p - 8⟩ ∧ b[7] = ⟨64, p + 40⟩ ∧ b[6] = ⟨64, 4⟩ ∧
      b[2] = ⟨64, p⟩ ∧ b[1] = ⟨64, 4⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] → b[i] = a[i]) := by
  dsimp only
  obtain ⟨sp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, win, _⟩ := h.atoms
  change a[4] = ⟨64, fr.rsp - 120⟩ at sp
  change Writable Extracted.programImage m (fr.rsp - 336) 336 at win
  have eqsp : a[4].get 64 = fr.rsp - 120 := congrArg (Value.get 64) sp
  have g0 := congrArg (Value.get 64) limbs.w0
  have g1 := congrArg (Value.get 64) limbs.w1
  have g2 := congrArg (Value.get 64) limbs.w2
  have g3 := congrArg (Value.get 64) limbs.w3
  simp only [Value.get_mk] at g0 g1 g2 g3
  refine ⟨?_, ?run, ?rest⟩
  case run =>
    unfold compareMemory
    cfg_eval [eqsp, g0, g1, g2, g3]
    simp only [reduceAddOffset, reduceSubOffset]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l106eed)
    rfl
  case rest =>
    refine ⟨?_, ?_, rfl, rfl, rfl, ?_⟩
    · simp only [reduceSubOffset]; rfl
    · simp only [reduceAddOffset]; rfl
    · intro ⟨i, hi⟩ mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem compareWrites {fr : Activation} (m : Ram)
    (room : 336 ≤ fr.rsp.toNat) (high : fr.rsp.toNat + 80 < 2^32) :
    RamWriteFrame m (compareMemory m (fr.rsp - 120) (word fr))
      [⟨(fr.rsp - 128).toNat, 80⟩] := by
  have off (k : BitVec 64) (h : k.toNat ≤ 336) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  simp only [compareMemory, reduceAddOffset, reduceSubOffset]
  repeat' (apply RamWriteFrame.memStore; rotate_left
           simp (disch := decide) only [InRegions, InRegion, List.mem_cons, List.not_mem_nil,
             or_false, exists_eq_left, off, BitVec.reduceToNat, Nat.reduceDiv]
           omega)
  exact RamWriteFrame.refl _ _

private theorem compareLoads (m : Ram) (p : BitVec 64) (w : Nat → BitVec 64) (i : Nat) (hi : i < 4) :
    memLoad (compareMemory m p w) (wordAddr (p + 40) 64 i) 64 = w i ∧
    memLoad (compareMemory m p w) (wordAddr p 64 i) 64 = 0 := by
  have vals : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases vals with rfl | rfl | rfl | rfl <;> constructor <;>
    simp (disch := first | decide | store_disch) only [compareMemory, wordAddr, Nat.reduceDiv, Nat.reduceMul,
      BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
      memLoad_memStore_same, memLoad_memStore_of_rangeApart]

set_option maxRecDepth 2048 in
private theorem compareFrame {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (low : fr.low = fr.rsp - 336) (room : 336 ≤ fr.rsp.toNat) (high : fr.rsp.toNat + 80 < 2^32)
    (h : Frame .l106eed fr a m) :
    Frame .l106eed fr a (compareMemory m (fr.rsp - 120) (word fr)) := by
  have wr := compareWrites m room high
  have off (k : BitVec 64) (h : k.toNat ≤ 336) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have keep (k : BitVec 64) (hk : k.toNat ≤ 48) :
      memLoad (compareMemory m (fr.rsp - 120) (word fr)) (fr.rsp - k) 64 = memLoad m (fr.rsp - k) 64 := by
    apply wr.memLoad_eq
    refine ⟨?_, fun r hr => Or.inr ?_⟩
    · rw [off k (by omega)]
      omega
    · obtain rfl := List.mem_singleton.mp hr
      change (fr.rsp - 128).toNat + 80 ≤ (fr.rsp - k).toNat
      simp (disch := first | decide | omega) only [off, BitVec.reduceToNat]
      omega
  obtain ⟨sp, df, bx, mx, ft, fc, bx', r12, r13, r14, r15, bp, rd, rt, bound, win, base, align, tail⟩ := h.atoms
  change Readable m fr.rsp 8 at rd
  change Writable Extracted.programImage m (fr.rsp - 336) 336 at win
  refine ⟨⟨sp, df, bx, mx, ft, fc, ?_, ?_, ?_, ?_, ?_, ?_, rd.of_frame wr, ?_, bound, win.of_frame wr, base, align, tail⟩,
    h.writes.trans wr ?_, h.widths⟩
  · exact (keep 48 (by decide)).trans bx'
  · exact (keep 40 (by decide)).trans r12
  · exact (keep 32 (by decide)).trans r13
  · exact (keep 24 (by decide)).trans r14
  · exact (keep 16 (by decide)).trans r15
  · exact (keep 8 (by decide)).trans bp
  · have unchanged := keep 0 (by decide)
    rw [show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega] at unchanged
    exact unchanged.trans rt
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;>
      simp (disch := decide) only [Activation.region, low, off, BitVec.reduceToNat] <;> omega

theorem compareNonzero {fr : Activation} {a : Verify.Core.Registers} {m : Ram}
    (low : fr.low = fr.rsp - 336) (room : 336 ≤ fr.rsp.toNat)
    (high : fr.rsp.toNat + 80 < 2^32)
    (h : Frame .l106eed fr a m) (limbs : Limbs fr a)
    (nz : ¬ ∀ i < 4, word fr i = 0) :
    ∃ b n, Verify.Core.Reaches .l106eed a m .l106f3b b n ∧ Frame .l106f3b fr b n ∧ Limbs fr b ∧ b[0].get 8 = 0 := by
  let p := fr.rsp - 120
  let n := compareMemory m p (word fr)
  have adjustSp : p - 8 = fr.rsp - 128 := by dsimp only [p]; bv_omega
  have adjustDi : p + 40 = fr.rsp - 80 := by dsimp only [p]; bv_omega
  obtain ⟨b, call, sp, di, si, dx, cx, kept⟩ := compareCallBlock h limbs
  have ret : memLoad n (fr.rsp - 128) 64 = 0x106f3b := by
    rw [← adjustSp]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have different : ¬ ∀ i < 4, memLoad n (wordAddr (fr.rsp - 80) 64 i) 64 =
      memLoad n (wordAddr p 64 i) 64 := by
    intro eq
    apply nz
    intro i hi
    obtain ⟨lhs, rhs⟩ := compareLoads m p (word fr) i hi
    exact lhs.symm.trans (by rw [adjustDi]; exact (eq i hi).trans rhs)
  obtain ⟨c, reaches, frame, regs, flag⟩ := equalNonzero call (compareFrame low room high h) limbs
    (adjustSp ▸ sp) (adjustDi ▸ di) dx si cx kept ret room different
  exact ⟨c, n, reaches, frame, regs, flag⟩

end K256.Proofs.Signing.SecretDecode
