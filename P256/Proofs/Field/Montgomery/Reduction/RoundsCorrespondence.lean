import P256.Proofs.Field.Montgomery.Reduction.Correspondence
import P256.Proofs.Field.Montgomery.Reduction.SecondRound
import P256.Proofs.Field.Montgomery.Reduction.ThirdRound
import P256.Proofs.Field.Montgomery.Reduction.FourthRound
import P256.Proofs.Field.Montgomery.Reduction.RoundsArithmetic

set_option autoImplicit false

namespace P256.Proofs.Field.Montgomery.Reduction

open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Limbs)

theorem low8_word (c : Bool) : (if c then 1 else 0 : BitVec 8) = BitVec.ofNat 8 c.toNat := by
  cases c <;> rfl

theorem low8_bit (c : Bool) : (if c then 1 else 0 : BitVec 8).getLsbD 0 = c := by
  cases c <;> rfl

theorem widen_carry (c : Bool) : (BitVec.ofNat 8 c.toNat).setWidth 64 = BitVec.ofNat 64 c.toNat := by
  cases c <;> rfl

def pendingRounds (s : RamState) : Limbs × (BitVec 64 × Bool) :=
  let x := adc64 ((Operand.reg 6 : Operand 64).read s) 0 (StatusFlags.ofRFLAGS s.RFLAGS).CF
  let z := adc64 ((Operand.reg 2 : Operand 64).read s) 0 x.2
  (⟨(Operand.reg 12 : Operand 64).read s, (Operand.reg 15 : Operand 64).read s, x.1, z.1⟩,
    ((Operand.reg 9 : Operand 64).read s, ((Operand.reg 1 : Operand 64).read s).setWidth 8 |>.getLsbD 0))

theorem secondRound_correspondence {s t : RamState}
    (h : (secondRoundEffect s).Holds s t)
    (hk : ((Operand.reg 11 : Operand 64).read s) = 0xffffffff00000001) :
    let r := shiftRound (⟨((Operand.reg 8 : Operand 64).read s), ((Operand.reg 14 : Operand 64).read s), ((Operand.reg 10 : Operand 64).read s), ((Operand.reg 9 : Operand 64).read s)⟩ : Limbs) ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 0) : Operand 64).read s)
    let e := adc64 ((Operand.reg 12 : Operand 64).read s) 0 r.2
    (⟨((Operand.reg 6 : Operand 64).read t), ((Operand.reg 15 : Operand 64).read t), ((Operand.reg 9 : Operand 64).read t), ((Operand.reg 8 : Operand 64).read t)⟩ : Limbs) = r.1 ∧
    ((Operand.reg 12 : Operand 64).read t) = e.1 ∧
    ((Operand.reg 2 : Operand 64).read t).setWidth 8 = BitVec.ofNat 8 e.2.toNat := by
  have hw := h.writes
  dsimp only [secondRoundEffect, Write.AllHold] at hw
  rcases hw with ⟨hr0, hr2, hr6, hr8, hr9, hr12, hr15⟩
  simp only [hr6, hr15, hr9, hr8, hr12, hr2, and_self, shiftRound, add64, adc64, product64, hk, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, low8_word]

theorem thirdRound_correspondence {s t : RamState} {c : Bool}
    (h : (thirdRoundEffect s).Holds s t)
    (hk : ((Operand.reg 11 : Operand 64).read s) = 0xffffffff00000001)
    (hc : ((Operand.reg 2 : Operand 64).read s).setWidth 8 = BitVec.ofNat 8 c.toNat) :
    let r := shiftRound (⟨((Operand.reg 6 : Operand 64).read s), ((Operand.reg 15 : Operand 64).read s), ((Operand.reg 9 : Operand 64).read s), ((Operand.reg 8 : Operand 64).read s)⟩ : Limbs) ((Operand.reg 12 : Operand 64).read s)
    let e := adc64 (BitVec.ofNat 64 c.toNat) ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 16) : Operand 64).read s) r.2
    (⟨((Operand.reg 10 : Operand 64).read t), ((Operand.reg 14 : Operand 64).read t), ((Operand.reg 8 : Operand 64).read t), ((Operand.reg 6 : Operand 64).read t)⟩ : Limbs) = r.1 ∧
    ((Operand.reg 13 : Operand 64).read t) = e.1 ∧
    ((Operand.reg 2 : Operand 64).read t).setWidth 8 = BitVec.ofNat 8 e.2.toNat := by
  have hw := h.writes
  dsimp only [thirdRoundEffect, Write.AllHold] at hw
  rcases hw with ⟨hr0, hr2, hr6, hr8, hr10, hr13, hr14⟩
  simp only [hr10, hr14, hr8, hr6, hr13, hr2, and_self, shiftRound, add64, adc64, product64, hk, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, low8_word, hc, widen_carry]

theorem fourthRound_correspondence {s t : RamState} {c : Bool}
    (h : (fourthRoundEffect s).Holds s t)
    (hk : ((Operand.reg 11 : Operand 64).read s) = 0xffffffff00000001)
    (hc : ((Operand.reg 2 : Operand 64).read s).setWidth 8 = BitVec.ofNat 8 c.toNat) :
    let r := shiftRound (⟨((Operand.reg 10 : Operand 64).read s), ((Operand.reg 14 : Operand 64).read s), ((Operand.reg 8 : Operand 64).read s), ((Operand.reg 6 : Operand 64).read s)⟩ : Limbs) ((Operand.reg 13 : Operand 64).read s)
    let e := adc64 (BitVec.ofNat 64 c.toNat) ((Operand.mem (((Operand.reg 1 : Operand 64).read s) + 24) : Operand 64).read s) r.2
    pendingRounds t = (r.1, e) := by
  have hw := h.writes
  dsimp only [fourthRoundEffect, Write.AllHold] at hw
  rcases hw with ⟨hr0, hr1, hr2, hr6, hr9, hr12, hr15⟩
  have hcf := h.flags.1
  simp only [pendingRounds]
  rw [hcf]
  simp only [hr12, hr15, hr6, hr2, hr9, hr1, shiftRound, add64, adc64, product64, hk, hc, widen_carry, P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8, low8_bit]

theorem rounds_correspondence {s t u v w x y : RamState}
    (hs : (firstSetupEffect s).Holds s t)
    (hc : (firstCarryEffect t).Holds t u)
    (hh : (firstHighEffect u).Holds u v)
    (h2 : (secondRoundEffect v).Holds v w)
    (h3 : (thirdRoundEffect w).Holds w x)
    (h4 : (fourthRoundEffect x).Holds x y) :
    pendingRounds y = rounds (readLimbs s ((Operand.reg 6 : Operand 64).read s))
      (readLimbs s ((Operand.reg 2 : Operand 64).read s)) := by
  let low := readLimbs s ((Operand.reg 6 : Operand 64).read s)
  let high := readLimbs s ((Operand.reg 2 : Operand 64).read s)
  let r0 := firstRound low
  let r1 := shiftRound r0 high.l0
  let e1 := adc64 high.l1 0 r1.2
  let r2 := shiftRound r1.1 e1.1
  let e2 := adc64 (BitVec.ofNat 64 e1.2.toNat) high.l2 r2.2
  let r3 := shiftRound r2.1 e2.1
  let e3 := adc64 (BitVec.ofNat 64 e2.2.toNat) high.l3 r3.2
  have f := firstRound_correspondence hs hc hh
  have m1 : t.external = s.external := hs.agrees.external (by simp [firstSetupEffect, Effect.components, Component.Covers])
  have m2 : u.external = s.external := (hc.agrees.external (by simp [firstCarryEffect, Effect.components, Component.Covers])).trans m1
  have m3 : v.external = s.external := (hh.agrees.external (by simp [firstHighEffect, Effect.components, Component.Covers])).trans m2
  have m4 : w.external = s.external := (h2.agrees.external (by simp [secondRoundEffect, Effect.components, Component.Covers])).trans m3
  have m5 : x.external = s.external := (h3.agrees.external (by simp [thirdRoundEffect, Effect.components, Component.Covers])).trans m4
  have mem3 (a : BitVec 64) : (Operand.mem a : Operand 64).read v = (Operand.mem a : Operand 64).read s := by
    change memLoad _ _ _ = memLoad _ _ _; rw [m3]
  have mem4 (a : BitVec 64) : (Operand.mem a : Operand 64).read w = (Operand.mem a : Operand 64).read s := by
    change memLoad _ _ _ = memLoad _ _ _; rw [m4]
  have mem5 (a : BitVec 64) : (Operand.mem a : Operand 64).read x = (Operand.mem a : Operand 64).read s := by
    change memLoad _ _ _ = memLoad _ _ _; rw [m5]
  have ptr4 : (Operand.reg 1 : Operand 64).read w = (Operand.reg 2 : Operand 64).read s :=
    (h2.agrees.read (by simp [secondRoundEffect, Effect.components])).trans f.2.1
  have ptr5 : (Operand.reg 1 : Operand 64).read x = (Operand.reg 2 : Operand 64).read s :=
    (h3.agrees.read (by simp [thirdRoundEffect, Effect.components])).trans ptr4
  have k4 : (Operand.reg 11 : Operand 64).read w = 0xffffffff00000001 :=
    (h2.agrees.read (by simp [secondRoundEffect, Effect.components])).trans f.2.2.2.2
  have k5 : (Operand.reg 11 : Operand 64).read x = 0xffffffff00000001 :=
    (h3.agrees.read (by simp [thirdRoundEffect, Effect.components])).trans k4
  have v2 := secondRound_correspondence h2 f.2.2.2.2
  dsimp only at v2
  rw [f.1, f.2.1, f.2.2.1, mem3] at v2
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at v2
  change (⟨(Operand.reg 6 : Operand 64).read w, (Operand.reg 15 : Operand 64).read w,
    (Operand.reg 9 : Operand 64).read w, (Operand.reg 8 : Operand 64).read w⟩ : Limbs) = r1.1 ∧
    (Operand.reg 12 : Operand 64).read w = e1.1 ∧
    ((Operand.reg 2 : Operand 64).read w).setWidth 8 = BitVec.ofNat 8 e1.2.toNat at v2
  have v3 := thirdRound_correspondence h3 k4 v2.2.2
  dsimp only at v3
  rw [v2.1, v2.2.1, ptr4, mem4] at v3
  change (⟨(Operand.reg 10 : Operand 64).read x, (Operand.reg 14 : Operand 64).read x,
    (Operand.reg 8 : Operand 64).read x, (Operand.reg 6 : Operand 64).read x⟩ : Limbs) = r2.1 ∧
    (Operand.reg 13 : Operand 64).read x = e2.1 ∧
    ((Operand.reg 2 : Operand 64).read x).setWidth 8 = BitVec.ofNat 8 e2.2.toNat at v3
  have v4 := fourthRound_correspondence h4 k5 v3.2.2
  dsimp only at v4
  rw [v3.1, v3.2.1, ptr5, mem5] at v4
  exact v4


end P256.Proofs.Field.Montgomery.Reduction
