import K256.Proofs.Ecdh.Decode.Packing.Image
import K256.Proofs.Ecdh.Decode.Packing.Route
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Ecdh.Decode.Packing

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Ecdh.LIR

def compressedZeros : StackImage :=
  let m0 := StackImage.original
  let m1 := m0.zero 118 true
  let m2 := m1.zero 110 true
  let m3 := m2.zero 102 true
  m3.zero 94 true

private def compressedCopies : StackImage :=
  let m4 := compressedZeros
  let m5 := m4.input m4 86 25 true (by decide)
  let m6 := m5.input m5 80 19 true (by decide)
  let m7 := m6.input m6 144 11 true (by decide)
  let m8 := m7.copy m7 168 96 true
  let m9 := m8.copy m8 176 104 true
  let m10 := m9.copy m9 184 112 true
  let m11 := m10.copy m10 152 80 true
  let m12 := m11.copy m11 160 88 true
  let m13 := m12.zero 190 true
  m13

private def compressedHead : StackImage :=
  let m13 := compressedCopies
  let m14 := m13.input m13 11 3 false (by decide)
  let m15 := m14.input m13 8 0 false (by decide)
  m15

def compressedImage : StackImage :=
  let m15 := compressedHead
  let m16 := m15.copy m15 62 190 true
  let m17 := m16.copy m16 56 184 true
  let m18 := m17.copy m17 48 176 true
  let m19 := m18.copy m18 40 168 true
  let m20 := m19.copy m19 32 160 true
  let m21 := m20.copy m20 24 152 true
  let m22 := m21.copy m20 16 144 true
  m22

def identityImage : StackImage :=
  let m0 := StackImage.original
  let m1 := m0.zero 11 false
  let m2 := m1.zero 8 false
  let m3 := m2.zero 16 true
  let m4 := m3.zero 24 true
  let m5 := m4.zero 32 true
  let m6 := m5.zero 40 true
  let m7 := m6.zero 48 true
  let m8 := m7.zero 56 true
  m8.zero 62 true

def packedImage (m0 : StackImage) : StackImage :=
  let m1 := m0.copy m0 75 11 false
  let m2 := m1.copy m0 72 8 false
  let m3 := m2.accumulator 79
  let m4 := m3.copy m3 83 16 true
  let m5 := m4.copy m3 91 24 true
  let m6 := m5.copy m5 99 32 true
  let m7 := m6.copy m6 107 40 true
  let m8 := m7.copy m7 115 48 true
  let m9 := m8.copy m8 123 56 true
  m9.copy m9 129 62 true

def affineResume : StackFrame Value Label signature Reg.count :=
  { target := .l121177, kept := #v[], arity := rfl, guard := some ⟨64, 0x121177⟩ }

def registersKept (a b : Values Value Reg.count) : Prop :=
  ∀ r ∈ [5, 9, 12, 13, 22, 39, 50, 51], ∀ hr : r < Reg.count, b[r] = a[r]

theorem registersKept.trans {a b c : Values Value Reg.count} :
    registersKept a b → registersKept b c → registersKept a c :=
  fun h₁ h₂ r hr ok => (h₂ r hr ok).trans (h₁ r hr ok)

macro "packing_guards" sp:ident src:ident code:ident win:ident read:ident cover:ident : tactic =>
  `(tactic| repeat'
    (refine Eq.trans (ite_eq_left ?_) ?_
     first
     | apply stackLoad (code := $code) (sp := $sp)
       · repeat' apply Writable.memStore
         exact $win
       · decide
     | apply inputLoad (src := $src)
       · repeat' apply Readable.memStore
         exact $read
       · decide
     | apply inputLoadBase (src := $src)
       · repeat' apply Readable.memStore
         exact $read
       · decide
     | refine stackStore (sp := $sp) ?_ rfl ?_ $cover ?_
       · repeat' apply Writable.memStore
         exact $win
       · decide
       · decide +kernel))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem compressedBlock {code : CodeMap} (regs : Values Value Reg.count)
    (m : Ram) (sp src : BitVec 64)
    (hsp : regs[4].get 64 = sp) (hsrc : regs[6].get 64 = src)
    (r8Width : regs[8].width = 64)
    (win : Writable code m (sp - 8) 272) (read : Readable m src 33)
    (hc : ∀ x ∈ fnCode, x ∈ code) :
    ∃ args : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l120f59, regs, m⟩ =
        .jump ⟨.l121105, args, compressedImage.memory sp src m 0⟩ ∧
      args[0].get 32 = memLoad (compressedZeros.memory sp src m 0) (src + 7) 32 ∧
      args[3] = regs[3] ∧ args[4].get 64 = sp ∧ args[15].get 8 = 1 ∧
      args[15] = ⟨64, args[15].get 64⟩ ∧ args[8].width = 64 ∧ registersKept regs args := by
  have cover := fun x hx => hc x (code_l120f59 x hx)
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [hsp, hsrc]
    cfg_name_stores
    extract_lets +lift _ _ _ _ _ _ _ _ _ _ _ _ m13 _ m15 _ _ _ _ _ _ m22
    packing_guards sp src code win read cover
    have copies : compressedCopies.memory sp src m 0 = m13 := rfl
    have head : compressedHead.memory sp src m 0 = m15 := by
      simp only [compressedHead, StackImage.memory, copies,
        show src + BitVec.ofNat 64 (0 : Fin 33).val = src from BitVec.add_zero src]
      rfl
    have result : compressedImage.memory sp src m 0 = m22 := by
      simp only [compressedImage, StackImage.memory, head]
      rfl
    rw [result]
  case post =>
    refine ⟨?_, rfl, hsp, ?_, rfl, ?_, ?_⟩
    · change ((memLoad _ (src + 7) 32).setWidth 64).setWidth 32 = _
      rw [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
      rfl
    · change (mergeGPR 8 1 (regs[15].get 64)).setWidth 8 = 1
      exact setWidth_mergeGPR8 _ _
    · exact r8Width
    · intro r hr _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem identityBlock {code : CodeMap} (regs : Values Value Reg.count)
    (m : Ram) (sp src : BitVec 64)
    (hsp : regs[4].get 64 = sp) (hsrc : regs[6].get 64 = src)
    (win : Writable code m (sp - 8) 272) (read : Readable m src 33)
    (zero : ∀ i < 33, memByte m (src + BitVec.ofNat 64 i) = 0)
    (hc : ∀ x ∈ fnCode, x ∈ code) :
    ∃ args : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l12105b, regs, m⟩ =
        .jump ⟨.l121105, args, identityImage.memory sp src m 0⟩ ∧
      args[0].get 32 = 0 ∧
      args[3] = regs[3] ∧ args[4].get 64 = sp ∧ args[15].get 8 = 1 ∧
      args[15] = ⟨64, args[15].get 64⟩ ∧ args[8].width = 64 ∧ registersKept regs args := by
  have cover := fun x hx => hc x (code_l12105b x hx)
  have load {off : Nat} {w : Nat} (hw : w % 8 = 0) (hi : off + w / 8 ≤ 33) :
      memLoad m (src + BitVec.ofNat 64 off) w = 0 := by
    apply memLoad_eq_of_memByte hw
    intro i hb
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, zero _ (by omega)]
    simp [storedByte]
  have h0 : memLoad m src 64 = 0 := by
    have h := load (off := 0) (w := 64) (by decide) (by decide)
    change memLoad m (src + (0 : BitVec 64)) 64 = 0 at h
    exact (congrArg (fun a => memLoad m a 64) (addr_self src)).trans h
  have h8 : memLoad m (src + 8) 64 = 0 := load (off := 8) (w := 64) (by decide) (by decide)
  have h16 : memLoad m (src + 16) 64 = 0 := load (off := 16) (w := 64) (by decide) (by decide)
  have h24 : memLoad m (src + 24) 64 = 0 := load (off := 24) (w := 64) (by decide) (by decide)
  have h32 : memLoad m (src + 32) 8 = 0 := load (off := 32) (w := 8) (by decide) (by decide)
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [hsp, hsrc, h0, h8, h16, h24, h32]
    packing_guards sp src code win read cover
    rfl
  case post =>
    refine ⟨rfl, rfl, hsp, ?_, rfl, ?_, ?_⟩
    · have low (v : BitVec 64) : (mergeGPR 16 1 v).setWidth 16 = 1 := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        simp only [mergeGPR, show (16 : Nat) ≠ 32 by decide, ite_false,
          BitVec.getLsbD_setWidth, hj]
        rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
        simp only [Nat.zero_le, decide_true, Nat.zero_add, hj, true_and,
          Bool.true_and, ite_true, Nat.sub_zero]
      have eight (v : BitVec 64) : (mergeGPR 16 1 v).setWidth 8 = 1 := by
        rw [← BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 16), low]
        rfl
      simp only [xorFlags, beq_self_eq_true, Option.getD_some, Bool.not_true,
        Bool.false_eq_true, ite_false, eight, low,
        BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
      change (((mergeGPR 16 1 (regs[1].get 64)).setWidth 32).setWidth 64).setWidth 8 = 1
      rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), eight]
    · rfl
    · intro r hr _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 500000 in
theorem affineCallBlock {code : CodeMap} (regs : Values Value Reg.count)
    (m : Ram) (sp : BitVec 64)
    (hsp : regs[4].get 64 = sp)
    (win : Writable code m (sp - 8) 272) (hc : ∀ x ∈ fnCode, x ∈ code) :
    ∃ args : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l121105, regs, m⟩ =
        .call ⟨.l121480, args, memStore
          ((packedImage .original).memory sp 0 m (regs[0].get 32))
          (sp - 8) (0x121177 : BitVec 64)⟩ affineResume ∧
      args[3] = regs[3] ∧ args[4] = ⟨64, sp - 8⟩ ∧ args[6] = ⟨64, sp + 72⟩ ∧
      args[7] = ⟨64, sp + 144⟩ ∧ args[14] = ⟨64, sp + 144⟩ ∧ args[15] = regs[15] ∧
      args[8] = regs[8] ∧
      registersKept regs args := by
  have cover := fun x hx => hc x (code_l121105 x hx)
  have acc : (regs[0].get 64).setWidth 32 = regs[0].get 32 :=
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [hsp, acc]
    packing_guards sp sp code win win cover
    refine Eq.trans (ite_eq_left ?_) ?_
    · refine stackStore (off := 0 - 8) ?_ (addr_sub _ _) (by decide) cover (by decide +kernel)
      repeat' apply Writable.memStore
      exact win
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro r hr _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Ecdh.Decode.Packing
