import K256.Proofs.Sec1.Affine.Compressed.Contract
import K256.Proofs.Sec1.Affine.Compressed.Entry
import K256.Proofs.Sec1.Affine.Compressed.Choice
import K256.Proofs.Sec1.Affine.Uncompressed.Choice

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

private theorem load_store_sub (m : Ram) (sp a b : Word) {w : Nat} (v : BitVec w) (k : Nat)
    (h : w / 8 ≤ ((0 - b) - (0 - a)).toNat ∧ k / 8 ≤ ((0 - a) - (0 - b)).toNat) :
    memLoad (memStore m (sp - a) v) (sp - b) k = memLoad m (sp - b) k :=
  memLoad_memStore_of_rangeApart m _ _ v k (RangeApart.of_offsets (addr_sub sp a) (addr_sub sp b) h)

private theorem entrySaved_slots (mem : Ram) (sp : Word) (args : Values Value Reg.count) :
    let m := entrySaved mem sp args
    memLoad m (sp - 352) 64 = args[7].get 64 ∧
    memLoad m (sp - 48) 64 = args[3].get 64 ∧
    memLoad m (sp - 40) 64 = args[12].get 64 ∧
    memLoad m (sp - 32) 64 = args[13].get 64 ∧
    memLoad m (sp - 24) 64 = args[14].get 64 ∧
    memLoad m (sp - 16) 64 = args[15].get 64 ∧
    memLoad m (sp - 8) 64 = args[5].get 64 ∧
    memLoad m (sp - 380) 8 = (args[2].get 64).setWidth 8 := by
  simp (disch := decide) only [entrySaved, memLoad_memStore_same, load_store_sub, true_and]
  rw [memLoad_memStore_within _ _ 8 0 (by simp) (by decide) (by decide) (by decide)]
  simp only [Nat.mul_zero, extractLsb'_zero_eq_setWidth _ 8 (by decide : 8 ≤ 32),
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)]

theorem startCall {code : CodeMap} (cover : ∀ e ∈ fnCode, e ∈ code) : StartCall code := by
  intro fr args mem want pre
  let sp := workSP fr
  let saved := entrySaved mem fr.rsp args
  let pushed := memStore saved (fr.rsp - 496) (0x120653 : Word)
  let v := inputs mem fr.rsi
  have room := pre.room
  have addr (off : Word) (h : off.toNat ≤ 0x418) :
      (fr.rsp - off).toNat = fr.rsp.toNat - off.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have within (off : Word) (len : Nat) (hle : off.toNat ≤ 0x418) (hlen : len ≤ off.toNat) :
      RegionsWithin [⟨(fr.rsp - off).toNat, len⟩] [fr.region] := by
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    refine ⟨_, List.mem_cons_self, ?_⟩
    change fr.low.toNat ≤ (fr.rsp - off).toNat ∧
      (fr.rsp - off).toNat + len ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
    rw [addr off (by omega)]
    omega
  have hsp8 : sp - 8 = fr.rsp - 496 := by dsimp only [sp, workSP]; bv_omega
  have hsp9 : sp - 9 = fr.rsp - 497 := by dsimp only [sp, workSP]; bv_omega
  have spParity : sp + 108 = fr.rsp - 380 := by dsimp only [sp, workSP]; bv_omega
  have savedFrame := entrySaved_frame mem fr.rsp args (by omega)
  have savedSrc : fr.rsi.toNat + 32 ≤ (fr.rsp - 496).toNat ∨
      (fr.rsp - 496).toNat + 496 ≤ fr.rsi.toNat := by
    have hap := pre.srcApart
    rw [addr 496 (by decide)]
    change _ ≤ fr.rsp.toNat - 496 ∨ fr.rsp.toNat - 496 + 496 ≤ _
    omega
  have inputLoad (off : Word) (bound : off.toNat + 8 ≤ 32) :
      memLoad (entrySaved mem fr.rsp args) (fr.rsi + off) 64 = memLoad mem (fr.rsi + off) 64 :=
    entrySaved_load fr.rsp fr.rsi args (by omega) pre.input savedSrc off bound
  obtain ⟨callee, step, initSP, invalid, reg12, reg13, reg14, reg3, reg15, reg5, df, mx, ft, fc⟩ :=
    entryCall code args mem fr.rsp fr.rsi pre.rsp pre.src
      (fun e he => cover e (code_l1205b0 e he))
      (pre.stack.of_offsets (addr_sub fr.rsp 496) (addr_sub fr.rsp 0x418) (by decide)) pre.input
  have input0 : memLoad (entrySaved mem fr.rsp args) fr.rsi 64 = memLoad mem fr.rsi 64 := by
    simpa only [show fr.rsi + (0 : Word) = fr.rsi from BitVec.add_zero _] using inputLoad 0 (by decide)
  simp only [input0, inputLoad 8 (by decide), inputLoad 16 (by decide), inputLoad 24 (by decide)]
    at invalid reg12 reg13 reg14 reg3 reg15
  have pushFrame : RamWriteFrame saved pushed [⟨(fr.rsp - 497).toNat, 9⟩] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (fr.rsp - 497).toNat ≤ (fr.rsp - 496).toNat ∧
      (fr.rsp - 496).toNat + 8 ≤ (fr.rsp - 497).toNat + 9 ∧
      (fr.rsp - 496).toNat + 8 ≤ 2 ^ 64
    rw [addr 497 (by decide), addr 496 (by decide)]
    change fr.rsp.toNat - 497 ≤ fr.rsp.toNat - 496 ∧
      fr.rsp.toNat - 496 + 8 ≤ fr.rsp.toNat - 497 + 9 ∧ fr.rsp.toNat - 496 + 8 ≤ 2 ^ 64
    have := fr.rsp.isLt
    omega
  have pushRet : memLoad pushed (sp - 8) 64 = 0x120653 := by
    rw [hsp8]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have choiceStack : Writable code pushed (sp - 9) 9 := by
    rw [hsp9]
    exact ((pre.stack.of_frame savedFrame).of_frame pushFrame).of_offsets
      (addr_sub fr.rsp 497) (addr_sub fr.rsp 0x418) (by decide)
  have calleeSP : callee[4].get 64 = sp - 8 := by rw [initSP, hsp8]; rfl
  obtain ⟨first, m₁, reach₁, rsp₁, ax₁, frame₁, keep₁⟩ :=
    Uncompressed.resumeChoice cover step calleeSP choiceStack pushRet (by decide)
  have rspGet : first[4].get 64 = sp := by rw [rsp₁]; rfl
  obtain ⟨regs, m, reach₂, ax₂, rsp₂, frame₂, keep₂⟩ :=
    ChoiceSite.pass .canonical code first m₁ sp cover rspGet (choiceStack.of_frame frame₁)
      (by intro h; cases h)
  have moreWrites : RamWriteFrame saved m [⟨(fr.rsp - 497).toNat, 9⟩] := by
    rw [hsp9] at frame₁ frame₂
    exact (pushFrame.trans frame₁ (by
      intro r hr
      rcases List.mem_singleton.mp hr with rfl
      exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.add_le_add_left (by decide : 1 ≤ 9) _⟩)).trans frame₂ (by
      intro r hr
      exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have frame : RamWriteFrame mem m [fr.region] :=
    ((RamWriteFrame.refl mem [fr.region]).trans savedFrame (within 496 496 (by decide) (by decide))).trans
      moreWrites (within 497 9 (by decide) (by decide))
  have slotLoad (off : Word) (len : Nat) (hoff : off.toNat ≤ 488) (hlen : len / 8 ≤ off.toNat) :
      memLoad m (fr.rsp - off) len = memLoad saved (fr.rsp - off) len := by
    apply moreWrites.memLoad_eq
    refine ⟨?_, fun r hr => ?_⟩
    · rw [addr off (by omega)]
      have := fr.rsp.isLt
      omega
    · rcases List.mem_singleton.mp hr with rfl
      right
      change (fr.rsp - 497).toNat + 9 ≤ (fr.rsp - off).toNat
      rw [addr 497 (by decide), addr off (by omega)]
      change fr.rsp.toNat - 497 + 9 ≤ fr.rsp.toNat - off.toNat
      omega
  have ret : memLoad m fr.rsp 64 = fr.ret := by
    refine (frame.memLoad_eq (k := 64) ?_).trans pre.ret
    have low := pre.slot.low
    refine ⟨by omega, fun r hr => ?_⟩
    rcases List.mem_singleton.mp hr with rfl
    right
    change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ fr.rsp.toNat
    omega
  obtain ⟨d, bx, r12, r13, r14, r15, bp, parity⟩ := entrySaved_slots mem fr.rsp args
  have kept (i : Fin Reg.count) (h : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      regs[i] = callee[i] := by
    apply (keep₂ i h).trans
    apply keep₁
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢
    omega
  have kept64 (i : Fin Reg.count) (h : i.val ∈ [3,5,12,13,14,15,22,39,50,51])
      {w : Word} (hi : callee[i] = ⟨64,w⟩) : regs[i].get 64 = w := by
    rw [kept i h, hi]
    rfl
  refine ⟨regs, m, reach₁.trans reach₂, ?_, frame⟩
  refine ⟨?_, pre.output.of_frame frame, ?_, ?_, kept64 12 (by decide) reg12,
    kept64 13 (by decide) reg13, kept64 14 (by decide) reg14, kept64 3 (by decide) reg3,
    kept64 15 (by decide) reg15, kept64 5 (by decide) reg5⟩
  · simp only [Fn1205b0.frameAt, Fn1205b0.frameAtG2, Atom.All, Atom.Holds]
    exact ⟨rsp₂, (kept 22 (by decide)).trans (df.trans pre.df),
      (kept 39 (by decide)).trans (mx.trans pre.mx), (kept 50 (by decide)).trans (ft.trans pre.ft),
      (kept 51 (by decide)).trans (fc.trans pre.fc),
      (slotLoad 352 64 (by decide) (by decide)).trans (d.trans pre.dst),
      (slotLoad 48 64 (by decide) (by decide)).trans (bx.trans pre.rbx),
      (slotLoad 40 64 (by decide) (by decide)).trans (r12.trans pre.r12),
      (slotLoad 32 64 (by decide) (by decide)).trans (r13.trans pre.r13),
      (slotLoad 24 64 (by decide) (by decide)).trans (r14.trans pre.r14),
      (slotLoad 16 64 (by decide) (by decide)).trans (r15.trans pre.r15),
      (slotLoad 8 64 (by decide) (by decide)).trans (bp.trans pre.rbp),
      pre.slot.of_frame frame, ret, pre.retLow, pre.stack.of_frame frame, room, pre.align, trivial⟩
  · rw [spParity]
    exact (slotLoad 380 8 (by decide) (by decide)).trans (parity.trans pre.parity)
  · have invalidEq : Uncompressed.invalid v.a v.b v.c v.d = !v.valid := by
      rw [Uncompressed.invalid_eq]
      change decide (modulus ≤ v.x) = !decide (v.x < modulus)
      simpa only [Nat.not_lt] using (decide_not (p := v.x < modulus))
    change callee[7].get 64 = BitVec.ofNat 64 (Uncompressed.invalid v.a v.b v.c v.d).toNat at invalid
    change (regs[0].get 64).setWidth 8 = BitVec.ofNat 8 v.valid.toNat
    rw [ax₂, ax₁, invalid, invalidEq]
    cases v.valid <;> rfl

end K256.Proofs.Sec1.Affine.Compressed
