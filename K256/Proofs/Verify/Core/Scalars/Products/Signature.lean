import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.Core.Scalars.Products.Call
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

open Generate.Generator.Multiply (scalarWords)
open ScalarProduct

private def signatureStage (m : Ram) (sp src : BitVec 64) : Ram :=
  let n := memStore m (sp + 32) (memLoad m (src + 24) 64)
  let n := memStore n (sp + 24) (memLoad m (src + 16) 64)
  let n := memStore n (sp + 16) (memLoad m (src + 8) 64)
  let n := memStore n (sp + 8) (memLoad m src 64)
  memStore n (sp - 8) (0x105256 : BitVec 64)

private theorem signatureStageWords {m : Ram} {sp src : BitVec 64} {v : Vector (BitVec 64) 4}
    (words : WordsAt m src 64 v) : WordsAt (signatureStage m sp src) (sp + 8) 64 v := by
  intro i hi
  rw [← words i hi]
  obtain rfl | rfl | rfl | rfl := show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega
  all_goals simp (disch := store_disch) only [signatureStage, wordAddr, Nat.reduceDiv, Nat.reduceMul,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
    memLoad_memStore_same, memLoad_memStore_of_rangeApart]

set_option maxRecDepth 4096 in
private theorem signatureCallBlock (a : Registers) (m : Ram) (sp src : BitVec 64)
    (rsp : a[4].get 64 = sp) (r15 : a[15].get 64 = src)
    (stack : Writable Extracted.programImage m (sp - 8) 48)
    (input : Readable m src 32) (source : src = sp + 848) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l105216, a, m⟩ =
        .call ⟨.l109f60, b, signatureStage m sp src⟩ (callFrame .l105256 0x105256) ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[6] = ⟨64, sp + 8⟩ ∧ b[2] = ⟨64, sp + 288⟩ ∧
      b[7] = ⟨64, sp + 416⟩ ∧ b[15] = ⟨64, sp + 416⟩ ∧
      b[1].width = 64 ∧
      ∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 22, 39, 50, 51] → b[i] = a[i] := by
  refine ⟨?b, ?step, ?regs⟩
  case step =>
    cases source
    cfg_eval [rsp, r15]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l105216)
    simp (disch := store_disch) only [signatureStage, BitVec.add_assoc, BitVec.reduceAdd,
      memLoad_memStore_of_rangeApart] <;> rfl
  case regs =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

variable {fr : Activation} {a : Registers} {p : Curve.Point} {digest : ByteArray} {r s : Nat}

private def signatureStageRegion (fr : Activation) : MemoryRegion :=
  ⟨(localSp fr - 8).toNat, 48⟩

private theorem signatureStageFrame (e : Entry fr a p digest r s) (m : Ram) :
    RamWriteFrame m (signatureStage m (localSp fr) fr.r8) [signatureStageRegion fr] := by
  have room := e.stackRoom
  have upper := e.low
  have start := pushNat e
  have slotIn {off : Nat} (h : off + 8 ≤ 40) :
      InRegions [signatureStageRegion fr] (slot fr off) 8 := by
    have pos := slotNat e (off := off) (by omega)
    exact ⟨_, List.mem_singleton_self _, by simp only [InRegion, signatureStageRegion]; omega⟩
  have pushIn : InRegions [signatureStageRegion fr] (localSp fr - 8) 8 :=
    ⟨_, List.mem_singleton_self _, by simp only [InRegion, signatureStageRegion]; omega⟩
  unfold signatureStage
  apply RamWriteFrame.memStore _ _ pushIn
  repeat' apply RamWriteFrame.memStore _ _ (slotIn (by decide))
  exact .refl _ _

private theorem signatureStageWithin (e : Entry fr a p digest r s) :
    RegionsWithin [signatureStageRegion fr] [fr.region] := by
  intro rr member
  obtain rfl := List.mem_singleton.mp member
  have bottom := e.low_toNat
  have room := e.stackRoom
  have start := pushNat e
  exact ⟨_, List.mem_singleton_self _, by simp only [signatureStageRegion, Activation.region]; omega⟩

private theorem signatureStageOutside (e : Entry fr a p digest r s) {off len : Nat}
    (lo : 40 ≤ off) (hi : off + len ≤ 488) :
    Outside [signatureStageRegion fr] (slot fr off) len := by
  have start := pushNat e
  have pos := slotNat e (off := off) (by omega)
  have room := e.stackRoom
  have upper := e.low
  refine ⟨by omega, fun rr member => Or.inr ?_⟩
  obtain rfl := List.mem_singleton.mp member
  simp only [signatureStageRegion]
  omega

theorem multiplySignature (e : Entry fr a p digest r s) {b m} (h : DigestProduct fr b m digest r s) :
    ∃ c n, Reaches .l105216 b m .l105256 c n ∧
      Products fr c n (digestScalar digest s) (signatureScalar r s) r := by
  have stack : Writable Extracted.programImage m (localSp fr - 8) 48 := by
    have room := e.stackRoom
    have bottom := e.low_toNat
    have start := pushNat e
    exact (e.stack.of_frame h.frame).sub (by omega) (by omega)
  have input : Readable m fr.r8 32 :=
    (e.upper.of_frame h.frame).readable.of_offsets (x := fr.rsp) (c := 360) (d := 8)
      e.sig rfl (by decide)
  have source : fr.r8 = localSp fr + 848 := by rw [e.sig]; unfold localSp; bv_omega
  obtain ⟨c, block, sp, si, dx, di, vp, cw, preserved⟩ :=
    signatureCallBlock b m (localSp fr) fr.r8 (congrArg (Value.get 64) h.sp)
      (congrArg (Value.get 64) h.sig) stack input source
  have args : CallRegisters fr c 8 288 416 := by
    refine ⟨sp, (preserved 22 (by decide)).trans h.df, si, dx, di, ?_,
      congrArg Value.width ((preserved 39 (by decide)).trans h.mxcsr),
      congrArg Value.width ((preserved 50 (by decide)).trans h.ftw),
      congrArg Value.width ((preserved 51 (by decide)).trans h.fcw)⟩
    intro ⟨i, _⟩ live
    simp only [List.mem_cons, List.not_mem_nil, or_false] at live
    rcases live with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cw
    · exact congrArg Value.width ((preserved 3 (by decide)).trans h.dst)
    · exact congrArg Value.width ((preserved 5 (by decide)).trans h.rbp)
    · exact congrArg Value.width ((preserved 12 (by decide)).trans h.uPtr)
    · exact congrArg Value.width ((preserved 13 (by decide)).trans h.sizeReg)
    · exact congrArg Value.width ((preserved 14 (by decide)).trans h.key)
    · exact congrArg Value.width vp
  let staged := signatureStage m (localSp fr) fr.r8
  have stagedFrame : RamWriteFrame m staged [signatureStageRegion fr] := signatureStageFrame e m
  have whole := h.frame.trans stagedFrame (signatureStageWithin e)
  have tag : memLoad staged (localSp fr - 8) 64 = 0x105256 := by
    unfold staged signatureStage
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have inputs := e.scalarWords_of_frame h.frame
  have lhs : WordsAt staged (slot fr 8) 64 (scalarWords r) := signatureStageWords inputs.1
  have rhs : WordsAt staged (slot fr 288) 64 (scalarWords (Curve.inverse domain.n s)) :=
    h.inverseAt.of_frame stagedFrame (by decide) (signatureStageOutside e (by decide) (by decide))
  obtain ⟨d, n, run, done_⟩ := invoke e block args whole tag
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    e.bounds.2.1 (inverseBound s) lhs rhs
  have keepReg (i : Fin 53) (hi : i.val ∈ [3, 5, 12, 13, 14, 22, 39, 50, 51]) :
      d[i] = b[i] := by
    apply (done_.keep i ?_).trans (preserved i hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  have keepSaved (off : Nat) (lo : 448 ≤ off) (hi : off + 8 ≤ 488)
      {addr value : BitVec 64} (atSlot : slot fr off = addr)
      (saved : memLoad m addr 64 = value) : memLoad n addr 64 = value := by
    have unchanged : memLoad n (slot fr off) 64 = memLoad m (slot fr off) 64 :=
      (done_.frame.memLoad_eq (outsideWrites e hi (by decide) (Or.inr lo))).trans
        (stagedFrame.memLoad_eq (signatureStageOutside e (by omega) hi))
    rw [atSlot] at unchanged
    exact unchanged.trans saved
  refine ⟨d, n, run, ?_⟩
  refine {
    sp := done_.sp
    dst := (keepReg 3 (by decide)).trans h.dst
    rbp := (keepReg 5 (by decide)).trans h.rbp
    df := (keepReg 22 (by decide)).trans h.df
    mxcsr := (keepReg 39 (by decide)).trans h.mxcsr
    ftw := (keepReg 50 (by decide)).trans h.ftw
    fcw := (keepReg 51 (by decide)).trans h.fcw
    rbx := keepSaved 448 (by decide) (by decide) (by unfold slot localSp; bv_omega) h.rbx
    r12 := keepSaved 456 (by decide) (by decide) (by unfold slot localSp; bv_omega) h.r12
    r13 := keepSaved 464 (by decide) (by decide) (by unfold slot localSp; bv_omega) h.r13
    r14 := keepSaved 472 (by decide) (by decide) (by unfold slot localSp; bv_omega) h.r14
    r15 := keepSaved 480 (by decide) (by decide) (by unfold slot localSp; bv_omega) h.r15
    frame := done_.whole
    key := (keepReg 14 (by decide)).trans h.key
    uPtr := (keepReg 12 (by decide)).trans h.uPtr
    vPtr := (done_.keep 15 (by decide)).trans vp
    uAt := ?_
    vAt := done_.words
    rAt := ?_ }
  · exact (h.uAt.of_frame stagedFrame (by decide) (signatureStageOutside e (by decide) (by decide))).of_frame
      done_.frame (by decide) (outsideWrites e (by decide) (by decide) (by decide))
  · exact (h.rAt.of_frame stagedFrame (by decide) (signatureStageOutside e (by decide) (by decide))).of_frame
      done_.frame (by decide) (outsideWrites e (by decide) (by decide) (by decide))

end K256.Proofs.Verify.Core
