import K256.Proofs.Verify.Core.Lincomb.Recode.BackEdge

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

private structure PaddingRegisters (a b : Registers) (sp dst : BitVec 64)
    (i s c j : Nat) : Prop where
  stack : b[4] = ⟨64,sp-136⟩
  width : b[12] = ⟨64,5⟩
  index : b[15] = ⟨64,BitVec.ofNat 64 i⟩
  stride : b[5] = ⟨64,BitVec.ofNat 64 s⟩
  carry : b[13] = ⟨64,BitVec.ofNat 64 c⟩
  saved : ControlSaved a b
  remaining : b[0] = ⟨64, BitVec.ofNat 64 (257-i)⟩
  digit : b[2] = ⟨64, BitVec.ofNat 64 j⟩
  resultLength : b[1] = ⟨64, BitVec.ofNat 64 (i+s)⟩
  offset : b[14] = ⟨64, digitAddr dst i⟩

private abbrev paddingLabel (s j : Nat) : Label := if j < s then .l110920 else .l110932

private theorem paddingStep {a b : Registers} {m : Ram} {sp dst : BitVec 64} {i s c j : Nat}
    (regs : PaddingRegisters a b sp dst i s c j)
    (limit : i+s ≤ 128) (stride : s ≤ 5) (next : j < s)
    (w : Writable Extracted.programImage m dst 257) :
    ∃ r, Continues .l110920 b m (paddingLabel s (j+1)) r
      (memStore m (digitAddr dst (i+j)) (0 : BitVec 8)) ∧
      PaddingRegisters a r sp dst i s c (j+1) := by
  have count : b[0].get 64 = BitVec.ofNat 64 (257-i) := congrArg (Value.get 64) regs.remaining
  have idx : b[2].get 64 = BitVec.ofNat 64 j := congrArg (Value.get 64) regs.digit
  have dest : b[14].get 64 = digitAddr dst i := congrArg (Value.get 64) regs.offset
  have skip : b[5].get 64 = BitVec.ofNat 64 s := congrArg (Value.get 64) regs.stride
  have avail : (cmpSpec (BitVec.ofNat 64 (257-i)) (BitVec.ofNat 64 j)).ZF = false :=
    (cmpNatZF (by omega : 257-i < 2^64) (by omega : j < 2^64)).trans (decide_eq_false (by omega))
  have inc : BitVec.ofNat 64 j + 1 = BitVec.ofNat 64 (j+1) := by rw [BitVec.ofNat_add]; rfl
  have ptr : digitAddr dst i + BitVec.ofNat 64 j = digitAddr dst (i+j) := by
    rw [digitAddr, BitVec.add_assoc, ← BitVec.ofNat_add]
  have ok : StoreOk Extracted.programImage m (digitAddr dst (i+j)) 1 0x110925 5 :=
    storeGuard (off := 0) (writableDigit w (by omega)) code_l110925 (by decide)
  have finish : (cmpSpec (BitVec.ofNat 64 s) (BitVec.ofNat 64 (j+1))).ZF =
      decide (s = j+1) := cmpNatZF (by omega : s < 2^64) (by omega : j+1 < 2^64)
  have route : ∃ p r : Registers,
      program.runBlock machine ⟨.l110920,b,m⟩ = .jump ⟨.l110925,p,m⟩ ∧
      program.runBlock machine ⟨.l110925,p,m⟩ =
        .jump ⟨paddingLabel s (j+1),r,memStore m (digitAddr dst (i+j)) (0 : BitVec 8)⟩ ∧
      PaddingRegisters a r sp dst i s c (j+1) := by
    by_cases more : j+1 < s
    all_goals
      refine ⟨?_, ?_, ?first, ?second, ?post⟩
      case first =>
        cfg_eval [idx, count, avail]
        rfl
      case second =>
        unfold digitAddr at ptr ok
        cfg_eval [idx, dest, skip, inc, ptr, ok, finish]
        have condition : (!decide (s = j+1)) = decide (j+1 < s) := by
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
          omega
        rw [condition]
        first
        | rw [decide_eq_true more, ite_eq_left (by rfl), show paddingLabel s (j+1) = .l110920 from ite_eq_left more]
        | rw [decide_eq_false more, ite_eq_right (by decide : false ≠ true),
            show paddingLabel s (j+1) = .l110932 from ite_eq_right more]
      case post =>
        refine ⟨regs.stack, regs.width, regs.index, regs.stride, regs.carry, ?_,
          regs.remaining, rfl, regs.resultLength, regs.offset⟩
        intro ⟨k,hk⟩ h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl
        · exact regs.saved 22 (by decide)
        · exact regs.saved 39 (by decide)
        · exact regs.saved 50 (by decide)
        · exact regs.saved 51 (by decide)
  obtain ⟨p,r,pstep,rstep,post⟩ := route
  exact ⟨r,(continueJump pstep).trans (continueJump rstep),post⟩

private theorem paddingLoop {a : Registers} {sp dst : BitVec 64} {i s c : Nat} {ds : List Int}
    (limit : i+s ≤ 128) (stride : s ≤ 5) (length : ds.length = i+1)
    (j : Nat) (lower : 1 ≤ j) (upper : j ≤ s)
    {b : Registers} {m : Ram} (regs : PaddingRegisters a b sp dst i s c j)
    (w : Writable Extracted.programImage m dst 257) (digits : DigitBytes m dst ds) :
    ∃ r n, Continues (paddingLabel s j) b m .l110932 r n ∧
      PaddingRegisters a r sp dst i s c s ∧ DigitBytes n dst ds ∧
      RamWriteFrame m n [⟨dst.toNat,257⟩] := by
  by_cases done : j = s
  · subst j
    exact ⟨b,m,by rw [show paddingLabel s s = .l110932 from ite_eq_right (Nat.lt_irrefl _)]; exact fun _ h => h,
      regs,digits,.refl _ _⟩
  · have next : j < s := by omega
    obtain ⟨r,step,post⟩ := paddingStep regs limit stride next w
    have len : i+j < 257 := by omega
    have frame := storeDigitFrame w len (0 : BitVec 8)
    have zero := digitBytes_zeroStore digits w len (by omega)
    obtain ⟨out,n,tail,last,values,noMore⟩ :=
      paddingLoop limit stride length (j+1) (by omega) (by omega) post (w.of_frame frame) zero
    refine ⟨out,n,?_,last,values, frame.trans noMore (fun reg h => ⟨reg,h,Nat.le_refl _,Nat.le_refl _⟩)⟩
    simpa only [paddingLabel, next, ite_true] using step.trans tail
termination_by s-j
decreasing_by omega

theorem padOddDigit {a b : Registers} {m : Ram} {sp dst : BitVec 64} {i w : Nat} {ds : List Int}
    (regs : OddRegisters a b sp dst i w) (writable : Writable Extracted.programImage m dst 257)
    (more : 2 ≤ Naf.skip (128-i) w) (bound : i + Naf.skip (128-i) w ≤ 128)
    (length : ds.length = i+1) (digits : DigitBytes m dst ds) :
    let s := Naf.skip (128-i) w
    ∃ r n, Continues .l110912 b m .l110833 r n ∧
      IndexAdvance a r sp i s (Naf.carry w) ∧ DigitBytes n dst (ds ++ List.replicate (s-1) 0) ∧
      RamWriteFrame m n [⟨dst.toNat,257⟩] := by
  let s := Naf.skip (128-i) w
  have len : b[14].get 64 = BitVec.ofNat 64 i := congrArg (Value.get 64) regs.length
  have stride : b[5].get 64 = BitVec.ofNat 64 s := congrArg (Value.get 64) regs.skip
  have dstGet : b[6].get 64 = dst := congrArg (Value.get 64) regs.dest
  have lenAdd : BitVec.ofNat 64 i + BitVec.ofNat 64 s = BitVec.ofNat 64 (i+s) :=
    (BitVec.ofNat_add i s).symm
  have begin : ∃ q, program.runBlock machine ⟨.l110912,b,m⟩ = .jump ⟨.l110920,q,m⟩ ∧
      PaddingRegisters a q sp dst i s (Naf.carry w) 1 := by
    refine ⟨?_, ?step, ?post⟩
    case step =>
      cfg_eval [len, stride, dstGet, lenAdd]
      rfl
    case post =>
      refine ⟨regs.stack, regs.width, regs.bitIndex, regs.skip, regs.carry, ?_, regs.room, rfl, ?_, ?_⟩
      · intro ⟨j,hj⟩ keep
        simp only [List.mem_cons, List.not_mem_nil, or_false] at keep
        rcases keep with rfl | rfl | rfl | rfl
        · exact regs.saved 22 (by decide)
        · exact regs.saved 39 (by decide)
        · exact regs.saved 50 (by decide)
        · exact regs.saved 51 (by decide)
      · first | rfl | exact congrArg (fun x : BitVec 64 => (⟨64,x⟩ : Value)) lenAdd
      · change (⟨64,BitVec.ofNat 64 i + dst⟩ : Value) = _
        rw [BitVec.add_comm]
  obtain ⟨q,step,init⟩ := begin
  have sBound : s ≤ 5 := Nat.min_le_left ..
  obtain ⟨last,n,tail,post,finalDigits,frame⟩ :=
    paddingLoop bound sBound length 1 (by omega) (by omega) init writable digits
  have continuation : Continues .l110920 q m .l110932 last n := by
    have label : paddingLabel (Naf.skip (128-i) w) 1 = .l110920 := ite_eq_left (by omega)
    rwa [label] at tail
  have finalValue : last[1].get 64 = BitVec.ofNat 64 (i+s) := congrArg (Value.get 64) post.resultLength
  have close : ∃ out, program.runBlock machine ⟨.l110932,last,n⟩ = .jump ⟨.l110833,out,n⟩ ∧
      IndexAdvance a out sp i s (Naf.carry w) := by
    refine ⟨?_, ?step, ?post⟩
    case step =>
      cfg_eval [finalValue]
      rfl
    case post =>
      refine ⟨post.stack,post.width,post.index,rfl,post.stride,
        post.carry,?_⟩
      intro ⟨j,hj⟩ keep
      simp only [List.mem_cons,List.not_mem_nil,or_false] at keep
      rcases keep with rfl | rfl | rfl | rfl
      · exact post.saved 22 (by decide)
      · exact post.saved 39 (by decide)
      · exact post.saved 50 (by decide)
      · exact post.saved 51 (by decide)
  obtain ⟨out,lastStep,result⟩ := close
  exact ⟨out,n,(continueJump step).trans (continuation.trans (continueJump lastStep)),result,
    digitBytes_append_zero finalDigits,frame⟩

end K256.Proofs.Verify.Core.Lincomb.Recode
