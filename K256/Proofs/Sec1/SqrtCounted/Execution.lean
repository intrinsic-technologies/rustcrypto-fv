import K256.Proofs.Sec1.SqrtCounted.Iterate
import K256.Proofs.Sec1.SqrtCounted.Copy
import K256.Proofs.Sec1.SqrtCounted.Call

namespace K256.Proofs.Sec1.SqrtCounted

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine LIR
open Common.Field Sqrt

private theorem round (site : SquareLoop) {code : CodeMap} {fr : Activation} {base : Word}
    (cover : ∀ x ∈ fnCode, x ∈ code) (hbase : base = fr.rsp - 440)
    (apart : base.toNat + 80 ≤ 0x1145f0 ∨ 0x1148c4 ≤ base.toNat - 112)
    {a m n words} (hs : LoopState site code fr base (n+1) words a m) (hn : n < 2^64) :
    ∃ b m', Parser.Reaches code site.head a m (if n = 0 then site.exit else site.head) b m' ∧
      LoopState site code fr base n (squareWords words) b m' ∧
      WordsAt m' (base + 40) 64 (squareWords words) ∧ Saved site a b ∧
      RamWriteFrame m m' [roundStack base] := by
  obtain ⟨rsp, df, mx, ftw, fcw, stack, room, al⟩ := loopGeometry hbase hs.frame
  obtain ⟨b, mb, run, rb, kb, out, fb, vb⟩ := call site cover rsp hs.src hs.dst df hs.widths mx ftw fcw
    stack room al apart hs.input hs.volatile
  have countMem : site.countReg.val ∈ [3,5,12,13,14,15,22,39,50,51] := by cases site <;> decide
  have cnt := (kb site.countReg countMem).trans hs.counter
  obtain ⟨c, mc, jump, rc, kc, keep, win, wout, vc, fc⟩ := copyBlock site cover
    (congrArg (Value.get 64) (rb.trans rsp)) (stack.of_frame fb) (congrArg (Value.get 64) cnt) out
  have dec : (⟨64, BitVec.ofNat 64 (n+1)⟩ : Value).get 64 - 1 = BitVec.ofNat 64 n := by
    change (BitVec.ofNat 64 (n+1)) - 1 = _
    rw [BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have zero : BitVec.ofNat 64 n = 0 ↔ n = 0 := by
    constructor
    · intro e
      have h := congrArg BitVec.toNat e
      change n % 2^64 = 0 at h
      rwa [Nat.mod_eq_of_lt hn] at h
    · rintro rfl
      rfl
  have lab : (if (⟨64, BitVec.ofNat 64 (n+1)⟩ : Value).get 64 - 1 = 0 then site.exit else site.head) =
      (if n = 0 then site.exit else site.head) := by rw [dec]; simp only [zero]
  rw [lab] at jump
  have cn : c[site.countReg] = ⟨64, BitVec.ofNat 64 n⟩ := by rw [dec] at kc; exact kc
  have saved : Saved site a c := fun i hi ne => (keep i hi ne).trans (kb i hi)
  have frame := fb.trans fc (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have frameRegs (i : Fin Reg.count) (hi : i.val ∈ [4,22,39,50,51]) : c[i] = a[i] := by
    rcases i with ⟨i, lt⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl
    · exact rc.trans rb
    all_goals exact saved _ (by decide +revert) (by cases site <;> decide +revert)
  refine ⟨c, mc, run.trans (Parser.reaches_jump jump), ⟨loopFrame_of_frame hbase hs.frame frameRegs frame,
    ?_, ?_, cn, ?_, win, fun i h => vc i h (vb i h)⟩, wout, saved, frame⟩
  · rw [saved site.srcReg (by cases site <;> decide) (by cases site <;> decide)]
    exact hs.src
  · rw [saved site.dstReg (by cases site <;> decide) (by cases site <;> decide)]
    exact hs.dst
  · intro i hi
    by_cases he : i = site.countReg
    · subst i
      rw [cn]
    · rw [saved i (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢; omega) he]
      exact hs.widths i hi

theorem executeRounds (site : SquareLoop) {code : CodeMap} {fr : Activation} {base : Word}
    {a : Values Value Reg.count} {m : Ram} {words : Limbs}
    (cover : ∀ x ∈ fnCode, x ∈ code) (hbase : base = fr.rsp - 440)
    (apart : base.toNat + 80 ≤ 0x1145f0 ∨ 0x1148c4 ≤ base.toNat - 112)
    (atoms : Atom.All code a m (Fn115950.frameAt site.head fr))
    (src : a[site.srcReg].get 64 = base) (dst : a[site.dstReg].get 64 = base + 40)
    (counter : a[site.countReg] = ⟨64, BitVec.ofNat 64 site.roundCount⟩)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → a[i].width = 64)
    (input : WordsAt m base 64 words)
    (volatile : ∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → a[i].width = 64) :
    ∃ b m', Parser.Reaches code site.head a m site.exit b m' ∧
      Atom.All code b m' (Fn115950.frameAt site.exit fr) ∧
      b[site.countReg] = ⟨64,0⟩ ∧ Saved site a b ∧
      WordsAt m' base 64 (SqrtChain.iter squareWords site.roundCount words) ∧
      WordsAt m' (base+40) 64 (SqrtChain.iter squareWords site.roundCount words) ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → b[i].width = 64) ∧
      RamWriteFrame m m' [roundStack base] := by
  rw [headFrame] at atoms
  have cnt : site.roundCount - 1 + 1 = site.roundCount := by cases site <;> decide
  have state : LoopState site code fr base (site.roundCount-1+1) words a m := by
    rw [cnt]
    exact ⟨atoms, src, dst, counter, widths, input, volatile⟩
  obtain ⟨b, m', reach, hs, out, kept, frame⟩ := iterate (round site cover hbase apart)
    (site.roundCount-1) (by cases site <;> decide) state
  rw [cnt] at hs out
  rw [exitFrame]
  exact ⟨b, m', reach, hs.frame, hs.counter, kept, hs.input, out, hs.volatile, frame⟩

end K256.Proofs.Sec1.SqrtCounted
