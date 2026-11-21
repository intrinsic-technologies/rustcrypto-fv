import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.LastFold
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Entry
import K256.Proofs.Generate.Generator.Entry

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR Common.Invert.LinearCombination

private theorem resumeBarrier {a : Registers} {m : Ram} {next : Label} {pc : BitVec 64}
    {o final : Output Value Ram Reg.count}
    (run : program.runBlock (dialect Extracted.programImage) ⟨.l127d50,a,m⟩ = .returned o)
    (tag : o.tag = some ⟨64,pc⟩)
    (tail : program.Exec (dialect Extracted.programImage) ⟨⟨next,o.values,o.store⟩,[]⟩ final) :
    program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,a,m⟩,[callFrame next pc]⟩ final := by
  refine .next (next := ⟨⟨next,o.values,o.store⟩,[]⟩) ?_ tail
  simp only [Program.step, run, Transfer.next]
  rw [show (callFrame next pc).Accepts (dialect Extracted.programImage) o.tag = true by
    rw [tag]; change decide ((⟨64,pc⟩ : Value) = ⟨64,pc⟩) = true; simp]
  rfl

private theorem enterBarrier {a b : Registers} {m n : Ram} {l next : Label} {pc : BitVec 64}
    {out : Output Value Ram Reg.count}
    (run : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ =
      .call ⟨.l127d50,b,n⟩ (callFrame next pc))
    (tail : program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,b,n⟩,[callFrame next pc]⟩ out) :
    program.Exec (dialect Extracted.programImage) ⟨⟨l,a,m⟩,[]⟩ out :=
  .next (by simp only [Program.step, run, Transfer.next]) tail

syntax "reduce_block" " using " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| reduce_block using $incl:term [$ls,*]) =>
    `(tactic| (
      arithmetic_segment using $incl [$ls,*, Lift.reduceAddOffset, Lift.reduceSubOffset,
      Lift.reduceAddNeg, Lift.reduceSubNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero]
      all_goals repeat' (refine Eq.trans (ite_eq_left ?_) ?_; constructor; slot_guard using $incl; decide)
      all_goals rfl))

structure Candidates (fr : Activation) (a : Registers) (m : Ram) (r d : Limbs) (high borrow : Bool) : Prop where
  sp : a[4].get 64 = fr.rsp - 128
  arg : a[7].get 64 = carryWord high
  sign : a[13].get 64 = -carryWord borrow
  diff₁ : a[12].get 64 = d.l1
  diff₂ : a[14].get 64 = d.l2
  diff₃ : a[5].get 64 = d.l3
  raw₂ : a[15].get 64 = r.l2
  raw₃ : a[3].get 64 = r.l3
  raw₀ : memLoad m (fr.rsp - 104) 64 = r.l0
  raw₁ : memLoad m (fr.rsp - 64) 64 = r.l1
  diff₀ : memLoad m (fr.rsp - 88) 64 = d.l0
  ret : memLoad m (fr.rsp - 128) 64 = 0x11b864

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem finish {fr : Activation} {a : Registers} {m : Ram} {r d : Limbs} {high borrow : Bool}
    (atoms : Atom.All Extracted.programImage a m (Fn11b510.frameAt .l11b864 fr).tail)
    (widths : ParseSignature.ArgumentWidths a)
    (vals : Candidates fr a m r d high borrow)
    (output : Writable Extracted.programImage m fr.rdi 32)
    (above : fr.rsp.toNat + 8 ≤ fr.rdi.toNat) :
    ∃ out, program.Exec (dialect Extracted.programImage)
      ⟨⟨.l127d50, a, m⟩, [callFrame .l11b864 0x11b864]⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store
        (Fn11b510.doneAt fr) ∧ ParseSignature.ArgumentWidths out.values ∧
      WordsAt out.store fr.rdi 64 (Common.Invert.ModularShift.words (if !borrow || high then d else r)) ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - 129,129⟩,⟨fr.rdi.toNat,32⟩] := by
  simp only [Fn11b510.frameAt, Fn11b510.frameAtG1, List.tail_cons, Atom.All, Atom.Holds] at atoms
  obtain ⟨df,mx,ftw,fcw,di,bx,r12,r13,r14,r15,bp,retRead,ret,retLow,stack,room,align,_⟩ := atoms
  obtain ⟨sp,arg,sign,d1,d2,d3,r2,r3,r0,r1,d0,tag⟩ := vals
  have upper := retRead.low
  have dest := output.readable.low
  refine ⟨?out, ?run, ?tag, ?done_, ?widths, ?words, ?frame⟩
  case run =>
    apply resumeBarrier
    · reduce_block using code_l127d50 [sp, arg, tag]
    · rfl
    apply enterBarrier (next := .l11b874) (pc := 0x11b874)
    · reduce_block using code_l11b864 [sp, sign]
    apply resumeBarrier
    · reduce_block using code_l127d50 [sp, arg, tag]
    · rfl
    apply enterBarrier (next := .l11b880) (pc := 0x11b880)
    · reduce_block using code_l11b874 [sp, sign]
    apply resumeBarrier
    · reduce_block using code_l127d50 [sp, arg, tag]
    · rfl
    apply enterBarrier (next := .l11b88c) (pc := 0x11b88c)
    · reduce_block using code_l11b880 [sp, sign]
    apply resumeBarrier
    · reduce_block using code_l127d50 [sp, arg, tag]
    · rfl
    refine .done ?_
    unfold Program.step
    generate_block [sp, di, d1, d2, d3, r2, r3, Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg, BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero]
    segment_words [di, bx, r12, r13, r14, r15, bp, ret, retLow, d0, r0, r1, and_true]
    repeat' (refine Eq.trans (congrArg _ (ite_eq_left ?_)) ?_; slot_guard using code_l11b88c)
    rfl
  case tag => rfl
  case done_ =>
    refine ⟨rfl, df, ?_, ?_, ?_, ?_, ?_, ?_, mx, ftw, fcw, trivial⟩
    all_goals segment_words [bx,bp,r12,r13,r14,r15]
    all_goals rfl
  case widths =>
    intro ⟨i,hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact widths ⟨_,hi⟩ (by decide +revert)
  case frame =>
    dsimp only
    have depth : 129 ≤ fr.rsp.toNat := by omega
    repeat' refine RamWriteFrame.memStore ?_ _ ?_
    exact RamWriteFrame.refl _ _
    all_goals simp only [InRegions, InRegion, List.mem_cons, List.not_mem_nil, or_false,
      exists_eq_or_imp, exists_eq_left] <;> bv_omega
  case words =>
    intro i hi
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals
      simp only [wordAddr,Nat.reduceDiv,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_zero]
      segment_words [d0,r0,r1]
      cases borrow <;> cases high <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction
