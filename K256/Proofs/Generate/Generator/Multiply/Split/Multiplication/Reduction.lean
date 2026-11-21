import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Terminal
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.ReplayBarrier
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.WordEquations
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Entry
import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Folds
import K256.Proofs.Generate.Generator.Multiply.Split.Contract
import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.Generate.LIR.Fn11b510.Frame

import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Finish

namespace K256.Proofs.Generate.Generator.Multiply.Split

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2500000 in
theorem reduceWide {fr : Activation} {a : Registers} {m : Ram} {w : Vector (BitVec 64) 8}
    (atoms : Atom.All Extracted.programImage a m (Fn11b510.frameAt .l11b510 fr))
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (zero : fr.rdx = 0) (input : Readable m fr.rsi 64)
    (output : Writable Extracted.programImage m fr.rdi 32)
    (above : fr.rsp.toNat + 8 ≤ fr.rsi.toNat)
    (apart : fr.rsi.toNat + 64 ≤ fr.rdi.toNat)
    (words : WordsAt m fr.rsi 64 w) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l11b510, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store
        (Fn11b510.doneAt fr) ∧ ParseSignature.ArgumentWidths out.values ∧
      WordsAt out.store fr.rdi 64 (scalarWords ((wideValue w) % domain.n)) ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - 0x81, 0x81⟩, ⟨fr.rdi.toNat, 32⟩] := by
  have _ := image
  obtain ⟨b, m₁, enter, saved, modulus₁, modulus₀, frame₁⟩ := reduceEntry atoms zero
  obtain ⟨c, m₂, initPath, ready, complement₀, slot₂, slot₃, slot₁, frame₂⟩ :=
    reduceConstants saved modulus₁ modulus₀
  have stack := frame₁.trans frame₂ (fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)
  have depth : 129 ≤ fr.rsp.toNat := by
    have h := atoms
    simp only [Fn11b510.frameAt,Fn11b510.frameAtG1,Atom.All,Atom.Holds] at h
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,room,_⟩ := h
    omega
  have keptWords : WordsAt m₂ fr.rsi 64 w := by
    apply WordsAt.of_frame words stack (by decide)
    have hi := input.low
    refine ⟨by change fr.rsi.toNat + 64 ≤ 2^64; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    change fr.rsp.toNat - 129 + 129 ≤ fr.rsi.toNat
    omega
  have src₂ := input.of_frame stack
  have body :
      ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l11b5ba,c,m₂⟩ =
          .call ⟨.l127d50,b,n⟩ (callFrame .l11b864 0x11b864) ∧
        Atom.All Extracted.programImage b n (Fn11b510.frameAt .l11b864 fr).tail ∧
        ParseSignature.ArgumentWidths b ∧
        RamWriteFrame m₂ n [⟨fr.rsp.toNat - 129,129⟩] := by
    simp only [Fn11b510.frameAt, Fn11b510.frameAtG1, Atom.All, Atom.Holds] at ready
    obtain ⟨sp,df,bx,bp,si,r8,r12,r13,r14,r15,mx,ftw,fcw,ds,bs,s12,s13,s14,s15,s5,
      retRead,ret,retLow,stack,room,align,_⟩ := ready
    have g4 : c[4].get 64 = fr.rsp - 120 := congrArg (Value.get 64) sp
    have g6 : c[6].get 64 = fr.rsi := congrArg (Value.get 64) si
    have g9 : c[9].get 64 = 0x402da1732fc9bebf := congrArg (Value.get 64) complement₀
    have upper := retRead.low
    have srcEnd := src₂.low
    have w0 : memLoad m₂ fr.rsi 64 = w[0] := by simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using keptWords 0 (by decide)
    have w1 : memLoad m₂ (fr.rsi + 8) 64 = w[1] := keptWords 1 (by decide)
    have w2 : memLoad m₂ (fr.rsi + 16) 64 = w[2] := keptWords 2 (by decide)
    have w3 : memLoad m₂ (fr.rsi + 24) 64 = w[3] := keptWords 3 (by decide)
    have w4 : memLoad m₂ (fr.rsi + 32) 64 = w[4] := keptWords 4 (by decide)
    have w5 : memLoad m₂ (fr.rsi + 40) 64 = w[5] := keptWords 5 (by decide)
    have w6 : memLoad m₂ (fr.rsi + 48) 64 = w[6] := keptWords 6 (by decide)
    have w7 : memLoad m₂ (fr.rsi + 56) 64 = w[7] := keptWords 7 (by decide)

    refine Exists.intro ?nextRegs (Exists.intro ?nextMemory (And.intro ?run (And.intro ?saved (And.intro ?widths ?frame))))
    case run =>
      arithmetic_segment using code_l11b5ba [g4,g6,g9,slot₁,slot₂,slot₃,w0,w1,w2,w3,w4,w5,w6,w7,
        Lift.reduceAddOffset, Lift.reduceSubOffset, Lift.reduceAddNeg, Lift.reduceSubNeg,
        BitVec.reduceAdd, BitVec.reduceSub, BitVec.add_zero]
    case saved =>
      simp only [Fn11b510.frameAt, Fn11b510.frameAtG1, List.tail_cons, Atom.All, Atom.Holds]
      refine ⟨df,mx,ftw,fcw,?_,?_,?_,?_,?_,?_,?_,?read,?_,retLow,?win,room,align,trivial⟩
      case' read | win => slot_state region
      all_goals refine_norm [ds,bs,s12,s13,s14,s15,s5,ret]
    case widths =>
      intro ⟨i,hi⟩ hm
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    case frame => slot_state region
  obtain ⟨args,n,call,frameAtoms,widths,writes⟩ := body
  let r := Reduction.lastFold (Reduction.secondFold (Reduction.firstFold w))
  let d := Common.Invert.LinearCombination.subRaw r.1 Reduction.orderLimbs
  simp only [Fn11b510.frameAt,Fn11b510.frameAtG1,Atom.All,Atom.Holds] at ready
  obtain ⟨rsp,_,_,_,rsi,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,window,_⟩ := ready
  have upper : fr.rsi.toNat + 64 ≤ 2^64 := by have h := src₂.low; omega
  have all : Reduction.Replay.Segment c fr w b_l11b5ba Reduction.Replay.barrier := Reduction.Replay.allSegments (w := w) rsp rsi complement₀ depth above upper
  obtain ⟨last,final,hv,hm,bar⟩ :=
    Reduction.Replay.replayBarrier all window src₂ keptWords slot₂ slot₃ slot₁ call
  have vals := Reduction.Replay.barrierCandidates hv hm bar r d
    (Reduction.Replay.word478_eq w) (Reduction.Replay.word476_eq w)
    (Reduction.Replay.word393_eq w) (Reduction.Replay.word424_eq w) (Reduction.Replay.word455_eq w)
    (Reduction.Replay.word359_eq w) (Reduction.Replay.word362_eq w) (Reduction.Replay.word353_eq w)
    (Reduction.Replay.word356_eq w) (Reduction.Replay.word368_eq w)
  obtain ⟨out,tailRun,tag,done_,widths',dst,stored⟩ :=
    Reduction.finish frameAtoms widths vals ((output.of_frame stack).of_frame writes) (by omega)
  have run : program.Exec (dialect Extracted.programImage) ⟨⟨.l11b5ba,c,m₂⟩,[]⟩ out :=
    .next (by simp only [Program.step, call, Transfer.next]) tailRun
  have dst' : WordsAt out.store fr.rdi 64 (Reduction.resultWords w) := by
    change WordsAt _ _ _ (Common.Invert.ModularShift.words
      (if d.2 = 0 ∨ r.2 then d.1 else r.1))
    change WordsAt _ _ _ (Common.Invert.ModularShift.words
      (if !(d.2 != 0) || r.2 then d.1 else r.1)) at dst
    simpa only [Bool.or_eq_true, Bool.not_eq_true', bne_eq_false_iff_eq] using dst
  rw [Reduction.resultWords_eq] at dst'
  refine ⟨out,Program.Exec.of_sem ((enter.trans initPath).exec run.sem),tag,done_,widths',dst',?_⟩
  have tmp := stack.trans writes (fun r hr => ⟨r,hr,Nat.le_refl _,Nat.le_refl _⟩)
  apply ((RamWriteFrame.refl m _).trans tmp ?_).trans stored
  · exact fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_,List.mem_cons_self,Nat.le_refl _,Nat.le_refl _⟩

end K256.Proofs.Generate.Generator.Multiply.Split
