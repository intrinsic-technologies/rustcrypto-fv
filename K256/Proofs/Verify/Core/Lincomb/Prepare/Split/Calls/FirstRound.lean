import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Routine
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.FirstRound.Entry

namespace K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Multiply.Split.Caller (Site)

set_option maxHeartbeats 1200000 in
theorem firstRound {a : Registers} {m : Ram} {sp src scalar tables digits : BitVec 64}
    {k : Nat} (entry : RoutineEntry a m sp 0x558)
    (di : a[7] = ⟨64, src⟩) (si : a[6] = ⟨64, scalar⟩) (dx : a[2] = ⟨64, tables⟩)
    (cx : a[1] = ⟨64, digits⟩) (bound : k < domain.n)
    (words : WordsAt m scalar 64 (scalarWords k)) (scalarRead : Readable m scalar 32)
    (scalarApart : Outside [scratch sp 0x558] scalar 32) :
    ∃ b n, Reaches .l10f150 a m .l10f188 b n ∧
      Returned .roundFirst a m sp src scalar tables digits b n ∧
      WordsAt n (slot sp 56) 64 (scalarWords (Site.roundFirst.value k)) := by
  obtain ⟨c,call,regs⟩ := roundBlock entry di si dx cx
  obtain ⟨b,frame⟩ := roundSavedFrame (src := src) (digits := digits) entry regs
  let n := roundFrame a m sp src digits
  have push := pushFoot (n := n) entry .roundFirst
  have whole := frame.frame.trans push (writesWithin entry .roundFirst)
  have win := entry.stack.of_frame whole
  have tag := memLoad_memStore_same n (frameSp sp-8) (ret .roundFirst) (by decide) (by decide)
  have child := regs.entry entry whole tag
  have param := Generate.Generator.Multiply.Split.parameterAt child.image
    (p := 0x202200) (x := Generate.Curve.g1) (by decide +kernel)
  have sep := scalarApart.2 _ (.head _)
  have psep := param.apart win (by decide)
  have wr : Writable Extracted.programImage _ (slot sp 56) 32 :=
    win.sub (by split_bounds entry) (by split_bounds entry)
  obtain ⟨out,run,post,w,args⟩ := execute .roundFirst child regs.di regs.si regs.dx regs.args
    regs.order (d := k) bound (scalarRead.of_frame whole) param.readable wr (by dsimp only [destination]; split_bounds entry)
    (by
      intro p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl <;> constructor <;> dsimp only [left,right,destination,Site.window] <;> split_bounds entry)
    (words.of_frame whole (by decide) scalarApart) param.words
  exact ⟨_,_,reachesCall call (execRoundArgs run)
    (post.tag.trans (congrArg (fun r => some (Value.mk 64 r)) tag)),
    afterReturn .roundFirst entry frame regs push post args,w⟩

end K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls
