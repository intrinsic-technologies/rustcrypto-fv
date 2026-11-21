import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Return
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Operands
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Routine
import K256.Proofs.Verify.Core.Lincomb.Prepare.Split.Calls.Blocks

namespace K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Multiply.Split.Caller (Site)

private theorem retainedFrom (s : Site) (k : Nat) {kv : Nat × Nat} (h : kv ∈ retained s k) :
    kv ∈ results s.prev k ∧ kv.1 + 32 ≤ 696 ∧
    (kv.1+32 ≤ destination s ∨ destination s+32 ≤ kv.1) := by
  cases s <;> simp only [retained,List.mem_singleton,List.not_mem_nil] at h
  all_goals first | contradiction | subst kv
  all_goals refine ⟨?_,by dsimp only; decide,by dsimp only; decide⟩
  all_goals first | exact .head _ | exact .tail _ (.head _)

private theorem Operand.pushed {a : Registers} {m n : Ram} {sp p : BitVec 64} {site : Site} {v : Nat}
    (e : RoutineEntry a m sp 0x558) (op : Operand site sp n p v) :
    WordsAt (memStore n (frameSp sp-8) (ret site)) p 64 (scalarWords v) := by
  have read := op.read.low
  have sep := op.stack
  apply op.words.write_apart
  apply RangeApart.of_toNat
  · change (frameSp sp-8).toNat+8 ≤ 2^64
    split_bounds e
  · change p.toNat+32 ≤ 2^64
    omega
  · change (frameSp sp-8).toNat+8 ≤ p.toNat ∨ p.toNat+32 ≤ (frameSp sp-8).toNat
    omega

theorem advance (site : Site) (later : site ≠ .roundFirst)
    {a b : Registers} {m n : Ram} {sp src scalar tables digits : BitVec 64} {k : Nat}
    (entry : RoutineEntry a m sp 0x558) (bound : k < domain.n)
    (words : WordsAt m scalar 64 (scalarWords k)) (scalarRead : Readable m scalar 32)
    (scalarApart : Outside [scratch sp 0x558] scalar 32)
    (s : Returned site.prev a m sp src scalar tables digits b n)
    (old : Stored sp n (results site.prev k)) :
    ∃ c q, Reaches (pc site) b n (afterPc site) c q ∧
      Returned site a m sp src scalar tables digits c q ∧ Stored sp q (results site k) := by
  obtain ⟨_,hw,dh,_⟩ := bounds site
  have win := entry.stack.of_frame s.frame
  have pushWrite : Writable Extracted.programImage n (frameSp sp-8) 8 :=
    win.sub (by split_bounds entry) (by split_bounds entry)
  obtain ⟨c,call,regs⟩ := callBlock site later s pushWrite
  have push := pushFoot (n := n) entry site
  have whole := s.frame.trans push (writesWithin entry site)
  have tag := memLoad_memStore_same n (frameSp sp-8) (ret site) (by decide) (by decide)
  have win' := entry.stack.of_frame whole
  have child := regs.entry entry whole tag
  obtain ⟨x,y⟩ := operands site later entry s.frame words scalarRead scalarApart old
  have wr : Writable Extracted.programImage _ (slot sp (destination site)) 32 :=
    win'.sub (by split_bounds entry) (by split_bounds entry)
  obtain ⟨out,exec,post,w,args⟩ := execute site child regs.di regs.si regs.dx regs.args regs.order bound
    (x.read.of_frame push) (y.read.of_frame push) wr (by split_bounds entry) (by
      intro q h
      rcases List.mem_cons.mp h with rfl|h
      · exact ⟨x.stack,x.dest⟩
      · obtain rfl := List.mem_singleton.mp h
        exact ⟨y.stack,y.dest⟩) (x.pushed entry) (y.pushed entry)
  refine ⟨out.values,out.store,reachesCall call exec (post.tag.trans (congrArg (fun r => some (Value.mk 64 r)) tag)),
    afterReturn site entry s.toSplitFrame regs push post args,?_⟩
  intro kv h
  rcases List.mem_cons.mp h with h|h
  · subst kv
    exact w
  · obtain ⟨mem,hi,sep⟩ := retainedFrom site k h
    exact (old kv mem).of_frame (push.trans post.frame (callWithin entry site)) (by decide)
      (outsideLocal entry site kv.1 32 hi sep)

end K256.Proofs.Verify.Core.Lincomb.Prepare.SplitCalls
