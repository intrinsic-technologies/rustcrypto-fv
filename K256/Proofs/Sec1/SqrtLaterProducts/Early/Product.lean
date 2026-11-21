import K256.Proofs.Sec1.SqrtLaterProducts.Early.Geometry
import K256.Proofs.Sec1.SqrtChainExecution.ProductCall

namespace K256.Proofs.Sec1.SqrtLaterProducts.Early

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution
open K256.Proofs.Sec1.LIR (lifted)

theorem productCallOfFrame {code fr a i args m} {child : lifted.Location} {ret : Word}
    (geo : Geometry code fr) (st : ProductState code fr a i.castSucc args m)
    (frameIn : StandardFrame code fr args m)
    (frameOut : LIR.Fn115950.frameAt squarePC[i] fr = LIR.Fn115950.frameAt .l116316 fr)
    (lab : child.label = .l1145f0)
    (rsp : child.arguments[4]'(by change 4 < Reg.count; decide) = ⟨64, fr.rsp - 440 - 8⟩)
    (rsi : child.arguments[6]'(by change 6 < Reg.count; decide) = ⟨64, fr.rsp - 440⟩)
    (rdi : child.arguments[7]'(by change 7 < Reg.count; decide) = ⟨64, fr.rsp - 440 + 40⟩)
    (control : ∀ j : Fin Reg.count, j.val ∈ [22,39,50,51] → child.arguments[j] = args[j])
    (widths : ∀ j : Fin Reg.count, j.val ∈ Activation.entryNumbers → child.arguments[j].width = 64)
    (writes : RamWriteFrame m child.store [scratchRegion (fr.rsp - 440)])
    (slot : memLoad child.store (fr.rsp - 440 - 8) 64 = ret)
    (retLow : ret.toNat < 2^32)
    (src : i.val ≠ 0 → child.arguments[(srcReg i).val].get 64 = fr.rsp - 440)
    (dst : i.val ≠ 0 → child.arguments[(dstReg i).val].get 64 = fr.rsp - 440 + 40)
    (saved : Atom.All code child.arguments child.store (savedAtoms i.succ (fr.rsp - 440) a))
    (input : WordsAt child.store (fr.rsp - 440) 64 (words a (2*(i.val+1)))) :
    ProductCall code fr a i child ret := by
  have win := window frameIn
  have hm := win.value
  have room := win.room
  obtain ⟨_, df, mx, ftw, fcw, _⟩ := id frameIn
  have df' := (control 22 (by decide)).trans df
  have mx' := (control 39 (by decide)).trans mx
  have ftw' := (control 50 (by decide)).trans ftw
  have fcw' := (control 51 (by decide)).trans fcw
  refine ⟨⟨lab, rsp, rsi, rdi, df', ?_, win.workspace.of_frame writes, slot, retLow,
    by omega, win.align, ?_, input⟩, ?_, saved, src, dst, preservedSource win geo st.source st.sourceRead writes,
    st.sourceRead.of_frame writes, st.destWrite.of_frame writes, extendWrites win st.writes writes⟩
  · intro ⟨j, hj⟩ h
    simp only [Sqrt.LiftedSquare.volatile, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact widths 1 (by decide)
      | exact widths 2 (by decide)
      | exact widths 8 (by decide)
      | exact widths 9 (by decide)
      | exact widths 3 (by decide)
      | exact widths 5 (by decide)
      | exact widths 12 (by decide)
      | exact widths 13 (by decide)
      | exact widths 14 (by decide)
      | exact widths 15 (by decide)
      | exact congrArg Value.width mx' |
        exact congrArg Value.width ftw' | exact congrArg Value.width fcw'
  · rcases geo.stackCode with h | h <;> omega
  · rw [frameOut]
    refine standardFrameOfWrites frameIn ?_ ?_ writes
    · simp only [callerArgs, Vector.getElem_set_self]
    · intro ⟨j, hj⟩ h
      have hne : 4 ≠ j := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        omega
      simpa only [callerArgs, Fin.getElem_fin, Vector.getElem_set_ne _ _ hne] using control ⟨j, hj⟩ h

theorem makeProductCall {code fr a i args m post offsets child frame ret}
    (geo : Geometry code fr) (st : ProductState code fr a i.castSucc args m)
    (frameIn : StandardFrame code fr args m)
    (frameOut : LIR.Fn115950.frameAt squarePC[i] fr = LIR.Fn115950.frameAt .l116316 fr)
    (retLow : ret.toNat < 2^32) (srcRegEq : srcReg i = 14)
    (bounded : ∀ off ∈ offsets, off.toNat ≤ 376)
    (entry : squareEntry args m (fr.rsp - 440) squarePC[i] ret (dstReg i) offsets post child frame)
    (save : ∀ regs scratch,
      Final.ScratchWrites m scratch (fr.rsp - 440) offsets →
      (∀ j : Fin Reg.count, j.val ∈ Activation.entryNumbers → regs[j].width = 64) →
      let m' := memStore scratch (fr.rsp - 440 - 8) ret
      post regs m' → WordsAt m' (fr.rsp - 440) 64 (words a (2*(i.val+1))) →
      Atom.All code regs m' (savedAtoms i.succ (fr.rsp - 440) a))
    (input : WordsAt child.store (fr.rsp - 440) 64 (words a (2*(i.val+1)))) :
    frame = Wrapper.callFrame squarePC[i] ret ∧ ProductCall code fr a i child ret := by
  obtain ⟨regs, scratch, rfl, rfl, rsp, rsi, rdi, dst, src, control, widths, writes, hpost⟩ := entry
  have win := window frameIn
  have := win.value
  have := win.room
  have := win.stackLow
  refine ⟨rfl, productCallOfFrame geo st frameIn frameOut rfl rsp rsi rdi control widths
    (pushedFrame writes (by omega) (by omega) bounded)
    (memLoad_memStore_same _ _ _ (by decide) (by decide)) retLow ?_ ?_
    (save regs scratch writes widths hpost input) input⟩
  · intro _
    rw [srcRegEq]
    exact congrArg (Value.get 64) src
  · intro _
    exact congrArg (Value.get 64) dst

end K256.Proofs.Sec1.SqrtLaterProducts.Early
