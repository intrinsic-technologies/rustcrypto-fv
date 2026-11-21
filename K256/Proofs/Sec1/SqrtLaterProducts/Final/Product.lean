import K256.Proofs.Sec1.SqrtLaterProducts.Final.SavedAtoms
import K256.Proofs.Sec1.SqrtLaterProducts.Early.Product

namespace K256.Proofs.Sec1.SqrtLaterProducts.Final

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution
open K256.Proofs.Sec1.LIR (lifted)

def returnAddress (i : Fin 13) : Word :=
  if i = 9 then 0x118da2 else if i = 10 then 0x119258 else if i = 11 then 0x119b94 else 0x11a110

private def maskAtCall (i : Fin 13) (child : lifted.Location) : Prop :=
  if i.val = 12 then child.arguments[12]'(by change 12 < Reg.count; decide) = ⟨64, 0x1000003d10⟩
  else True

private theorem lateCases (i : Fin 13) (h : 9 ≤ i.val) :
    i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 := by
  omega

theorem frameLayouts (i : Fin 13) (late : 9 ≤ i.val) (fr : Activation) :
    LIR.Fn115950.frameAt productPC[i.castSucc] fr = LIR.Fn115950.frameAt .l116316 fr ∧
    LIR.Fn115950.frameAt squarePC[i] fr = LIR.Fn115950.frameAt .l116316 fr := by
  rcases lateCases i late with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

private theorem block {code fr args mem} {i : Fin 13} (late : 9 ≤ i.val)
    (geo : Geometry code fr) (w : Early.Window code fr args mem (fr.rsp - 440)) :
    CallTo (lifted := lifted)
      (CallsSquare args mem (fr.rsp - 440) squarePC[i] (returnAddress i) (offsets i) (maskAtCall i))
      (lifted.program.runBlock (dialect code) ⟨productPC[i.castSucc], args, mem⟩) := by
  obtain ⟨lo, hi, apart⟩ := w.blockBounds (start := 0x118991) (finish := 0x11a110)
    geo (by decide) (by decide)
  rcases lateCases i late with rfl | rfl | rfl | rfl
  · exact stageTen w.rsp w.writable lo hi (by omega)
  · exact stageEleven w.rsp w.writable lo hi (by omega)
  · exact stageTwelve w.rsp w.writable lo hi (by omega)
  · exact stageThirteen w.rsp w.writable lo hi (by omega)

theorem call {code fr a args mem} {i : Fin 13} (late : 9 ≤ i.val)
    (geo : Geometry code fr) (st : ProductState code fr a i.castSucc args mem) :
    ∃ child : lifted.Location, lifted.program.runBlock (dialect code)
      ⟨productPC[i.castSucc], args, mem⟩ = .call child (Wrapper.callFrame squarePC[i] (returnAddress i)) ∧
      (WordsAt child.store (fr.rsp - 440) 64 (words a (2 * (i.val+1))) →
        ProductCall code fr a i child (returnAddress i)) := by
  obtain ⟨fin, fout⟩ := frameLayouts i late fr
  have old : Early.StandardFrame code fr args mem := by
    unfold Early.StandardFrame
    rw [← fin]
    exact st.frame
  have w := Early.window old
  obtain ⟨lo, hi, _⟩ := w.blockBounds (start := 0x118991) (finish := 0x11a110)
    geo (by decide) (by decide)
  have step := block late geo w
  generalize he : lifted.program.runBlock (dialect code) ⟨productPC[i.castSucc], args, mem⟩ = tr at step ⊢
  cases tr with
  | jump | returned | stuck => exact step.elim
  | call child frame =>
    obtain ⟨regs, scratch, rfl, rfl, rc, writes, mask⟩ := step
    refine ⟨_, rfl, fun word => Early.productCallOfFrame geo st old fout rfl rc.rsp rc.rsi rc.rdi
      rc.control rc.widths (Early.pushedFrame writes lo hi ?_) ?_ ?_ ?_ ?_ ?_ word⟩
    · have bounded : ∀ j : Fin 13, (offsets j).all (fun off => decide (off.toNat ≤ 376)) = true := by
        decide +kernel
      exact fun off h => of_decide_eq_true (List.all_eq_true.mp (bounded i) off h)
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · have all : ∀ j : Fin 13, (returnAddress j).toNat < 2^32 := by decide +kernel
      exact all i
    · intro _
      rw [show srcReg i = 14 by simp [srcReg, show i.val ≠ 6 by omega]]
      exact congrArg (Value.get 64) rc.r14
    · intro _
      rw [show dstReg i = 3 by simp [dstReg, show i.val ≠ 6 by omega, show i.val ≠ 4 by omega]]
      exact congrArg (Value.get 64) rc.rbx
    · apply savedAfter late st.saved writes lo hi
      intro h
      simpa only [maskAtCall, h, ite_true] using mask

end K256.Proofs.Sec1.SqrtLaterProducts.Final
