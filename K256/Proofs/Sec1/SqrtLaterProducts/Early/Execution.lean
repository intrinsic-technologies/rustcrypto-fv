import K256.Proofs.Sec1.SqrtLaterProducts.Early.Saved
import K256.Proofs.Sec1.SqrtLaterProducts.Early.Product

namespace K256.Proofs.Sec1.SqrtLaterProducts.Early

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution
open K256.Proofs.Sec1.LIR (lifted)

def returnAddress (i : Fin 13) : Word :=
  if i = 2 then 0x116747 else if i = 3 then 0x116bd8 else 0x11703f

private def offsets (i : Fin 13) : List Word :=
  if i = 2 then offsetsThree else if i = 3 then offsetsFour else offsetsFive

private def aliases (i : Fin 13) (sp : Word) (args regs : Values Value Reg.count) (m : Ram) : Prop :=
  if i = 2 then memLoad m (sp + 176) 64 = args[13].get 64 ∧ memLoad m (sp + 208) 64 = args[15].get 64
  else if i = 3 then True
  else memLoad m (sp + 88) 64 = memLoad m sp 64 ∧ regs[15].get 64 = memLoad m (sp + 8) 64 ∧
    regs[13].get 64 = memLoad m (sp + 16) 64 ∧ regs[3].get 64 = memLoad m (sp + 24) 64 ∧
    memLoad m (sp + 80) 64 = memLoad m (sp + 32) 64

private theorem casesEarly (i : Fin 13) (lo : 2 ≤ i.val) (hi : i.val ≤ 4) :
    i = 2 ∨ i = 3 ∨ i = 4 := by omega

private theorem direct {code fr args mem} {i : Fin 13} (lo : 2 ≤ i.val) (hi : i.val ≤ 4)
    (geo : Geometry code fr) (w : Window code fr args mem (fr.rsp - 440)) :
    CallTo (lifted := lifted)
      (squareEntry args mem (fr.rsp - 440) squarePC[i] (returnAddress i) (dstReg i) (offsets i)
        (aliases i (fr.rsp - 440) args))
      (lifted.program.runBlock (dialect code) ⟨productPC[i.castSucc], args, mem⟩) := by
  obtain ⟨hb, hl, ha⟩ := w.blockBounds (start := 0x116316) (finish := 0x11703f) geo (by decide) (by decide)
  rcases casesEarly i lo hi with rfl | rfl | rfl
  · exact stageThree w.rsp w.writable hb hl (by omega)
  · exact stageFour w.rsp w.writable hb hl (by omega)
  · exact stageFive w.rsp w.writable hb hl (by omega)

theorem call {code fr a args mem} {i : Fin 13} (lo : 2 ≤ i.val) (hi : i.val ≤ 4)
    (geo : Geometry code fr) (st : ProductState code fr a i.castSucc args mem) :
    ∃ child : lifted.Location, lifted.program.runBlock (dialect code)
      ⟨productPC[i.castSucc], args, mem⟩ = .call child (Wrapper.callFrame squarePC[i] (returnAddress i)) ∧
      (WordsAt child.store (fr.rsp - 440) 64 (words a (2*(i.val+1))) →
        ProductCall code fr a i child (returnAddress i)) := by
  have hin : LIR.Fn115950.frameAt productPC[i.castSucc] fr = LIR.Fn115950.frameAt .l116316 fr := by
    rcases casesEarly i lo hi with rfl | rfl | rfl <;> rfl
  have hout : LIR.Fn115950.frameAt squarePC[i] fr = LIR.Fn115950.frameAt .l116316 fr := by
    rcases casesEarly i lo hi with rfl | rfl | rfl <;> rfl
  have old : StandardFrame code fr args mem := by
    have h := st.frame
    rwa [hin] at h
  have w := window old
  obtain ⟨hb, hl, _⟩ := w.blockBounds (start := 0x116316) (finish := 0x11703f) geo (by decide) (by decide)
  have step := direct lo hi geo w
  generalize eq : lifted.program.runBlock (dialect code) ⟨productPC[i.castSucc], args, mem⟩ = tr at step ⊢
  cases tr with
  | jump | returned | stuck => exact step.elim
  | call child frame =>
    have hframe : frame = Wrapper.callFrame squarePC[i] (returnAddress i) := step.choose_spec.choose_spec.2.1
    refine ⟨child, congrArg (Transfer.call child) hframe, fun input => (makeProductCall geo st old hout ?_ ?_ ?_ step ?_ input).2⟩
    · rcases casesEarly i lo hi with rfl | rfl | rfl <;> decide
    · rcases casesEarly i lo hi with rfl | rfl | rfl <;> rfl
    · have cert : (offsets i).all (fun k => decide (k.toNat ≤ 376)) = true := by
        rcases casesEarly i lo hi with rfl | rfl | rfl <;> decide +kernel
      exact fun k hk => of_decide_eq_true (List.all_eq_true.mp cert k hk)
    · intro regs scratch writes widths m' als wordsAt
      rcases casesEarly i lo hi with rfl | rfl | rfl
      · exact savedThree st.saved writes hb hl als.1 als.2
      · exact savedFour st.saved writes hb hl
      · exact savedFive st.saved writes hb hl widths wordsAt als

end K256.Proofs.Sec1.SqrtLaterProducts.Early
