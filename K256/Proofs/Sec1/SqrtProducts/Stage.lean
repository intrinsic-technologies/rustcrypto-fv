import K256.Proofs.Common.Field.Multiply.SqrtSchedule.Commutative
import K256.Proofs.Sec1.SqrtProducts.Second
import K256.Proofs.Sec1.SqrtLaterProducts.Early.Product
import K256.Proofs.Sec1.SqrtChainExecution.ProductResume

namespace K256.Proofs.Sec1.SqrtProducts

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution SqrtLaterProducts.Early
open K256.Proofs.Sec1.LIR (lifted)

private theorem offsetBound {k : Word} (hk : k ∈ secondOffsets) : k.toNat ≤ 208 :=
  of_decide_eq_true (List.all_eq_true.mp
    (show secondOffsets.all (fun o => decide (o.toNat ≤ 208)) = true by decide) k hk)

private theorem savedSecond {code : CodeMap} {args regs : Values Value Reg.count}
    {a : Limbs} {mem scratch : Ram} {base ret : Word}
    (old : Atom.All code args mem (savedAtoms 1 base a))
    (writes : SqrtLaterProducts.Final.ScratchWrites mem scratch base secondOffsets)
    (lo : 8 ≤ base.toNat) (hi : base.toNat + 432 ≤ 2^32)
    (data : SecondResult base (words a 4) regs (memStore scratch (base - 8) ret)) :
    Atom.All code regs (memStore scratch (base - 8) ret) (savedAtoms 2 base a) := by
  have keep (k : Word) (hk : 216 ≤ k.toNat) (hk' : k.toNat ≤ 352) :=
    retained (ret := ret) (k := k) writes lo hi (by omega) (fun off h =>
      have b := offsetBound h
      ⟨by omega, Or.inr (by omega)⟩)
  obtain ⟨b0,b1,b2,b3,b4,p0,p1,p2,p3,p4,_⟩ := old
  exact ⟨(keep 352 (by decide) (by decide)).trans b0, (keep 328 (by decide) (by decide)).trans b1,
    (keep 304 (by decide) (by decide)).trans b2, (keep 336 (by decide) (by decide)).trans b3,
    (keep 320 (by decide) (by decide)).trans b4, (keep 240 (by decide) (by decide)).trans p0,
    (keep 288 (by decide) (by decide)).trans p1, (keep 312 (by decide) (by decide)).trans p2,
    (keep 256 (by decide) (by decide)).trans p3, (keep 248 (by decide) (by decide)).trans p4,
    data.saved0, data.r13, data.r15, data.r12, data.saved3, data.rbp, data.saved4, trivial⟩

theorem secondStage {code : CodeMap} {fr : Activation} {a : Limbs}
    (geo : Geometry code fr) : MultiplyStage code fr a 1 := by
  intro args mem st
  let base := fr.rsp - 440
  have win := window st.frame
  obtain ⟨lo,hi,apart⟩ := win.blockBounds geo (start := 0x115e4d) (finish := 0x11629e)
    (by decide) (by decide)
  obtain ⟨b0,b1,b2,b3,b4,_⟩ := st.saved
  have addr : base + 40 = fr.rsp - 400 := by
    dsimp only [base]
    rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have squared : WordsAt mem (base + 40) 64 (words a 3) := addr.symm ▸ st.squared
  have h := secondMultiply (b := a) win.rsp win.writable lo hi apart squared b0 b1 b2 b3 b4
  have product := (chainWord_step squareWords mulWords a 1).1
  change words a 4 = mulWords (words a 0) (words a 3) at product
  have z : words a 0 = a := (chainWord_first squareWords mulWords a).1
  rw [z] at product
  rw [Common.Field.Multiply.SqrtSchedule.mulWords_comm (words a 3) a, ← product] at h
  generalize ht : lifted.program.runBlock (dialect code) ⟨.l115e4d,args,mem⟩ = result at h
  cases result with
  | call child frame =>
    change squareEntry _ _ _ _ _ _ _ (SecondResult base (words a 4)) _ _ at h
    have input : WordsAt child.store base 64 (words a 4) := by
      obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,data⟩ := h
      exact data.input
    obtain ⟨cont,entry⟩ := makeProductCall (i := 1) geo st st.frame rfl (by decide) rfl
      (fun off ho => Nat.le_trans (offsetBound ho) (by decide)) h
      (fun _ _ writes _ data _ => savedSecond st.saved writes lo hi data) input
    rw [cont] at ht
    exact productResume geo (by decide) ht entry
  | _ => exact False.elim h

end K256.Proofs.Sec1.SqrtProducts
