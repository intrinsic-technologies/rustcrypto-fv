import K256.Proofs.Sec1.SqrtChainExecution.Stages
import K256.Proofs.Sec1.Sqrt.Finish.Status

namespace K256.Proofs.Sec1.SqrtChainExecution

open X86 X86.Machine X86.UserProcess X86Proofs Prelude CFG Lift Refine Common.Field

theorem throughProducts {code : CodeMap} {fr : Activation} {a : Limbs} {args mem}
    (initial : ProductState code fr a 0 args mem)
    (mul : ∀ i, MultiplyStage code fr a i) (square : ∀ i, SquareStage code fr a i) :
    ∃ b m, Parser.Reaches code productPC[0] args mem productPC[13] b m ∧
      ProductState code fr a 13 b m := by
  have toStage (n : Nat) (hn : n < 14) :
      ∃ b m, Parser.Reaches code productPC[0] args mem productPC[n] b m ∧
        ProductState code fr a ⟨n,hn⟩ b m := by
    induction n with
    | zero => exact ⟨args,mem,.refl _,initial⟩
    | succ n ih =>
      obtain ⟨b,m,reach,h⟩ := ih (by omega)
      let i : Fin 13 := ⟨n,by omega⟩
      obtain ⟨c,mc,rm,hc⟩ := mul i h
      obtain ⟨d,md,rs,hd⟩ := square i hc
      exact ⟨d,md,(reach.trans rm).trans rs,hd⟩
  exact toStage 13 (by decide)

def candidate (x : Fin modulus) : Fin modulus :=
  ⟨Nat.mod (x.val ^ ((modulus + 1) / 4)) modulus, Nat.mod_lt _ (by decide)⟩

def Return (code : CodeMap) (fr : Activation) (limbs : Limbs) (flag : BitVec 8)
    (o : Output Value Ram Reg.count) : Prop :=
  o.tag = some ⟨64,fr.ret⟩ ∧ Atom.All code o.values o.store (LIR.Fn115950.doneAt fr) ∧
    o.values[0] = ⟨64,fr.rdi⟩ ∧ WordsAt o.store fr.rdi 64 limbs ∧
    memLoad o.store (fr.rdi + 40) 8 = flag ∧
    RamWriteFrame fr.original o.store [fr.region,⟨fr.rdi.toNat,41⟩]

def CompareStage (code : CodeMap) (fr : Activation) (a : Limbs) : Prop :=
  ∀ {args mem}, ProductState code fr a 13 args mem →
    ∃ o, LIR.program.Exec (dialect code) ⟨⟨.l11a14c,args,mem⟩,[]⟩ o ∧
      Return code fr (words a 27) ((Sqrt.Finish.comparisonStatus (words a 27) a).setWidth 8) o

theorem finishChain {code : CodeMap} {fr : Activation} {a : Limbs} {x : Fin modulus} {args mem}
    (ha : FieldRepr a x 8) (initial : ProductState code fr a 0 args mem)
    (mul : ∀ i, MultiplyStage code fr a i) (square : ∀ i, SquareStage code fr a i)
    (finish : CompareStage code fr a) :
    ∃ o, LIR.program.Exec (dialect code) ⟨⟨.l1159a4,args,mem⟩,[]⟩ o ∧
      FieldRepr (words a 27) (candidate x) 8 ∧
      Return code fr (words a 27) (if candidate x * candidate x = x then 1 else 0) o := by
  obtain ⟨b,m,reach,post⟩ := throughProducts initial mul square
  obtain ⟨o,run,hr⟩ := finish post
  have repr : FieldRepr (words a 27) (candidate x) 8 := SqrtChain.mulWords_result_repr ha
  have eq := Sqrt.Finish.comparisonStatus_correct _ _ _ _ _ repr ha (by decide)
  have flag : (Sqrt.Finish.comparisonStatus (words a 27) a).setWidth 8 =
      (if candidate x * candidate x = x then 1 else 0) := by
    rw [eq]
    split <;> rfl
  exact ⟨o,Program.Exec.of_sem (reach.exec run.sem),repr,flag ▸ hr⟩

end K256.Proofs.Sec1.SqrtChainExecution
