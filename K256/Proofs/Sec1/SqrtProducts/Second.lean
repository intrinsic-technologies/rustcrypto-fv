import K256.Proofs.Sec1.SqrtLaterProducts.Early.Call
import K256.Proofs.Sec1.Sqrt.WordEquality
import K256.Proofs.Sec1.SqrtProducts.SecondSchedule

namespace K256.Proofs.Sec1.SqrtProducts

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtLaterProducts.Early
open K256.Proofs.Sec1.LIR (lifted)

def secondOffsets : List Word := [0,8,16,24,32,80,104,112,136,144,160,168,176,192,208]

structure SecondResult (sp : Word) (product : Limbs) (regs : Values Value Reg.count) (mem : Ram) : Prop where
  input : WordsAt mem sp 64 product
  r13 : regs[13] = ⟨64, product[1]⟩
  r15 : regs[15] = ⟨64, product[2]⟩
  r12 : regs[12] = ⟨64, product[3]⟩
  rbp : regs[5] = ⟨64, product[4]⟩
  saved0 : memLoad mem (sp + 160) 64 = product[0]
  saved3 : memLoad mem (sp + 168) 64 = product[3]
  saved4 : memLoad mem (sp + 144) 64 = product[4]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem secondMultiply {code : CodeMap} {a b : Limbs} {args : Values Value Reg.count}
    {mem : Ram} {sp : Word} (hsp : args[4].get 64 = sp)
    (hs : Writable code mem (sp - 8) 440)
    (hbase : 8 ≤ sp.toNat) (hlow : sp.toNat + 432 ≤ 2^32)
    (hcode : sp.toNat + 432 ≤ 0x115e4d ∨ 0x11629e + 8 ≤ sp.toNat)
    (ha : WordsAt mem (sp + 40) 64 a)
    (hb0 : memLoad mem (sp + 352) 64 = b[0])
    (hb1 : memLoad mem (sp + 328) 64 = b[1])
    (hb2 : memLoad mem (sp + 304) 64 = b[2])
    (hb3 : memLoad mem (sp + 336) 64 = b[3])
    (hb4 : memLoad mem (sp + 320) 64 = b[4]) :
    CallTo (lifted := lifted) (squareEntry args mem sp .l11629e 0x11629e 3 secondOffsets
      (SecondResult sp (mulWords a b)))
      (lifted.program.runBlock (dialect code) ⟨.l115e4d,args,mem⟩) := by
  rw [← secondProduct_eq_mulWords]
  have haddr : (sp - (8 : Word)).toNat = sp.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by change (8 : Word).toNat ≤ sp.toNat; exact hbase)]
    rfl
  lifted_registers [hsp]
  subst sp
  have data : WordsAt mem _ 64 a ∧ True := ⟨ha, trivial⟩
  run_tac Lean.Elab.Tactic.withMainContext do
    let d ← Lean.Meta.getLocalDeclFromUserName `data
    let names ← Refine.Tactic.introAtoms d.fvarId "input"
    Lean.Elab.Tactic.withMainContext (Refine.Tactic.registerNames .rewrite names)
  final_product_block
  refine ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · early_registers
  · early_registers
  · final_product_frame
  constructor
  case r13 | r15 | r12 | rbp =>
    apply congrArg (Value.mk 64)
    lifted_word_reads [word0, word1, word2, word3, word4, hb0, hb1, hb2, hb3, hb4]
    dsimp -zeta only [secondProduct, secondCoefficients, Common.Field.Multiply.SqrtSchedule.reduceWords]
    lifted_word_eq []
  all_goals lifted_word_reads [word0, word1, word2, word3, word4, hb0, hb1, hb2, hb3, hb4]
  all_goals dsimp -zeta only [secondProduct, secondCoefficients, Common.Field.Multiply.SqrtSchedule.reduceWords]
  all_goals lifted_word_eq []

end K256.Proofs.Sec1.SqrtProducts
