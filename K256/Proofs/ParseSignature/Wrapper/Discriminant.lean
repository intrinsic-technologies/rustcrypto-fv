import K256.Proofs.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.ParseSignature

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

theorem resultBranch {code : CodeMap} {args : Vector Value 53} {mem : Ram}
    {sp : BitVec 64} {entry ok err : Label}
    (site : (entry, ok, err) ∈ [(.l102468, .l10246f, .l1024df),
      (.l103b07, .l103b12, .l103c4d), (.l103b75, .l103b80, .l103c4d)])
    (hsp : args[4] = ⟨64, sp⟩) (hread : LoadOk mem (sp + 8) 4) :
    let tag := (memLoad mem (sp + 8) 64).setWidth 32
    program.runBlock (dialect code) ⟨entry, args, mem⟩ =
      .jump ⟨if tag = 1 then err else ok, args.set 19 (.ofBool (tag == 1)), mem⟩ := by
  have rsp : Value.get 64 args[4] = sp := by rw [hsp]; rfl
  have low : (memLoad mem (sp + 8) 64).setWidth 32 = memLoad mem (sp + 8) 32 := by
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
    simpa only [Nat.zero_div, BitVec.add_zero] using
      extractLsb'_memLoad mem (sp + 8) (n := 64) 0 32 (by decide) (by decide) (by decide)
  dsimp only
  rw [low]
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at site
  rcases site with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    cfg_eval <;> simp only [rsp, hread, cmpSpec_ZF, beq_iff_eq, ↓reduceIte] <;>
    split <;> rename_i htag <;> congr 2 <;>
    (first | exact (ite_eq_left htag).symm | exact (ite_eq_right htag).symm | skip) <;>
    apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
      fun h => Vector.ext fun i hi => h ⟨i, hi⟩) <;>
    intro j <;> finite_cases j <;> simp only [Vector.getElem_set] <;> rfl

end K256.Proofs.ParseSignature
