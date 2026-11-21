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

namespace K256.Proofs.SignatureSlice

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift LIR

theorem returnBlock {code : CodeMap} {args : Vector Value 53} {mem : Ram}
    {sp : BitVec 64} (hsp : args[4] = ⟨64, sp - 88⟩)
    (hpop : LoadOk mem (sp - 8) 8) (hret : LoadOk mem sp 8)
    (hlow : (memLoad mem sp 64).toNat < 2 ^ 32) :
    ∃ out : Output Value Ram Reg.count,
      program.runBlock (dialect code) ⟨.l1024d0, args, mem⟩ = .returned out ∧
      out.store = mem ∧ out.tag = some ⟨64, memLoad mem sp 64⟩ ∧
      out.values[3] = ⟨64, memLoad mem (sp - 8) 64⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
      ∀ i : Fin 53, i.val ∈ [0, 5, 12, 13, 14, 15, 22] → out.values[i] = args[i] := by
  have hspBits : Value.get 64 args[4] = sp - 88 := by rw [hsp]; rfl
  have hpopAddr : sp - 88 + 80 = sp - 8 := by
    calc
      sp - 88 + 80 = (sp - 8 - 80) + 80 := by rw [BitVec.sub_sub]; rfl
      _ = sp - 8 := BitVec.sub_add_cancel _ _
  have hstack : sp - 88 + 96 = sp + 8 := by
    calc
      sp - 88 + 96 = sp - 88 + (88 + 8) := rfl
      _ = sp + 8 := by rw [← BitVec.add_assoc, BitVec.sub_add_cancel]
  refine ⟨?out, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [hspBits, hpopAddr, BitVec.sub_add_cancel, hstack, hpop, hret, hlow,
      and_self, ite_true]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.SignatureSlice
