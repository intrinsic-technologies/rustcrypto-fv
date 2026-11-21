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

theorem lengthBlock {code : CodeMap} {args : Vector Value 53} {mem : Ram}
    {sp dx bx : BitVec 64} (hsp : args[4] = ⟨64, sp⟩) (hdx : args[2] = ⟨64, dx⟩)
    (hbx : args[3] = ⟨64, bx⟩) (hpush : StoreOk code mem (sp - 8) 8 0x102450 1) :
    let next := (args.set 4 ⟨64, sp - 88⟩).set 19 (.ofBool (dx == 64))
    if dx = 64 then
      program.runBlock (dialect code) ⟨.l102450, args, mem⟩ =
        .jump ⟨.l10245b, next, memStore mem (sp - 8) bx⟩
    else
      program.runBlock (dialect code) ⟨.l102450, args, mem⟩ =
        .jump ⟨.l1024d6, next, memStore mem (sp - 8) bx⟩ := by
  have rsp : Value.get 64 args[4] = sp := by rw [hsp]; rfl
  have rdx : Value.get 64 args[2] = dx := by rw [hdx]; rfl
  have rbx : Value.get 64 args[3] = bx := by rw [hbx]; rfl
  dsimp only
  by_cases heq : dx = 64
  all_goals first | simp only [ite_eq_left heq] | simp only [ite_eq_right heq]
  all_goals
    cfg_eval
    simp only [rsp, rdx, rbx, hpush, cmpSpec_ZF, Bool.not_eq_true',
      beq_eq_false_iff_ne, ne_eq, heq, not_true_eq_false, not_false_eq_true, ↓reduceIte]
    congr 2
    apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
      fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
    intro j
    finite_cases j <;> simp only [Vector.getElem_set] <;> rfl

end K256.Proofs.SignatureSlice
