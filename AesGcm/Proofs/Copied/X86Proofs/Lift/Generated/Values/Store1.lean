import AesGcm.Proofs.Copied.X86Proofs.Lift.Eval
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

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG

@[cfg_eval ↓] theorem_by andMREffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (andMREffect p len 32 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [andMREffect]
  · simp only [andMREffect_components]; rfl

@[cfg_eval ↓] theorem_by andMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (andMREffect p len 64 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [andMREffect]
  · simp only [andMREffect_components]; rfl

@[cfg_eval ↓] theorem_by xorMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (xorMREffect p len 64 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorMREffect]
  · simp only [xorMREffect_components]; rfl

@[cfg_eval ↓] theorem_by xorM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (xorM8Imm8Effect p len am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorM8Imm8Effect]
  · simp only [xorM8Imm8Effect_components]; rfl

end X86Proofs.Lift
