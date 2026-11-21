import AesGcm.Proofs.Copied.X86Proofs.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.AccImm8.Triple
import X86Proofs.Instructions.Adc.Generated.Imm32.Triple
import X86Proofs.Instructions.Adc.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.AccImm8.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.R8Imm8.Triple
import X86Proofs.Instructions.And.Generated.AccImm8.Triple
import X86Proofs.Instructions.And.Generated.Imm32.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm32.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.AccImm8.Triple
import X86Proofs.Instructions.Or.Generated.Imm32.Triple
import X86Proofs.Instructions.Or.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.AccImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.Imm32.Triple
import X86Proofs.Instructions.Sbb.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.AccImm8.Triple
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Test.Generated.Imm32.Triple
import X86Proofs.Instructions.Test.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.Imm32.Triple
import X86Proofs.Instructions.Xor.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.R8Imm8.Triple

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG

@[cfg_eval] theorem_by andR32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR32Imm8Effect p len dst imm t) t' = _ := by lift_value [andR32Imm8Effect]

@[cfg_eval] theorem andR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR32Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR32Imm8Effect_components])

@[cfg_eval] theorem_by andR64Imm8Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR64Imm8Effect p dst imm t) t' = _ := by lift_value [andR64Imm8Effect]

@[cfg_eval] theorem_by andR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR64Imm8Effect p dst imm t) t' = _ := by lift_value [andR64Imm8Effect]

@[cfg_eval] theorem andR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR64Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR64Imm8Effect_components])

@[cfg_eval] theorem_by subR64Imm8Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR64Imm8Effect p dst imm t) t' = _ := by lift_value [subR64Imm8Effect]

@[cfg_eval] theorem subR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR64Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR64Imm8Effect_components])

@[cfg_eval] theorem_by cmpR32Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR32Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm8Effect]

@[cfg_eval] theorem cmpR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR32Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR32Imm8Effect_components])

@[cfg_eval] theorem_by cmpR64Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR64Imm8Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm8Effect]

@[cfg_eval] theorem_by cmpR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR64Imm8Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm8Effect]

@[cfg_eval] theorem cmpR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR64Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR64Imm8Effect_components])

@[cfg_eval] theorem_by addR64Imm32Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR64Imm32Effect p dst imm t) t' = _ := by lift_value [addR64Imm32Effect]

@[cfg_eval] theorem addR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR64Imm32Effect_components])

@[cfg_eval] theorem_by andR32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR32Imm32Effect p len dst imm t) t' = _ := by lift_value [andR32Imm32Effect]

@[cfg_eval] theorem andR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR32Imm32Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR32Imm32Effect_components])

@[cfg_eval] theorem_by subR64Imm32Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR64Imm32Effect p dst imm t) t' = _ := by lift_value [subR64Imm32Effect]

@[cfg_eval] theorem subR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR64Imm32Effect_components])

@[cfg_eval] theorem_by cmpR64Imm32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR64Imm32Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm32Effect]

@[cfg_eval] theorem cmpR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR64Imm32Effect_components])

end X86Proofs.Lift
