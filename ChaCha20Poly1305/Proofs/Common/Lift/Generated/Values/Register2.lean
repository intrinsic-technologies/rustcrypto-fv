import ChaCha20Poly1305.Proofs.Common.Lift.Eval
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

namespace ChaCha20Poly1305.Proofs.Lift
open X86Proofs

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG

@[cfg_eval] theorem_by andR32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR32Imm8Effect p len dst imm t) t' = _ := by lift_value [andR32Imm8Effect]

@[cfg_eval] theorem_by andR32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR32Imm8Effect p len dst imm t) t' = _ := by lift_value [andR32Imm8Effect]

@[cfg_eval] theorem_by andR32Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR32Imm8Effect p len dst imm t) t' = _ := by lift_value [andR32Imm8Effect]

@[cfg_eval] theorem_by andR32Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR32Imm8Effect p len dst imm t) t' = _ := by lift_value [andR32Imm8Effect]

@[cfg_eval] theorem_by andR32Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR32Imm8Effect p len dst imm t) t' = _ := by lift_value [andR32Imm8Effect]

@[cfg_eval] theorem_by andR32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR32Imm8Effect p len dst imm t) t' = _ := by lift_value [andR32Imm8Effect]

@[cfg_eval] theorem andR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR32Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR32Imm8Effect_components])

@[cfg_eval] theorem_by andR64Imm8Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR64Imm8Effect p dst imm t) t' = _ := by lift_value [andR64Imm8Effect]

@[cfg_eval] theorem_by andR64Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR64Imm8Effect p dst imm t) t' = _ := by lift_value [andR64Imm8Effect]

@[cfg_eval] theorem_by andR64Imm8Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR64Imm8Effect p dst imm t) t' = _ := by lift_value [andR64Imm8Effect]

@[cfg_eval] theorem_by andR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR64Imm8Effect p dst imm t) t' = _ := by lift_value [andR64Imm8Effect]

@[cfg_eval] theorem_by andR64Imm8Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR64Imm8Effect p dst imm t) t' = _ := by lift_value [andR64Imm8Effect]

@[cfg_eval] theorem_by andR64Imm8Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR64Imm8Effect p dst imm t) t' = _ := by lift_value [andR64Imm8Effect]

@[cfg_eval] theorem andR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR64Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR64Imm8Effect_components])

@[cfg_eval] theorem_by subR16Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR16Imm8Effect p len dst imm t) t' = _ := by lift_value [subR16Imm8Effect]

@[cfg_eval] theorem_by subR16Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR16Imm8Effect p len dst imm t) t' = _ := by lift_value [subR16Imm8Effect]

@[cfg_eval] theorem_by subR16Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR16Imm8Effect p len dst imm t) t' = _ := by lift_value [subR16Imm8Effect]

@[cfg_eval] theorem_by subR16Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR16Imm8Effect p len dst imm t) t' = _ := by lift_value [subR16Imm8Effect]

@[cfg_eval] theorem_by subR16Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR16Imm8Effect p len dst imm t) t' = _ := by lift_value [subR16Imm8Effect]

@[cfg_eval] theorem_by subR16Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR16Imm8Effect p len dst imm t) t' = _ := by lift_value [subR16Imm8Effect]

@[cfg_eval] theorem_by subR16Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR16Imm8Effect p len dst imm t) t' = _ := by lift_value [subR16Imm8Effect]

@[cfg_eval] theorem subR16Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR16Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR16Imm8Effect_components])

@[cfg_eval] theorem_by subR32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR32Imm8Effect p len dst imm t) t' = _ := by lift_value [subR32Imm8Effect]

@[cfg_eval] theorem_by subR32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR32Imm8Effect p len dst imm t) t' = _ := by lift_value [subR32Imm8Effect]

@[cfg_eval] theorem_by subR32Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR32Imm8Effect p len dst imm t) t' = _ := by lift_value [subR32Imm8Effect]

@[cfg_eval] theorem_by subR32Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR32Imm8Effect p len dst imm t) t' = _ := by lift_value [subR32Imm8Effect]

@[cfg_eval] theorem_by subR32Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR32Imm8Effect p len dst imm t) t' = _ := by lift_value [subR32Imm8Effect]

@[cfg_eval] theorem_by subR32Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR32Imm8Effect p len dst imm t) t' = _ := by lift_value [subR32Imm8Effect]

@[cfg_eval] theorem_by subR32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR32Imm8Effect p len dst imm t) t' = _ := by lift_value [subR32Imm8Effect]

@[cfg_eval] theorem subR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR32Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR32Imm8Effect_components])

@[cfg_eval] theorem_by subR64Imm8Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR64Imm8Effect p dst imm t) t' = _ := by lift_value [subR64Imm8Effect]

@[cfg_eval] theorem_by subR64Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR64Imm8Effect p dst imm t) t' = _ := by lift_value [subR64Imm8Effect]

@[cfg_eval] theorem_by subR64Imm8Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR64Imm8Effect p dst imm t) t' = _ := by lift_value [subR64Imm8Effect]

@[cfg_eval] theorem_by subR64Imm8Effect_AF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR64Imm8Effect p dst imm t) t' = _ := by lift_value [subR64Imm8Effect]

@[cfg_eval] theorem_by subR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR64Imm8Effect p dst imm t) t' = _ := by lift_value [subR64Imm8Effect]

@[cfg_eval] theorem_by subR64Imm8Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR64Imm8Effect p dst imm t) t' = _ := by lift_value [subR64Imm8Effect]

@[cfg_eval] theorem_by subR64Imm8Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR64Imm8Effect p dst imm t) t' = _ := by lift_value [subR64Imm8Effect]

@[cfg_eval] theorem subR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR64Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR64Imm8Effect_components])

@[cfg_eval] theorem_by xorR16Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR16Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm8Effect]

@[cfg_eval] theorem_by xorR16Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR16Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm8Effect]

@[cfg_eval] theorem_by xorR16Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR16Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm8Effect]

@[cfg_eval] theorem_by xorR16Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR16Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm8Effect]

@[cfg_eval] theorem_by xorR16Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR16Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm8Effect]

@[cfg_eval] theorem_by xorR16Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR16Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm8Effect]

@[cfg_eval] theorem xorR16Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR16Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR16Imm8Effect_components])

@[cfg_eval] theorem_by xorR32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR32Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm8Effect]

@[cfg_eval] theorem_by xorR32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR32Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm8Effect]

@[cfg_eval] theorem_by xorR32Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR32Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm8Effect]

@[cfg_eval] theorem_by xorR32Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR32Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm8Effect]

@[cfg_eval] theorem_by xorR32Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR32Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm8Effect]

@[cfg_eval] theorem_by xorR32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR32Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm8Effect]

@[cfg_eval] theorem xorR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR32Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR32Imm8Effect_components])

@[cfg_eval] theorem_by xorR64Imm8Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR64Imm8Effect p dst imm t) t' = _ := by lift_value [xorR64Imm8Effect]

@[cfg_eval] theorem_by xorR64Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR64Imm8Effect p dst imm t) t' = _ := by lift_value [xorR64Imm8Effect]

@[cfg_eval] theorem_by xorR64Imm8Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR64Imm8Effect p dst imm t) t' = _ := by lift_value [xorR64Imm8Effect]

@[cfg_eval] theorem_by xorR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR64Imm8Effect p dst imm t) t' = _ := by lift_value [xorR64Imm8Effect]

@[cfg_eval] theorem_by xorR64Imm8Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR64Imm8Effect p dst imm t) t' = _ := by lift_value [xorR64Imm8Effect]

@[cfg_eval] theorem_by xorR64Imm8Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR64Imm8Effect p dst imm t) t' = _ := by lift_value [xorR64Imm8Effect]

@[cfg_eval] theorem xorR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR64Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR64Imm8Effect_components])

@[cfg_eval] theorem_by cmpR16Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR16Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm8Effect]

@[cfg_eval] theorem_by cmpR16Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR16Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm8Effect]

@[cfg_eval] theorem_by cmpR16Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR16Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm8Effect]

@[cfg_eval] theorem_by cmpR16Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR16Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm8Effect]

@[cfg_eval] theorem_by cmpR16Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR16Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm8Effect]

@[cfg_eval] theorem_by cmpR16Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR16Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm8Effect]

@[cfg_eval] theorem cmpR16Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR16Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR16Imm8Effect_components])

@[cfg_eval] theorem_by cmpR32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR32Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm8Effect]

@[cfg_eval] theorem_by cmpR32Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR32Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm8Effect]

@[cfg_eval] theorem_by cmpR32Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR32Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm8Effect]

@[cfg_eval] theorem_by cmpR32Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR32Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm8Effect]

@[cfg_eval] theorem_by cmpR32Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR32Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm8Effect]

@[cfg_eval] theorem_by cmpR32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR32Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm8Effect]

@[cfg_eval] theorem cmpR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR32Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR32Imm8Effect_components])

@[cfg_eval] theorem_by cmpR64Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR64Imm8Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm8Effect]

@[cfg_eval] theorem_by cmpR64Imm8Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR64Imm8Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm8Effect]

@[cfg_eval] theorem_by cmpR64Imm8Effect_AF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR64Imm8Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm8Effect]

@[cfg_eval] theorem_by cmpR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR64Imm8Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm8Effect]

@[cfg_eval] theorem_by cmpR64Imm8Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR64Imm8Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm8Effect]

@[cfg_eval] theorem_by cmpR64Imm8Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR64Imm8Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm8Effect]

@[cfg_eval] theorem cmpR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR64Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR64Imm8Effect_components])

@[cfg_eval] theorem_by addR16Imm16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR16Imm16Effect p len dst imm t) t' = _ := by lift_value [addR16Imm16Effect]

@[cfg_eval] theorem_by addR16Imm16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR16Imm16Effect p len dst imm t) t' = _ := by lift_value [addR16Imm16Effect]

@[cfg_eval] theorem_by addR16Imm16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR16Imm16Effect p len dst imm t) t' = _ := by lift_value [addR16Imm16Effect]

@[cfg_eval] theorem_by addR16Imm16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR16Imm16Effect p len dst imm t) t' = _ := by lift_value [addR16Imm16Effect]

@[cfg_eval] theorem_by addR16Imm16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR16Imm16Effect p len dst imm t) t' = _ := by lift_value [addR16Imm16Effect]

@[cfg_eval] theorem_by addR16Imm16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR16Imm16Effect p len dst imm t) t' = _ := by lift_value [addR16Imm16Effect]

@[cfg_eval] theorem_by addR16Imm16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR16Imm16Effect p len dst imm t) t' = _ := by lift_value [addR16Imm16Effect]

@[cfg_eval] theorem addR16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR16Imm16Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR16Imm16Effect_components])

@[cfg_eval] theorem_by addR32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR32Imm32Effect p len dst imm t) t' = _ := by lift_value [addR32Imm32Effect]

@[cfg_eval] theorem_by addR32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR32Imm32Effect p len dst imm t) t' = _ := by lift_value [addR32Imm32Effect]

@[cfg_eval] theorem_by addR32Imm32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR32Imm32Effect p len dst imm t) t' = _ := by lift_value [addR32Imm32Effect]

@[cfg_eval] theorem_by addR32Imm32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR32Imm32Effect p len dst imm t) t' = _ := by lift_value [addR32Imm32Effect]

@[cfg_eval] theorem_by addR32Imm32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR32Imm32Effect p len dst imm t) t' = _ := by lift_value [addR32Imm32Effect]

@[cfg_eval] theorem_by addR32Imm32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR32Imm32Effect p len dst imm t) t' = _ := by lift_value [addR32Imm32Effect]

@[cfg_eval] theorem_by addR32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR32Imm32Effect p len dst imm t) t' = _ := by lift_value [addR32Imm32Effect]

@[cfg_eval] theorem addR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR32Imm32Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR32Imm32Effect_components])

@[cfg_eval] theorem_by addR64Imm32Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR64Imm32Effect p dst imm t) t' = _ := by lift_value [addR64Imm32Effect]

@[cfg_eval] theorem_by addR64Imm32Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR64Imm32Effect p dst imm t) t' = _ := by lift_value [addR64Imm32Effect]

@[cfg_eval] theorem_by addR64Imm32Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR64Imm32Effect p dst imm t) t' = _ := by lift_value [addR64Imm32Effect]

@[cfg_eval] theorem_by addR64Imm32Effect_AF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR64Imm32Effect p dst imm t) t' = _ := by lift_value [addR64Imm32Effect]

@[cfg_eval] theorem_by addR64Imm32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR64Imm32Effect p dst imm t) t' = _ := by lift_value [addR64Imm32Effect]

@[cfg_eval] theorem_by addR64Imm32Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR64Imm32Effect p dst imm t) t' = _ := by lift_value [addR64Imm32Effect]

@[cfg_eval] theorem_by addR64Imm32Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR64Imm32Effect p dst imm t) t' = _ := by lift_value [addR64Imm32Effect]

@[cfg_eval] theorem addR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR64Imm32Effect_components])

@[cfg_eval] theorem_by orR16Imm16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR16Imm16Effect p len dst imm t) t' = _ := by lift_value [orR16Imm16Effect]

@[cfg_eval] theorem_by orR16Imm16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR16Imm16Effect p len dst imm t) t' = _ := by lift_value [orR16Imm16Effect]

@[cfg_eval] theorem_by orR16Imm16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR16Imm16Effect p len dst imm t) t' = _ := by lift_value [orR16Imm16Effect]

@[cfg_eval] theorem_by orR16Imm16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR16Imm16Effect p len dst imm t) t' = _ := by lift_value [orR16Imm16Effect]

@[cfg_eval] theorem_by orR16Imm16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR16Imm16Effect p len dst imm t) t' = _ := by lift_value [orR16Imm16Effect]

@[cfg_eval] theorem_by orR16Imm16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR16Imm16Effect p len dst imm t) t' = _ := by lift_value [orR16Imm16Effect]

@[cfg_eval] theorem orR16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR16Imm16Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR16Imm16Effect_components])

@[cfg_eval] theorem_by orR32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR32Imm32Effect p len dst imm t) t' = _ := by lift_value [orR32Imm32Effect]

@[cfg_eval] theorem_by orR32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR32Imm32Effect p len dst imm t) t' = _ := by lift_value [orR32Imm32Effect]

@[cfg_eval] theorem_by orR32Imm32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR32Imm32Effect p len dst imm t) t' = _ := by lift_value [orR32Imm32Effect]

@[cfg_eval] theorem_by orR32Imm32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR32Imm32Effect p len dst imm t) t' = _ := by lift_value [orR32Imm32Effect]

@[cfg_eval] theorem_by orR32Imm32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR32Imm32Effect p len dst imm t) t' = _ := by lift_value [orR32Imm32Effect]

@[cfg_eval] theorem_by orR32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR32Imm32Effect p len dst imm t) t' = _ := by lift_value [orR32Imm32Effect]

@[cfg_eval] theorem orR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR32Imm32Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR32Imm32Effect_components])

@[cfg_eval] theorem_by orR64Imm32Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR64Imm32Effect p dst imm t) t' = _ := by lift_value [orR64Imm32Effect]

@[cfg_eval] theorem_by orR64Imm32Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR64Imm32Effect p dst imm t) t' = _ := by lift_value [orR64Imm32Effect]

@[cfg_eval] theorem_by orR64Imm32Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR64Imm32Effect p dst imm t) t' = _ := by lift_value [orR64Imm32Effect]

@[cfg_eval] theorem_by orR64Imm32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR64Imm32Effect p dst imm t) t' = _ := by lift_value [orR64Imm32Effect]

@[cfg_eval] theorem_by orR64Imm32Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR64Imm32Effect p dst imm t) t' = _ := by lift_value [orR64Imm32Effect]

@[cfg_eval] theorem_by orR64Imm32Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR64Imm32Effect p dst imm t) t' = _ := by lift_value [orR64Imm32Effect]

@[cfg_eval] theorem orR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR64Imm32Effect_components])

@[cfg_eval] theorem_by adcR16Imm16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm16Effect, atFlags]

@[cfg_eval] theorem adcR16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR16Imm16Effect p len dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR16Imm16Effect_components])

@[cfg_eval] theorem_by adcR32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm32Effect, atFlags]

@[cfg_eval] theorem adcR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR32Imm32Effect p len dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR32Imm32Effect_components])

@[cfg_eval] theorem_by adcR64Imm32Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR64Imm32Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm32Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR64Imm32Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm32Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR64Imm32Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm32Effect_AF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR64Imm32Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR64Imm32Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm32Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR64Imm32Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm32Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR64Imm32Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm32Effect, atFlags]

@[cfg_eval] theorem adcR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR64Imm32Effect p dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR64Imm32Effect_components])

@[cfg_eval] theorem_by sbbR16Imm16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR16Imm16Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm16Effect, atFlags]

@[cfg_eval] theorem sbbR16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR16Imm16Effect p len dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR16Imm16Effect_components])

@[cfg_eval] theorem_by sbbR32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR32Imm32Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm32Effect, atFlags]

@[cfg_eval] theorem sbbR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR32Imm32Effect p len dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR32Imm32Effect_components])

@[cfg_eval] theorem_by sbbR64Imm32Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR64Imm32Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm32Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR64Imm32Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm32Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR64Imm32Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm32Effect_AF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR64Imm32Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR64Imm32Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm32Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR64Imm32Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm32Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm32Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR64Imm32Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm32Effect, atFlags]

@[cfg_eval] theorem sbbR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR64Imm32Effect p dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR64Imm32Effect_components])

@[cfg_eval] theorem_by andR16Imm16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR16Imm16Effect p len dst imm t) t' = _ := by lift_value [andR16Imm16Effect]

@[cfg_eval] theorem_by andR16Imm16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR16Imm16Effect p len dst imm t) t' = _ := by lift_value [andR16Imm16Effect]

@[cfg_eval] theorem_by andR16Imm16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR16Imm16Effect p len dst imm t) t' = _ := by lift_value [andR16Imm16Effect]

@[cfg_eval] theorem_by andR16Imm16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR16Imm16Effect p len dst imm t) t' = _ := by lift_value [andR16Imm16Effect]

@[cfg_eval] theorem_by andR16Imm16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR16Imm16Effect p len dst imm t) t' = _ := by lift_value [andR16Imm16Effect]

@[cfg_eval] theorem_by andR16Imm16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR16Imm16Effect p len dst imm t) t' = _ := by lift_value [andR16Imm16Effect]

@[cfg_eval] theorem andR16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR16Imm16Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR16Imm16Effect_components])

@[cfg_eval] theorem_by andR32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR32Imm32Effect p len dst imm t) t' = _ := by lift_value [andR32Imm32Effect]

@[cfg_eval] theorem_by andR32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR32Imm32Effect p len dst imm t) t' = _ := by lift_value [andR32Imm32Effect]

@[cfg_eval] theorem_by andR32Imm32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR32Imm32Effect p len dst imm t) t' = _ := by lift_value [andR32Imm32Effect]

@[cfg_eval] theorem_by andR32Imm32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR32Imm32Effect p len dst imm t) t' = _ := by lift_value [andR32Imm32Effect]

@[cfg_eval] theorem_by andR32Imm32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR32Imm32Effect p len dst imm t) t' = _ := by lift_value [andR32Imm32Effect]

@[cfg_eval] theorem_by andR32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR32Imm32Effect p len dst imm t) t' = _ := by lift_value [andR32Imm32Effect]

@[cfg_eval] theorem andR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR32Imm32Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR32Imm32Effect_components])

@[cfg_eval] theorem_by andR64Imm32Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR64Imm32Effect p dst imm t) t' = _ := by lift_value [andR64Imm32Effect]

@[cfg_eval] theorem_by andR64Imm32Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR64Imm32Effect p dst imm t) t' = _ := by lift_value [andR64Imm32Effect]

@[cfg_eval] theorem_by andR64Imm32Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR64Imm32Effect p dst imm t) t' = _ := by lift_value [andR64Imm32Effect]

@[cfg_eval] theorem_by andR64Imm32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR64Imm32Effect p dst imm t) t' = _ := by lift_value [andR64Imm32Effect]

@[cfg_eval] theorem_by andR64Imm32Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR64Imm32Effect p dst imm t) t' = _ := by lift_value [andR64Imm32Effect]

@[cfg_eval] theorem_by andR64Imm32Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR64Imm32Effect p dst imm t) t' = _ := by lift_value [andR64Imm32Effect]

@[cfg_eval] theorem andR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR64Imm32Effect_components])

@[cfg_eval] theorem_by subR16Imm16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR16Imm16Effect p len dst imm t) t' = _ := by lift_value [subR16Imm16Effect]

@[cfg_eval] theorem_by subR16Imm16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR16Imm16Effect p len dst imm t) t' = _ := by lift_value [subR16Imm16Effect]

@[cfg_eval] theorem_by subR16Imm16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR16Imm16Effect p len dst imm t) t' = _ := by lift_value [subR16Imm16Effect]

@[cfg_eval] theorem_by subR16Imm16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR16Imm16Effect p len dst imm t) t' = _ := by lift_value [subR16Imm16Effect]

@[cfg_eval] theorem_by subR16Imm16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR16Imm16Effect p len dst imm t) t' = _ := by lift_value [subR16Imm16Effect]

@[cfg_eval] theorem_by subR16Imm16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR16Imm16Effect p len dst imm t) t' = _ := by lift_value [subR16Imm16Effect]

@[cfg_eval] theorem_by subR16Imm16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR16Imm16Effect p len dst imm t) t' = _ := by lift_value [subR16Imm16Effect]

@[cfg_eval] theorem subR16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR16Imm16Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR16Imm16Effect_components])

@[cfg_eval] theorem_by subR32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR32Imm32Effect p len dst imm t) t' = _ := by lift_value [subR32Imm32Effect]

@[cfg_eval] theorem_by subR32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR32Imm32Effect p len dst imm t) t' = _ := by lift_value [subR32Imm32Effect]

@[cfg_eval] theorem_by subR32Imm32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR32Imm32Effect p len dst imm t) t' = _ := by lift_value [subR32Imm32Effect]

@[cfg_eval] theorem_by subR32Imm32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR32Imm32Effect p len dst imm t) t' = _ := by lift_value [subR32Imm32Effect]

@[cfg_eval] theorem_by subR32Imm32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR32Imm32Effect p len dst imm t) t' = _ := by lift_value [subR32Imm32Effect]

@[cfg_eval] theorem_by subR32Imm32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR32Imm32Effect p len dst imm t) t' = _ := by lift_value [subR32Imm32Effect]

@[cfg_eval] theorem_by subR32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR32Imm32Effect p len dst imm t) t' = _ := by lift_value [subR32Imm32Effect]

@[cfg_eval] theorem subR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR32Imm32Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR32Imm32Effect_components])

@[cfg_eval] theorem_by subR64Imm32Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR64Imm32Effect p dst imm t) t' = _ := by lift_value [subR64Imm32Effect]

@[cfg_eval] theorem_by subR64Imm32Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR64Imm32Effect p dst imm t) t' = _ := by lift_value [subR64Imm32Effect]

@[cfg_eval] theorem_by subR64Imm32Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR64Imm32Effect p dst imm t) t' = _ := by lift_value [subR64Imm32Effect]

@[cfg_eval] theorem_by subR64Imm32Effect_AF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR64Imm32Effect p dst imm t) t' = _ := by lift_value [subR64Imm32Effect]

@[cfg_eval] theorem_by subR64Imm32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR64Imm32Effect p dst imm t) t' = _ := by lift_value [subR64Imm32Effect]

@[cfg_eval] theorem_by subR64Imm32Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR64Imm32Effect p dst imm t) t' = _ := by lift_value [subR64Imm32Effect]

@[cfg_eval] theorem_by subR64Imm32Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR64Imm32Effect p dst imm t) t' = _ := by lift_value [subR64Imm32Effect]

@[cfg_eval] theorem subR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR64Imm32Effect_components])

@[cfg_eval] theorem_by xorR16Imm16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR16Imm16Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm16Effect]

@[cfg_eval] theorem_by xorR16Imm16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR16Imm16Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm16Effect]

@[cfg_eval] theorem_by xorR16Imm16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR16Imm16Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm16Effect]

@[cfg_eval] theorem_by xorR16Imm16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR16Imm16Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm16Effect]

@[cfg_eval] theorem_by xorR16Imm16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR16Imm16Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm16Effect]

@[cfg_eval] theorem_by xorR16Imm16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR16Imm16Effect p len dst imm t) t' = _ := by lift_value [xorR16Imm16Effect]

@[cfg_eval] theorem xorR16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR16Imm16Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR16Imm16Effect_components])

@[cfg_eval] theorem_by xorR32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR32Imm32Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm32Effect]

@[cfg_eval] theorem_by xorR32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR32Imm32Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm32Effect]

@[cfg_eval] theorem_by xorR32Imm32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR32Imm32Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm32Effect]

@[cfg_eval] theorem_by xorR32Imm32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR32Imm32Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm32Effect]

@[cfg_eval] theorem_by xorR32Imm32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR32Imm32Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm32Effect]

@[cfg_eval] theorem_by xorR32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR32Imm32Effect p len dst imm t) t' = _ := by lift_value [xorR32Imm32Effect]

@[cfg_eval] theorem xorR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR32Imm32Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR32Imm32Effect_components])

@[cfg_eval] theorem_by xorR64Imm32Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR64Imm32Effect p dst imm t) t' = _ := by lift_value [xorR64Imm32Effect]

@[cfg_eval] theorem_by xorR64Imm32Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR64Imm32Effect p dst imm t) t' = _ := by lift_value [xorR64Imm32Effect]

@[cfg_eval] theorem_by xorR64Imm32Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR64Imm32Effect p dst imm t) t' = _ := by lift_value [xorR64Imm32Effect]

@[cfg_eval] theorem_by xorR64Imm32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR64Imm32Effect p dst imm t) t' = _ := by lift_value [xorR64Imm32Effect]

@[cfg_eval] theorem_by xorR64Imm32Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR64Imm32Effect p dst imm t) t' = _ := by lift_value [xorR64Imm32Effect]

@[cfg_eval] theorem_by xorR64Imm32Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR64Imm32Effect p dst imm t) t' = _ := by lift_value [xorR64Imm32Effect]

@[cfg_eval] theorem xorR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR64Imm32Effect_components])

@[cfg_eval] theorem_by cmpR16Imm16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR16Imm16Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm16Effect]

@[cfg_eval] theorem_by cmpR16Imm16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR16Imm16Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm16Effect]

@[cfg_eval] theorem_by cmpR16Imm16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR16Imm16Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm16Effect]

@[cfg_eval] theorem_by cmpR16Imm16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR16Imm16Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm16Effect]

@[cfg_eval] theorem_by cmpR16Imm16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR16Imm16Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm16Effect]

@[cfg_eval] theorem_by cmpR16Imm16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR16Imm16Effect p len dst imm t) t' = _ := by lift_value [cmpR16Imm16Effect]

@[cfg_eval] theorem cmpR16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR16Imm16Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR16Imm16Effect_components])

@[cfg_eval] theorem_by cmpR32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR32Imm32Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm32Effect]

@[cfg_eval] theorem_by cmpR32Imm32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR32Imm32Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm32Effect]

@[cfg_eval] theorem_by cmpR32Imm32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR32Imm32Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm32Effect]

@[cfg_eval] theorem_by cmpR32Imm32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR32Imm32Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm32Effect]

@[cfg_eval] theorem_by cmpR32Imm32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR32Imm32Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm32Effect]

@[cfg_eval] theorem_by cmpR32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR32Imm32Effect p len dst imm t) t' = _ := by lift_value [cmpR32Imm32Effect]

@[cfg_eval] theorem cmpR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR32Imm32Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR32Imm32Effect_components])

@[cfg_eval] theorem_by cmpR64Imm32Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR64Imm32Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm32Effect]

@[cfg_eval] theorem_by cmpR64Imm32Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR64Imm32Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm32Effect]

@[cfg_eval] theorem_by cmpR64Imm32Effect_AF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR64Imm32Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm32Effect]

@[cfg_eval] theorem_by cmpR64Imm32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR64Imm32Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm32Effect]

@[cfg_eval] theorem_by cmpR64Imm32Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR64Imm32Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm32Effect]

@[cfg_eval] theorem_by cmpR64Imm32Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR64Imm32Effect p dst imm t) t' = _ := by lift_value [cmpR64Imm32Effect]

@[cfg_eval] theorem cmpR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR64Imm32Effect_components])

@[cfg_eval] theorem_by testR16Imm16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (testR16Imm16Effect p len dst imm t) t' = _ := by lift_value [testR16Imm16Effect]

@[cfg_eval] theorem_by testR16Imm16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (testR16Imm16Effect p len dst imm t) t' = _ := by lift_value [testR16Imm16Effect]

@[cfg_eval] theorem_by testR16Imm16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testR16Imm16Effect p len dst imm t) t' = _ := by lift_value [testR16Imm16Effect]

@[cfg_eval] theorem_by testR16Imm16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (testR16Imm16Effect p len dst imm t) t' = _ := by lift_value [testR16Imm16Effect]

@[cfg_eval] theorem_by testR16Imm16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (testR16Imm16Effect p len dst imm t) t' = _ := by lift_value [testR16Imm16Effect]

@[cfg_eval] theorem testR16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testR16Imm16Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testR16Imm16Effect_components])

@[cfg_eval] theorem_by testR32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (testR32Imm32Effect p len dst imm t) t' = _ := by lift_value [testR32Imm32Effect]

@[cfg_eval] theorem_by testR32Imm32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (testR32Imm32Effect p len dst imm t) t' = _ := by lift_value [testR32Imm32Effect]

@[cfg_eval] theorem_by testR32Imm32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testR32Imm32Effect p len dst imm t) t' = _ := by lift_value [testR32Imm32Effect]

@[cfg_eval] theorem_by testR32Imm32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (testR32Imm32Effect p len dst imm t) t' = _ := by lift_value [testR32Imm32Effect]

@[cfg_eval] theorem_by testR32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (testR32Imm32Effect p len dst imm t) t' = _ := by lift_value [testR32Imm32Effect]

@[cfg_eval] theorem testR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testR32Imm32Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testR32Imm32Effect_components])

@[cfg_eval] theorem_by testR64Imm32Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (testR64Imm32Effect p dst imm t) t' = _ := by lift_value [testR64Imm32Effect]

@[cfg_eval] theorem_by testR64Imm32Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (testR64Imm32Effect p dst imm t) t' = _ := by lift_value [testR64Imm32Effect]

@[cfg_eval] theorem_by testR64Imm32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testR64Imm32Effect p dst imm t) t' = _ := by lift_value [testR64Imm32Effect]

@[cfg_eval] theorem_by testR64Imm32Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (testR64Imm32Effect p dst imm t) t' = _ := by lift_value [testR64Imm32Effect]

@[cfg_eval] theorem_by testR64Imm32Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (testR64Imm32Effect p dst imm t) t' = _ := by lift_value [testR64Imm32Effect]

@[cfg_eval] theorem testR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testR64Imm32Effect_components])

@[cfg_eval] theorem_by addR8Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR8Imm8Effect p len dst imm t) t' = _ := by lift_value [addR8Imm8Effect]

@[cfg_eval] theorem_by addR8Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR8Imm8Effect p len dst imm t) t' = _ := by lift_value [addR8Imm8Effect]

@[cfg_eval] theorem_by addR8Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR8Imm8Effect p len dst imm t) t' = _ := by lift_value [addR8Imm8Effect]

@[cfg_eval] theorem_by addR8Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR8Imm8Effect p len dst imm t) t' = _ := by lift_value [addR8Imm8Effect]

@[cfg_eval] theorem_by addR8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR8Imm8Effect p len dst imm t) t' = _ := by lift_value [addR8Imm8Effect]

@[cfg_eval] theorem_by addR8Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR8Imm8Effect p len dst imm t) t' = _ := by lift_value [addR8Imm8Effect]

@[cfg_eval] theorem_by addR8Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR8Imm8Effect p len dst imm t) t' = _ := by lift_value [addR8Imm8Effect]

@[cfg_eval] theorem addR8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR8Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR8Imm8Effect_components])

@[cfg_eval] theorem_by orR8Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR8Imm8Effect p len dst imm t) t' = _ := by lift_value [orR8Imm8Effect]

@[cfg_eval] theorem_by orR8Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR8Imm8Effect p len dst imm t) t' = _ := by lift_value [orR8Imm8Effect]

@[cfg_eval] theorem_by orR8Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR8Imm8Effect p len dst imm t) t' = _ := by lift_value [orR8Imm8Effect]

@[cfg_eval] theorem_by orR8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR8Imm8Effect p len dst imm t) t' = _ := by lift_value [orR8Imm8Effect]

@[cfg_eval] theorem_by orR8Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR8Imm8Effect p len dst imm t) t' = _ := by lift_value [orR8Imm8Effect]

@[cfg_eval] theorem_by orR8Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR8Imm8Effect p len dst imm t) t' = _ := by lift_value [orR8Imm8Effect]

@[cfg_eval] theorem orR8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR8Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR8Imm8Effect_components])

@[cfg_eval] theorem_by adcR8Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR8Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR8Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR8Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR8Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR8Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR8Imm8Effect, atFlags]

@[cfg_eval] theorem adcR8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR8Imm8Effect p len dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR8Imm8Effect_components])

@[cfg_eval] theorem_by sbbR8Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR8Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR8Imm8Effect, atFlags]

@[cfg_eval] theorem sbbR8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR8Imm8Effect p len dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR8Imm8Effect_components])

@[cfg_eval] theorem_by andR8Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR8Imm8Effect p len dst imm t) t' = _ := by lift_value [andR8Imm8Effect]

@[cfg_eval] theorem_by andR8Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR8Imm8Effect p len dst imm t) t' = _ := by lift_value [andR8Imm8Effect]

@[cfg_eval] theorem_by andR8Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR8Imm8Effect p len dst imm t) t' = _ := by lift_value [andR8Imm8Effect]

@[cfg_eval] theorem_by andR8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR8Imm8Effect p len dst imm t) t' = _ := by lift_value [andR8Imm8Effect]

@[cfg_eval] theorem_by andR8Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR8Imm8Effect p len dst imm t) t' = _ := by lift_value [andR8Imm8Effect]

@[cfg_eval] theorem_by andR8Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR8Imm8Effect p len dst imm t) t' = _ := by lift_value [andR8Imm8Effect]

@[cfg_eval] theorem andR8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR8Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR8Imm8Effect_components])

@[cfg_eval] theorem_by subR8Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR8Imm8Effect p len dst imm t) t' = _ := by lift_value [subR8Imm8Effect]

@[cfg_eval] theorem_by subR8Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR8Imm8Effect p len dst imm t) t' = _ := by lift_value [subR8Imm8Effect]

@[cfg_eval] theorem_by subR8Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR8Imm8Effect p len dst imm t) t' = _ := by lift_value [subR8Imm8Effect]

@[cfg_eval] theorem_by subR8Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR8Imm8Effect p len dst imm t) t' = _ := by lift_value [subR8Imm8Effect]

@[cfg_eval] theorem_by subR8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR8Imm8Effect p len dst imm t) t' = _ := by lift_value [subR8Imm8Effect]

@[cfg_eval] theorem_by subR8Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR8Imm8Effect p len dst imm t) t' = _ := by lift_value [subR8Imm8Effect]

@[cfg_eval] theorem_by subR8Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR8Imm8Effect p len dst imm t) t' = _ := by lift_value [subR8Imm8Effect]

@[cfg_eval] theorem subR8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR8Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR8Imm8Effect_components])

@[cfg_eval] theorem_by xorR8Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR8Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR8Imm8Effect]

@[cfg_eval] theorem_by xorR8Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR8Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR8Imm8Effect]

@[cfg_eval] theorem_by xorR8Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR8Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR8Imm8Effect]

@[cfg_eval] theorem_by xorR8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR8Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR8Imm8Effect]

@[cfg_eval] theorem_by xorR8Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR8Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR8Imm8Effect]

@[cfg_eval] theorem_by xorR8Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR8Imm8Effect p len dst imm t) t' = _ := by lift_value [xorR8Imm8Effect]

@[cfg_eval] theorem xorR8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR8Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR8Imm8Effect_components])

@[cfg_eval] theorem_by cmpR8Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR8Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR8Imm8Effect]

@[cfg_eval] theorem_by cmpR8Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR8Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR8Imm8Effect]

@[cfg_eval] theorem_by cmpR8Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR8Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR8Imm8Effect]

@[cfg_eval] theorem_by cmpR8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR8Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR8Imm8Effect]

@[cfg_eval] theorem_by cmpR8Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR8Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR8Imm8Effect]

@[cfg_eval] theorem_by cmpR8Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR8Imm8Effect p len dst imm t) t' = _ := by lift_value [cmpR8Imm8Effect]

@[cfg_eval] theorem cmpR8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR8Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR8Imm8Effect_components])

@[cfg_eval] theorem_by testR8Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (testR8Imm8Effect p dst imm t) t' = _ := by lift_value [testR8Imm8Effect]

@[cfg_eval] theorem_by testR8Imm8Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (testR8Imm8Effect p dst imm t) t' = _ := by lift_value [testR8Imm8Effect]

@[cfg_eval] theorem_by testR8Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testR8Imm8Effect p dst imm t) t' = _ := by lift_value [testR8Imm8Effect]

@[cfg_eval] theorem_by testR8Imm8Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (testR8Imm8Effect p dst imm t) t' = _ := by lift_value [testR8Imm8Effect]

@[cfg_eval] theorem_by testR8Imm8Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (testR8Imm8Effect p dst imm t) t' = _ := by lift_value [testR8Imm8Effect]

@[cfg_eval] theorem testR8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testR8Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testR8Imm8Effect_components])

@[cfg_eval] theorem_by testR8Imm8LowEffect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (testR8Imm8LowEffect p dst imm t) t' = _ := by lift_value [testR8Imm8LowEffect]

@[cfg_eval] theorem_by testR8Imm8LowEffect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (testR8Imm8LowEffect p dst imm t) t' = _ := by lift_value [testR8Imm8LowEffect]

@[cfg_eval] theorem_by testR8Imm8LowEffect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testR8Imm8LowEffect p dst imm t) t' = _ := by lift_value [testR8Imm8LowEffect]

@[cfg_eval] theorem_by testR8Imm8LowEffect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (testR8Imm8LowEffect p dst imm t) t' = _ := by lift_value [testR8Imm8LowEffect]

@[cfg_eval] theorem_by testR8Imm8LowEffect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (testR8Imm8LowEffect p dst imm t) t' = _ := by lift_value [testR8Imm8LowEffect]

@[cfg_eval] theorem testR8Imm8LowEffect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testR8Imm8LowEffect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testR8Imm8LowEffect_components])

@[cfg_eval] theorem_by addAlImm8Effect_rax (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (addAlImm8Effect p imm t) t' = _ := by lift_value [addAlImm8Effect]

@[cfg_eval] theorem_by addAlImm8Effect_CF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (addAlImm8Effect p imm t) t' = _ := by lift_value [addAlImm8Effect]

@[cfg_eval] theorem_by addAlImm8Effect_PF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (addAlImm8Effect p imm t) t' = _ := by lift_value [addAlImm8Effect]

@[cfg_eval] theorem_by addAlImm8Effect_AF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (addAlImm8Effect p imm t) t' = _ := by lift_value [addAlImm8Effect]

@[cfg_eval] theorem_by addAlImm8Effect_ZF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addAlImm8Effect p imm t) t' = _ := by lift_value [addAlImm8Effect]

@[cfg_eval] theorem_by addAlImm8Effect_SF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (addAlImm8Effect p imm t) t' = _ := by lift_value [addAlImm8Effect]

@[cfg_eval] theorem_by addAlImm8Effect_OF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (addAlImm8Effect p imm t) t' = _ := by lift_value [addAlImm8Effect]

@[cfg_eval] theorem addAlImm8Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addAlImm8Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addAlImm8Effect_components])

@[cfg_eval] theorem_by orAlImm8Effect_rax (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (orAlImm8Effect p imm t) t' = _ := by lift_value [orAlImm8Effect]

@[cfg_eval] theorem_by orAlImm8Effect_CF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (orAlImm8Effect p imm t) t' = _ := by lift_value [orAlImm8Effect]

@[cfg_eval] theorem_by orAlImm8Effect_PF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (orAlImm8Effect p imm t) t' = _ := by lift_value [orAlImm8Effect]

@[cfg_eval] theorem_by orAlImm8Effect_ZF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orAlImm8Effect p imm t) t' = _ := by lift_value [orAlImm8Effect]

@[cfg_eval] theorem_by orAlImm8Effect_SF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (orAlImm8Effect p imm t) t' = _ := by lift_value [orAlImm8Effect]

@[cfg_eval] theorem_by orAlImm8Effect_OF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (orAlImm8Effect p imm t) t' = _ := by lift_value [orAlImm8Effect]

@[cfg_eval] theorem orAlImm8Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orAlImm8Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orAlImm8Effect_components])

@[cfg_eval] theorem_by adcAlImm8Effect_rax (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (atFlags StatusFlags.CF (adcAlImm8Effect p imm) t) t' = _ := by lift_value [adcAlImm8Effect, atFlags]

@[cfg_eval] theorem_by adcAlImm8Effect_CF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcAlImm8Effect p imm) t) t' = _ := by lift_value [adcAlImm8Effect, atFlags]

@[cfg_eval] theorem_by adcAlImm8Effect_PF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcAlImm8Effect p imm) t) t' = _ := by lift_value [adcAlImm8Effect, atFlags]

@[cfg_eval] theorem_by adcAlImm8Effect_AF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcAlImm8Effect p imm) t) t' = _ := by lift_value [adcAlImm8Effect, atFlags]

@[cfg_eval] theorem_by adcAlImm8Effect_ZF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcAlImm8Effect p imm) t) t' = _ := by lift_value [adcAlImm8Effect, atFlags]

@[cfg_eval] theorem_by adcAlImm8Effect_SF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcAlImm8Effect p imm) t) t' = _ := by lift_value [adcAlImm8Effect, atFlags]

@[cfg_eval] theorem_by adcAlImm8Effect_OF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcAlImm8Effect p imm) t) t' = _ := by lift_value [adcAlImm8Effect, atFlags]

@[cfg_eval] theorem adcAlImm8Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcAlImm8Effect p imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcAlImm8Effect_components])

@[cfg_eval] theorem_by sbbAlImm8Effect_rax (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (atFlags StatusFlags.CF (sbbAlImm8Effect p imm) t) t' = _ := by lift_value [sbbAlImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbAlImm8Effect_CF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbAlImm8Effect p imm) t) t' = _ := by lift_value [sbbAlImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbAlImm8Effect_PF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbAlImm8Effect p imm) t) t' = _ := by lift_value [sbbAlImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbAlImm8Effect_AF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbAlImm8Effect p imm) t) t' = _ := by lift_value [sbbAlImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbAlImm8Effect_ZF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbAlImm8Effect p imm) t) t' = _ := by lift_value [sbbAlImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbAlImm8Effect_SF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbAlImm8Effect p imm) t) t' = _ := by lift_value [sbbAlImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbAlImm8Effect_OF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbAlImm8Effect p imm) t) t' = _ := by lift_value [sbbAlImm8Effect, atFlags]

@[cfg_eval] theorem sbbAlImm8Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbAlImm8Effect p imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbAlImm8Effect_components])

@[cfg_eval] theorem_by andAlImm8Effect_rax (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (andAlImm8Effect p imm t) t' = _ := by lift_value [andAlImm8Effect]

@[cfg_eval] theorem_by andAlImm8Effect_CF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (andAlImm8Effect p imm t) t' = _ := by lift_value [andAlImm8Effect]

@[cfg_eval] theorem_by andAlImm8Effect_PF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (andAlImm8Effect p imm t) t' = _ := by lift_value [andAlImm8Effect]

@[cfg_eval] theorem_by andAlImm8Effect_ZF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andAlImm8Effect p imm t) t' = _ := by lift_value [andAlImm8Effect]

@[cfg_eval] theorem_by andAlImm8Effect_SF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (andAlImm8Effect p imm t) t' = _ := by lift_value [andAlImm8Effect]

@[cfg_eval] theorem_by andAlImm8Effect_OF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (andAlImm8Effect p imm t) t' = _ := by lift_value [andAlImm8Effect]

@[cfg_eval] theorem andAlImm8Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andAlImm8Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andAlImm8Effect_components])

@[cfg_eval] theorem_by subAlImm8Effect_rax (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (subAlImm8Effect p imm t) t' = _ := by lift_value [subAlImm8Effect]

@[cfg_eval] theorem_by subAlImm8Effect_CF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (subAlImm8Effect p imm t) t' = _ := by lift_value [subAlImm8Effect]

@[cfg_eval] theorem_by subAlImm8Effect_PF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (subAlImm8Effect p imm t) t' = _ := by lift_value [subAlImm8Effect]

@[cfg_eval] theorem_by subAlImm8Effect_AF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (subAlImm8Effect p imm t) t' = _ := by lift_value [subAlImm8Effect]

@[cfg_eval] theorem_by subAlImm8Effect_ZF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subAlImm8Effect p imm t) t' = _ := by lift_value [subAlImm8Effect]

@[cfg_eval] theorem_by subAlImm8Effect_SF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (subAlImm8Effect p imm t) t' = _ := by lift_value [subAlImm8Effect]

@[cfg_eval] theorem_by subAlImm8Effect_OF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (subAlImm8Effect p imm t) t' = _ := by lift_value [subAlImm8Effect]

@[cfg_eval] theorem subAlImm8Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subAlImm8Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subAlImm8Effect_components])

end ChaCha20Poly1305.Proofs.Lift
