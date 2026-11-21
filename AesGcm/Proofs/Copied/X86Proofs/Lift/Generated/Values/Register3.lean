import AesGcm.Proofs.Copied.X86Proofs.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.AccImm32.Triple
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.And.Generated.AccImm32.Triple
import X86Proofs.Instructions.Cmp.Generated.AccImm32.Triple
import X86Proofs.Instructions.Cmp.Generated.AccImm8.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Dec.Generated.R8.Triple
import X86Proofs.Instructions.Inc.Generated.R.Triple
import X86Proofs.Instructions.Inc.Generated.R8.Triple
import X86Proofs.Instructions.Neg.Generated.R.Triple
import X86Proofs.Instructions.Neg.Generated.R8.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Not.Generated.R8.Triple
import X86Proofs.Instructions.Or.Generated.AccImm32.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.Ror.Generated.R.Triple
import X86Proofs.Instructions.Sbb.Generated.AccImm32.Triple
import X86Proofs.Instructions.Shl.Generated.R.Triple
import X86Proofs.Instructions.Sub.Generated.AccImm32.Triple
import X86Proofs.Instructions.Test.Generated.AccImm32.Triple
import X86Proofs.Instructions.Test.Generated.AccImm8.Triple
import X86Proofs.Instructions.Xor.Generated.AccImm32.Triple
import X86Proofs.Instructions.Xor.Generated.AccImm8.Triple

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG

@[cfg_eval] theorem_by andEaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (andEaxImm32Effect p imm t) t' = _ := by lift_value [andEaxImm32Effect]

@[cfg_eval] theorem andEaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andEaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andEaxImm32Effect_components])

@[cfg_eval] theorem_by incR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (incR32Effect p len dst t) t' = _ := by lift_value [incR32Effect, incSpec]

@[cfg_eval] theorem incR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (incR32Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [incR32Effect_components])

@[cfg_eval] theorem_by incR64Effect_dst (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (incR64Effect p dst t) t' = _ := by lift_value [incR64Effect, incSpec]

@[cfg_eval] theorem incR64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (incR64Effect p dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [incR64Effect_components])

@[cfg_eval] theorem_by notR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (notR32Effect p len dst t) t' = _ := by lift_value [notR32Effect]

@[cfg_eval] theorem notR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (notR32Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [notR32Effect_components])

@[cfg_eval] theorem_by negR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (negR32Effect p len dst t) t' = _ := by lift_value [negR32Effect]

@[cfg_eval] theorem negR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (negR32Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [negR32Effect_components])

@[cfg_eval] theorem_by rolR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR16Effect p len dst c t) t' = _ := by lift_value [rolR16Effect, rolFlags]

@[cfg_eval] theorem rolR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rolR16Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rolR16Effect_components])

@[cfg_eval] theorem_by rolR64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR64Effect p len dst c t) t' = _ := by lift_value [rolR64Effect, rolFlags]

@[cfg_eval] theorem rolR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rolR64Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rolR64Effect_components])

@[cfg_eval] theorem_by rorR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rorR16Effect p len dst c t) t' = _ := by lift_value [rorR16Effect, rorFlags]

@[cfg_eval] theorem rorR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rorR16Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rorR16Effect_components])

@[cfg_eval] theorem_by shlR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR32Effect p len dst c t) t' = _ := by lift_value [shlR32Effect, shlFlags]

@[cfg_eval] theorem shlR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR32Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR32Effect_components])

@[cfg_eval] theorem_by shlR64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR64Effect p len dst c t) t' = _ := by lift_value [shlR64Effect, shlFlags]

@[cfg_eval] theorem shlR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR64Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR64Effect_components])

end X86Proofs.Lift
