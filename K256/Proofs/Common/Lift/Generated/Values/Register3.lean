import K256.Proofs.Common.Lift.Eval
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
namespace K256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG

@[cfg_eval] theorem_by cmpAlImm8Effect_CF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpAlImm8Effect p imm t) t' = _ := by lift_value [cmpAlImm8Effect]

@[cfg_eval] theorem_by cmpAlImm8Effect_PF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpAlImm8Effect p imm t) t' = _ := by lift_value [cmpAlImm8Effect]

@[cfg_eval] theorem_by cmpAlImm8Effect_AF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpAlImm8Effect p imm t) t' = _ := by lift_value [cmpAlImm8Effect]

@[cfg_eval] theorem_by cmpAlImm8Effect_ZF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpAlImm8Effect p imm t) t' = _ := by lift_value [cmpAlImm8Effect]

@[cfg_eval] theorem_by cmpAlImm8Effect_SF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpAlImm8Effect p imm t) t' = _ := by lift_value [cmpAlImm8Effect]

@[cfg_eval] theorem_by cmpAlImm8Effect_OF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpAlImm8Effect p imm t) t' = _ := by lift_value [cmpAlImm8Effect]

@[cfg_eval] theorem cmpAlImm8Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpAlImm8Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpAlImm8Effect_components])

@[cfg_eval] theorem_by testAlImm8Effect_CF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (testAlImm8Effect p imm t) t' = _ := by lift_value [testAlImm8Effect]

@[cfg_eval] theorem_by testAlImm8Effect_PF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (testAlImm8Effect p imm t) t' = _ := by lift_value [testAlImm8Effect]

@[cfg_eval] theorem_by testAlImm8Effect_ZF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testAlImm8Effect p imm t) t' = _ := by lift_value [testAlImm8Effect]

@[cfg_eval] theorem_by testAlImm8Effect_SF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (testAlImm8Effect p imm t) t' = _ := by lift_value [testAlImm8Effect]

@[cfg_eval] theorem_by testAlImm8Effect_OF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (testAlImm8Effect p imm t) t' = _ := by lift_value [testAlImm8Effect]

@[cfg_eval] theorem testAlImm8Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testAlImm8Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testAlImm8Effect_components])

@[cfg_eval] theorem_by orEaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (orEaxImm32Effect p imm t) t' = _ := by lift_value [orEaxImm32Effect]

@[cfg_eval] theorem_by orEaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (orEaxImm32Effect p imm t) t' = _ := by lift_value [orEaxImm32Effect]

@[cfg_eval] theorem_by orEaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (orEaxImm32Effect p imm t) t' = _ := by lift_value [orEaxImm32Effect]

@[cfg_eval] theorem_by orEaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orEaxImm32Effect p imm t) t' = _ := by lift_value [orEaxImm32Effect]

@[cfg_eval] theorem_by orEaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (orEaxImm32Effect p imm t) t' = _ := by lift_value [orEaxImm32Effect]

@[cfg_eval] theorem_by orEaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (orEaxImm32Effect p imm t) t' = _ := by lift_value [orEaxImm32Effect]

@[cfg_eval] theorem orEaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orEaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orEaxImm32Effect_components])

@[cfg_eval] theorem_by andEaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (andEaxImm32Effect p imm t) t' = _ := by lift_value [andEaxImm32Effect]

@[cfg_eval] theorem_by andEaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (andEaxImm32Effect p imm t) t' = _ := by lift_value [andEaxImm32Effect]

@[cfg_eval] theorem_by andEaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (andEaxImm32Effect p imm t) t' = _ := by lift_value [andEaxImm32Effect]

@[cfg_eval] theorem_by andEaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andEaxImm32Effect p imm t) t' = _ := by lift_value [andEaxImm32Effect]

@[cfg_eval] theorem_by andEaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (andEaxImm32Effect p imm t) t' = _ := by lift_value [andEaxImm32Effect]

@[cfg_eval] theorem_by andEaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (andEaxImm32Effect p imm t) t' = _ := by lift_value [andEaxImm32Effect]

@[cfg_eval] theorem andEaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andEaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andEaxImm32Effect_components])

@[cfg_eval] theorem_by incR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (incR32Effect p len dst t) t' = _ := by lift_value [incR32Effect, incSpec]

@[cfg_eval] theorem_by incR32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (incR32Effect p len dst t) t' = _ := by lift_value [incR32Effect, incSpec]

@[cfg_eval] theorem_by incR32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (incR32Effect p len dst t) t' = _ := by lift_value [incR32Effect, incSpec]

@[cfg_eval] theorem_by incR32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (incR32Effect p len dst t) t' = _ := by lift_value [incR32Effect, incSpec]

@[cfg_eval] theorem_by incR32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (incR32Effect p len dst t) t' = _ := by lift_value [incR32Effect, incSpec]

@[cfg_eval] theorem_by incR32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (incR32Effect p len dst t) t' = _ := by lift_value [incR32Effect, incSpec]

@[cfg_eval] theorem_by incR32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (incR32Effect p len dst t) t' = _ := by lift_value [incR32Effect, incSpec]

@[cfg_eval] theorem incR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (incR32Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [incR32Effect_components])

@[cfg_eval] theorem_by incR64Effect_dst (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (incR64Effect p dst t) t' = _ := by lift_value [incR64Effect, incSpec]

@[cfg_eval] theorem_by incR64Effect_CF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (incR64Effect p dst t) t' = _ := by lift_value [incR64Effect, incSpec]

@[cfg_eval] theorem_by incR64Effect_PF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (incR64Effect p dst t) t' = _ := by lift_value [incR64Effect, incSpec]

@[cfg_eval] theorem_by incR64Effect_AF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (incR64Effect p dst t) t' = _ := by lift_value [incR64Effect, incSpec]

@[cfg_eval] theorem_by incR64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (incR64Effect p dst t) t' = _ := by lift_value [incR64Effect, incSpec]

@[cfg_eval] theorem_by incR64Effect_SF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (incR64Effect p dst t) t' = _ := by lift_value [incR64Effect, incSpec]

@[cfg_eval] theorem_by incR64Effect_OF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (incR64Effect p dst t) t' = _ := by lift_value [incR64Effect, incSpec]

@[cfg_eval] theorem incR64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (incR64Effect p dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [incR64Effect_components])

@[cfg_eval] theorem_by decR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (decR16Effect p len dst t) t' = _ := by lift_value [decR16Effect, decSpec]

@[cfg_eval] theorem_by decR16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (decR16Effect p len dst t) t' = _ := by lift_value [decR16Effect, decSpec]

@[cfg_eval] theorem_by decR16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (decR16Effect p len dst t) t' = _ := by lift_value [decR16Effect, decSpec]

@[cfg_eval] theorem_by decR16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (decR16Effect p len dst t) t' = _ := by lift_value [decR16Effect, decSpec]

@[cfg_eval] theorem_by decR16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (decR16Effect p len dst t) t' = _ := by lift_value [decR16Effect, decSpec]

@[cfg_eval] theorem_by decR16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (decR16Effect p len dst t) t' = _ := by lift_value [decR16Effect, decSpec]

@[cfg_eval] theorem_by decR16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (decR16Effect p len dst t) t' = _ := by lift_value [decR16Effect, decSpec]

@[cfg_eval] theorem decR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (decR16Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [decR16Effect_components])

@[cfg_eval] theorem_by decR64Effect_dst (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (decR64Effect p dst t) t' = _ := by lift_value [decR64Effect, decSpec]

@[cfg_eval] theorem_by decR64Effect_CF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (decR64Effect p dst t) t' = _ := by lift_value [decR64Effect, decSpec]

@[cfg_eval] theorem_by decR64Effect_PF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (decR64Effect p dst t) t' = _ := by lift_value [decR64Effect, decSpec]

@[cfg_eval] theorem_by decR64Effect_AF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (decR64Effect p dst t) t' = _ := by lift_value [decR64Effect, decSpec]

@[cfg_eval] theorem_by decR64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (decR64Effect p dst t) t' = _ := by lift_value [decR64Effect, decSpec]

@[cfg_eval] theorem_by decR64Effect_SF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (decR64Effect p dst t) t' = _ := by lift_value [decR64Effect, decSpec]

@[cfg_eval] theorem_by decR64Effect_OF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (decR64Effect p dst t) t' = _ := by lift_value [decR64Effect, decSpec]

@[cfg_eval] theorem decR64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (decR64Effect p dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [decR64Effect_components])

@[cfg_eval] theorem_by notR64Effect_dst (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (notR64Effect p dst t) t' = _ := by lift_value [notR64Effect]

@[cfg_eval] theorem notR64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (notR64Effect p dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [notR64Effect_components])

@[cfg_eval] theorem_by negR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (negR32Effect p len dst t) t' = _ := by lift_value [negR32Effect]

@[cfg_eval] theorem_by negR32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (negR32Effect p len dst t) t' = _ := by lift_value [negR32Effect]

@[cfg_eval] theorem_by negR32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (negR32Effect p len dst t) t' = _ := by lift_value [negR32Effect]

@[cfg_eval] theorem_by negR32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (negR32Effect p len dst t) t' = _ := by lift_value [negR32Effect]

@[cfg_eval] theorem_by negR32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (negR32Effect p len dst t) t' = _ := by lift_value [negR32Effect]

@[cfg_eval] theorem_by negR32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (negR32Effect p len dst t) t' = _ := by lift_value [negR32Effect]

@[cfg_eval] theorem_by negR32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (negR32Effect p len dst t) t' = _ := by lift_value [negR32Effect]

@[cfg_eval] theorem negR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (negR32Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [negR32Effect_components])

@[cfg_eval] theorem_by negR64Effect_dst (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (negR64Effect p dst t) t' = _ := by lift_value [negR64Effect]

@[cfg_eval] theorem_by negR64Effect_CF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (negR64Effect p dst t) t' = _ := by lift_value [negR64Effect]

@[cfg_eval] theorem_by negR64Effect_PF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (negR64Effect p dst t) t' = _ := by lift_value [negR64Effect]

@[cfg_eval] theorem_by negR64Effect_AF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (negR64Effect p dst t) t' = _ := by lift_value [negR64Effect]

@[cfg_eval] theorem_by negR64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (negR64Effect p dst t) t' = _ := by lift_value [negR64Effect]

@[cfg_eval] theorem_by negR64Effect_SF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (negR64Effect p dst t) t' = _ := by lift_value [negR64Effect]

@[cfg_eval] theorem_by negR64Effect_OF (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (negR64Effect p dst t) t' = _ := by lift_value [negR64Effect]

@[cfg_eval] theorem negR64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (negR64Effect p dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [negR64Effect_components])

@[cfg_eval] theorem_by negR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (negR8Effect p len dst t) t' = _ := by lift_value [negR8Effect]

@[cfg_eval] theorem_by negR8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (negR8Effect p len dst t) t' = _ := by lift_value [negR8Effect]

@[cfg_eval] theorem_by negR8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (negR8Effect p len dst t) t' = _ := by lift_value [negR8Effect]

@[cfg_eval] theorem_by negR8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (negR8Effect p len dst t) t' = _ := by lift_value [negR8Effect]

@[cfg_eval] theorem_by negR8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (negR8Effect p len dst t) t' = _ := by lift_value [negR8Effect]

@[cfg_eval] theorem_by negR8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (negR8Effect p len dst t) t' = _ := by lift_value [negR8Effect]

@[cfg_eval] theorem_by negR8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (negR8Effect p len dst t) t' = _ := by lift_value [negR8Effect]

@[cfg_eval] theorem negR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (negR8Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [negR8Effect_components])

@[cfg_eval] theorem_by shlR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR32Effect p len dst c t) t' = _ := by lift_value [shlR32Effect, shlFlags]

@[cfg_eval] theorem_by shlR32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shlR32Effect p len dst c t) t' = _ := by lift_value [shlR32Effect, shlFlags]

@[cfg_eval] theorem_by shlR32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shlR32Effect p len dst c t) t' = _ := by lift_value [shlR32Effect, shlFlags]

@[cfg_eval] theorem_by shlR32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shlR32Effect p len dst c t) t' = _ := by lift_value [shlR32Effect, shlFlags]

@[cfg_eval] theorem_by shlR32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shlR32Effect p len dst c t) t' = _ := by lift_value [shlR32Effect, shlFlags]

@[cfg_eval] theorem_by shlR32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shlR32Effect p len dst c t) t' = _ := by lift_value [shlR32Effect, shlFlags]

@[cfg_eval] theorem_by shlR32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shlR32Effect p len dst c t) t' = _ := by lift_value [shlR32Effect, shlFlags]

@[cfg_eval] theorem shlR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR32Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR32Effect_components])

@[cfg_eval] theorem_by shlR64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR64Effect p len dst c t) t' = _ := by lift_value [shlR64Effect, shlFlags]

@[cfg_eval] theorem_by shlR64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shlR64Effect p len dst c t) t' = _ := by lift_value [shlR64Effect, shlFlags]

@[cfg_eval] theorem_by shlR64Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shlR64Effect p len dst c t) t' = _ := by lift_value [shlR64Effect, shlFlags]

@[cfg_eval] theorem_by shlR64Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shlR64Effect p len dst c t) t' = _ := by lift_value [shlR64Effect, shlFlags]

@[cfg_eval] theorem_by shlR64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shlR64Effect p len dst c t) t' = _ := by lift_value [shlR64Effect, shlFlags]

@[cfg_eval] theorem_by shlR64Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shlR64Effect p len dst c t) t' = _ := by lift_value [shlR64Effect, shlFlags]

@[cfg_eval] theorem_by shlR64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shlR64Effect p len dst c t) t' = _ := by lift_value [shlR64Effect, shlFlags]

@[cfg_eval] theorem shlR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR64Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR64Effect_components])

end K256.Proofs.Lift
