import ChaCha20Poly1305.Proofs.Common.Lift.Eval
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

namespace ChaCha20Poly1305.Proofs.Lift
open X86Proofs

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG

@[cfg_eval] theorem_by xorAlImm8Effect_rax (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (xorAlImm8Effect p imm t) t' = _ := by lift_value [xorAlImm8Effect]

@[cfg_eval] theorem_by xorAlImm8Effect_CF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorAlImm8Effect p imm t) t' = _ := by lift_value [xorAlImm8Effect]

@[cfg_eval] theorem_by xorAlImm8Effect_PF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorAlImm8Effect p imm t) t' = _ := by lift_value [xorAlImm8Effect]

@[cfg_eval] theorem_by xorAlImm8Effect_ZF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorAlImm8Effect p imm t) t' = _ := by lift_value [xorAlImm8Effect]

@[cfg_eval] theorem_by xorAlImm8Effect_SF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorAlImm8Effect p imm t) t' = _ := by lift_value [xorAlImm8Effect]

@[cfg_eval] theorem_by xorAlImm8Effect_OF (p : BitVec 64) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorAlImm8Effect p imm t) t' = _ := by lift_value [xorAlImm8Effect]

@[cfg_eval] theorem xorAlImm8Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorAlImm8Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorAlImm8Effect_components])

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

@[cfg_eval] theorem_by addAxImm16Effect_rax (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (addAxImm16Effect p imm t) t' = _ := by lift_value [addAxImm16Effect]

@[cfg_eval] theorem_by addAxImm16Effect_CF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (addAxImm16Effect p imm t) t' = _ := by lift_value [addAxImm16Effect]

@[cfg_eval] theorem_by addAxImm16Effect_PF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (addAxImm16Effect p imm t) t' = _ := by lift_value [addAxImm16Effect]

@[cfg_eval] theorem_by addAxImm16Effect_AF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .AF).value (addAxImm16Effect p imm t) t' = _ := by lift_value [addAxImm16Effect]

@[cfg_eval] theorem_by addAxImm16Effect_ZF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addAxImm16Effect p imm t) t' = _ := by lift_value [addAxImm16Effect]

@[cfg_eval] theorem_by addAxImm16Effect_SF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (addAxImm16Effect p imm t) t' = _ := by lift_value [addAxImm16Effect]

@[cfg_eval] theorem_by addAxImm16Effect_OF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (addAxImm16Effect p imm t) t' = _ := by lift_value [addAxImm16Effect]

@[cfg_eval] theorem addAxImm16Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addAxImm16Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addAxImm16Effect_components])

@[cfg_eval] theorem_by addEaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (addEaxImm32Effect p imm t) t' = _ := by lift_value [addEaxImm32Effect]

@[cfg_eval] theorem_by addEaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (addEaxImm32Effect p imm t) t' = _ := by lift_value [addEaxImm32Effect]

@[cfg_eval] theorem_by addEaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (addEaxImm32Effect p imm t) t' = _ := by lift_value [addEaxImm32Effect]

@[cfg_eval] theorem_by addEaxImm32Effect_AF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (addEaxImm32Effect p imm t) t' = _ := by lift_value [addEaxImm32Effect]

@[cfg_eval] theorem_by addEaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addEaxImm32Effect p imm t) t' = _ := by lift_value [addEaxImm32Effect]

@[cfg_eval] theorem_by addEaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (addEaxImm32Effect p imm t) t' = _ := by lift_value [addEaxImm32Effect]

@[cfg_eval] theorem_by addEaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (addEaxImm32Effect p imm t) t' = _ := by lift_value [addEaxImm32Effect]

@[cfg_eval] theorem addEaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addEaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addEaxImm32Effect_components])

@[cfg_eval] theorem_by addRaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (addRaxImm32Effect p imm t) t' = _ := by lift_value [addRaxImm32Effect]

@[cfg_eval] theorem_by addRaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (addRaxImm32Effect p imm t) t' = _ := by lift_value [addRaxImm32Effect]

@[cfg_eval] theorem_by addRaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (addRaxImm32Effect p imm t) t' = _ := by lift_value [addRaxImm32Effect]

@[cfg_eval] theorem_by addRaxImm32Effect_AF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (addRaxImm32Effect p imm t) t' = _ := by lift_value [addRaxImm32Effect]

@[cfg_eval] theorem_by addRaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addRaxImm32Effect p imm t) t' = _ := by lift_value [addRaxImm32Effect]

@[cfg_eval] theorem_by addRaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (addRaxImm32Effect p imm t) t' = _ := by lift_value [addRaxImm32Effect]

@[cfg_eval] theorem_by addRaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (addRaxImm32Effect p imm t) t' = _ := by lift_value [addRaxImm32Effect]

@[cfg_eval] theorem addRaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addRaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addRaxImm32Effect_components])

@[cfg_eval] theorem_by orAxImm16Effect_rax (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (orAxImm16Effect p imm t) t' = _ := by lift_value [orAxImm16Effect]

@[cfg_eval] theorem_by orAxImm16Effect_CF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (orAxImm16Effect p imm t) t' = _ := by lift_value [orAxImm16Effect]

@[cfg_eval] theorem_by orAxImm16Effect_PF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (orAxImm16Effect p imm t) t' = _ := by lift_value [orAxImm16Effect]

@[cfg_eval] theorem_by orAxImm16Effect_ZF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orAxImm16Effect p imm t) t' = _ := by lift_value [orAxImm16Effect]

@[cfg_eval] theorem_by orAxImm16Effect_SF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (orAxImm16Effect p imm t) t' = _ := by lift_value [orAxImm16Effect]

@[cfg_eval] theorem_by orAxImm16Effect_OF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (orAxImm16Effect p imm t) t' = _ := by lift_value [orAxImm16Effect]

@[cfg_eval] theorem orAxImm16Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orAxImm16Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orAxImm16Effect_components])

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

@[cfg_eval] theorem_by orRaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (orRaxImm32Effect p imm t) t' = _ := by lift_value [orRaxImm32Effect]

@[cfg_eval] theorem_by orRaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (orRaxImm32Effect p imm t) t' = _ := by lift_value [orRaxImm32Effect]

@[cfg_eval] theorem_by orRaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (orRaxImm32Effect p imm t) t' = _ := by lift_value [orRaxImm32Effect]

@[cfg_eval] theorem_by orRaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orRaxImm32Effect p imm t) t' = _ := by lift_value [orRaxImm32Effect]

@[cfg_eval] theorem_by orRaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (orRaxImm32Effect p imm t) t' = _ := by lift_value [orRaxImm32Effect]

@[cfg_eval] theorem_by orRaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (orRaxImm32Effect p imm t) t' = _ := by lift_value [orRaxImm32Effect]

@[cfg_eval] theorem orRaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orRaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orRaxImm32Effect_components])

@[cfg_eval] theorem_by adcAxImm16Effect_rax (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (atFlags StatusFlags.CF (adcAxImm16Effect p imm) t) t' = _ := by lift_value [adcAxImm16Effect, atFlags]

@[cfg_eval] theorem_by adcAxImm16Effect_CF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcAxImm16Effect p imm) t) t' = _ := by lift_value [adcAxImm16Effect, atFlags]

@[cfg_eval] theorem_by adcAxImm16Effect_PF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcAxImm16Effect p imm) t) t' = _ := by lift_value [adcAxImm16Effect, atFlags]

@[cfg_eval] theorem_by adcAxImm16Effect_AF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcAxImm16Effect p imm) t) t' = _ := by lift_value [adcAxImm16Effect, atFlags]

@[cfg_eval] theorem_by adcAxImm16Effect_ZF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcAxImm16Effect p imm) t) t' = _ := by lift_value [adcAxImm16Effect, atFlags]

@[cfg_eval] theorem_by adcAxImm16Effect_SF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcAxImm16Effect p imm) t) t' = _ := by lift_value [adcAxImm16Effect, atFlags]

@[cfg_eval] theorem_by adcAxImm16Effect_OF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcAxImm16Effect p imm) t) t' = _ := by lift_value [adcAxImm16Effect, atFlags]

@[cfg_eval] theorem adcAxImm16Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcAxImm16Effect p imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcAxImm16Effect_components])

@[cfg_eval] theorem_by adcEaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (atFlags StatusFlags.CF (adcEaxImm32Effect p imm) t) t' = _ := by lift_value [adcEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcEaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcEaxImm32Effect p imm) t) t' = _ := by lift_value [adcEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcEaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcEaxImm32Effect p imm) t) t' = _ := by lift_value [adcEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcEaxImm32Effect_AF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcEaxImm32Effect p imm) t) t' = _ := by lift_value [adcEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcEaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcEaxImm32Effect p imm) t) t' = _ := by lift_value [adcEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcEaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcEaxImm32Effect p imm) t) t' = _ := by lift_value [adcEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcEaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcEaxImm32Effect p imm) t) t' = _ := by lift_value [adcEaxImm32Effect, atFlags]

@[cfg_eval] theorem adcEaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcEaxImm32Effect p imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcEaxImm32Effect_components])

@[cfg_eval] theorem_by adcRaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (atFlags StatusFlags.CF (adcRaxImm32Effect p imm) t) t' = _ := by lift_value [adcRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcRaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcRaxImm32Effect p imm) t) t' = _ := by lift_value [adcRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcRaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcRaxImm32Effect p imm) t) t' = _ := by lift_value [adcRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcRaxImm32Effect_AF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcRaxImm32Effect p imm) t) t' = _ := by lift_value [adcRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcRaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcRaxImm32Effect p imm) t) t' = _ := by lift_value [adcRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcRaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcRaxImm32Effect p imm) t) t' = _ := by lift_value [adcRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by adcRaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcRaxImm32Effect p imm) t) t' = _ := by lift_value [adcRaxImm32Effect, atFlags]

@[cfg_eval] theorem adcRaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcRaxImm32Effect p imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcRaxImm32Effect_components])

@[cfg_eval] theorem_by sbbAxImm16Effect_rax (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (atFlags StatusFlags.CF (sbbAxImm16Effect p imm) t) t' = _ := by lift_value [sbbAxImm16Effect, atFlags]

@[cfg_eval] theorem_by sbbAxImm16Effect_CF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbAxImm16Effect p imm) t) t' = _ := by lift_value [sbbAxImm16Effect, atFlags]

@[cfg_eval] theorem_by sbbAxImm16Effect_PF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbAxImm16Effect p imm) t) t' = _ := by lift_value [sbbAxImm16Effect, atFlags]

@[cfg_eval] theorem_by sbbAxImm16Effect_AF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbAxImm16Effect p imm) t) t' = _ := by lift_value [sbbAxImm16Effect, atFlags]

@[cfg_eval] theorem_by sbbAxImm16Effect_ZF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbAxImm16Effect p imm) t) t' = _ := by lift_value [sbbAxImm16Effect, atFlags]

@[cfg_eval] theorem_by sbbAxImm16Effect_SF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbAxImm16Effect p imm) t) t' = _ := by lift_value [sbbAxImm16Effect, atFlags]

@[cfg_eval] theorem_by sbbAxImm16Effect_OF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbAxImm16Effect p imm) t) t' = _ := by lift_value [sbbAxImm16Effect, atFlags]

@[cfg_eval] theorem sbbAxImm16Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbAxImm16Effect p imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbAxImm16Effect_components])

@[cfg_eval] theorem_by sbbEaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (atFlags StatusFlags.CF (sbbEaxImm32Effect p imm) t) t' = _ := by lift_value [sbbEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbEaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbEaxImm32Effect p imm) t) t' = _ := by lift_value [sbbEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbEaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbEaxImm32Effect p imm) t) t' = _ := by lift_value [sbbEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbEaxImm32Effect_AF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbEaxImm32Effect p imm) t) t' = _ := by lift_value [sbbEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbEaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbEaxImm32Effect p imm) t) t' = _ := by lift_value [sbbEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbEaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbEaxImm32Effect p imm) t) t' = _ := by lift_value [sbbEaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbEaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbEaxImm32Effect p imm) t) t' = _ := by lift_value [sbbEaxImm32Effect, atFlags]

@[cfg_eval] theorem sbbEaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbEaxImm32Effect p imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbEaxImm32Effect_components])

@[cfg_eval] theorem_by sbbRaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (atFlags StatusFlags.CF (sbbRaxImm32Effect p imm) t) t' = _ := by lift_value [sbbRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbRaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbRaxImm32Effect p imm) t) t' = _ := by lift_value [sbbRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbRaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbRaxImm32Effect p imm) t) t' = _ := by lift_value [sbbRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbRaxImm32Effect_AF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbRaxImm32Effect p imm) t) t' = _ := by lift_value [sbbRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbRaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbRaxImm32Effect p imm) t) t' = _ := by lift_value [sbbRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbRaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbRaxImm32Effect p imm) t) t' = _ := by lift_value [sbbRaxImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbRaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbRaxImm32Effect p imm) t) t' = _ := by lift_value [sbbRaxImm32Effect, atFlags]

@[cfg_eval] theorem sbbRaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbRaxImm32Effect p imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbRaxImm32Effect_components])

@[cfg_eval] theorem_by andAxImm16Effect_rax (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (andAxImm16Effect p imm t) t' = _ := by lift_value [andAxImm16Effect]

@[cfg_eval] theorem_by andAxImm16Effect_CF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (andAxImm16Effect p imm t) t' = _ := by lift_value [andAxImm16Effect]

@[cfg_eval] theorem_by andAxImm16Effect_PF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (andAxImm16Effect p imm t) t' = _ := by lift_value [andAxImm16Effect]

@[cfg_eval] theorem_by andAxImm16Effect_ZF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andAxImm16Effect p imm t) t' = _ := by lift_value [andAxImm16Effect]

@[cfg_eval] theorem_by andAxImm16Effect_SF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (andAxImm16Effect p imm t) t' = _ := by lift_value [andAxImm16Effect]

@[cfg_eval] theorem_by andAxImm16Effect_OF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (andAxImm16Effect p imm t) t' = _ := by lift_value [andAxImm16Effect]

@[cfg_eval] theorem andAxImm16Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andAxImm16Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andAxImm16Effect_components])

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

@[cfg_eval] theorem_by andRaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (andRaxImm32Effect p imm t) t' = _ := by lift_value [andRaxImm32Effect]

@[cfg_eval] theorem_by andRaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (andRaxImm32Effect p imm t) t' = _ := by lift_value [andRaxImm32Effect]

@[cfg_eval] theorem_by andRaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (andRaxImm32Effect p imm t) t' = _ := by lift_value [andRaxImm32Effect]

@[cfg_eval] theorem_by andRaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andRaxImm32Effect p imm t) t' = _ := by lift_value [andRaxImm32Effect]

@[cfg_eval] theorem_by andRaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (andRaxImm32Effect p imm t) t' = _ := by lift_value [andRaxImm32Effect]

@[cfg_eval] theorem_by andRaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (andRaxImm32Effect p imm t) t' = _ := by lift_value [andRaxImm32Effect]

@[cfg_eval] theorem andRaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andRaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andRaxImm32Effect_components])

@[cfg_eval] theorem_by subAxImm16Effect_rax (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (subAxImm16Effect p imm t) t' = _ := by lift_value [subAxImm16Effect]

@[cfg_eval] theorem_by subAxImm16Effect_CF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (subAxImm16Effect p imm t) t' = _ := by lift_value [subAxImm16Effect]

@[cfg_eval] theorem_by subAxImm16Effect_PF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (subAxImm16Effect p imm t) t' = _ := by lift_value [subAxImm16Effect]

@[cfg_eval] theorem_by subAxImm16Effect_AF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .AF).value (subAxImm16Effect p imm t) t' = _ := by lift_value [subAxImm16Effect]

@[cfg_eval] theorem_by subAxImm16Effect_ZF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subAxImm16Effect p imm t) t' = _ := by lift_value [subAxImm16Effect]

@[cfg_eval] theorem_by subAxImm16Effect_SF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (subAxImm16Effect p imm t) t' = _ := by lift_value [subAxImm16Effect]

@[cfg_eval] theorem_by subAxImm16Effect_OF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (subAxImm16Effect p imm t) t' = _ := by lift_value [subAxImm16Effect]

@[cfg_eval] theorem subAxImm16Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subAxImm16Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subAxImm16Effect_components])

@[cfg_eval] theorem_by subEaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (subEaxImm32Effect p imm t) t' = _ := by lift_value [subEaxImm32Effect]

@[cfg_eval] theorem_by subEaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (subEaxImm32Effect p imm t) t' = _ := by lift_value [subEaxImm32Effect]

@[cfg_eval] theorem_by subEaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (subEaxImm32Effect p imm t) t' = _ := by lift_value [subEaxImm32Effect]

@[cfg_eval] theorem_by subEaxImm32Effect_AF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (subEaxImm32Effect p imm t) t' = _ := by lift_value [subEaxImm32Effect]

@[cfg_eval] theorem_by subEaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subEaxImm32Effect p imm t) t' = _ := by lift_value [subEaxImm32Effect]

@[cfg_eval] theorem_by subEaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (subEaxImm32Effect p imm t) t' = _ := by lift_value [subEaxImm32Effect]

@[cfg_eval] theorem_by subEaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (subEaxImm32Effect p imm t) t' = _ := by lift_value [subEaxImm32Effect]

@[cfg_eval] theorem subEaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subEaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subEaxImm32Effect_components])

@[cfg_eval] theorem_by subRaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (subRaxImm32Effect p imm t) t' = _ := by lift_value [subRaxImm32Effect]

@[cfg_eval] theorem_by subRaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (subRaxImm32Effect p imm t) t' = _ := by lift_value [subRaxImm32Effect]

@[cfg_eval] theorem_by subRaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (subRaxImm32Effect p imm t) t' = _ := by lift_value [subRaxImm32Effect]

@[cfg_eval] theorem_by subRaxImm32Effect_AF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (subRaxImm32Effect p imm t) t' = _ := by lift_value [subRaxImm32Effect]

@[cfg_eval] theorem_by subRaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subRaxImm32Effect p imm t) t' = _ := by lift_value [subRaxImm32Effect]

@[cfg_eval] theorem_by subRaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (subRaxImm32Effect p imm t) t' = _ := by lift_value [subRaxImm32Effect]

@[cfg_eval] theorem_by subRaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (subRaxImm32Effect p imm t) t' = _ := by lift_value [subRaxImm32Effect]

@[cfg_eval] theorem subRaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subRaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subRaxImm32Effect_components])

@[cfg_eval] theorem_by xorAxImm16Effect_rax (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (xorAxImm16Effect p imm t) t' = _ := by lift_value [xorAxImm16Effect]

@[cfg_eval] theorem_by xorAxImm16Effect_CF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorAxImm16Effect p imm t) t' = _ := by lift_value [xorAxImm16Effect]

@[cfg_eval] theorem_by xorAxImm16Effect_PF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorAxImm16Effect p imm t) t' = _ := by lift_value [xorAxImm16Effect]

@[cfg_eval] theorem_by xorAxImm16Effect_ZF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorAxImm16Effect p imm t) t' = _ := by lift_value [xorAxImm16Effect]

@[cfg_eval] theorem_by xorAxImm16Effect_SF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorAxImm16Effect p imm t) t' = _ := by lift_value [xorAxImm16Effect]

@[cfg_eval] theorem_by xorAxImm16Effect_OF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorAxImm16Effect p imm t) t' = _ := by lift_value [xorAxImm16Effect]

@[cfg_eval] theorem xorAxImm16Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorAxImm16Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorAxImm16Effect_components])

@[cfg_eval] theorem_by xorEaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (xorEaxImm32Effect p imm t) t' = _ := by lift_value [xorEaxImm32Effect]

@[cfg_eval] theorem_by xorEaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorEaxImm32Effect p imm t) t' = _ := by lift_value [xorEaxImm32Effect]

@[cfg_eval] theorem_by xorEaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorEaxImm32Effect p imm t) t' = _ := by lift_value [xorEaxImm32Effect]

@[cfg_eval] theorem_by xorEaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorEaxImm32Effect p imm t) t' = _ := by lift_value [xorEaxImm32Effect]

@[cfg_eval] theorem_by xorEaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorEaxImm32Effect p imm t) t' = _ := by lift_value [xorEaxImm32Effect]

@[cfg_eval] theorem_by xorEaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorEaxImm32Effect p imm t) t' = _ := by lift_value [xorEaxImm32Effect]

@[cfg_eval] theorem xorEaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorEaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorEaxImm32Effect_components])

@[cfg_eval] theorem_by xorRaxImm32Effect_rax (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (xorRaxImm32Effect p imm t) t' = _ := by lift_value [xorRaxImm32Effect]

@[cfg_eval] theorem_by xorRaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorRaxImm32Effect p imm t) t' = _ := by lift_value [xorRaxImm32Effect]

@[cfg_eval] theorem_by xorRaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorRaxImm32Effect p imm t) t' = _ := by lift_value [xorRaxImm32Effect]

@[cfg_eval] theorem_by xorRaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorRaxImm32Effect p imm t) t' = _ := by lift_value [xorRaxImm32Effect]

@[cfg_eval] theorem_by xorRaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorRaxImm32Effect p imm t) t' = _ := by lift_value [xorRaxImm32Effect]

@[cfg_eval] theorem_by xorRaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorRaxImm32Effect p imm t) t' = _ := by lift_value [xorRaxImm32Effect]

@[cfg_eval] theorem xorRaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorRaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorRaxImm32Effect_components])

@[cfg_eval] theorem_by cmpAxImm16Effect_CF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpAxImm16Effect p imm t) t' = _ := by lift_value [cmpAxImm16Effect]

@[cfg_eval] theorem_by cmpAxImm16Effect_PF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpAxImm16Effect p imm t) t' = _ := by lift_value [cmpAxImm16Effect]

@[cfg_eval] theorem_by cmpAxImm16Effect_AF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpAxImm16Effect p imm t) t' = _ := by lift_value [cmpAxImm16Effect]

@[cfg_eval] theorem_by cmpAxImm16Effect_ZF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpAxImm16Effect p imm t) t' = _ := by lift_value [cmpAxImm16Effect]

@[cfg_eval] theorem_by cmpAxImm16Effect_SF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpAxImm16Effect p imm t) t' = _ := by lift_value [cmpAxImm16Effect]

@[cfg_eval] theorem_by cmpAxImm16Effect_OF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpAxImm16Effect p imm t) t' = _ := by lift_value [cmpAxImm16Effect]

@[cfg_eval] theorem cmpAxImm16Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpAxImm16Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpAxImm16Effect_components])

@[cfg_eval] theorem_by cmpEaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpEaxImm32Effect p imm t) t' = _ := by lift_value [cmpEaxImm32Effect]

@[cfg_eval] theorem_by cmpEaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpEaxImm32Effect p imm t) t' = _ := by lift_value [cmpEaxImm32Effect]

@[cfg_eval] theorem_by cmpEaxImm32Effect_AF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpEaxImm32Effect p imm t) t' = _ := by lift_value [cmpEaxImm32Effect]

@[cfg_eval] theorem_by cmpEaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpEaxImm32Effect p imm t) t' = _ := by lift_value [cmpEaxImm32Effect]

@[cfg_eval] theorem_by cmpEaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpEaxImm32Effect p imm t) t' = _ := by lift_value [cmpEaxImm32Effect]

@[cfg_eval] theorem_by cmpEaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpEaxImm32Effect p imm t) t' = _ := by lift_value [cmpEaxImm32Effect]

@[cfg_eval] theorem cmpEaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpEaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpEaxImm32Effect_components])

@[cfg_eval] theorem_by cmpRaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpRaxImm32Effect p imm t) t' = _ := by lift_value [cmpRaxImm32Effect]

@[cfg_eval] theorem_by cmpRaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpRaxImm32Effect p imm t) t' = _ := by lift_value [cmpRaxImm32Effect]

@[cfg_eval] theorem_by cmpRaxImm32Effect_AF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpRaxImm32Effect p imm t) t' = _ := by lift_value [cmpRaxImm32Effect]

@[cfg_eval] theorem_by cmpRaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpRaxImm32Effect p imm t) t' = _ := by lift_value [cmpRaxImm32Effect]

@[cfg_eval] theorem_by cmpRaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpRaxImm32Effect p imm t) t' = _ := by lift_value [cmpRaxImm32Effect]

@[cfg_eval] theorem_by cmpRaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpRaxImm32Effect p imm t) t' = _ := by lift_value [cmpRaxImm32Effect]

@[cfg_eval] theorem cmpRaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpRaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpRaxImm32Effect_components])

@[cfg_eval] theorem_by testAxImm16Effect_CF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (testAxImm16Effect p imm t) t' = _ := by lift_value [testAxImm16Effect]

@[cfg_eval] theorem_by testAxImm16Effect_PF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .PF).value (testAxImm16Effect p imm t) t' = _ := by lift_value [testAxImm16Effect]

@[cfg_eval] theorem_by testAxImm16Effect_ZF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testAxImm16Effect p imm t) t' = _ := by lift_value [testAxImm16Effect]

@[cfg_eval] theorem_by testAxImm16Effect_SF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .SF).value (testAxImm16Effect p imm t) t' = _ := by lift_value [testAxImm16Effect]

@[cfg_eval] theorem_by testAxImm16Effect_OF (p : BitVec 64) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (testAxImm16Effect p imm t) t' = _ := by lift_value [testAxImm16Effect]

@[cfg_eval] theorem testAxImm16Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testAxImm16Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testAxImm16Effect_components])

@[cfg_eval] theorem_by testEaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (testEaxImm32Effect p imm t) t' = _ := by lift_value [testEaxImm32Effect]

@[cfg_eval] theorem_by testEaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (testEaxImm32Effect p imm t) t' = _ := by lift_value [testEaxImm32Effect]

@[cfg_eval] theorem_by testEaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testEaxImm32Effect p imm t) t' = _ := by lift_value [testEaxImm32Effect]

@[cfg_eval] theorem_by testEaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (testEaxImm32Effect p imm t) t' = _ := by lift_value [testEaxImm32Effect]

@[cfg_eval] theorem_by testEaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (testEaxImm32Effect p imm t) t' = _ := by lift_value [testEaxImm32Effect]

@[cfg_eval] theorem testEaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testEaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testEaxImm32Effect_components])

@[cfg_eval] theorem_by testRaxImm32Effect_CF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (testRaxImm32Effect p imm t) t' = _ := by lift_value [testRaxImm32Effect]

@[cfg_eval] theorem_by testRaxImm32Effect_PF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (testRaxImm32Effect p imm t) t' = _ := by lift_value [testRaxImm32Effect]

@[cfg_eval] theorem_by testRaxImm32Effect_ZF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testRaxImm32Effect p imm t) t' = _ := by lift_value [testRaxImm32Effect]

@[cfg_eval] theorem_by testRaxImm32Effect_SF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (testRaxImm32Effect p imm t) t' = _ := by lift_value [testRaxImm32Effect]

@[cfg_eval] theorem_by testRaxImm32Effect_OF (p : BitVec 64) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (testRaxImm32Effect p imm t) t' = _ := by lift_value [testRaxImm32Effect]

@[cfg_eval] theorem testRaxImm32Effect_exec (code : CodeMap) (p : BitVec 64) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testRaxImm32Effect p imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testRaxImm32Effect_components])

@[cfg_eval] theorem_by incR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (incR16Effect p len dst t) t' = _ := by lift_value [incR16Effect, incSpec]

@[cfg_eval] theorem_by incR16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (incR16Effect p len dst t) t' = _ := by lift_value [incR16Effect, incSpec]

@[cfg_eval] theorem_by incR16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (incR16Effect p len dst t) t' = _ := by lift_value [incR16Effect, incSpec]

@[cfg_eval] theorem_by incR16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (incR16Effect p len dst t) t' = _ := by lift_value [incR16Effect, incSpec]

@[cfg_eval] theorem_by incR16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (incR16Effect p len dst t) t' = _ := by lift_value [incR16Effect, incSpec]

@[cfg_eval] theorem_by incR16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (incR16Effect p len dst t) t' = _ := by lift_value [incR16Effect, incSpec]

@[cfg_eval] theorem_by incR16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (incR16Effect p len dst t) t' = _ := by lift_value [incR16Effect, incSpec]

@[cfg_eval] theorem incR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (incR16Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [incR16Effect_components])

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

@[cfg_eval] theorem_by decR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (decR32Effect p len dst t) t' = _ := by lift_value [decR32Effect, decSpec]

@[cfg_eval] theorem_by decR32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (decR32Effect p len dst t) t' = _ := by lift_value [decR32Effect, decSpec]

@[cfg_eval] theorem_by decR32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (decR32Effect p len dst t) t' = _ := by lift_value [decR32Effect, decSpec]

@[cfg_eval] theorem_by decR32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (decR32Effect p len dst t) t' = _ := by lift_value [decR32Effect, decSpec]

@[cfg_eval] theorem_by decR32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (decR32Effect p len dst t) t' = _ := by lift_value [decR32Effect, decSpec]

@[cfg_eval] theorem_by decR32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (decR32Effect p len dst t) t' = _ := by lift_value [decR32Effect, decSpec]

@[cfg_eval] theorem_by decR32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (decR32Effect p len dst t) t' = _ := by lift_value [decR32Effect, decSpec]

@[cfg_eval] theorem decR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (decR32Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [decR32Effect_components])

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

@[cfg_eval] theorem_by notR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (notR16Effect p len dst t) t' = _ := by lift_value [notR16Effect]

@[cfg_eval] theorem notR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (notR16Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [notR16Effect_components])

@[cfg_eval] theorem_by notR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (notR32Effect p len dst t) t' = _ := by lift_value [notR32Effect]

@[cfg_eval] theorem notR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (notR32Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [notR32Effect_components])

@[cfg_eval] theorem_by notR64Effect_dst (p : BitVec 64) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (notR64Effect p dst t) t' = _ := by lift_value [notR64Effect]

@[cfg_eval] theorem notR64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (notR64Effect p dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [notR64Effect_components])

@[cfg_eval] theorem_by negR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (negR16Effect p len dst t) t' = _ := by lift_value [negR16Effect]

@[cfg_eval] theorem_by negR16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (negR16Effect p len dst t) t' = _ := by lift_value [negR16Effect]

@[cfg_eval] theorem_by negR16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (negR16Effect p len dst t) t' = _ := by lift_value [negR16Effect]

@[cfg_eval] theorem_by negR16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (negR16Effect p len dst t) t' = _ := by lift_value [negR16Effect]

@[cfg_eval] theorem_by negR16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (negR16Effect p len dst t) t' = _ := by lift_value [negR16Effect]

@[cfg_eval] theorem_by negR16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (negR16Effect p len dst t) t' = _ := by lift_value [negR16Effect]

@[cfg_eval] theorem_by negR16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (negR16Effect p len dst t) t' = _ := by lift_value [negR16Effect]

@[cfg_eval] theorem negR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (negR16Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [negR16Effect_components])

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

@[cfg_eval] theorem_by incR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (incR8Effect p len dst t) t' = _ := by lift_value [incR8Effect, incSpec]

@[cfg_eval] theorem_by incR8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (incR8Effect p len dst t) t' = _ := by lift_value [incR8Effect, incSpec]

@[cfg_eval] theorem_by incR8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (incR8Effect p len dst t) t' = _ := by lift_value [incR8Effect, incSpec]

@[cfg_eval] theorem_by incR8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (incR8Effect p len dst t) t' = _ := by lift_value [incR8Effect, incSpec]

@[cfg_eval] theorem_by incR8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (incR8Effect p len dst t) t' = _ := by lift_value [incR8Effect, incSpec]

@[cfg_eval] theorem_by incR8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (incR8Effect p len dst t) t' = _ := by lift_value [incR8Effect, incSpec]

@[cfg_eval] theorem_by incR8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (incR8Effect p len dst t) t' = _ := by lift_value [incR8Effect, incSpec]

@[cfg_eval] theorem incR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (incR8Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [incR8Effect_components])

@[cfg_eval] theorem_by decR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (decR8Effect p len dst t) t' = _ := by lift_value [decR8Effect, decSpec]

@[cfg_eval] theorem_by decR8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (decR8Effect p len dst t) t' = _ := by lift_value [decR8Effect, decSpec]

@[cfg_eval] theorem_by decR8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (decR8Effect p len dst t) t' = _ := by lift_value [decR8Effect, decSpec]

@[cfg_eval] theorem_by decR8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (decR8Effect p len dst t) t' = _ := by lift_value [decR8Effect, decSpec]

@[cfg_eval] theorem_by decR8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (decR8Effect p len dst t) t' = _ := by lift_value [decR8Effect, decSpec]

@[cfg_eval] theorem_by decR8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (decR8Effect p len dst t) t' = _ := by lift_value [decR8Effect, decSpec]

@[cfg_eval] theorem_by decR8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (decR8Effect p len dst t) t' = _ := by lift_value [decR8Effect, decSpec]

@[cfg_eval] theorem decR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (decR8Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [decR8Effect_components])

@[cfg_eval] theorem_by notR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (notR8Effect p len dst t) t' = _ := by lift_value [notR8Effect]

@[cfg_eval] theorem notR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (notR8Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [notR8Effect_components])

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

@[cfg_eval] theorem_by rolR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR16Effect p len dst c t) t' = _ := by lift_value [rolR16Effect, rolFlags]

@[cfg_eval] theorem_by rolR16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rolR16Effect p len dst c t) t' = _ := by lift_value [rolR16Effect, rolFlags]

@[cfg_eval] theorem_by rolR16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rolR16Effect p len dst c t) t' = _ := by lift_value [rolR16Effect, rolFlags]

@[cfg_eval] theorem_by rolR16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rolR16Effect p len dst c t) t' = _ := by lift_value [rolR16Effect, rolFlags]

@[cfg_eval] theorem_by rolR16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rolR16Effect p len dst c t) t' = _ := by lift_value [rolR16Effect, rolFlags]

@[cfg_eval] theorem_by rolR16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rolR16Effect p len dst c t) t' = _ := by lift_value [rolR16Effect, rolFlags]

@[cfg_eval] theorem_by rolR16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rolR16Effect p len dst c t) t' = _ := by lift_value [rolR16Effect, rolFlags]

@[cfg_eval] theorem rolR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rolR16Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rolR16Effect_components])

@[cfg_eval] theorem_by rolR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR32Effect p len dst c t) t' = _ := by lift_value [rolR32Effect, rolFlags]

@[cfg_eval] theorem_by rolR32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rolR32Effect p len dst c t) t' = _ := by lift_value [rolR32Effect, rolFlags]

@[cfg_eval] theorem_by rolR32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rolR32Effect p len dst c t) t' = _ := by lift_value [rolR32Effect, rolFlags]

@[cfg_eval] theorem_by rolR32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rolR32Effect p len dst c t) t' = _ := by lift_value [rolR32Effect, rolFlags]

@[cfg_eval] theorem_by rolR32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rolR32Effect p len dst c t) t' = _ := by lift_value [rolR32Effect, rolFlags]

@[cfg_eval] theorem_by rolR32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rolR32Effect p len dst c t) t' = _ := by lift_value [rolR32Effect, rolFlags]

@[cfg_eval] theorem_by rolR32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rolR32Effect p len dst c t) t' = _ := by lift_value [rolR32Effect, rolFlags]

@[cfg_eval] theorem rolR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rolR32Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rolR32Effect_components])

@[cfg_eval] theorem_by rolR64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR64Effect p len dst c t) t' = _ := by lift_value [rolR64Effect, rolFlags]

@[cfg_eval] theorem_by rolR64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rolR64Effect p len dst c t) t' = _ := by lift_value [rolR64Effect, rolFlags]

@[cfg_eval] theorem_by rolR64Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rolR64Effect p len dst c t) t' = _ := by lift_value [rolR64Effect, rolFlags]

@[cfg_eval] theorem_by rolR64Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rolR64Effect p len dst c t) t' = _ := by lift_value [rolR64Effect, rolFlags]

@[cfg_eval] theorem_by rolR64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rolR64Effect p len dst c t) t' = _ := by lift_value [rolR64Effect, rolFlags]

@[cfg_eval] theorem_by rolR64Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rolR64Effect p len dst c t) t' = _ := by lift_value [rolR64Effect, rolFlags]

@[cfg_eval] theorem_by rolR64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rolR64Effect p len dst c t) t' = _ := by lift_value [rolR64Effect, rolFlags]

@[cfg_eval] theorem rolR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rolR64Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rolR64Effect_components])

@[cfg_eval] theorem_by rorR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rorR16Effect p len dst c t) t' = _ := by lift_value [rorR16Effect, rorFlags]

@[cfg_eval] theorem_by rorR16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rorR16Effect p len dst c t) t' = _ := by lift_value [rorR16Effect, rorFlags]

@[cfg_eval] theorem_by rorR16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rorR16Effect p len dst c t) t' = _ := by lift_value [rorR16Effect, rorFlags]

@[cfg_eval] theorem_by rorR16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rorR16Effect p len dst c t) t' = _ := by lift_value [rorR16Effect, rorFlags]

@[cfg_eval] theorem_by rorR16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rorR16Effect p len dst c t) t' = _ := by lift_value [rorR16Effect, rorFlags]

@[cfg_eval] theorem_by rorR16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rorR16Effect p len dst c t) t' = _ := by lift_value [rorR16Effect, rorFlags]

@[cfg_eval] theorem_by rorR16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rorR16Effect p len dst c t) t' = _ := by lift_value [rorR16Effect, rorFlags]

@[cfg_eval] theorem rorR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rorR16Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rorR16Effect_components])

@[cfg_eval] theorem_by rorR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rorR32Effect p len dst c t) t' = _ := by lift_value [rorR32Effect, rorFlags]

@[cfg_eval] theorem_by rorR32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rorR32Effect p len dst c t) t' = _ := by lift_value [rorR32Effect, rorFlags]

@[cfg_eval] theorem_by rorR32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rorR32Effect p len dst c t) t' = _ := by lift_value [rorR32Effect, rorFlags]

@[cfg_eval] theorem_by rorR32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rorR32Effect p len dst c t) t' = _ := by lift_value [rorR32Effect, rorFlags]

@[cfg_eval] theorem_by rorR32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rorR32Effect p len dst c t) t' = _ := by lift_value [rorR32Effect, rorFlags]

@[cfg_eval] theorem_by rorR32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rorR32Effect p len dst c t) t' = _ := by lift_value [rorR32Effect, rorFlags]

@[cfg_eval] theorem_by rorR32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rorR32Effect p len dst c t) t' = _ := by lift_value [rorR32Effect, rorFlags]

@[cfg_eval] theorem rorR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rorR32Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rorR32Effect_components])

@[cfg_eval] theorem_by rorR64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rorR64Effect p len dst c t) t' = _ := by lift_value [rorR64Effect, rorFlags]

@[cfg_eval] theorem_by rorR64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rorR64Effect p len dst c t) t' = _ := by lift_value [rorR64Effect, rorFlags]

@[cfg_eval] theorem_by rorR64Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rorR64Effect p len dst c t) t' = _ := by lift_value [rorR64Effect, rorFlags]

@[cfg_eval] theorem_by rorR64Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rorR64Effect p len dst c t) t' = _ := by lift_value [rorR64Effect, rorFlags]

@[cfg_eval] theorem_by rorR64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rorR64Effect p len dst c t) t' = _ := by lift_value [rorR64Effect, rorFlags]

@[cfg_eval] theorem_by rorR64Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rorR64Effect p len dst c t) t' = _ := by lift_value [rorR64Effect, rorFlags]

@[cfg_eval] theorem_by rorR64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rorR64Effect p len dst c t) t' = _ := by lift_value [rorR64Effect, rorFlags]

@[cfg_eval] theorem rorR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rorR64Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rorR64Effect_components])

@[cfg_eval] theorem_by shlR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR16Effect p len dst c t) t' = _ := by lift_value [shlR16Effect, shlFlags]

@[cfg_eval] theorem_by shlR16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shlR16Effect p len dst c t) t' = _ := by lift_value [shlR16Effect, shlFlags]

@[cfg_eval] theorem_by shlR16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shlR16Effect p len dst c t) t' = _ := by lift_value [shlR16Effect, shlFlags]

@[cfg_eval] theorem_by shlR16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shlR16Effect p len dst c t) t' = _ := by lift_value [shlR16Effect, shlFlags]

@[cfg_eval] theorem_by shlR16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shlR16Effect p len dst c t) t' = _ := by lift_value [shlR16Effect, shlFlags]

@[cfg_eval] theorem_by shlR16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shlR16Effect p len dst c t) t' = _ := by lift_value [shlR16Effect, shlFlags]

@[cfg_eval] theorem_by shlR16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shlR16Effect p len dst c t) t' = _ := by lift_value [shlR16Effect, shlFlags]

@[cfg_eval] theorem shlR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR16Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR16Effect_components])

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

end ChaCha20Poly1305.Proofs.Lift
