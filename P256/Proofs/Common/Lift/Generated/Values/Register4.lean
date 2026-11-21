import P256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Bsf.Generated.RR.Triple
import X86Proofs.Instructions.Bsr.Generated.RR.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Cmov.Generated.RR.Triple
import X86Proofs.Instructions.Imul.Generated.R.Triple
import X86Proofs.Instructions.Imul.Generated.R8.Triple
import X86Proofs.Instructions.Imul.Generated.RR.Triple
import X86Proofs.Instructions.Imul.Generated.RRImm32.Triple
import X86Proofs.Instructions.Imul.Generated.RRImm8.Triple
import X86Proofs.Instructions.Lea.Generated.RM.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Generated.R16Imm16.Triple
import X86Proofs.Instructions.Mov.Generated.R8.Triple
import X86Proofs.Instructions.Mov.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Mov.Generated.RR16.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Movsx.Generated.RR16.Triple
import X86Proofs.Instructions.Movsx.Generated.RR8.Triple
import X86Proofs.Instructions.Movsxd.Generated.RR32.Triple
import X86Proofs.Instructions.Movzx.Generated.RR16.Triple
import X86Proofs.Instructions.Movzx.Generated.RR8.Triple
import X86Proofs.Instructions.Mul.Generated.R.Triple
import X86Proofs.Instructions.Mul.Generated.R8.Triple
import X86Proofs.Instructions.Nop.Triple
import X86Proofs.Instructions.Rol.Generated.Cl.Triple
import X86Proofs.Instructions.Rol.Generated.R8.Triple
import X86Proofs.Instructions.Rol.Generated.R8Cl.Triple
import X86Proofs.Instructions.Ror.Generated.Cl.Triple
import X86Proofs.Instructions.Ror.Generated.R8.Triple
import X86Proofs.Instructions.Ror.Generated.R8Cl.Triple
import X86Proofs.Instructions.Sal.Generated.Cl.Triple
import X86Proofs.Instructions.Sal.Generated.R.Triple
import X86Proofs.Instructions.Sal.Generated.R8.Triple
import X86Proofs.Instructions.Sal.Generated.R8Cl.Triple
import X86Proofs.Instructions.Sar.Generated.Cl.Triple
import X86Proofs.Instructions.Sar.Generated.R.Triple
import X86Proofs.Instructions.Sar.Generated.R8.Triple
import X86Proofs.Instructions.Sar.Generated.R8Cl.Triple
import X86Proofs.Instructions.Setcc.Generated.R8.Triple
import X86Proofs.Instructions.Shl.Generated.Cl.Triple
import X86Proofs.Instructions.Shl.Generated.R8.Triple
import X86Proofs.Instructions.Shl.Generated.R8Cl.Triple
import X86Proofs.Instructions.Shld.Generated.RRCl.Triple
import X86Proofs.Instructions.Shld.Generated.RRImm8.Triple
import X86Proofs.Instructions.Shr.Generated.Cl.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Shr.Generated.R8.Triple
import X86Proofs.Instructions.Shr.Generated.R8Cl.Triple
import X86Proofs.Instructions.Shrd.Generated.RRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.RRImm8.Triple
import X86Proofs.Instructions.Xchg.Generated.Acc.Triple
import X86Proofs.Instructions.Xchg.Generated.R8.Triple
import X86Proofs.Instructions.Xchg.Generated.RR.Triple

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG

@[cfg_eval] theorem_by salR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (salR16Effect p len dst c t) t' = _ := by lift_value [salR16Effect, shlFlags]

@[cfg_eval] theorem_by salR16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (salR16Effect p len dst c t) t' = _ := by lift_value [salR16Effect, shlFlags]

@[cfg_eval] theorem_by salR16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (salR16Effect p len dst c t) t' = _ := by lift_value [salR16Effect, shlFlags]

@[cfg_eval] theorem_by salR16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (salR16Effect p len dst c t) t' = _ := by lift_value [salR16Effect, shlFlags]

@[cfg_eval] theorem_by salR16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (salR16Effect p len dst c t) t' = _ := by lift_value [salR16Effect, shlFlags]

@[cfg_eval] theorem_by salR16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (salR16Effect p len dst c t) t' = _ := by lift_value [salR16Effect, shlFlags]

@[cfg_eval] theorem_by salR16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (salR16Effect p len dst c t) t' = _ := by lift_value [salR16Effect, shlFlags]

@[cfg_eval] theorem salR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (salR16Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [salR16Effect_components])

@[cfg_eval] theorem_by salR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (salR32Effect p len dst c t) t' = _ := by lift_value [salR32Effect, shlFlags]

@[cfg_eval] theorem_by salR32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (salR32Effect p len dst c t) t' = _ := by lift_value [salR32Effect, shlFlags]

@[cfg_eval] theorem_by salR32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (salR32Effect p len dst c t) t' = _ := by lift_value [salR32Effect, shlFlags]

@[cfg_eval] theorem_by salR32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (salR32Effect p len dst c t) t' = _ := by lift_value [salR32Effect, shlFlags]

@[cfg_eval] theorem_by salR32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (salR32Effect p len dst c t) t' = _ := by lift_value [salR32Effect, shlFlags]

@[cfg_eval] theorem_by salR32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (salR32Effect p len dst c t) t' = _ := by lift_value [salR32Effect, shlFlags]

@[cfg_eval] theorem_by salR32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (salR32Effect p len dst c t) t' = _ := by lift_value [salR32Effect, shlFlags]

@[cfg_eval] theorem salR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (salR32Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [salR32Effect_components])

@[cfg_eval] theorem_by salR64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (salR64Effect p len dst c t) t' = _ := by lift_value [salR64Effect, shlFlags]

@[cfg_eval] theorem_by salR64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (salR64Effect p len dst c t) t' = _ := by lift_value [salR64Effect, shlFlags]

@[cfg_eval] theorem_by salR64Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (salR64Effect p len dst c t) t' = _ := by lift_value [salR64Effect, shlFlags]

@[cfg_eval] theorem_by salR64Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (salR64Effect p len dst c t) t' = _ := by lift_value [salR64Effect, shlFlags]

@[cfg_eval] theorem_by salR64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (salR64Effect p len dst c t) t' = _ := by lift_value [salR64Effect, shlFlags]

@[cfg_eval] theorem_by salR64Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (salR64Effect p len dst c t) t' = _ := by lift_value [salR64Effect, shlFlags]

@[cfg_eval] theorem_by salR64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (salR64Effect p len dst c t) t' = _ := by lift_value [salR64Effect, shlFlags]

@[cfg_eval] theorem salR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (salR64Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [salR64Effect_components])

@[cfg_eval] theorem_by shrR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR16Effect p len dst c t) t' = _ := by lift_value [shrR16Effect, shrFlags]

@[cfg_eval] theorem_by shrR16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrR16Effect p len dst c t) t' = _ := by lift_value [shrR16Effect, shrFlags]

@[cfg_eval] theorem_by shrR16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrR16Effect p len dst c t) t' = _ := by lift_value [shrR16Effect, shrFlags]

@[cfg_eval] theorem_by shrR16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrR16Effect p len dst c t) t' = _ := by lift_value [shrR16Effect, shrFlags]

@[cfg_eval] theorem_by shrR16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrR16Effect p len dst c t) t' = _ := by lift_value [shrR16Effect, shrFlags]

@[cfg_eval] theorem_by shrR16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrR16Effect p len dst c t) t' = _ := by lift_value [shrR16Effect, shrFlags]

@[cfg_eval] theorem_by shrR16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrR16Effect p len dst c t) t' = _ := by lift_value [shrR16Effect, shrFlags]

@[cfg_eval] theorem shrR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrR16Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrR16Effect_components])

@[cfg_eval] theorem_by shrR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR32Effect p len dst c t) t' = _ := by lift_value [shrR32Effect, shrFlags]

@[cfg_eval] theorem_by shrR32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrR32Effect p len dst c t) t' = _ := by lift_value [shrR32Effect, shrFlags]

@[cfg_eval] theorem_by shrR32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrR32Effect p len dst c t) t' = _ := by lift_value [shrR32Effect, shrFlags]

@[cfg_eval] theorem_by shrR32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrR32Effect p len dst c t) t' = _ := by lift_value [shrR32Effect, shrFlags]

@[cfg_eval] theorem_by shrR32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrR32Effect p len dst c t) t' = _ := by lift_value [shrR32Effect, shrFlags]

@[cfg_eval] theorem_by shrR32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrR32Effect p len dst c t) t' = _ := by lift_value [shrR32Effect, shrFlags]

@[cfg_eval] theorem_by shrR32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrR32Effect p len dst c t) t' = _ := by lift_value [shrR32Effect, shrFlags]

@[cfg_eval] theorem shrR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrR32Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrR32Effect_components])

@[cfg_eval] theorem_by shrR64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR64Effect p len dst c t) t' = _ := by lift_value [shrR64Effect, shrFlags]

@[cfg_eval] theorem_by shrR64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrR64Effect p len dst c t) t' = _ := by lift_value [shrR64Effect, shrFlags]

@[cfg_eval] theorem_by shrR64Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrR64Effect p len dst c t) t' = _ := by lift_value [shrR64Effect, shrFlags]

@[cfg_eval] theorem_by shrR64Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrR64Effect p len dst c t) t' = _ := by lift_value [shrR64Effect, shrFlags]

@[cfg_eval] theorem_by shrR64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrR64Effect p len dst c t) t' = _ := by lift_value [shrR64Effect, shrFlags]

@[cfg_eval] theorem_by shrR64Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrR64Effect p len dst c t) t' = _ := by lift_value [shrR64Effect, shrFlags]

@[cfg_eval] theorem_by shrR64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrR64Effect p len dst c t) t' = _ := by lift_value [shrR64Effect, shrFlags]

@[cfg_eval] theorem shrR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrR64Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrR64Effect_components])

@[cfg_eval] theorem_by sarR16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (sarR16Effect p len dst c t) t' = _ := by lift_value [sarR16Effect, sarFlags]

@[cfg_eval] theorem_by sarR16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (sarR16Effect p len dst c t) t' = _ := by lift_value [sarR16Effect, sarFlags]

@[cfg_eval] theorem_by sarR16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (sarR16Effect p len dst c t) t' = _ := by lift_value [sarR16Effect, sarFlags]

@[cfg_eval] theorem_by sarR16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (sarR16Effect p len dst c t) t' = _ := by lift_value [sarR16Effect, sarFlags]

@[cfg_eval] theorem_by sarR16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (sarR16Effect p len dst c t) t' = _ := by lift_value [sarR16Effect, sarFlags]

@[cfg_eval] theorem_by sarR16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (sarR16Effect p len dst c t) t' = _ := by lift_value [sarR16Effect, sarFlags]

@[cfg_eval] theorem_by sarR16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (sarR16Effect p len dst c t) t' = _ := by lift_value [sarR16Effect, sarFlags]

@[cfg_eval] theorem sarR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (sarR16Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [sarR16Effect_components])

@[cfg_eval] theorem_by sarR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (sarR32Effect p len dst c t) t' = _ := by lift_value [sarR32Effect, sarFlags]

@[cfg_eval] theorem_by sarR32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (sarR32Effect p len dst c t) t' = _ := by lift_value [sarR32Effect, sarFlags]

@[cfg_eval] theorem_by sarR32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (sarR32Effect p len dst c t) t' = _ := by lift_value [sarR32Effect, sarFlags]

@[cfg_eval] theorem_by sarR32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (sarR32Effect p len dst c t) t' = _ := by lift_value [sarR32Effect, sarFlags]

@[cfg_eval] theorem_by sarR32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (sarR32Effect p len dst c t) t' = _ := by lift_value [sarR32Effect, sarFlags]

@[cfg_eval] theorem_by sarR32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (sarR32Effect p len dst c t) t' = _ := by lift_value [sarR32Effect, sarFlags]

@[cfg_eval] theorem_by sarR32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (sarR32Effect p len dst c t) t' = _ := by lift_value [sarR32Effect, sarFlags]

@[cfg_eval] theorem sarR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (sarR32Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [sarR32Effect_components])

@[cfg_eval] theorem_by sarR64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (sarR64Effect p len dst c t) t' = _ := by lift_value [sarR64Effect, sarFlags]

@[cfg_eval] theorem_by sarR64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (sarR64Effect p len dst c t) t' = _ := by lift_value [sarR64Effect, sarFlags]

@[cfg_eval] theorem_by sarR64Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (sarR64Effect p len dst c t) t' = _ := by lift_value [sarR64Effect, sarFlags]

@[cfg_eval] theorem_by sarR64Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (sarR64Effect p len dst c t) t' = _ := by lift_value [sarR64Effect, sarFlags]

@[cfg_eval] theorem_by sarR64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (sarR64Effect p len dst c t) t' = _ := by lift_value [sarR64Effect, sarFlags]

@[cfg_eval] theorem_by sarR64Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (sarR64Effect p len dst c t) t' = _ := by lift_value [sarR64Effect, sarFlags]

@[cfg_eval] theorem_by sarR64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (sarR64Effect p len dst c t) t' = _ := by lift_value [sarR64Effect, sarFlags]

@[cfg_eval] theorem sarR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (sarR64Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [sarR64Effect_components])

@[cfg_eval] theorem_by rolR16ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR16ClEffect p len dst t) t' = _ := by lift_value [rolR16ClEffect, rolR16Effect, rolFlags]

@[cfg_eval] theorem rolR16ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rolR16ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rolR16ClEffect_components])

@[cfg_eval] theorem_by rolR32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR32ClEffect p len dst t) t' = _ := by lift_value [rolR32ClEffect, rolR32Effect, rolFlags]

@[cfg_eval] theorem rolR32ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rolR32ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rolR32ClEffect_components])

@[cfg_eval] theorem_by rolR64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR64ClEffect p len dst t) t' = _ := by lift_value [rolR64ClEffect, rolR64Effect, rolFlags]

@[cfg_eval] theorem rolR64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rolR64ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rolR64ClEffect_components])

@[cfg_eval] theorem_by rorR16ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rorR16ClEffect p len dst t) t' = _ := by lift_value [rorR16ClEffect, rorR16Effect, rorFlags]

@[cfg_eval] theorem rorR16ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rorR16ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rorR16ClEffect_components])

@[cfg_eval] theorem_by rorR32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rorR32ClEffect p len dst t) t' = _ := by lift_value [rorR32ClEffect, rorR32Effect, rorFlags]

@[cfg_eval] theorem rorR32ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rorR32ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rorR32ClEffect_components])

@[cfg_eval] theorem_by rorR64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rorR64ClEffect p len dst t) t' = _ := by lift_value [rorR64ClEffect, rorR64Effect, rorFlags]

@[cfg_eval] theorem rorR64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rorR64ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rorR64ClEffect_components])

@[cfg_eval] theorem_by shlR16ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR16ClEffect p len dst t) t' = _ := by lift_value [shlR16ClEffect, shlR16Effect, shlFlags]

@[cfg_eval] theorem shlR16ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR16ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR16ClEffect_components])

@[cfg_eval] theorem_by shlR32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR32ClEffect p len dst t) t' = _ := by lift_value [shlR32ClEffect, shlR32Effect, shlFlags]

@[cfg_eval] theorem shlR32ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR32ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR32ClEffect_components])

@[cfg_eval] theorem_by shlR64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR64ClEffect p len dst t) t' = _ := by lift_value [shlR64ClEffect, shlR64Effect, shlFlags]

@[cfg_eval] theorem shlR64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR64ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR64ClEffect_components])

@[cfg_eval] theorem_by salR16ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (salR16ClEffect p len dst t) t' = _ := by lift_value [salR16ClEffect, salR16Effect, shlFlags]

@[cfg_eval] theorem salR16ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (salR16ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [salR16ClEffect_components])

@[cfg_eval] theorem_by salR32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (salR32ClEffect p len dst t) t' = _ := by lift_value [salR32ClEffect, salR32Effect, shlFlags]

@[cfg_eval] theorem salR32ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (salR32ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [salR32ClEffect_components])

@[cfg_eval] theorem_by salR64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (salR64ClEffect p len dst t) t' = _ := by lift_value [salR64ClEffect, salR64Effect, shlFlags]

@[cfg_eval] theorem salR64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (salR64ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [salR64ClEffect_components])

@[cfg_eval] theorem_by shrR16ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR16ClEffect p len dst t) t' = _ := by lift_value [shrR16ClEffect, shrR16Effect, shrFlags]

@[cfg_eval] theorem shrR16ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrR16ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrR16ClEffect_components])

@[cfg_eval] theorem_by shrR32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR32ClEffect p len dst t) t' = _ := by lift_value [shrR32ClEffect, shrR32Effect, shrFlags]

@[cfg_eval] theorem shrR32ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrR32ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrR32ClEffect_components])

@[cfg_eval] theorem_by shrR64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR64ClEffect p len dst t) t' = _ := by lift_value [shrR64ClEffect, shrR64Effect, shrFlags]

@[cfg_eval] theorem shrR64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrR64ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrR64ClEffect_components])

@[cfg_eval] theorem_by sarR16ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (sarR16ClEffect p len dst t) t' = _ := by lift_value [sarR16ClEffect, sarR16Effect, sarFlags]

@[cfg_eval] theorem sarR16ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (sarR16ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [sarR16ClEffect_components])

@[cfg_eval] theorem_by sarR32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (sarR32ClEffect p len dst t) t' = _ := by lift_value [sarR32ClEffect, sarR32Effect, sarFlags]

@[cfg_eval] theorem sarR32ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (sarR32ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [sarR32ClEffect_components])

@[cfg_eval] theorem_by sarR64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (sarR64ClEffect p len dst t) t' = _ := by lift_value [sarR64ClEffect, sarR64Effect, sarFlags]

@[cfg_eval] theorem sarR64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (sarR64ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [sarR64ClEffect_components])

@[cfg_eval] theorem_by rolR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR8Effect p len dst c t) t' = _ := by lift_value [rolR8Effect, rolFlags]

@[cfg_eval] theorem_by rolR8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rolR8Effect p len dst c t) t' = _ := by lift_value [rolR8Effect, rolFlags]

@[cfg_eval] theorem_by rolR8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rolR8Effect p len dst c t) t' = _ := by lift_value [rolR8Effect, rolFlags]

@[cfg_eval] theorem_by rolR8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rolR8Effect p len dst c t) t' = _ := by lift_value [rolR8Effect, rolFlags]

@[cfg_eval] theorem_by rolR8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rolR8Effect p len dst c t) t' = _ := by lift_value [rolR8Effect, rolFlags]

@[cfg_eval] theorem_by rolR8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rolR8Effect p len dst c t) t' = _ := by lift_value [rolR8Effect, rolFlags]

@[cfg_eval] theorem_by rolR8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rolR8Effect p len dst c t) t' = _ := by lift_value [rolR8Effect, rolFlags]

@[cfg_eval] theorem rolR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rolR8Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rolR8Effect_components])

@[cfg_eval] theorem_by rorR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rorR8Effect p len dst c t) t' = _ := by lift_value [rorR8Effect, rorFlags]

@[cfg_eval] theorem_by rorR8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rorR8Effect p len dst c t) t' = _ := by lift_value [rorR8Effect, rorFlags]

@[cfg_eval] theorem_by rorR8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rorR8Effect p len dst c t) t' = _ := by lift_value [rorR8Effect, rorFlags]

@[cfg_eval] theorem_by rorR8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rorR8Effect p len dst c t) t' = _ := by lift_value [rorR8Effect, rorFlags]

@[cfg_eval] theorem_by rorR8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rorR8Effect p len dst c t) t' = _ := by lift_value [rorR8Effect, rorFlags]

@[cfg_eval] theorem_by rorR8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rorR8Effect p len dst c t) t' = _ := by lift_value [rorR8Effect, rorFlags]

@[cfg_eval] theorem_by rorR8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rorR8Effect p len dst c t) t' = _ := by lift_value [rorR8Effect, rorFlags]

@[cfg_eval] theorem rorR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rorR8Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rorR8Effect_components])

@[cfg_eval] theorem_by shlR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR8Effect p len dst c t) t' = _ := by lift_value [shlR8Effect, shlFlags]

@[cfg_eval] theorem_by shlR8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shlR8Effect p len dst c t) t' = _ := by lift_value [shlR8Effect, shlFlags]

@[cfg_eval] theorem_by shlR8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shlR8Effect p len dst c t) t' = _ := by lift_value [shlR8Effect, shlFlags]

@[cfg_eval] theorem_by shlR8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shlR8Effect p len dst c t) t' = _ := by lift_value [shlR8Effect, shlFlags]

@[cfg_eval] theorem_by shlR8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shlR8Effect p len dst c t) t' = _ := by lift_value [shlR8Effect, shlFlags]

@[cfg_eval] theorem_by shlR8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shlR8Effect p len dst c t) t' = _ := by lift_value [shlR8Effect, shlFlags]

@[cfg_eval] theorem_by shlR8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shlR8Effect p len dst c t) t' = _ := by lift_value [shlR8Effect, shlFlags]

@[cfg_eval] theorem shlR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR8Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR8Effect_components])

@[cfg_eval] theorem_by salR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (salR8Effect p len dst c t) t' = _ := by lift_value [salR8Effect, shlFlags]

@[cfg_eval] theorem_by salR8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (salR8Effect p len dst c t) t' = _ := by lift_value [salR8Effect, shlFlags]

@[cfg_eval] theorem_by salR8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (salR8Effect p len dst c t) t' = _ := by lift_value [salR8Effect, shlFlags]

@[cfg_eval] theorem_by salR8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (salR8Effect p len dst c t) t' = _ := by lift_value [salR8Effect, shlFlags]

@[cfg_eval] theorem_by salR8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (salR8Effect p len dst c t) t' = _ := by lift_value [salR8Effect, shlFlags]

@[cfg_eval] theorem_by salR8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (salR8Effect p len dst c t) t' = _ := by lift_value [salR8Effect, shlFlags]

@[cfg_eval] theorem_by salR8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (salR8Effect p len dst c t) t' = _ := by lift_value [salR8Effect, shlFlags]

@[cfg_eval] theorem salR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (salR8Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [salR8Effect_components])

@[cfg_eval] theorem_by shrR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR8Effect p len dst c t) t' = _ := by lift_value [shrR8Effect, shrFlags]

@[cfg_eval] theorem_by shrR8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrR8Effect p len dst c t) t' = _ := by lift_value [shrR8Effect, shrFlags]

@[cfg_eval] theorem_by shrR8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrR8Effect p len dst c t) t' = _ := by lift_value [shrR8Effect, shrFlags]

@[cfg_eval] theorem_by shrR8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrR8Effect p len dst c t) t' = _ := by lift_value [shrR8Effect, shrFlags]

@[cfg_eval] theorem_by shrR8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrR8Effect p len dst c t) t' = _ := by lift_value [shrR8Effect, shrFlags]

@[cfg_eval] theorem_by shrR8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrR8Effect p len dst c t) t' = _ := by lift_value [shrR8Effect, shrFlags]

@[cfg_eval] theorem_by shrR8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrR8Effect p len dst c t) t' = _ := by lift_value [shrR8Effect, shrFlags]

@[cfg_eval] theorem shrR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrR8Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrR8Effect_components])

@[cfg_eval] theorem_by sarR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (sarR8Effect p len dst c t) t' = _ := by lift_value [sarR8Effect, sarFlags]

@[cfg_eval] theorem_by sarR8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (sarR8Effect p len dst c t) t' = _ := by lift_value [sarR8Effect, sarFlags]

@[cfg_eval] theorem_by sarR8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (sarR8Effect p len dst c t) t' = _ := by lift_value [sarR8Effect, sarFlags]

@[cfg_eval] theorem_by sarR8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (sarR8Effect p len dst c t) t' = _ := by lift_value [sarR8Effect, sarFlags]

@[cfg_eval] theorem_by sarR8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (sarR8Effect p len dst c t) t' = _ := by lift_value [sarR8Effect, sarFlags]

@[cfg_eval] theorem_by sarR8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (sarR8Effect p len dst c t) t' = _ := by lift_value [sarR8Effect, sarFlags]

@[cfg_eval] theorem_by sarR8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (sarR8Effect p len dst c t) t' = _ := by lift_value [sarR8Effect, sarFlags]

@[cfg_eval] theorem sarR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (sarR8Effect p len dst c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [sarR8Effect_components])

@[cfg_eval] theorem_by rolR8ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR8ClEffect p len dst t) t' = _ := by lift_value [rolR8ClEffect, rolR8Effect, rolFlags]

@[cfg_eval] theorem rolR8ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rolR8ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rolR8ClEffect_components])

@[cfg_eval] theorem_by rorR8ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rorR8ClEffect p len dst t) t' = _ := by lift_value [rorR8ClEffect, rorR8Effect, rorFlags]

@[cfg_eval] theorem rorR8ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (rorR8ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [rorR8ClEffect_components])

@[cfg_eval] theorem_by shlR8ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR8ClEffect p len dst t) t' = _ := by lift_value [shlR8ClEffect, shlR8Effect, shlFlags]

@[cfg_eval] theorem shlR8ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR8ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR8ClEffect_components])

@[cfg_eval] theorem_by salR8ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (salR8ClEffect p len dst t) t' = _ := by lift_value [salR8ClEffect, salR8Effect, shlFlags]

@[cfg_eval] theorem salR8ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (salR8ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [salR8ClEffect_components])

@[cfg_eval] theorem_by shrR8ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR8ClEffect p len dst t) t' = _ := by lift_value [shrR8ClEffect, shrR8Effect, shrFlags]

@[cfg_eval] theorem shrR8ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrR8ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrR8ClEffect_components])

@[cfg_eval] theorem_by sarR8ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (sarR8ClEffect p len dst t) t' = _ := by lift_value [sarR8ClEffect, sarR8Effect, sarFlags]

@[cfg_eval] theorem sarR8ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (sarR8ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [sarR8ClEffect_components])

@[cfg_eval] theorem_by shldR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shldR16R16Effect p len dst src c t) t' = _ := by lift_value [shldR16R16Effect, shldFlags]

@[cfg_eval] theorem_by shldR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shldR16R16Effect p len dst src c t) t' = _ := by lift_value [shldR16R16Effect, shldFlags]

@[cfg_eval] theorem_by shldR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shldR16R16Effect p len dst src c t) t' = _ := by lift_value [shldR16R16Effect, shldFlags]

@[cfg_eval] theorem_by shldR16R16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shldR16R16Effect p len dst src c t) t' = _ := by lift_value [shldR16R16Effect, shldFlags]

@[cfg_eval] theorem_by shldR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shldR16R16Effect p len dst src c t) t' = _ := by lift_value [shldR16R16Effect, shldFlags]

@[cfg_eval] theorem_by shldR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shldR16R16Effect p len dst src c t) t' = _ := by lift_value [shldR16R16Effect, shldFlags]

@[cfg_eval] theorem_by shldR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shldR16R16Effect p len dst src c t) t' = _ := by lift_value [shldR16R16Effect, shldFlags]

@[cfg_eval] theorem shldR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shldR16R16Effect p len dst src c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shldR16R16Effect_components])

@[cfg_eval] theorem_by shldR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shldR32R32Effect p len dst src c t) t' = _ := by lift_value [shldR32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shldR32R32Effect p len dst src c t) t' = _ := by lift_value [shldR32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shldR32R32Effect p len dst src c t) t' = _ := by lift_value [shldR32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldR32R32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shldR32R32Effect p len dst src c t) t' = _ := by lift_value [shldR32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shldR32R32Effect p len dst src c t) t' = _ := by lift_value [shldR32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shldR32R32Effect p len dst src c t) t' = _ := by lift_value [shldR32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shldR32R32Effect p len dst src c t) t' = _ := by lift_value [shldR32R32Effect, shldFlags]

@[cfg_eval] theorem shldR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shldR32R32Effect p len dst src c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shldR32R32Effect_components])

@[cfg_eval] theorem_by shldR64R64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shldR64R64Effect p len dst src c t) t' = _ := by lift_value [shldR64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldR64R64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shldR64R64Effect p len dst src c t) t' = _ := by lift_value [shldR64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldR64R64Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shldR64R64Effect p len dst src c t) t' = _ := by lift_value [shldR64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldR64R64Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shldR64R64Effect p len dst src c t) t' = _ := by lift_value [shldR64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldR64R64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shldR64R64Effect p len dst src c t) t' = _ := by lift_value [shldR64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldR64R64Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shldR64R64Effect p len dst src c t) t' = _ := by lift_value [shldR64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldR64R64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shldR64R64Effect p len dst src c t) t' = _ := by lift_value [shldR64R64Effect, shldFlags]

@[cfg_eval] theorem shldR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shldR64R64Effect p len dst src c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shldR64R64Effect_components])

@[cfg_eval] theorem_by shldR32R32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shldR32R32ClEffect p len dst src t) t' = _ := by lift_value [shldR32R32ClEffect, shldR32R32Effect, shldFlags]

@[cfg_eval] theorem shldR32R32ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shldR32R32ClEffect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shldR32R32ClEffect_components])

@[cfg_eval] theorem_by shldR64R64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shldR64R64ClEffect p len dst src t) t' = _ := by lift_value [shldR64R64ClEffect, shldR64R64Effect, shldFlags]

@[cfg_eval] theorem shldR64R64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shldR64R64ClEffect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shldR64R64ClEffect_components])

@[cfg_eval] theorem_by shrdR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrdR16R16Effect p len dst src c t) t' = _ := by lift_value [shrdR16R16Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrdR16R16Effect p len dst src c t) t' = _ := by lift_value [shrdR16R16Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrdR16R16Effect p len dst src c t) t' = _ := by lift_value [shrdR16R16Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR16R16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrdR16R16Effect p len dst src c t) t' = _ := by lift_value [shrdR16R16Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrdR16R16Effect p len dst src c t) t' = _ := by lift_value [shrdR16R16Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrdR16R16Effect p len dst src c t) t' = _ := by lift_value [shrdR16R16Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrdR16R16Effect p len dst src c t) t' = _ := by lift_value [shrdR16R16Effect, shrdFlags]

@[cfg_eval] theorem shrdR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrdR16R16Effect p len dst src c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrdR16R16Effect_components])

@[cfg_eval] theorem_by shrdR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrdR32R32Effect p len dst src c t) t' = _ := by lift_value [shrdR32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrdR32R32Effect p len dst src c t) t' = _ := by lift_value [shrdR32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrdR32R32Effect p len dst src c t) t' = _ := by lift_value [shrdR32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR32R32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrdR32R32Effect p len dst src c t) t' = _ := by lift_value [shrdR32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrdR32R32Effect p len dst src c t) t' = _ := by lift_value [shrdR32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrdR32R32Effect p len dst src c t) t' = _ := by lift_value [shrdR32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrdR32R32Effect p len dst src c t) t' = _ := by lift_value [shrdR32R32Effect, shrdFlags]

@[cfg_eval] theorem shrdR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrdR32R32Effect p len dst src c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrdR32R32Effect_components])

@[cfg_eval] theorem_by shrdR64R64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrdR64R64Effect p len dst src c t) t' = _ := by lift_value [shrdR64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR64R64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrdR64R64Effect p len dst src c t) t' = _ := by lift_value [shrdR64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR64R64Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrdR64R64Effect p len dst src c t) t' = _ := by lift_value [shrdR64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR64R64Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrdR64R64Effect p len dst src c t) t' = _ := by lift_value [shrdR64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR64R64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrdR64R64Effect p len dst src c t) t' = _ := by lift_value [shrdR64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR64R64Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrdR64R64Effect p len dst src c t) t' = _ := by lift_value [shrdR64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdR64R64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrdR64R64Effect p len dst src c t) t' = _ := by lift_value [shrdR64R64Effect, shrdFlags]

@[cfg_eval] theorem shrdR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrdR64R64Effect p len dst src c) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrdR64R64Effect_components])

@[cfg_eval] theorem_by shrdR32R32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrdR32R32ClEffect p len dst src t) t' = _ := by lift_value [shrdR32R32ClEffect, shrdR32R32Effect, shrdFlags]

@[cfg_eval] theorem shrdR32R32ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrdR32R32ClEffect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrdR32R32ClEffect_components])

@[cfg_eval] theorem_by shrdR64R64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrdR64R64ClEffect p len dst src t) t' = _ := by lift_value [shrdR64R64ClEffect, shrdR64R64Effect, shrdFlags]

@[cfg_eval] theorem shrdR64R64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrdR64R64ClEffect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrdR64R64ClEffect_components])

@[cfg_eval] theorem_by imulR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR16R16Effect p len dst src t) t' = _ := by lift_value [imulR16R16Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR16R16Effect p len dst src t) t' = _ := by lift_value [imulR16R16Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR16R16Effect p len dst src t) t' = _ := by lift_value [imulR16R16Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR16R16Effect_components])

@[cfg_eval] theorem_by imulR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR32R32Effect p len dst src t) t' = _ := by lift_value [imulR32R32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR32R32Effect p len dst src t) t' = _ := by lift_value [imulR32R32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR32R32Effect p len dst src t) t' = _ := by lift_value [imulR32R32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR32R32Effect_components])

@[cfg_eval] theorem_by imulR64R64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR64R64Effect p len dst src t) t' = _ := by lift_value [imulR64R64Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR64R64Effect p len dst src t) t' = _ := by lift_value [imulR64R64Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR64R64Effect p len dst src t) t' = _ := by lift_value [imulR64R64Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR64R64Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR64R64Effect_components])

@[cfg_eval] theorem_by imulR16R16Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR16R16Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR16R16Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR16R16Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR16R16Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR16R16Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR16R16Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR16R16Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR16R16Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR16R16Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR16R16Imm8Effect p len dst src imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR16R16Imm8Effect_components])

@[cfg_eval] theorem_by imulR32R32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR32R32Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32R32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR32R32Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32R32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR32R32Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR32R32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR32R32Imm8Effect p len dst src imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR32R32Imm8Effect_components])

@[cfg_eval] theorem_by imulR64R64Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR64R64Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR64R64Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR64R64Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR64R64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR64R64Imm8Effect p len dst src imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR64R64Imm8Effect_components])

@[cfg_eval] theorem_by imulR16R16Imm16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR16R16Imm16Effect p len dst src imm t) t' = _ := by lift_value [imulR16R16Imm16Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR16R16Imm16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR16R16Imm16Effect p len dst src imm t) t' = _ := by lift_value [imulR16R16Imm16Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR16R16Imm16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR16R16Imm16Effect p len dst src imm t) t' = _ := by lift_value [imulR16R16Imm16Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR16R16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR16R16Imm16Effect p len dst src imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR16R16Imm16Effect_components])

@[cfg_eval] theorem_by imulR32R32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR32R32Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32R32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR32R32Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32R32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR32R32Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR32R32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR32R32Imm32Effect p len dst src imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR32R32Imm32Effect_components])

@[cfg_eval] theorem_by imulR64R64Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR64R64Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR64R64Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR64R64Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR64R64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR64R64Imm32Effect p len dst src imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR64R64Imm32Effect_components])

@[cfg_eval] theorem_by mulR16Effect_rax (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (mulR16Effect p len src t) t' = _ := by lift_value [mulR16Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR16Effect_rdx (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 2)).value (mulR16Effect p len src t) t' = _ := by lift_value [mulR16Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR16Effect_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (mulR16Effect p len src t) t' = _ := by lift_value [mulR16Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR16Effect_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (mulR16Effect p len src t) t' = _ := by lift_value [mulR16Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem mulR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (mulR16Effect p len src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [mulR16Effect_components])

@[cfg_eval] theorem_by mulR32Effect_rax (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (mulR32Effect p len src t) t' = _ := by lift_value [mulR32Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR32Effect_rdx (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 2)).value (mulR32Effect p len src t) t' = _ := by lift_value [mulR32Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR32Effect_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (mulR32Effect p len src t) t' = _ := by lift_value [mulR32Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR32Effect_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (mulR32Effect p len src t) t' = _ := by lift_value [mulR32Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem mulR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (mulR32Effect p len src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [mulR32Effect_components])

@[cfg_eval] theorem_by mulR64Effect_rax (p : BitVec 64) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (mulR64Effect p src t) t' = _ := by lift_value [mulR64Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR64Effect_rdx (p : BitVec 64) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 2)).value (mulR64Effect p src t) t' = _ := by lift_value [mulR64Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR64Effect_CF (p : BitVec 64) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (mulR64Effect p src t) t' = _ := by lift_value [mulR64Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR64Effect_OF (p : BitVec 64) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (mulR64Effect p src t) t' = _ := by lift_value [mulR64Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem mulR64Effect_exec (code : CodeMap) (p : BitVec 64) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (mulR64Effect p src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [mulR64Effect_components])

@[cfg_eval] theorem_by imulR16Effect_rax (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (imulR16Effect p len src t) t' = _ := by lift_value [imulR16Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR16Effect_rdx (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 2)).value (imulR16Effect p len src t) t' = _ := by lift_value [imulR16Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR16Effect_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR16Effect p len src t) t' = _ := by lift_value [imulR16Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR16Effect_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR16Effect p len src t) t' = _ := by lift_value [imulR16Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem imulR16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR16Effect p len src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR16Effect_components])

@[cfg_eval] theorem_by imulR32Effect_rax (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (imulR32Effect p len src t) t' = _ := by lift_value [imulR32Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR32Effect_rdx (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 2)).value (imulR32Effect p len src t) t' = _ := by lift_value [imulR32Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR32Effect_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR32Effect p len src t) t' = _ := by lift_value [imulR32Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR32Effect_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR32Effect p len src t) t' = _ := by lift_value [imulR32Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem imulR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR32Effect p len src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR32Effect_components])

@[cfg_eval] theorem_by imulR64Effect_rax (p : BitVec 64) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (imulR64Effect p src t) t' = _ := by lift_value [imulR64Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR64Effect_rdx (p : BitVec 64) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 2)).value (imulR64Effect p src t) t' = _ := by lift_value [imulR64Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR64Effect_CF (p : BitVec 64) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR64Effect p src t) t' = _ := by lift_value [imulR64Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR64Effect_OF (p : BitVec 64) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR64Effect p src t) t' = _ := by lift_value [imulR64Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem imulR64Effect_exec (code : CodeMap) (p : BitVec 64) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR64Effect p src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR64Effect_components])

@[cfg_eval] theorem_by mulR8Effect_rax (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (mulR8Effect p len src t) t' = _ := by lift_value [mulR8Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR8Effect_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (mulR8Effect p len src t) t' = _ := by lift_value [mulR8Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulR8Effect_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (mulR8Effect p len src t) t' = _ := by lift_value [mulR8Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem mulR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (mulR8Effect p len src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [mulR8Effect_components])

@[cfg_eval] theorem_by imulR8Effect_rax (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (imulR8Effect p len src t) t' = _ := by lift_value [imulR8Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR8Effect_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR8Effect p len src t) t' = _ := by lift_value [imulR8Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulR8Effect_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR8Effect p len src t) t' = _ := by lift_value [imulR8Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem imulR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR8Effect p len src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR8Effect_components])

@[cfg_eval] theorem_by bswapR32Effect_r (p : BitVec 64) (len : Nat) (r : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr r)).value (bswapR32Effect p len r t) t' = _ := by lift_value [bswapR32Effect]

@[cfg_eval] theorem bswapR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (r : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bswapR32Effect p len r) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bswapR32Effect_components])

@[cfg_eval] theorem_by bswapR64Effect_r (p : BitVec 64) (len : Nat) (r : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr r)).value (bswapR64Effect p len r t) t' = _ := by lift_value [bswapR64Effect]

@[cfg_eval] theorem bswapR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (r : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bswapR64Effect p len r) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bswapR64Effect_components])

@[cfg_eval] theorem_by bsfR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsfR16R16Effect p len dst src t) t' = _ := by lift_value [bsfR16R16Effect]

@[cfg_eval] theorem_by bsfR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsfR16R16Effect p len dst src t) t' = _ := by lift_value [bsfR16R16Effect]

@[cfg_eval] theorem bsfR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bsfR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bsfR16R16Effect_components])

@[cfg_eval] theorem_by bsfR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsfR32R32Effect p len dst src t) t' = _ := by lift_value [bsfR32R32Effect]

@[cfg_eval] theorem_by bsfR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsfR32R32Effect p len dst src t) t' = _ := by lift_value [bsfR32R32Effect]

@[cfg_eval] theorem bsfR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bsfR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bsfR32R32Effect_components])

@[cfg_eval] theorem_by bsfR64R64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsfR64R64Effect p len dst src t) t' = _ := by lift_value [bsfR64R64Effect]

@[cfg_eval] theorem_by bsfR64R64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsfR64R64Effect p len dst src t) t' = _ := by lift_value [bsfR64R64Effect]

@[cfg_eval] theorem bsfR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bsfR64R64Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bsfR64R64Effect_components])

@[cfg_eval] theorem_by bsrR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsrR16R16Effect p len dst src t) t' = _ := by lift_value [bsrR16R16Effect]

@[cfg_eval] theorem_by bsrR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsrR16R16Effect p len dst src t) t' = _ := by lift_value [bsrR16R16Effect]

@[cfg_eval] theorem bsrR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bsrR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bsrR16R16Effect_components])

@[cfg_eval] theorem_by bsrR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsrR32R32Effect p len dst src t) t' = _ := by lift_value [bsrR32R32Effect]

@[cfg_eval] theorem_by bsrR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsrR32R32Effect p len dst src t) t' = _ := by lift_value [bsrR32R32Effect]

@[cfg_eval] theorem bsrR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bsrR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bsrR32R32Effect_components])

@[cfg_eval] theorem_by bsrR64R64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsrR64R64Effect p len dst src t) t' = _ := by lift_value [bsrR64R64Effect]

@[cfg_eval] theorem_by bsrR64R64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsrR64R64Effect p len dst src t) t' = _ := by lift_value [bsrR64R64Effect]

@[cfg_eval] theorem bsrR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bsrR64R64Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bsrR64R64Effect_components])

@[cfg_eval] theorem_by movzxR32R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movzxR32R8Effect p len dst src t) t' = _ := by lift_value [movzxR32R8Effect]

@[cfg_eval] theorem movzxR32R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movzxR32R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movzxR32R8Effect_components])

@[cfg_eval] theorem_by movzxR32R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movzxR32R16Effect p len dst src t) t' = _ := by lift_value [movzxR32R16Effect]

@[cfg_eval] theorem movzxR32R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movzxR32R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movzxR32R16Effect_components])

@[cfg_eval] theorem_by movsxR32R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxR32R8Effect p len dst src t) t' = _ := by lift_value [movsxR32R8Effect]

@[cfg_eval] theorem movsxR32R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movsxR32R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movsxR32R8Effect_components])

@[cfg_eval] theorem_by movsxR64R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxR64R8Effect p len dst src t) t' = _ := by lift_value [movsxR64R8Effect]

@[cfg_eval] theorem movsxR64R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movsxR64R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movsxR64R8Effect_components])

@[cfg_eval] theorem_by movsxR32R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxR32R16Effect p len dst src t) t' = _ := by lift_value [movsxR32R16Effect]

@[cfg_eval] theorem movsxR32R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movsxR32R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movsxR32R16Effect_components])

@[cfg_eval] theorem_by movsxR64R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxR64R16Effect p len dst src t) t' = _ := by lift_value [movsxR64R16Effect]

@[cfg_eval] theorem movsxR64R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movsxR64R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movsxR64R16Effect_components])

@[cfg_eval] theorem_by movsxdR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxdR32R32Effect p len dst src t) t' = _ := by lift_value [movsxdR32R32Effect]

@[cfg_eval] theorem movsxdR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movsxdR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movsxdR32R32Effect_components])

@[cfg_eval] theorem_by movsxdR64R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxdR64R32Effect p len dst src t) t' = _ := by lift_value [movsxdR64R32Effect]

@[cfg_eval] theorem movsxdR64R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movsxdR64R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movsxdR64R32Effect_components])

@[cfg_eval] theorem_by movR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR16R16Effect p len dst src t) t' = _ := by lift_value [movR16R16Effect]

@[cfg_eval] theorem movR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movR16R16Effect_components])

@[cfg_eval] theorem_by movR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR32R32Effect p len dst src t) t' = _ := by lift_value [movR32R32Effect]

@[cfg_eval] theorem movR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movR32R32Effect_components])

@[cfg_eval] theorem_by movR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR64R64Effect p dst src t) t' = _ := by lift_value [movR64R64Effect]

@[cfg_eval] theorem movR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movR64R64Effect_components])

@[cfg_eval] theorem_by movR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR8R8Effect p len dst src t) t' = _ := by lift_value [movR8R8Effect]

@[cfg_eval] theorem movR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movR8R8Effect_components])

@[cfg_eval] theorem_by movR8Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR8Imm8Effect p len dst imm t) t' = _ := by lift_value [movR8Imm8Effect]

@[cfg_eval] theorem movR8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movR8Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movR8Imm8Effect_components])

@[cfg_eval] theorem_by movR16Imm16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR16Imm16Effect p len dst imm t) t' = _ := by lift_value [movR16Imm16Effect]

@[cfg_eval] theorem movR16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 16) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movR16Imm16Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movR16Imm16Effect_components])

@[cfg_eval] theorem_by movR32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR32Imm32Effect p len dst imm t) t' = _ := by lift_value [movR32Imm32Effect]

@[cfg_eval] theorem movR32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movR32Imm32Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movR32Imm32Effect_components])

@[cfg_eval] theorem_by movR64Imm32Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR64Imm32Effect p dst imm t) t' = _ := by lift_value [movR64Imm32Effect]

@[cfg_eval] theorem movR64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movR64Imm32Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movR64Imm32Effect_components])

@[cfg_eval] theorem_by movR64Imm64Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR64Imm64Effect p dst imm t) t' = _ := by lift_value [movR64Imm64Effect]

@[cfg_eval] theorem movR64Imm64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 64) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movR64Imm64Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movR64Imm64Effect_components])

@[cfg_eval] theorem_by xchgR16R16Effect_src (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr src)).value (xchgR16R16Effect p len dst src t) t' = _ := by lift_value [xchgR16R16Effect]

@[cfg_eval] theorem_by xchgR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xchgR16R16Effect p len dst src t) t' = _ := by lift_value [xchgR16R16Effect]

@[cfg_eval] theorem xchgR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xchgR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xchgR16R16Effect_components])

@[cfg_eval] theorem_by xchgR32R32Effect_src (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr src)).value (xchgR32R32Effect p len dst src t) t' = _ := by lift_value [xchgR32R32Effect]

@[cfg_eval] theorem_by xchgR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xchgR32R32Effect p len dst src t) t' = _ := by lift_value [xchgR32R32Effect]

@[cfg_eval] theorem xchgR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xchgR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xchgR32R32Effect_components])

@[cfg_eval] theorem_by xchgR64R64Effect_src (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr src)).value (xchgR64R64Effect p len dst src t) t' = _ := by lift_value [xchgR64R64Effect]

@[cfg_eval] theorem_by xchgR64R64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xchgR64R64Effect p len dst src t) t' = _ := by lift_value [xchgR64R64Effect]

@[cfg_eval] theorem xchgR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xchgR64R64Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xchgR64R64Effect_components])

@[cfg_eval] theorem_by xchgR8R8Effect_src (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr src)).value (xchgR8R8Effect p len dst src t) t' = _ := by lift_value [xchgR8R8Effect]

@[cfg_eval] theorem_by xchgR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xchgR8R8Effect p len dst src t) t' = _ := by lift_value [xchgR8R8Effect]

@[cfg_eval] theorem xchgR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xchgR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xchgR8R8Effect_components])

@[cfg_eval] theorem_by xchgR16AxEffect_rax (p : BitVec 64) (len : Nat) (r : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (xchgR16AxEffect p len r t) t' = _ := by lift_value [xchgR16AxEffect]

@[cfg_eval] theorem_by xchgR16AxEffect_r (p : BitVec 64) (len : Nat) (r : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr r)).value (xchgR16AxEffect p len r t) t' = _ := by lift_value [xchgR16AxEffect]

@[cfg_eval] theorem xchgR16AxEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (r : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xchgR16AxEffect p len r) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xchgR16AxEffect_components])

@[cfg_eval] theorem_by xchgR32EaxEffect_rax (p : BitVec 64) (len : Nat) (r : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (xchgR32EaxEffect p len r t) t' = _ := by lift_value [xchgR32EaxEffect]

@[cfg_eval] theorem_by xchgR32EaxEffect_r (p : BitVec 64) (len : Nat) (r : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr r)).value (xchgR32EaxEffect p len r t) t' = _ := by lift_value [xchgR32EaxEffect]

@[cfg_eval] theorem xchgR32EaxEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (r : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xchgR32EaxEffect p len r) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xchgR32EaxEffect_components])

@[cfg_eval] theorem_by xchgR64RaxEffect_rax (p : BitVec 64) (len : Nat) (r : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (xchgR64RaxEffect p len r t) t' = _ := by lift_value [xchgR64RaxEffect]

@[cfg_eval] theorem_by xchgR64RaxEffect_r (p : BitVec 64) (len : Nat) (r : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr r)).value (xchgR64RaxEffect p len r t) t' = _ := by lift_value [xchgR64RaxEffect]

@[cfg_eval] theorem xchgR64RaxEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (r : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xchgR64RaxEffect p len r) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xchgR64RaxEffect_components])

@[cfg_eval] theorem nopEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (fun _ => nopEffect p len) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [nopEffect, Effect.components])

@[cfg_eval] theorem_by cmovR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (cc : BitVec 4) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags (condHolds cc) (cmovR16R16Effect p len dst src) t) t' = _ := by lift_value [cmovR16R16Effect, atFlags]

@[cfg_eval] theorem cmovR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (cc : BitVec 4) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags (condHolds cc) (cmovR16R16Effect p len dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, cmovR16R16Effect_components])

@[cfg_eval] theorem_by cmovR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (cc : BitVec 4) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags (condHolds cc) (cmovR32R32Effect p len dst src) t) t' = _ := by lift_value [cmovR32R32Effect, atFlags]

@[cfg_eval] theorem cmovR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (cc : BitVec 4) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags (condHolds cc) (cmovR32R32Effect p len dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, cmovR32R32Effect_components])

@[cfg_eval] theorem_by cmovR64R64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (cc : BitVec 4) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags (condHolds cc) (cmovR64R64Effect p len dst src) t) t' = _ := by lift_value [cmovR64R64Effect, atFlags]

@[cfg_eval] theorem cmovR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (cc : BitVec 4) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags (condHolds cc) (cmovR64R64Effect p len dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, cmovR64R64Effect_components])

@[cfg_eval] theorem_by setccR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cc : BitVec 4) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags (condHolds cc) (setccR8Effect p len dst) t) t' = _ := by lift_value [setccR8Effect, atFlags]

@[cfg_eval] theorem setccR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (cc : BitVec 4) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags (condHolds cc) (setccR8Effect p len dst)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, setccR8Effect_components])

@[cfg_eval] theorem_by leaR64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (leaR64Effect p dst am t) t' = _ := by lift_value [leaR64Effect, leaLen]

@[cfg_eval] theorem leaR64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (leaR64Effect p dst am) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [leaR64Effect_components])

@[cfg_eval] theorem_by leaR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (leaR32Effect p len dst am t) t' = _ := by lift_value [leaR32Effect, leaSpec]

@[cfg_eval] theorem leaR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (leaR32Effect p len dst am) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [leaR32Effect_components])

end P256.Proofs.Lift
