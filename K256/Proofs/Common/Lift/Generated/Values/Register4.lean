import K256.Proofs.Common.Lift.Eval
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
namespace K256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG

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

@[cfg_eval] theorem_by shlR64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR64ClEffect p len dst t) t' = _ := by lift_value [shlR64ClEffect, shlR64Effect, shlFlags]

@[cfg_eval] theorem shlR64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shlR64ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shlR64ClEffect_components])

@[cfg_eval] theorem_by shrR64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR64ClEffect p len dst t) t' = _ := by lift_value [shrR64ClEffect, shrR64Effect, shrFlags]

@[cfg_eval] theorem shrR64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrR64ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrR64ClEffect_components])

@[cfg_eval] theorem_by imulR64R64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR64R64Effect p len dst src t) t' = _ := by lift_value [imulR64R64Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR64R64Effect p len dst src t) t' = _ := by lift_value [imulR64R64Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR64R64Effect p len dst src t) t' = _ := by lift_value [imulR64R64Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR64R64Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR64R64Effect_components])

@[cfg_eval] theorem_by imulR32R32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR32R32Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32R32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR32R32Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32R32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR32R32Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR32R32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR32R32Imm8Effect p len dst src imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR32R32Imm8Effect_components])

@[cfg_eval] theorem_by imulR32R32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR32R32Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32R32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR32R32Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32R32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR32R32Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR32R32Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR32R32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR32R32Imm32Effect p len dst src imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR32R32Imm32Effect_components])

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

@[cfg_eval] theorem_by bswapR64Effect_r (p : BitVec 64) (len : Nat) (r : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr r)).value (bswapR64Effect p len r t) t' = _ := by lift_value [bswapR64Effect]

@[cfg_eval] theorem bswapR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (r : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bswapR64Effect p len r) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bswapR64Effect_components])

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

@[cfg_eval] theorem nopEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (fun _ => nopEffect p len) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [nopEffect, Effect.components])

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

end K256.Proofs.Lift
