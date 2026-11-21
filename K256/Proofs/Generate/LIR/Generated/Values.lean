import K256.Proofs.Common.Lift.Eval
import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Generate.LIR.Generated.Footprints
import K256.Proofs.Sec1.LIR.Generated.Values
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.R8M8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Cmp.Generated.MR.Triple
import X86Proofs.Instructions.Imul.Generated.RRImm32.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Or.Generated.R8M8.Triple
import X86Proofs.Instructions.Sar.Generated.Cl.Triple
import X86Proofs.Instructions.Sar.Generated.R.Triple
import X86Proofs.Instructions.Sar.Generated.R8.Triple
import X86Proofs.Instructions.Sar.Generated.R8Cl.Triple
import X86Proofs.Instructions.Sbb.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.R8.Triple

namespace K256.Proofs.Generate.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

open K256.Proofs.Sec1.LIR

@[cfg_eval] theorem_by addR8M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR8M8Effect p len dst am t) t' = _ := by lift_value [addR8M8Effect]

@[cfg_eval] theorem_by addR8M8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR8M8Effect p len dst am t) t' = _ := by lift_value [addR8M8Effect]

@[cfg_eval] theorem_by addR8M8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR8M8Effect p len dst am t) t' = _ := by lift_value [addR8M8Effect]

@[cfg_eval] theorem_by addR8M8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR8M8Effect p len dst am t) t' = _ := by lift_value [addR8M8Effect]

@[cfg_eval] theorem_by addR8M8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR8M8Effect p len dst am t) t' = _ := by lift_value [addR8M8Effect]

@[cfg_eval] theorem_by addR8M8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR8M8Effect p len dst am t) t' = _ := by lift_value [addR8M8Effect]

@[cfg_eval] theorem_by addR8M8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR8M8Effect p len dst am t) t' = _ := by lift_value [addR8M8Effect]

@[cfg_eval ↓] theorem addR8M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (addR8M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [addR8M8Effect_components])

@[cfg_eval] theorem_by orR8M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR8M8Effect p len dst am t) t' = _ := by lift_value [orR8M8Effect]

@[cfg_eval] theorem_by orR8M8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR8M8Effect p len dst am t) t' = _ := by lift_value [orR8M8Effect]

@[cfg_eval] theorem_by orR8M8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR8M8Effect p len dst am t) t' = _ := by lift_value [orR8M8Effect]

@[cfg_eval] theorem_by orR8M8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR8M8Effect p len dst am t) t' = _ := by lift_value [orR8M8Effect]

@[cfg_eval] theorem_by orR8M8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR8M8Effect p len dst am t) t' = _ := by lift_value [orR8M8Effect]

@[cfg_eval] theorem_by orR8M8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR8M8Effect p len dst am t) t' = _ := by lift_value [orR8M8Effect]

@[cfg_eval ↓] theorem orR8M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (orR8M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [orR8M8Effect_components])

@[cfg_eval] theorem_by cmpMREffect32_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpMREffect p len 32 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect32_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpMREffect p len 32 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect32_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpMREffect p len 32 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect32_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpMREffect p len 32 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect32_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpMREffect p len 32 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect32_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpMREffect p len 32 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval ↓] theorem cmpMREffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (cmpMREffect p len 32 src am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpMREffect_components])

@[cfg_eval] theorem_by cmpMREffect64_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpMREffect p len 64 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect64_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpMREffect p len 64 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect64_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpMREffect p len 64 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect64_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpMREffect p len 64 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect64_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpMREffect p len 64 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect64_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpMREffect p len 64 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval ↓] theorem cmpMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (cmpMREffect p len 64 src am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpMREffect_components])

@[cfg_eval] theorem_by cmpMREffect8_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpMREffect p len 8 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect8_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpMREffect p len 8 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect8_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpMREffect p len 8 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect8_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpMREffect p len 8 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect8_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpMREffect p len 8 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval] theorem_by cmpMREffect8_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpMREffect p len 8 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval ↓] theorem cmpMREffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (cmpMREffect p len 8 src am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpMREffect_components])

@[cfg_eval] theorem_by sbbR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR64R64Effect p dst src) t) t' = _ := by lift_value [sbbR64R64Effect, atFlags]

@[cfg_eval] theorem_by sbbR64R64Effect_CF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR64R64Effect p dst src) t) t' = _ := by lift_value [sbbR64R64Effect, atFlags]

@[cfg_eval] theorem_by sbbR64R64Effect_PF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR64R64Effect p dst src) t) t' = _ := by lift_value [sbbR64R64Effect, atFlags]

@[cfg_eval] theorem_by sbbR64R64Effect_AF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR64R64Effect p dst src) t) t' = _ := by lift_value [sbbR64R64Effect, atFlags]

@[cfg_eval] theorem_by sbbR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR64R64Effect p dst src) t) t' = _ := by lift_value [sbbR64R64Effect, atFlags]

@[cfg_eval] theorem_by sbbR64R64Effect_SF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR64R64Effect p dst src) t) t' = _ := by lift_value [sbbR64R64Effect, atFlags]

@[cfg_eval] theorem_by sbbR64R64Effect_OF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR64R64Effect p dst src) t) t' = _ := by lift_value [sbbR64R64Effect, atFlags]

@[cfg_eval] theorem sbbR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR64R64Effect p dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR64R64Effect_components])

@[cfg_eval] theorem_by xorR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR8R8Effect p len dst src t) t' = _ := by lift_value [xorR8R8Effect]

@[cfg_eval] theorem_by xorR8R8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR8R8Effect p len dst src t) t' = _ := by lift_value [xorR8R8Effect]

@[cfg_eval] theorem_by xorR8R8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR8R8Effect p len dst src t) t' = _ := by lift_value [xorR8R8Effect]

@[cfg_eval] theorem_by xorR8R8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR8R8Effect p len dst src t) t' = _ := by lift_value [xorR8R8Effect]

@[cfg_eval] theorem_by xorR8R8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR8R8Effect p len dst src t) t' = _ := by lift_value [xorR8R8Effect]

@[cfg_eval] theorem_by xorR8R8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR8R8Effect p len dst src t) t' = _ := by lift_value [xorR8R8Effect]

@[cfg_eval] theorem xorR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR8R8Effect_components])

@[cfg_eval] theorem_by notR32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (notR32Effect p len dst t) t' = _ := by lift_value [notR32Effect]

@[cfg_eval] theorem notR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (notR32Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [notR32Effect_components])

@[cfg_eval] theorem_by sarR64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (sarR64ClEffect p len dst t) t' = _ := by lift_value [sarR64ClEffect, sarR64Effect, sarFlags]

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

@[cfg_eval] theorem_by sarR8ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (sarR8ClEffect p len dst t) t' = _ := by lift_value [sarR8ClEffect, sarR8Effect, sarFlags]

@[cfg_eval] theorem_by imulR64R64Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR64R64Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR64R64Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR64R64Imm32Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR64R64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR64R64Imm32Effect p len dst src imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR64R64Imm32Effect_components])

@[cfg_eval] theorem_by addMREffect32_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (addMREffect p len 32 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect32_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (addMREffect p len 32 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect32_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (addMREffect p len 32 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect32_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addMREffect p len 32 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect32_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (addMREffect p len 32 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect32_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (addMREffect p len 32 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval ↓] theorem_by addMREffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (addMREffect p len 32 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [addMREffect]
  · simp only [addMREffect_components]; rfl

@[cfg_eval] theorem_by addMREffect64_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (addMREffect p len 64 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect64_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (addMREffect p len 64 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect64_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (addMREffect p len 64 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect64_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addMREffect p len 64 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect64_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (addMREffect p len 64 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect64_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (addMREffect p len 64 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval ↓] theorem_by addMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (addMREffect p len 64 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [addMREffect]
  · simp only [addMREffect_components]; rfl

@[cfg_eval] theorem_by addMREffect8_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (addMREffect p len 8 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect8_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (addMREffect p len 8 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect8_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (addMREffect p len 8 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect8_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addMREffect p len 8 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect8_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (addMREffect p len 8 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval] theorem_by addMREffect8_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (addMREffect p len 8 src am t) t' = _ := by lift_value [addMREffect]

@[cfg_eval ↓] theorem_by addMREffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (addMREffect p len 8 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [addMREffect]
  · simp only [addMREffect_components]; rfl

@[cfg_eval] theorem_by andMREffect32_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (andMREffect p len 32 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect32_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (andMREffect p len 32 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect32_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andMREffect p len 32 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect32_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (andMREffect p len 32 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect32_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (andMREffect p len 32 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval ↓] theorem_by andMREffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (andMREffect p len 32 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [andMREffect]
  · simp only [andMREffect_components]; rfl

@[cfg_eval] theorem_by andMREffect64_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (andMREffect p len 64 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect64_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (andMREffect p len 64 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect64_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andMREffect p len 64 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect64_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (andMREffect p len 64 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect64_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (andMREffect p len 64 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval ↓] theorem_by andMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (andMREffect p len 64 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [andMREffect]
  · simp only [andMREffect_components]; rfl

@[cfg_eval] theorem_by andMREffect8_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (andMREffect p len 8 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect8_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (andMREffect p len 8 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect8_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andMREffect p len 8 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect8_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (andMREffect p len 8 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval] theorem_by andMREffect8_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (andMREffect p len 8 src am t) t' = _ := by lift_value [andMREffect]

@[cfg_eval ↓] theorem_by andMREffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (andMREffect p len 8 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [andMREffect]
  · simp only [andMREffect_components]; rfl

@[cfg_eval] theorem_by addM8Imm8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (addM8Imm8Effect p len am imm t) t' = _ := by lift_value [addM8Imm8Effect]

@[cfg_eval] theorem_by addM8Imm8Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (addM8Imm8Effect p len am imm t) t' = _ := by lift_value [addM8Imm8Effect]

@[cfg_eval] theorem_by addM8Imm8Effect_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (addM8Imm8Effect p len am imm t) t' = _ := by lift_value [addM8Imm8Effect]

@[cfg_eval] theorem_by addM8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addM8Imm8Effect p len am imm t) t' = _ := by lift_value [addM8Imm8Effect]

@[cfg_eval] theorem_by addM8Imm8Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (addM8Imm8Effect p len am imm t) t' = _ := by lift_value [addM8Imm8Effect]

@[cfg_eval] theorem_by addM8Imm8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (addM8Imm8Effect p len am imm t) t' = _ := by lift_value [addM8Imm8Effect]

@[cfg_eval ↓] theorem_by addM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (addM8Imm8Effect p len am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [addM8Imm8Effect]
  · simp only [addM8Imm8Effect_components]; rfl

end K256.Proofs.Generate.LIR
