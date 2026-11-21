import K256.Proofs.Common.Lift.Eval
import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Sec1.LIR.Generated.Footprints
import X86Proofs.Instructions.Adc.Generated.Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.RM.Triple
import X86Proofs.Instructions.Adc.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Add.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.Imm32.Triple
import X86Proofs.Instructions.And.Generated.R8.Triple
import X86Proofs.Instructions.And.Generated.R8Imm8.Triple
import X86Proofs.Instructions.And.Generated.R8M8.Triple
import X86Proofs.Instructions.And.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.R8.Triple
import X86Proofs.Instructions.Cmp.Generated.RM.Triple
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Mov.Generated.R8.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Movsx.Generated.RM8.Triple
import X86Proofs.Instructions.Mul.Generated.M.Triple
import X86Proofs.Instructions.Not.Generated.R8.Triple
import X86Proofs.Instructions.Or.Generated.AccImm8.Triple
import X86Proofs.Instructions.Or.Generated.Imm8.Triple
import X86Proofs.Instructions.Or.Generated.R8.Triple
import X86Proofs.Instructions.Or.Generated.RM.Triple
import X86Proofs.Instructions.Or.Generated.RR.Triple
import X86Proofs.Instructions.Sbb.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shl.Generated.Cl.Triple
import X86Proofs.Instructions.Shl.Generated.R.Triple
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
import X86Proofs.Instructions.Stos.Generated.Rep.Triple
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Sub.Generated.R8.Triple
import X86Proofs.Instructions.Test.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.R8M8.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

@[cfg_eval] theorem_by mulM64Effect_rax (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (mulM64Effect p len am t) t' = _ := by lift_value [mulM64Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulM64Effect_rdx (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 2)).value (mulM64Effect p len am t) t' = _ := by lift_value [mulM64Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulM64Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (mulM64Effect p len am t) t' = _ := by lift_value [mulM64Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulM64Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (mulM64Effect p len am t) t' = _ := by lift_value [mulM64Effect, mulFlags, mulResult_fst]

@[cfg_eval ↓] theorem mulM64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (mulM64Effect p len am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [mulM64Effect_components])

@[cfg_eval] theorem_by movsxR32M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxR32M8Effect p len dst am t) t' = _ := by lift_value [movsxR32M8Effect]

@[cfg_eval ↓] theorem movsxR32M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (movsxR32M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movsxR32M8Effect_components])

@[cfg_eval] theorem_by addR64M64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR64M64Effect p dst am t) t' = _ := by lift_value [addR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by addR64M64Effect_CF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR64M64Effect p dst am t) t' = _ := by lift_value [addR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by addR64M64Effect_PF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR64M64Effect p dst am t) t' = _ := by lift_value [addR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by addR64M64Effect_AF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR64M64Effect p dst am t) t' = _ := by lift_value [addR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by addR64M64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR64M64Effect p dst am t) t' = _ := by lift_value [addR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by addR64M64Effect_SF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR64M64Effect p dst am t) t' = _ := by lift_value [addR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by addR64M64Effect_OF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR64M64Effect p dst am t) t' = _ := by lift_value [addR64M64Effect, movLoadLen]

@[cfg_eval ↓] theorem addR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (addR64M64Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [addR64M64Effect_components])

@[cfg_eval] theorem_by orR64M64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR64M64Effect p dst am t) t' = _ := by lift_value [orR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by orR64M64Effect_CF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR64M64Effect p dst am t) t' = _ := by lift_value [orR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by orR64M64Effect_PF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR64M64Effect p dst am t) t' = _ := by lift_value [orR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by orR64M64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR64M64Effect p dst am t) t' = _ := by lift_value [orR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by orR64M64Effect_SF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR64M64Effect p dst am t) t' = _ := by lift_value [orR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by orR64M64Effect_OF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR64M64Effect p dst am t) t' = _ := by lift_value [orR64M64Effect, movLoadLen]

@[cfg_eval ↓] theorem orR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (orR64M64Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [orR64M64Effect_components])

@[cfg_eval] theorem_by adcR64M64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR64M64Effect p dst am) t) t' = _ := by lift_value [adcR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by adcR64M64Effect_CF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR64M64Effect p dst am) t) t' = _ := by lift_value [adcR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by adcR64M64Effect_PF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR64M64Effect p dst am) t) t' = _ := by lift_value [adcR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by adcR64M64Effect_AF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR64M64Effect p dst am) t) t' = _ := by lift_value [adcR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by adcR64M64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR64M64Effect p dst am) t) t' = _ := by lift_value [adcR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by adcR64M64Effect_SF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR64M64Effect p dst am) t) t' = _ := by lift_value [adcR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by adcR64M64Effect_OF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR64M64Effect p dst am) t) t' = _ := by lift_value [adcR64M64Effect, atFlags, movLoadLen]

@[cfg_eval ↓] theorem adcR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (atFlags StatusFlags.CF (adcR64M64Effect p dst am)) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [atFlags, adcR64M64Effect_components])

@[cfg_eval] theorem_by andR64M64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR64M64Effect p dst am t) t' = _ := by lift_value [andR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by andR64M64Effect_CF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR64M64Effect p dst am t) t' = _ := by lift_value [andR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by andR64M64Effect_PF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR64M64Effect p dst am t) t' = _ := by lift_value [andR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by andR64M64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR64M64Effect p dst am t) t' = _ := by lift_value [andR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by andR64M64Effect_SF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR64M64Effect p dst am t) t' = _ := by lift_value [andR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by andR64M64Effect_OF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR64M64Effect p dst am t) t' = _ := by lift_value [andR64M64Effect, movLoadLen]

@[cfg_eval ↓] theorem andR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (andR64M64Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [andR64M64Effect_components])

@[cfg_eval] theorem_by andR8M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR8M8Effect p len dst am t) t' = _ := by lift_value [andR8M8Effect]

@[cfg_eval] theorem_by andR8M8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR8M8Effect p len dst am t) t' = _ := by lift_value [andR8M8Effect]

@[cfg_eval] theorem_by andR8M8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR8M8Effect p len dst am t) t' = _ := by lift_value [andR8M8Effect]

@[cfg_eval] theorem_by andR8M8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR8M8Effect p len dst am t) t' = _ := by lift_value [andR8M8Effect]

@[cfg_eval] theorem_by andR8M8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR8M8Effect p len dst am t) t' = _ := by lift_value [andR8M8Effect]

@[cfg_eval] theorem_by andR8M8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR8M8Effect p len dst am t) t' = _ := by lift_value [andR8M8Effect]

@[cfg_eval ↓] theorem andR8M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (andR8M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [andR8M8Effect_components])

@[cfg_eval] theorem_by xorR64M64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR64M64Effect p dst am t) t' = _ := by lift_value [xorR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by xorR64M64Effect_CF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR64M64Effect p dst am t) t' = _ := by lift_value [xorR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by xorR64M64Effect_PF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR64M64Effect p dst am t) t' = _ := by lift_value [xorR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by xorR64M64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR64M64Effect p dst am t) t' = _ := by lift_value [xorR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by xorR64M64Effect_SF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR64M64Effect p dst am t) t' = _ := by lift_value [xorR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by xorR64M64Effect_OF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR64M64Effect p dst am t) t' = _ := by lift_value [xorR64M64Effect, movLoadLen]

@[cfg_eval ↓] theorem xorR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (xorR64M64Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [xorR64M64Effect_components])

@[cfg_eval] theorem_by xorR8M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR8M8Effect p len dst am t) t' = _ := by lift_value [xorR8M8Effect]

@[cfg_eval] theorem_by xorR8M8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR8M8Effect p len dst am t) t' = _ := by lift_value [xorR8M8Effect]

@[cfg_eval] theorem_by xorR8M8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR8M8Effect p len dst am t) t' = _ := by lift_value [xorR8M8Effect]

@[cfg_eval] theorem_by xorR8M8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR8M8Effect p len dst am t) t' = _ := by lift_value [xorR8M8Effect]

@[cfg_eval] theorem_by xorR8M8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR8M8Effect p len dst am t) t' = _ := by lift_value [xorR8M8Effect]

@[cfg_eval] theorem_by xorR8M8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR8M8Effect p len dst am t) t' = _ := by lift_value [xorR8M8Effect]

@[cfg_eval ↓] theorem xorR8M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (xorR8M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [xorR8M8Effect_components])

@[cfg_eval] theorem_by cmpR32M32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR32M32Effect p len dst am t) t' = _ := by lift_value [cmpR32M32Effect]

@[cfg_eval] theorem_by cmpR32M32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR32M32Effect p len dst am t) t' = _ := by lift_value [cmpR32M32Effect]

@[cfg_eval] theorem_by cmpR32M32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR32M32Effect p len dst am t) t' = _ := by lift_value [cmpR32M32Effect]

@[cfg_eval] theorem_by cmpR32M32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR32M32Effect p len dst am t) t' = _ := by lift_value [cmpR32M32Effect]

@[cfg_eval] theorem_by cmpR32M32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR32M32Effect p len dst am t) t' = _ := by lift_value [cmpR32M32Effect]

@[cfg_eval] theorem_by cmpR32M32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR32M32Effect p len dst am t) t' = _ := by lift_value [cmpR32M32Effect]

@[cfg_eval ↓] theorem cmpR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (cmpR32M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpR32M32Effect_components])

@[cfg_eval] theorem_by cmpR64M64Effect_CF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR64M64Effect p dst am t) t' = _ := by lift_value [cmpR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by cmpR64M64Effect_PF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR64M64Effect p dst am t) t' = _ := by lift_value [cmpR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by cmpR64M64Effect_AF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR64M64Effect p dst am t) t' = _ := by lift_value [cmpR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by cmpR64M64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR64M64Effect p dst am t) t' = _ := by lift_value [cmpR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by cmpR64M64Effect_SF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR64M64Effect p dst am t) t' = _ := by lift_value [cmpR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by cmpR64M64Effect_OF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR64M64Effect p dst am t) t' = _ := by lift_value [cmpR64M64Effect, movLoadLen]

@[cfg_eval ↓] theorem cmpR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (cmpR64M64Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpR64M64Effect_components])

@[cfg_eval] theorem_by repStosbEffect_rdi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 7)).value (repStosbEffect p t) t' = _ := by lift_value [repStosbEffect, Nat.one_mul]

@[cfg_eval] theorem_by repStosbEffect_rcx (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 1)).value (repStosbEffect p t) t' = _ := by lift_value [repStosbEffect, Nat.one_mul]

@[cfg_eval] theorem_by repStosqEffect_rdi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 7)).value (repStosqEffect p t) t' = _ := by lift_value [repStosqEffect, Nat.one_mul]

@[cfg_eval] theorem_by repStosqEffect_rcx (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 1)).value (repStosqEffect p t) t' = _ := by lift_value [repStosqEffect, Nat.one_mul]

@[cfg_eval] theorem_by andR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR32R32Effect p len dst src t) t' = _ := by lift_value [andR32R32Effect]

@[cfg_eval] theorem_by andR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR32R32Effect p len dst src t) t' = _ := by lift_value [andR32R32Effect]

@[cfg_eval] theorem_by andR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR32R32Effect p len dst src t) t' = _ := by lift_value [andR32R32Effect]

@[cfg_eval] theorem_by andR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR32R32Effect p len dst src t) t' = _ := by lift_value [andR32R32Effect]

@[cfg_eval] theorem_by andR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR32R32Effect p len dst src t) t' = _ := by lift_value [andR32R32Effect]

@[cfg_eval] theorem_by andR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR32R32Effect p len dst src t) t' = _ := by lift_value [andR32R32Effect]

@[cfg_eval] theorem andR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR32R32Effect_components])

@[cfg_eval] theorem_by adcR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR64R64Effect p dst src) t) t' = _ := by lift_value [adcR64R64Effect, atFlags]

@[cfg_eval] theorem_by adcR64R64Effect_CF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR64R64Effect p dst src) t) t' = _ := by lift_value [adcR64R64Effect, atFlags]

@[cfg_eval] theorem_by adcR64R64Effect_PF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR64R64Effect p dst src) t) t' = _ := by lift_value [adcR64R64Effect, atFlags]

@[cfg_eval] theorem_by adcR64R64Effect_AF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR64R64Effect p dst src) t) t' = _ := by lift_value [adcR64R64Effect, atFlags]

@[cfg_eval] theorem_by adcR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR64R64Effect p dst src) t) t' = _ := by lift_value [adcR64R64Effect, atFlags]

@[cfg_eval] theorem_by adcR64R64Effect_SF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR64R64Effect p dst src) t) t' = _ := by lift_value [adcR64R64Effect, atFlags]

@[cfg_eval] theorem_by adcR64R64Effect_OF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR64R64Effect p dst src) t) t' = _ := by lift_value [adcR64R64Effect, atFlags]

@[cfg_eval] theorem adcR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR64R64Effect p dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR64R64Effect_components])

@[cfg_eval] theorem_by orR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR32R32Effect p len dst src t) t' = _ := by lift_value [orR32R32Effect]

@[cfg_eval] theorem_by orR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR32R32Effect p len dst src t) t' = _ := by lift_value [orR32R32Effect]

@[cfg_eval] theorem_by orR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR32R32Effect p len dst src t) t' = _ := by lift_value [orR32R32Effect]

@[cfg_eval] theorem_by orR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR32R32Effect p len dst src t) t' = _ := by lift_value [orR32R32Effect]

@[cfg_eval] theorem_by orR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR32R32Effect p len dst src t) t' = _ := by lift_value [orR32R32Effect]

@[cfg_eval] theorem_by orR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR32R32Effect p len dst src t) t' = _ := by lift_value [orR32R32Effect]

@[cfg_eval] theorem orR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR32R32Effect_components])

@[cfg_eval] theorem_by subR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR8R8Effect p len dst src t) t' = _ := by lift_value [subR8R8Effect]

@[cfg_eval] theorem_by subR8R8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR8R8Effect p len dst src t) t' = _ := by lift_value [subR8R8Effect]

@[cfg_eval] theorem_by subR8R8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR8R8Effect p len dst src t) t' = _ := by lift_value [subR8R8Effect]

@[cfg_eval] theorem_by subR8R8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR8R8Effect p len dst src t) t' = _ := by lift_value [subR8R8Effect]

@[cfg_eval] theorem_by subR8R8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR8R8Effect p len dst src t) t' = _ := by lift_value [subR8R8Effect]

@[cfg_eval] theorem_by subR8R8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR8R8Effect p len dst src t) t' = _ := by lift_value [subR8R8Effect]

@[cfg_eval] theorem_by subR8R8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR8R8Effect p len dst src t) t' = _ := by lift_value [subR8R8Effect]

@[cfg_eval] theorem subR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR8R8Effect_components])

@[cfg_eval] theorem_by andR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR8R8Effect p len dst src t) t' = _ := by lift_value [andR8R8Effect]

@[cfg_eval] theorem_by andR8R8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR8R8Effect p len dst src t) t' = _ := by lift_value [andR8R8Effect]

@[cfg_eval] theorem_by andR8R8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR8R8Effect p len dst src t) t' = _ := by lift_value [andR8R8Effect]

@[cfg_eval] theorem_by andR8R8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR8R8Effect p len dst src t) t' = _ := by lift_value [andR8R8Effect]

@[cfg_eval] theorem_by andR8R8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR8R8Effect p len dst src t) t' = _ := by lift_value [andR8R8Effect]

@[cfg_eval] theorem_by andR8R8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR8R8Effect p len dst src t) t' = _ := by lift_value [andR8R8Effect]

@[cfg_eval] theorem andR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR8R8Effect_components])

@[cfg_eval] theorem_by orR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR8R8Effect p len dst src t) t' = _ := by lift_value [orR8R8Effect]

@[cfg_eval] theorem_by orR8R8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR8R8Effect p len dst src t) t' = _ := by lift_value [orR8R8Effect]

@[cfg_eval] theorem_by orR8R8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR8R8Effect p len dst src t) t' = _ := by lift_value [orR8R8Effect]

@[cfg_eval] theorem_by orR8R8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR8R8Effect p len dst src t) t' = _ := by lift_value [orR8R8Effect]

@[cfg_eval] theorem_by orR8R8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR8R8Effect p len dst src t) t' = _ := by lift_value [orR8R8Effect]

@[cfg_eval] theorem_by orR8R8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR8R8Effect p len dst src t) t' = _ := by lift_value [orR8R8Effect]

@[cfg_eval] theorem orR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR8R8Effect_components])

@[cfg_eval] theorem_by cmpR8R8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR8R8Effect p len dst src t) t' = _ := by lift_value [cmpR8R8Effect]

@[cfg_eval] theorem_by cmpR8R8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR8R8Effect p len dst src t) t' = _ := by lift_value [cmpR8R8Effect]

@[cfg_eval] theorem_by cmpR8R8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR8R8Effect p len dst src t) t' = _ := by lift_value [cmpR8R8Effect]

@[cfg_eval] theorem_by cmpR8R8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR8R8Effect p len dst src t) t' = _ := by lift_value [cmpR8R8Effect]

@[cfg_eval] theorem_by cmpR8R8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR8R8Effect p len dst src t) t' = _ := by lift_value [cmpR8R8Effect]

@[cfg_eval] theorem_by cmpR8R8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR8R8Effect p len dst src t) t' = _ := by lift_value [cmpR8R8Effect]

@[cfg_eval] theorem cmpR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR8R8Effect_components])

@[cfg_eval] theorem_by orR64Imm8Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR64Imm8Effect p dst imm t) t' = _ := by lift_value [orR64Imm8Effect]

@[cfg_eval] theorem_by orR64Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR64Imm8Effect p dst imm t) t' = _ := by lift_value [orR64Imm8Effect]

@[cfg_eval] theorem_by orR64Imm8Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR64Imm8Effect p dst imm t) t' = _ := by lift_value [orR64Imm8Effect]

@[cfg_eval] theorem_by orR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR64Imm8Effect p dst imm t) t' = _ := by lift_value [orR64Imm8Effect]

@[cfg_eval] theorem_by orR64Imm8Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR64Imm8Effect p dst imm t) t' = _ := by lift_value [orR64Imm8Effect]

@[cfg_eval] theorem_by orR64Imm8Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR64Imm8Effect p dst imm t) t' = _ := by lift_value [orR64Imm8Effect]

@[cfg_eval] theorem orR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR64Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR64Imm8Effect_components])

@[cfg_eval] theorem_by adcR64Imm8Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm8Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm8Effect_AF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm8Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR64Imm8Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm) t) t' = _ := by lift_value [adcR64Imm8Effect, atFlags]

@[cfg_eval] theorem adcR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR64Imm8Effect p dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR64Imm8Effect_components])

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

@[cfg_eval] theorem_by notR8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (notR8Effect p len dst t) t' = _ := by lift_value [notR8Effect]

@[cfg_eval] theorem notR8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (notR8Effect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [notR8Effect_components])

@[cfg_eval] theorem_by shlR32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR32ClEffect p len dst t) t' = _ := by lift_value [shlR32ClEffect, shlR32Effect, shlFlags]

@[cfg_eval] theorem_by shrR32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR32ClEffect p len dst t) t' = _ := by lift_value [shrR32ClEffect, shrR32Effect, shrFlags]

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

@[cfg_eval] theorem_by shlR8ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shlR8ClEffect p len dst t) t' = _ := by lift_value [shlR8ClEffect, shlR8Effect, shlFlags]

@[cfg_eval] theorem_by shrR8ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrR8ClEffect p len dst t) t' = _ := by lift_value [shrR8ClEffect, shrR8Effect, shrFlags]

@[cfg_eval] theorem shrR8ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrR8ClEffect p len dst) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrR8ClEffect_components])

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

@[cfg_eval] theorem_by shldR64R64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shldR64R64ClEffect p len dst src t) t' = _ := by lift_value [shldR64R64ClEffect, shldR64R64Effect, shldFlags]

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

@[cfg_eval] theorem_by shrdR64R64ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (shrdR64R64ClEffect p len dst src t) t' = _ := by lift_value [shrdR64R64ClEffect, shrdR64R64Effect, shrdFlags]

@[cfg_eval] theorem shrdR64R64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (shrdR64R64ClEffect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [shrdR64R64ClEffect_components])

@[cfg_eval] theorem_by movR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR8R8Effect p len dst src t) t' = _ := by lift_value [movR8R8Effect]

@[cfg_eval] theorem movR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movR8R8Effect_components])

@[cfg_eval ↓] theorem_by setccM8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (cc : BitVec 4) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (atFlags (condHolds cc) (setccM8Effect p len am)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [setccM8Effect, atFlags, storeEffect]
  · simp only [atFlags, setccM8Effect, storeEffect_components]; rfl

@[cfg_eval ↓] theorem_by movM8Imm8RexEffect_exec (code : CodeMap) (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) (L : Nat) (hL : 4 + am.tail.length = L) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p L (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (movM8Imm8RexEffect p am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM8Imm8RexEffect, storeEffect, storeAddrAt, hL]
  · subst hL; simp only [movM8Imm8RexEffect_components]; rfl

end K256.Proofs.Sec1.LIR
