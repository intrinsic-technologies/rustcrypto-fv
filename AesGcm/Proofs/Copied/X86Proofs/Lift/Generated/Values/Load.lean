import AesGcm.Proofs.Copied.X86Proofs.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.R8M8.Triple
import X86Proofs.Instructions.Adc.Generated.RM.Triple
import X86Proofs.Instructions.Add.Generated.R8M8.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.And.Generated.R8M8.Triple
import X86Proofs.Instructions.And.Generated.RM.Triple
import X86Proofs.Instructions.Bsf.Generated.RM.Triple
import X86Proofs.Instructions.Bsr.Generated.RM.Triple
import X86Proofs.Instructions.Cmov.Generated.RM.Triple
import X86Proofs.Instructions.Cmp.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm32.Triple
import X86Proofs.Instructions.Cmp.Generated.MImm8.Triple
import X86Proofs.Instructions.Cmp.Generated.MR.Triple
import X86Proofs.Instructions.Cmp.Generated.R8M8.Triple
import X86Proofs.Instructions.Cmp.Generated.RM.Triple
import X86Proofs.Instructions.Imul.Generated.M.Triple
import X86Proofs.Instructions.Imul.Generated.M8.Triple
import X86Proofs.Instructions.Imul.Generated.RM.Triple
import X86Proofs.Instructions.Imul.Generated.RMImm32.Triple
import X86Proofs.Instructions.Imul.Generated.RMImm8.Triple
import X86Proofs.Instructions.Mov.Generated.R8M8.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Movsx.Generated.RM16.Triple
import X86Proofs.Instructions.Movsx.Generated.RM8.Triple
import X86Proofs.Instructions.Movsxd.Generated.RM32.Triple
import X86Proofs.Instructions.Movzx.Generated.RM16.Triple
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.Mul.Generated.M.Triple
import X86Proofs.Instructions.Mul.Generated.M8.Triple
import X86Proofs.Instructions.Or.Generated.R8M8.Triple
import X86Proofs.Instructions.Or.Generated.RM.Triple
import X86Proofs.Instructions.Sbb.Generated.R8M8.Triple
import X86Proofs.Instructions.Sbb.Generated.RM.Triple
import X86Proofs.Instructions.Sub.Generated.R8M8.Triple
import X86Proofs.Instructions.Sub.Generated.RM.Triple
import X86Proofs.Instructions.Test.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Test.Generated.MImm32.Triple
import X86Proofs.Instructions.Test.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.R8M8.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG

@[cfg_eval] theorem_by movzxR32M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movzxR32M8Effect p len dst am t) t' = _ := by lift_value [movzxR32M8Effect]

@[cfg_eval ↓] theorem movzxR32M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (movzxR32M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movzxR32M8Effect_components])

@[cfg_eval] theorem_by movzxR32M16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movzxR32M16Effect p len dst am t) t' = _ := by lift_value [movzxR32M16Effect]

@[cfg_eval ↓] theorem movzxR32M16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 2) (movzxR32M16Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 2 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movzxR32M16Effect_components])

@[cfg_eval] theorem_by andR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR32M32Effect p len dst am t) t' = _ := by lift_value [andR32M32Effect]

@[cfg_eval ↓] theorem andR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (andR32M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [andR32M32Effect_components])

@[cfg_eval] theorem_by andR64M64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR64M64Effect p dst am t) t' = _ := by lift_value [andR64M64Effect, movLoadLen]

@[cfg_eval ↓] theorem andR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (andR64M64Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [andR64M64Effect_components])

@[cfg_eval] theorem_by xorR32M32Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR32M32Effect p dst am t) t' = _ := by lift_value [xorR32M32Effect, movLoadLen]

@[cfg_eval ↓] theorem xorR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (xorR32M32Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [xorR32M32Effect_components])

@[cfg_eval] theorem_by xorR32M32LowEffect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR32M32LowEffect p dst am t) t' = _ := by lift_value [xorR32M32LowEffect]

@[cfg_eval ↓] theorem xorR32M32LowEffect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (xorR32M32LowEffect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [xorR32M32LowEffect_components])

@[cfg_eval] theorem_by xorR64M64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR64M64Effect p dst am t) t' = _ := by lift_value [xorR64M64Effect, movLoadLen]

@[cfg_eval ↓] theorem xorR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (xorR64M64Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [xorR64M64Effect_components])

@[cfg_eval] theorem_by xorR8M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR8M8Effect p len dst am t) t' = _ := by lift_value [xorR8M8Effect]

@[cfg_eval ↓] theorem xorR8M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (xorR8M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [xorR8M8Effect_components])

@[cfg_eval] theorem_by cmpMREffect64_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpMREffect p len 64 src am t) t' = _ := by lift_value [cmpMREffect]

@[cfg_eval ↓] theorem cmpMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (cmpMREffect p len 64 src am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpMREffect_components])

@[cfg_eval] theorem_by cmpM8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpM8Imm8Effect p len am imm t) t' = _ := by lift_value [cmpM8Imm8Effect]

@[cfg_eval ↓] theorem cmpM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (cmpM8Imm8Effect p len am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpM8Imm8Effect_components])

@[cfg_eval] theorem_by cmpMImm8Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpMImm8Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval ↓] theorem cmpMImm8Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (cmpMImm8Effect p len 32 am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpMImm8Effect_components])

@[cfg_eval] theorem_by movR32M32Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR32M32Effect p dst am t) t' = _ := by lift_value [movR32M32Effect, movLoadLen]

@[cfg_eval ↓] theorem movR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (movR32M32Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movR32M32Effect_components])

@[cfg_eval] theorem_by movR64M64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR64M64Effect p dst am t) t' = _ := by lift_value [movR64M64Effect, movLoadLen]

@[cfg_eval ↓] theorem movR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (movR64M64Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movR64M64Effect_components])

@[cfg_eval] theorem_by movR32M32LowEffect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR32M32LowEffect p dst am t) t' = _ := by lift_value [movR32M32LowEffect]

@[cfg_eval ↓] theorem movR32M32LowEffect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (movR32M32LowEffect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movR32M32LowEffect_components])

end X86Proofs.Lift
