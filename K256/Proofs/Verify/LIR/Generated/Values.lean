import K256.Proofs.Common.Lift.Eval
import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Verify.LIR.Generated.Footprints
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Generate.LIR.Generated.Values
import K256.Proofs.Ecdh.LIR.Generated.Values
import X86Proofs.Instructions.Add.Generated.AccImm32.Triple
import X86Proofs.Instructions.Add.Generated.R8.Triple
import X86Proofs.Instructions.Add.Generated.RM.Triple
import X86Proofs.Instructions.Bsr.Generated.RM.Triple
import X86Proofs.Instructions.Bsr.Generated.RR.Triple
import X86Proofs.Instructions.Bswap.Generated.R.Triple
import X86Proofs.Instructions.Cmov.Generated.RM.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Imul.Generated.RRImm8.Triple
import X86Proofs.Instructions.Inc.Generated.M.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Movsx.Generated.RR8.Triple
import X86Proofs.Instructions.Or.Generated.R8Imm8.Triple
import X86Proofs.Instructions.Push.Generated.Imm8.Triple
import X86Proofs.Instructions.Rol.Generated.Cl.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

open K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

@[cfg_eval] theorem_by bsrR64M64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsrR64M64Effect p len dst am t) t' = _ := by lift_value [bsrR64M64Effect]

@[cfg_eval] theorem_by bsrR64M64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsrR64M64Effect p len dst am t) t' = _ := by lift_value [bsrR64M64Effect]

@[cfg_eval ↓] theorem bsrR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (bsrR64M64Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [bsrR64M64Effect_components])

@[cfg_eval] theorem_by cmovR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (cc : BitVec 4) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags (condHolds cc) (cmovR32M32Effect p len dst am) t) t' = _ := by lift_value [cmovR32M32Effect, atFlags]

@[cfg_eval ↓] theorem cmovR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (cc : BitVec 4) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (atFlags (condHolds cc) (cmovR32M32Effect p len dst am)) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [atFlags, cmovR32M32Effect_components])

@[cfg_eval] theorem_by addR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR32M32Effect p len dst am t) t' = _ := by lift_value [addR32M32Effect]

@[cfg_eval] theorem_by addR32M32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR32M32Effect p len dst am t) t' = _ := by lift_value [addR32M32Effect]

@[cfg_eval] theorem_by addR32M32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR32M32Effect p len dst am t) t' = _ := by lift_value [addR32M32Effect]

@[cfg_eval] theorem_by addR32M32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR32M32Effect p len dst am t) t' = _ := by lift_value [addR32M32Effect]

@[cfg_eval] theorem_by addR32M32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR32M32Effect p len dst am t) t' = _ := by lift_value [addR32M32Effect]

@[cfg_eval] theorem_by addR32M32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR32M32Effect p len dst am t) t' = _ := by lift_value [addR32M32Effect]

@[cfg_eval] theorem_by addR32M32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR32M32Effect p len dst am t) t' = _ := by lift_value [addR32M32Effect]

@[cfg_eval ↓] theorem addR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (addR32M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [addR32M32Effect_components])

@[cfg_eval] theorem_by xorR32M32Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR32M32Effect p dst am t) t' = _ := by lift_value [xorR32M32Effect, movLoadLen]

@[cfg_eval] theorem_by xorR32M32Effect_CF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR32M32Effect p dst am t) t' = _ := by lift_value [xorR32M32Effect, movLoadLen]

@[cfg_eval] theorem_by xorR32M32Effect_PF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR32M32Effect p dst am t) t' = _ := by lift_value [xorR32M32Effect, movLoadLen]

@[cfg_eval] theorem_by xorR32M32Effect_ZF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR32M32Effect p dst am t) t' = _ := by lift_value [xorR32M32Effect, movLoadLen]

@[cfg_eval] theorem_by xorR32M32Effect_SF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR32M32Effect p dst am t) t' = _ := by lift_value [xorR32M32Effect, movLoadLen]

@[cfg_eval] theorem_by xorR32M32Effect_OF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR32M32Effect p dst am t) t' = _ := by lift_value [xorR32M32Effect, movLoadLen]

@[cfg_eval ↓] theorem xorR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (xorR32M32Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [xorR32M32Effect_components])

@[cfg_eval] theorem_by xorR32M32LowEffect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR32M32LowEffect p dst am t) t' = _ := by lift_value [xorR32M32LowEffect]

@[cfg_eval] theorem_by xorR32M32LowEffect_CF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR32M32LowEffect p dst am t) t' = _ := by lift_value [xorR32M32LowEffect]

@[cfg_eval] theorem_by xorR32M32LowEffect_PF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR32M32LowEffect p dst am t) t' = _ := by lift_value [xorR32M32LowEffect]

@[cfg_eval] theorem_by xorR32M32LowEffect_ZF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR32M32LowEffect p dst am t) t' = _ := by lift_value [xorR32M32LowEffect]

@[cfg_eval] theorem_by xorR32M32LowEffect_SF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR32M32LowEffect p dst am t) t' = _ := by lift_value [xorR32M32LowEffect]

@[cfg_eval] theorem_by xorR32M32LowEffect_OF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR32M32LowEffect p dst am t) t' = _ := by lift_value [xorR32M32LowEffect]

@[cfg_eval ↓] theorem xorR32M32LowEffect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (xorR32M32LowEffect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [xorR32M32LowEffect_components])

@[cfg_eval] theorem_by pushImm8Effect_rsp (p : BitVec 64) (len : Nat) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr 4)).value (pushImm8Effect p len imm t) t' = _ := by lift_value [pushImm8Effect, pushEffect]

@[cfg_eval] theorem_by pushImm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (PushPre p len) (pushImm8Effect p len imm) R) args mem = _ := by lift_value [pushImm8Effect, Op.eval_exec_push]

@[cfg_eval] theorem_by cmpR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR16R16Effect p len dst src t) t' = _ := by lift_value [cmpR16R16Effect]

@[cfg_eval] theorem_by cmpR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR16R16Effect p len dst src t) t' = _ := by lift_value [cmpR16R16Effect]

@[cfg_eval] theorem_by cmpR16R16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR16R16Effect p len dst src t) t' = _ := by lift_value [cmpR16R16Effect]

@[cfg_eval] theorem_by cmpR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR16R16Effect p len dst src t) t' = _ := by lift_value [cmpR16R16Effect]

@[cfg_eval] theorem_by cmpR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR16R16Effect p len dst src t) t' = _ := by lift_value [cmpR16R16Effect]

@[cfg_eval] theorem_by cmpR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR16R16Effect p len dst src t) t' = _ := by lift_value [cmpR16R16Effect]

@[cfg_eval] theorem cmpR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR16R16Effect_components])

@[cfg_eval] theorem_by addR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR8R8Effect p len dst src t) t' = _ := by lift_value [addR8R8Effect]

@[cfg_eval] theorem_by addR8R8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR8R8Effect p len dst src t) t' = _ := by lift_value [addR8R8Effect]

@[cfg_eval] theorem_by addR8R8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR8R8Effect p len dst src t) t' = _ := by lift_value [addR8R8Effect]

@[cfg_eval] theorem_by addR8R8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR8R8Effect p len dst src t) t' = _ := by lift_value [addR8R8Effect]

@[cfg_eval] theorem_by addR8R8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR8R8Effect p len dst src t) t' = _ := by lift_value [addR8R8Effect]

@[cfg_eval] theorem_by addR8R8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR8R8Effect p len dst src t) t' = _ := by lift_value [addR8R8Effect]

@[cfg_eval] theorem_by addR8R8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR8R8Effect p len dst src t) t' = _ := by lift_value [addR8R8Effect]

@[cfg_eval] theorem addR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR8R8Effect_components])

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

@[cfg_eval] theorem_by rolR32ClEffect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (rolR32ClEffect p len dst t) t' = _ := by lift_value [rolR32ClEffect, rolR32Effect, rolFlags]

@[cfg_eval] theorem_by imulR64R64Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR64R64Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR64R64Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64R64Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR64R64Imm8Effect p len dst src imm t) t' = _ := by lift_value [imulR64R64Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem imulR64R64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (imulR64R64Imm8Effect p len dst src imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [imulR64R64Imm8Effect_components])

@[cfg_eval] theorem_by bswapR32Effect_r (p : BitVec 64) (len : Nat) (r : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr r)).value (bswapR32Effect p len r t) t' = _ := by lift_value [bswapR32Effect]

@[cfg_eval] theorem bswapR32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (r : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bswapR32Effect p len r) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bswapR32Effect_components])

@[cfg_eval] theorem_by bsrR64R64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsrR64R64Effect p len dst src t) t' = _ := by lift_value [bsrR64R64Effect]

@[cfg_eval] theorem_by bsrR64R64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsrR64R64Effect p len dst src t) t' = _ := by lift_value [bsrR64R64Effect]

@[cfg_eval] theorem bsrR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (bsrR64R64Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [bsrR64R64Effect_components])

@[cfg_eval] theorem_by movsxR64R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxR64R8Effect p len dst src t) t' = _ := by lift_value [movsxR64R8Effect]

@[cfg_eval] theorem movsxR64R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (movsxR64R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [movsxR64R8Effect_components])

@[cfg_eval] theorem_by xorM8Imm8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorM8Imm8Effect p len am imm t) t' = _ := by lift_value [xorM8Imm8Effect]

@[cfg_eval] theorem_by xorM8Imm8Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorM8Imm8Effect p len am imm t) t' = _ := by lift_value [xorM8Imm8Effect]

@[cfg_eval] theorem_by xorM8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorM8Imm8Effect p len am imm t) t' = _ := by lift_value [xorM8Imm8Effect]

@[cfg_eval] theorem_by xorM8Imm8Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorM8Imm8Effect p len am imm t) t' = _ := by lift_value [xorM8Imm8Effect]

@[cfg_eval] theorem_by xorM8Imm8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorM8Imm8Effect p len am imm t) t' = _ := by lift_value [xorM8Imm8Effect]

@[cfg_eval ↓] theorem_by xorM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (xorM8Imm8Effect p len am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorM8Imm8Effect]
  · simp only [xorM8Imm8Effect_components]; rfl

@[cfg_eval] theorem_by incMEffect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (incMEffect p len 32 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (incMEffect p len 32 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (incMEffect p len 32 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (incMEffect p len 32 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (incMEffect p len 32 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (incMEffect p len 32 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval ↓] theorem_by incMEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (incMEffect p len 32 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [incMEffect, incSpec]
  · simp only [incMEffect_components]; rfl

@[cfg_eval] theorem_by incMEffect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (incMEffect p len 64 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (incMEffect p len 64 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (incMEffect p len 64 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (incMEffect p len 64 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (incMEffect p len 64 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (incMEffect p len 64 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval ↓] theorem_by incMEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (incMEffect p len 64 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [incMEffect, incSpec]
  · simp only [incMEffect_components]; rfl

@[cfg_eval] theorem_by incMEffect8_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (incMEffect p len 8 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect8_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (incMEffect p len 8 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect8_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (incMEffect p len 8 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect8_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (incMEffect p len 8 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect8_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (incMEffect p len 8 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval] theorem_by incMEffect8_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (incMEffect p len 8 am t) t' = _ := by lift_value [incMEffect, incSpec]

@[cfg_eval ↓] theorem_by incMEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (incMEffect p len 8 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [incMEffect, incSpec]
  · simp only [incMEffect_components]; rfl

end K256.Proofs.Verify.LIR
