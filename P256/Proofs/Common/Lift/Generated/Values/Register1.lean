import P256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.R8.Triple
import X86Proofs.Instructions.Adc.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Add.Generated.R8.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.R8.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Call.Triple
import X86Proofs.Instructions.Cmp.Generated.R8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Jmp.Generated.M.Triple
import X86Proofs.Instructions.Jmp.Generated.R.Triple
import X86Proofs.Instructions.Movs.Generated.Rep.Triple
import X86Proofs.Instructions.Or.Generated.Imm8.Triple
import X86Proofs.Instructions.Or.Generated.R8.Triple
import X86Proofs.Instructions.Or.Generated.RR.Triple
import X86Proofs.Instructions.Pop.Triple
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Sbb.Generated.Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.R8.Triple
import X86Proofs.Instructions.Sbb.Generated.RR.Triple
import X86Proofs.Instructions.Stos.Generated.Rep.Triple
import X86Proofs.Instructions.Sub.Generated.R8.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.R8.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Xor.Generated.R8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import P256.Proofs.Common.Lift.Rep

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG

@[cfg_eval] theorem_by pushR64Effect_rsp (p : BitVec 64) (len : Nat) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 4)).value (pushR64Effect p len src t) t' = _ := by lift_value [pushR64Effect, pushEffect]

@[cfg_eval] theorem_by pushR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (PushPre p len) (pushR64Effect p len src) R) args mem = _ := by lift_value [pushR64Effect, Op.eval_exec_push]

@[cfg_eval] theorem_by popR64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (popR64Effect p len dst t) t' = _ := by lift_value [popR64Effect]

@[cfg_eval] theorem_by popR64Effect_rsp (p : BitVec 64) (len : Nat) (dst : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr 4)).value (popR64Effect p len dst t) t' = _ := by lift_value [popR64Effect]

@[cfg_eval] theorem_by popR64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (PopPre p) (popR64Effect p len dst) R) args mem = _ := by lift_value [Op.eval_exec_load (e := popR64Effect p len dst) (by lift_no_mem [popR64Effect_components])]

@[cfg_eval] theorem_by callEffect_rsp (target : BitVec 64) (ret : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 4)).value (callEffect (fun _ => target) ret t) t' = _ := by lift_value [callEffect, pushEffect]

@[cfg_eval] theorem_by callEffect_exec (code : CodeMap) (p : BitVec 64) (target : BitVec 64) (ret : BitVec 64) (len : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (PushPre p len) (callEffect (fun _ => target) ret) R) args mem = _ := by lift_value [Op.eval_exec_push]

@[cfg_eval] theorem_by retEffect_rsp  (t t' : RamState) :
    (EffectPart.reg (.gpr 4)).value (retEffect t) t' = _ := by lift_value [retEffect]

@[cfg_eval] theorem_by retEffect_target  (t t' : RamState) :
    EffectPart.target.value (retEffect t) t' = _ := by lift_value [retEffect]

@[cfg_eval] theorem_by retEffect_exec (code : CodeMap) (p : BitVec 64) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (RetPre p) (retEffect) R) args mem = _ := by lift_value [Op.eval_exec_ret (e := retEffect) (by lift_no_mem [retEffect_components])]

@[cfg_eval] theorem_by callRegEffect_rsp (r : BitVec 5) (ret : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 4)).value (callEffect (fun s => (Operand.reg r : Operand 64).read s) ret t) t' = _ := by lift_value [callEffect, pushEffect]

@[cfg_eval ↓] theorem_by callRegEffect_rip (r : BitVec 5) (ret : BitVec 64) (t : RamState) :
    (callEffect (fun s => (Operand.reg r : Operand 64).read s) ret t).rip = _ := by lift_value [callEffect, pushEffect]

@[cfg_eval] theorem_by callRegEffect_exec (code : CodeMap) (p : BitVec 64) (r : BitVec 5) (ret : BitVec 64) (len : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (CallPre p len (fun s => (Operand.reg r : Operand 64).read s)) (callEffect (fun s => (Operand.reg r : Operand 64).read s) ret) R) args mem = _ := by lift_value [Op.eval_exec_call]

@[cfg_eval ↓] theorem_by jmpR64Effect_rip (r : BitVec 5) (t : RamState) :
    (jmpR64Effect r t).rip = _ := by lift_value [jmpR64Effect]

@[cfg_eval] theorem_by jmpR64Effect_exec (code : CodeMap) (p : BitVec 64) (r : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (JmpRegPre p r) (jmpR64Effect r) R) args mem = _ := by lift_value [Op.eval_exec_jmpReg (e := jmpR64Effect r) (by lift_no_mem [jmpR64Effect_components])]

@[cfg_eval] theorem_by callMemEffect_rsp (p : BitVec 64) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 4)).value (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am)) t) t' = _ := by lift_value [callEffect, pushEffect, callMemPtr, callMemLen]

@[cfg_eval ↓] theorem_by callMemEffect_rip (p : BitVec 64) (am : AddrMode) (t : RamState) :
    (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am)) t).rip = _ := by lift_value [callEffect, pushEffect, callMemPtr, callMemLen]

@[cfg_eval ↓] theorem_by callMemEffect_exec (code : CodeMap) (p : BitVec 64) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (CallMemPre p am) (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am))) R) args mem = _ := by lift_value [callEffect, pushEffect, callMemPtr, callMemLen, Op.eval_exec_callMem]

@[cfg_eval ↓] theorem_by jmpM64Effect_rip (p : BitVec 64) (len : Nat) (am : AddrMode) (t : RamState) :
    (jmpM64Effect p len am t).rip = _ := by lift_value [jmpM64Effect]

@[cfg_eval ↓] theorem_by jmpM64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (JmpMemPre p len am) (jmpM64Effect p len am) R) args mem = _ := by lift_value [jmpM64Effect, Op.eval_exec_jmpMem]

@[cfg_eval] theorem_by repMovsbEffect_rsi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 6)).value (repMovsbEffect p t) t' = _ := by lift_value [repMovsbEffect, Nat.one_mul]

@[cfg_eval] theorem_by repMovsbEffect_rdi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 7)).value (repMovsbEffect p t) t' = _ := by lift_value [repMovsbEffect, Nat.one_mul]

@[cfg_eval] theorem_by repMovsbEffect_rcx (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 1)).value (repMovsbEffect p t) t' = _ := by lift_value [repMovsbEffect, Nat.one_mul]

@[cfg_eval] theorem_by repMovsqEffect_rsi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 6)).value (repMovsqEffect p t) t' = _ := by lift_value [repMovsqEffect, Nat.one_mul]

@[cfg_eval] theorem_by repMovsqEffect_rdi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 7)).value (repMovsqEffect p t) t' = _ := by lift_value [repMovsqEffect, Nat.one_mul]

@[cfg_eval] theorem_by repMovsqEffect_rcx (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 1)).value (repMovsqEffect p t) t' = _ := by lift_value [repMovsqEffect, Nat.one_mul]

@[cfg_eval] theorem_by repStosbEffect_rdi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 7)).value (repStosbEffect p t) t' = _ := by lift_value [repStosbEffect, Nat.one_mul]

@[cfg_eval] theorem_by repStosbEffect_rcx (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 1)).value (repStosbEffect p t) t' = _ := by lift_value [repStosbEffect, Nat.one_mul]

@[cfg_eval] theorem_by repStosqEffect_rdi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 7)).value (repStosqEffect p t) t' = _ := by lift_value [repStosqEffect, Nat.one_mul]

@[cfg_eval] theorem_by repStosqEffect_rcx (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 1)).value (repStosqEffect p t) t' = _ := by lift_value [repStosqEffect, Nat.one_mul]

@[cfg_eval] theorem_by xorR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR16R16Effect p len dst src t) t' = _ := by lift_value [xorR16R16Effect]

@[cfg_eval] theorem_by xorR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR16R16Effect p len dst src t) t' = _ := by lift_value [xorR16R16Effect]

@[cfg_eval] theorem_by xorR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR16R16Effect p len dst src t) t' = _ := by lift_value [xorR16R16Effect]

@[cfg_eval] theorem_by xorR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR16R16Effect p len dst src t) t' = _ := by lift_value [xorR16R16Effect]

@[cfg_eval] theorem_by xorR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR16R16Effect p len dst src t) t' = _ := by lift_value [xorR16R16Effect]

@[cfg_eval] theorem_by xorR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR16R16Effect p len dst src t) t' = _ := by lift_value [xorR16R16Effect]

@[cfg_eval] theorem xorR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR16R16Effect_components])

@[cfg_eval] theorem_by xorR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR32R32Effect p len dst src t) t' = _ := by lift_value [xorR32R32Effect]

@[cfg_eval] theorem_by xorR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR32R32Effect p len dst src t) t' = _ := by lift_value [xorR32R32Effect]

@[cfg_eval] theorem_by xorR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR32R32Effect p len dst src t) t' = _ := by lift_value [xorR32R32Effect]

@[cfg_eval] theorem_by xorR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR32R32Effect p len dst src t) t' = _ := by lift_value [xorR32R32Effect]

@[cfg_eval] theorem_by xorR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR32R32Effect p len dst src t) t' = _ := by lift_value [xorR32R32Effect]

@[cfg_eval] theorem_by xorR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR32R32Effect p len dst src t) t' = _ := by lift_value [xorR32R32Effect]

@[cfg_eval] theorem xorR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR32R32Effect_components])

@[cfg_eval] theorem_by xorR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR64R64Effect p dst src t) t' = _ := by lift_value [xorR64R64Effect]

@[cfg_eval] theorem_by xorR64R64Effect_CF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorR64R64Effect p dst src t) t' = _ := by lift_value [xorR64R64Effect]

@[cfg_eval] theorem_by xorR64R64Effect_PF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorR64R64Effect p dst src t) t' = _ := by lift_value [xorR64R64Effect]

@[cfg_eval] theorem_by xorR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR64R64Effect p dst src t) t' = _ := by lift_value [xorR64R64Effect]

@[cfg_eval] theorem_by xorR64R64Effect_SF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorR64R64Effect p dst src t) t' = _ := by lift_value [xorR64R64Effect]

@[cfg_eval] theorem_by xorR64R64Effect_OF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorR64R64Effect p dst src t) t' = _ := by lift_value [xorR64R64Effect]

@[cfg_eval] theorem xorR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR64R64Effect_components])

@[cfg_eval] theorem_by andR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR16R16Effect p len dst src t) t' = _ := by lift_value [andR16R16Effect]

@[cfg_eval] theorem_by andR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR16R16Effect p len dst src t) t' = _ := by lift_value [andR16R16Effect]

@[cfg_eval] theorem_by andR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR16R16Effect p len dst src t) t' = _ := by lift_value [andR16R16Effect]

@[cfg_eval] theorem_by andR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR16R16Effect p len dst src t) t' = _ := by lift_value [andR16R16Effect]

@[cfg_eval] theorem_by andR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR16R16Effect p len dst src t) t' = _ := by lift_value [andR16R16Effect]

@[cfg_eval] theorem_by andR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR16R16Effect p len dst src t) t' = _ := by lift_value [andR16R16Effect]

@[cfg_eval] theorem andR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR16R16Effect_components])

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

@[cfg_eval] theorem_by andR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR64R64Effect p dst src t) t' = _ := by lift_value [andR64R64Effect]

@[cfg_eval] theorem_by andR64R64Effect_CF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR64R64Effect p dst src t) t' = _ := by lift_value [andR64R64Effect]

@[cfg_eval] theorem_by andR64R64Effect_PF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR64R64Effect p dst src t) t' = _ := by lift_value [andR64R64Effect]

@[cfg_eval] theorem_by andR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR64R64Effect p dst src t) t' = _ := by lift_value [andR64R64Effect]

@[cfg_eval] theorem_by andR64R64Effect_SF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR64R64Effect p dst src t) t' = _ := by lift_value [andR64R64Effect]

@[cfg_eval] theorem_by andR64R64Effect_OF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR64R64Effect p dst src t) t' = _ := by lift_value [andR64R64Effect]

@[cfg_eval] theorem andR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR64R64Effect_components])

@[cfg_eval] theorem_by addR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR16R16Effect p len dst src t) t' = _ := by lift_value [addR16R16Effect]

@[cfg_eval] theorem_by addR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR16R16Effect p len dst src t) t' = _ := by lift_value [addR16R16Effect]

@[cfg_eval] theorem_by addR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR16R16Effect p len dst src t) t' = _ := by lift_value [addR16R16Effect]

@[cfg_eval] theorem_by addR16R16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR16R16Effect p len dst src t) t' = _ := by lift_value [addR16R16Effect]

@[cfg_eval] theorem_by addR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR16R16Effect p len dst src t) t' = _ := by lift_value [addR16R16Effect]

@[cfg_eval] theorem_by addR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR16R16Effect p len dst src t) t' = _ := by lift_value [addR16R16Effect]

@[cfg_eval] theorem_by addR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR16R16Effect p len dst src t) t' = _ := by lift_value [addR16R16Effect]

@[cfg_eval] theorem addR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR16R16Effect_components])

@[cfg_eval] theorem_by addR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR32R32Effect p len dst src t) t' = _ := by lift_value [addR32R32Effect]

@[cfg_eval] theorem_by addR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR32R32Effect p len dst src t) t' = _ := by lift_value [addR32R32Effect]

@[cfg_eval] theorem_by addR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR32R32Effect p len dst src t) t' = _ := by lift_value [addR32R32Effect]

@[cfg_eval] theorem_by addR32R32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR32R32Effect p len dst src t) t' = _ := by lift_value [addR32R32Effect]

@[cfg_eval] theorem_by addR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR32R32Effect p len dst src t) t' = _ := by lift_value [addR32R32Effect]

@[cfg_eval] theorem_by addR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR32R32Effect p len dst src t) t' = _ := by lift_value [addR32R32Effect]

@[cfg_eval] theorem_by addR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR32R32Effect p len dst src t) t' = _ := by lift_value [addR32R32Effect]

@[cfg_eval] theorem addR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR32R32Effect_components])

@[cfg_eval] theorem_by addR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR64R64Effect p dst src t) t' = _ := by lift_value [addR64R64Effect]

@[cfg_eval] theorem_by addR64R64Effect_CF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR64R64Effect p dst src t) t' = _ := by lift_value [addR64R64Effect]

@[cfg_eval] theorem_by addR64R64Effect_PF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR64R64Effect p dst src t) t' = _ := by lift_value [addR64R64Effect]

@[cfg_eval] theorem_by addR64R64Effect_AF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR64R64Effect p dst src t) t' = _ := by lift_value [addR64R64Effect]

@[cfg_eval] theorem_by addR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR64R64Effect p dst src t) t' = _ := by lift_value [addR64R64Effect]

@[cfg_eval] theorem_by addR64R64Effect_SF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR64R64Effect p dst src t) t' = _ := by lift_value [addR64R64Effect]

@[cfg_eval] theorem_by addR64R64Effect_OF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR64R64Effect p dst src t) t' = _ := by lift_value [addR64R64Effect]

@[cfg_eval] theorem addR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR64R64Effect_components])

@[cfg_eval] theorem_by subR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR16R16Effect p len dst src t) t' = _ := by lift_value [subR16R16Effect]

@[cfg_eval] theorem_by subR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR16R16Effect p len dst src t) t' = _ := by lift_value [subR16R16Effect]

@[cfg_eval] theorem_by subR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR16R16Effect p len dst src t) t' = _ := by lift_value [subR16R16Effect]

@[cfg_eval] theorem_by subR16R16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR16R16Effect p len dst src t) t' = _ := by lift_value [subR16R16Effect]

@[cfg_eval] theorem_by subR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR16R16Effect p len dst src t) t' = _ := by lift_value [subR16R16Effect]

@[cfg_eval] theorem_by subR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR16R16Effect p len dst src t) t' = _ := by lift_value [subR16R16Effect]

@[cfg_eval] theorem_by subR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR16R16Effect p len dst src t) t' = _ := by lift_value [subR16R16Effect]

@[cfg_eval] theorem subR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR16R16Effect_components])

@[cfg_eval] theorem_by subR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR32R32Effect p len dst src t) t' = _ := by lift_value [subR32R32Effect]

@[cfg_eval] theorem_by subR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR32R32Effect p len dst src t) t' = _ := by lift_value [subR32R32Effect]

@[cfg_eval] theorem_by subR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR32R32Effect p len dst src t) t' = _ := by lift_value [subR32R32Effect]

@[cfg_eval] theorem_by subR32R32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR32R32Effect p len dst src t) t' = _ := by lift_value [subR32R32Effect]

@[cfg_eval] theorem_by subR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR32R32Effect p len dst src t) t' = _ := by lift_value [subR32R32Effect]

@[cfg_eval] theorem_by subR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR32R32Effect p len dst src t) t' = _ := by lift_value [subR32R32Effect]

@[cfg_eval] theorem_by subR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR32R32Effect p len dst src t) t' = _ := by lift_value [subR32R32Effect]

@[cfg_eval] theorem subR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR32R32Effect_components])

@[cfg_eval] theorem_by subR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR64R64Effect p dst src t) t' = _ := by lift_value [subR64R64Effect]

@[cfg_eval] theorem_by subR64R64Effect_CF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR64R64Effect p dst src t) t' = _ := by lift_value [subR64R64Effect]

@[cfg_eval] theorem_by subR64R64Effect_PF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR64R64Effect p dst src t) t' = _ := by lift_value [subR64R64Effect]

@[cfg_eval] theorem_by subR64R64Effect_AF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR64R64Effect p dst src t) t' = _ := by lift_value [subR64R64Effect]

@[cfg_eval] theorem_by subR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR64R64Effect p dst src t) t' = _ := by lift_value [subR64R64Effect]

@[cfg_eval] theorem_by subR64R64Effect_SF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR64R64Effect p dst src t) t' = _ := by lift_value [subR64R64Effect]

@[cfg_eval] theorem_by subR64R64Effect_OF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR64R64Effect p dst src t) t' = _ := by lift_value [subR64R64Effect]

@[cfg_eval] theorem subR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR64R64Effect_components])

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

@[cfg_eval] theorem_by cmpR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR32R32Effect p len dst src t) t' = _ := by lift_value [cmpR32R32Effect]

@[cfg_eval] theorem_by cmpR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR32R32Effect p len dst src t) t' = _ := by lift_value [cmpR32R32Effect]

@[cfg_eval] theorem_by cmpR32R32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR32R32Effect p len dst src t) t' = _ := by lift_value [cmpR32R32Effect]

@[cfg_eval] theorem_by cmpR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR32R32Effect p len dst src t) t' = _ := by lift_value [cmpR32R32Effect]

@[cfg_eval] theorem_by cmpR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR32R32Effect p len dst src t) t' = _ := by lift_value [cmpR32R32Effect]

@[cfg_eval] theorem_by cmpR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR32R32Effect p len dst src t) t' = _ := by lift_value [cmpR32R32Effect]

@[cfg_eval] theorem cmpR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR32R32Effect_components])

@[cfg_eval] theorem_by cmpR64R64Effect_CF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR64R64Effect p dst src t) t' = _ := by lift_value [cmpR64R64Effect]

@[cfg_eval] theorem_by cmpR64R64Effect_PF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR64R64Effect p dst src t) t' = _ := by lift_value [cmpR64R64Effect]

@[cfg_eval] theorem_by cmpR64R64Effect_AF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR64R64Effect p dst src t) t' = _ := by lift_value [cmpR64R64Effect]

@[cfg_eval] theorem_by cmpR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR64R64Effect p dst src t) t' = _ := by lift_value [cmpR64R64Effect]

@[cfg_eval] theorem_by cmpR64R64Effect_SF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR64R64Effect p dst src t) t' = _ := by lift_value [cmpR64R64Effect]

@[cfg_eval] theorem_by cmpR64R64Effect_OF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR64R64Effect p dst src t) t' = _ := by lift_value [cmpR64R64Effect]

@[cfg_eval] theorem cmpR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR64R64Effect_components])

@[cfg_eval] theorem_by testR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (testR16R16Effect p len dst src t) t' = _ := by lift_value [testR16R16Effect]

@[cfg_eval] theorem_by testR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (testR16R16Effect p len dst src t) t' = _ := by lift_value [testR16R16Effect]

@[cfg_eval] theorem_by testR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testR16R16Effect p len dst src t) t' = _ := by lift_value [testR16R16Effect]

@[cfg_eval] theorem_by testR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (testR16R16Effect p len dst src t) t' = _ := by lift_value [testR16R16Effect]

@[cfg_eval] theorem_by testR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (testR16R16Effect p len dst src t) t' = _ := by lift_value [testR16R16Effect]

@[cfg_eval] theorem testR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testR16R16Effect_components])

@[cfg_eval] theorem_by testR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (testR32R32Effect p len dst src t) t' = _ := by lift_value [testR32R32Effect]

@[cfg_eval] theorem_by testR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (testR32R32Effect p len dst src t) t' = _ := by lift_value [testR32R32Effect]

@[cfg_eval] theorem_by testR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testR32R32Effect p len dst src t) t' = _ := by lift_value [testR32R32Effect]

@[cfg_eval] theorem_by testR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (testR32R32Effect p len dst src t) t' = _ := by lift_value [testR32R32Effect]

@[cfg_eval] theorem_by testR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (testR32R32Effect p len dst src t) t' = _ := by lift_value [testR32R32Effect]

@[cfg_eval] theorem testR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testR32R32Effect_components])

@[cfg_eval] theorem_by testR64R64Effect_CF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (testR64R64Effect p dst src t) t' = _ := by lift_value [testR64R64Effect]

@[cfg_eval] theorem_by testR64R64Effect_PF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (testR64R64Effect p dst src t) t' = _ := by lift_value [testR64R64Effect]

@[cfg_eval] theorem_by testR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testR64R64Effect p dst src t) t' = _ := by lift_value [testR64R64Effect]

@[cfg_eval] theorem_by testR64R64Effect_SF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (testR64R64Effect p dst src t) t' = _ := by lift_value [testR64R64Effect]

@[cfg_eval] theorem_by testR64R64Effect_OF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (testR64R64Effect p dst src t) t' = _ := by lift_value [testR64R64Effect]

@[cfg_eval] theorem testR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testR64R64Effect_components])

@[cfg_eval] theorem_by adcR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR16R16Effect p len dst src) t) t' = _ := by lift_value [adcR16R16Effect, atFlags]

@[cfg_eval] theorem_by adcR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR16R16Effect p len dst src) t) t' = _ := by lift_value [adcR16R16Effect, atFlags]

@[cfg_eval] theorem_by adcR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR16R16Effect p len dst src) t) t' = _ := by lift_value [adcR16R16Effect, atFlags]

@[cfg_eval] theorem_by adcR16R16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR16R16Effect p len dst src) t) t' = _ := by lift_value [adcR16R16Effect, atFlags]

@[cfg_eval] theorem_by adcR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR16R16Effect p len dst src) t) t' = _ := by lift_value [adcR16R16Effect, atFlags]

@[cfg_eval] theorem_by adcR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR16R16Effect p len dst src) t) t' = _ := by lift_value [adcR16R16Effect, atFlags]

@[cfg_eval] theorem_by adcR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR16R16Effect p len dst src) t) t' = _ := by lift_value [adcR16R16Effect, atFlags]

@[cfg_eval] theorem adcR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR16R16Effect p len dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR16R16Effect_components])

@[cfg_eval] theorem_by adcR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR32R32Effect p len dst src) t) t' = _ := by lift_value [adcR32R32Effect, atFlags]

@[cfg_eval] theorem_by adcR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR32R32Effect p len dst src) t) t' = _ := by lift_value [adcR32R32Effect, atFlags]

@[cfg_eval] theorem_by adcR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR32R32Effect p len dst src) t) t' = _ := by lift_value [adcR32R32Effect, atFlags]

@[cfg_eval] theorem_by adcR32R32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR32R32Effect p len dst src) t) t' = _ := by lift_value [adcR32R32Effect, atFlags]

@[cfg_eval] theorem_by adcR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR32R32Effect p len dst src) t) t' = _ := by lift_value [adcR32R32Effect, atFlags]

@[cfg_eval] theorem_by adcR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR32R32Effect p len dst src) t) t' = _ := by lift_value [adcR32R32Effect, atFlags]

@[cfg_eval] theorem_by adcR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR32R32Effect p len dst src) t) t' = _ := by lift_value [adcR32R32Effect, atFlags]

@[cfg_eval] theorem adcR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR32R32Effect p len dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR32R32Effect_components])

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

@[cfg_eval] theorem_by sbbR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR16R16Effect p len dst src) t) t' = _ := by lift_value [sbbR16R16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR16R16Effect p len dst src) t) t' = _ := by lift_value [sbbR16R16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR16R16Effect p len dst src) t) t' = _ := by lift_value [sbbR16R16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16R16Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR16R16Effect p len dst src) t) t' = _ := by lift_value [sbbR16R16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR16R16Effect p len dst src) t) t' = _ := by lift_value [sbbR16R16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR16R16Effect p len dst src) t) t' = _ := by lift_value [sbbR16R16Effect, atFlags]

@[cfg_eval] theorem_by sbbR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR16R16Effect p len dst src) t) t' = _ := by lift_value [sbbR16R16Effect, atFlags]

@[cfg_eval] theorem sbbR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR16R16Effect p len dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR16R16Effect_components])

@[cfg_eval] theorem_by sbbR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src) t) t' = _ := by lift_value [sbbR32R32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32R32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src) t) t' = _ := by lift_value [sbbR32R32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32R32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src) t) t' = _ := by lift_value [sbbR32R32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32R32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src) t) t' = _ := by lift_value [sbbR32R32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32R32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src) t) t' = _ := by lift_value [sbbR32R32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32R32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src) t) t' = _ := by lift_value [sbbR32R32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32R32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src) t) t' = _ := by lift_value [sbbR32R32Effect, atFlags]

@[cfg_eval] theorem sbbR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR32R32Effect p len dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR32R32Effect_components])

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

@[cfg_eval] theorem_by orR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR16R16Effect p len dst src t) t' = _ := by lift_value [orR16R16Effect]

@[cfg_eval] theorem_by orR16R16Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR16R16Effect p len dst src t) t' = _ := by lift_value [orR16R16Effect]

@[cfg_eval] theorem_by orR16R16Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR16R16Effect p len dst src t) t' = _ := by lift_value [orR16R16Effect]

@[cfg_eval] theorem_by orR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR16R16Effect p len dst src t) t' = _ := by lift_value [orR16R16Effect]

@[cfg_eval] theorem_by orR16R16Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR16R16Effect p len dst src t) t' = _ := by lift_value [orR16R16Effect]

@[cfg_eval] theorem_by orR16R16Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR16R16Effect p len dst src t) t' = _ := by lift_value [orR16R16Effect]

@[cfg_eval] theorem orR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR16R16Effect_components])

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

@[cfg_eval] theorem_by orR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR64R64Effect p dst src t) t' = _ := by lift_value [orR64R64Effect]

@[cfg_eval] theorem_by orR64R64Effect_CF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR64R64Effect p dst src t) t' = _ := by lift_value [orR64R64Effect]

@[cfg_eval] theorem_by orR64R64Effect_PF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR64R64Effect p dst src t) t' = _ := by lift_value [orR64R64Effect]

@[cfg_eval] theorem_by orR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR64R64Effect p dst src t) t' = _ := by lift_value [orR64R64Effect]

@[cfg_eval] theorem_by orR64R64Effect_SF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR64R64Effect p dst src t) t' = _ := by lift_value [orR64R64Effect]

@[cfg_eval] theorem_by orR64R64Effect_OF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR64R64Effect p dst src t) t' = _ := by lift_value [orR64R64Effect]

@[cfg_eval] theorem orR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR64R64Effect_components])

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

@[cfg_eval] theorem_by adcR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR8R8Effect p len dst src) t) t' = _ := by lift_value [adcR8R8Effect, atFlags]

@[cfg_eval] theorem_by adcR8R8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR8R8Effect p len dst src) t) t' = _ := by lift_value [adcR8R8Effect, atFlags]

@[cfg_eval] theorem_by adcR8R8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR8R8Effect p len dst src) t) t' = _ := by lift_value [adcR8R8Effect, atFlags]

@[cfg_eval] theorem_by adcR8R8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR8R8Effect p len dst src) t) t' = _ := by lift_value [adcR8R8Effect, atFlags]

@[cfg_eval] theorem_by adcR8R8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR8R8Effect p len dst src) t) t' = _ := by lift_value [adcR8R8Effect, atFlags]

@[cfg_eval] theorem_by adcR8R8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR8R8Effect p len dst src) t) t' = _ := by lift_value [adcR8R8Effect, atFlags]

@[cfg_eval] theorem_by adcR8R8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR8R8Effect p len dst src) t) t' = _ := by lift_value [adcR8R8Effect, atFlags]

@[cfg_eval] theorem adcR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR8R8Effect p len dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR8R8Effect_components])

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

@[cfg_eval] theorem_by sbbR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR8R8Effect p len dst src) t) t' = _ := by lift_value [sbbR8R8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8R8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR8R8Effect p len dst src) t) t' = _ := by lift_value [sbbR8R8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8R8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR8R8Effect p len dst src) t) t' = _ := by lift_value [sbbR8R8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8R8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR8R8Effect p len dst src) t) t' = _ := by lift_value [sbbR8R8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8R8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR8R8Effect p len dst src) t) t' = _ := by lift_value [sbbR8R8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8R8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR8R8Effect p len dst src) t) t' = _ := by lift_value [sbbR8R8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8R8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR8R8Effect p len dst src) t) t' = _ := by lift_value [sbbR8R8Effect, atFlags]

@[cfg_eval] theorem sbbR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR8R8Effect p len dst src)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR8R8Effect_components])

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

@[cfg_eval] theorem_by testR8R8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (testR8R8Effect p len dst src t) t' = _ := by lift_value [testR8R8Effect]

@[cfg_eval] theorem_by testR8R8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .PF).value (testR8R8Effect p len dst src t) t' = _ := by lift_value [testR8R8Effect]

@[cfg_eval] theorem_by testR8R8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testR8R8Effect p len dst src t) t' = _ := by lift_value [testR8R8Effect]

@[cfg_eval] theorem_by testR8R8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .SF).value (testR8R8Effect p len dst src t) t' = _ := by lift_value [testR8R8Effect]

@[cfg_eval] theorem_by testR8R8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .OF).value (testR8R8Effect p len dst src t) t' = _ := by lift_value [testR8R8Effect]

@[cfg_eval] theorem testR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testR8R8Effect_components])

@[cfg_eval] theorem_by addR16Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR16Imm8Effect p len dst imm t) t' = _ := by lift_value [addR16Imm8Effect]

@[cfg_eval] theorem_by addR16Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR16Imm8Effect p len dst imm t) t' = _ := by lift_value [addR16Imm8Effect]

@[cfg_eval] theorem_by addR16Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR16Imm8Effect p len dst imm t) t' = _ := by lift_value [addR16Imm8Effect]

@[cfg_eval] theorem_by addR16Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR16Imm8Effect p len dst imm t) t' = _ := by lift_value [addR16Imm8Effect]

@[cfg_eval] theorem_by addR16Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR16Imm8Effect p len dst imm t) t' = _ := by lift_value [addR16Imm8Effect]

@[cfg_eval] theorem_by addR16Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR16Imm8Effect p len dst imm t) t' = _ := by lift_value [addR16Imm8Effect]

@[cfg_eval] theorem_by addR16Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR16Imm8Effect p len dst imm t) t' = _ := by lift_value [addR16Imm8Effect]

@[cfg_eval] theorem addR16Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR16Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR16Imm8Effect_components])

@[cfg_eval] theorem_by addR32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR32Imm8Effect p len dst imm t) t' = _ := by lift_value [addR32Imm8Effect]

@[cfg_eval] theorem_by addR32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR32Imm8Effect p len dst imm t) t' = _ := by lift_value [addR32Imm8Effect]

@[cfg_eval] theorem_by addR32Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR32Imm8Effect p len dst imm t) t' = _ := by lift_value [addR32Imm8Effect]

@[cfg_eval] theorem_by addR32Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR32Imm8Effect p len dst imm t) t' = _ := by lift_value [addR32Imm8Effect]

@[cfg_eval] theorem_by addR32Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR32Imm8Effect p len dst imm t) t' = _ := by lift_value [addR32Imm8Effect]

@[cfg_eval] theorem_by addR32Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR32Imm8Effect p len dst imm t) t' = _ := by lift_value [addR32Imm8Effect]

@[cfg_eval] theorem_by addR32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR32Imm8Effect p len dst imm t) t' = _ := by lift_value [addR32Imm8Effect]

@[cfg_eval] theorem addR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR32Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR32Imm8Effect_components])

@[cfg_eval] theorem_by addR64Imm8Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR64Imm8Effect p dst imm t) t' = _ := by lift_value [addR64Imm8Effect]

@[cfg_eval] theorem_by addR64Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (addR64Imm8Effect p dst imm t) t' = _ := by lift_value [addR64Imm8Effect]

@[cfg_eval] theorem_by addR64Imm8Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (addR64Imm8Effect p dst imm t) t' = _ := by lift_value [addR64Imm8Effect]

@[cfg_eval] theorem_by addR64Imm8Effect_AF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (addR64Imm8Effect p dst imm t) t' = _ := by lift_value [addR64Imm8Effect]

@[cfg_eval] theorem_by addR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR64Imm8Effect p dst imm t) t' = _ := by lift_value [addR64Imm8Effect]

@[cfg_eval] theorem_by addR64Imm8Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (addR64Imm8Effect p dst imm t) t' = _ := by lift_value [addR64Imm8Effect]

@[cfg_eval] theorem_by addR64Imm8Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (addR64Imm8Effect p dst imm t) t' = _ := by lift_value [addR64Imm8Effect]

@[cfg_eval] theorem addR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR64Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR64Imm8Effect_components])

@[cfg_eval] theorem_by orR16Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR16Imm8Effect p len dst imm t) t' = _ := by lift_value [orR16Imm8Effect]

@[cfg_eval] theorem_by orR16Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR16Imm8Effect p len dst imm t) t' = _ := by lift_value [orR16Imm8Effect]

@[cfg_eval] theorem_by orR16Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR16Imm8Effect p len dst imm t) t' = _ := by lift_value [orR16Imm8Effect]

@[cfg_eval] theorem_by orR16Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR16Imm8Effect p len dst imm t) t' = _ := by lift_value [orR16Imm8Effect]

@[cfg_eval] theorem_by orR16Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR16Imm8Effect p len dst imm t) t' = _ := by lift_value [orR16Imm8Effect]

@[cfg_eval] theorem_by orR16Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR16Imm8Effect p len dst imm t) t' = _ := by lift_value [orR16Imm8Effect]

@[cfg_eval] theorem orR16Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR16Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR16Imm8Effect_components])

@[cfg_eval] theorem_by orR32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR32Imm8Effect p len dst imm t) t' = _ := by lift_value [orR32Imm8Effect]

@[cfg_eval] theorem_by orR32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR32Imm8Effect p len dst imm t) t' = _ := by lift_value [orR32Imm8Effect]

@[cfg_eval] theorem_by orR32Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR32Imm8Effect p len dst imm t) t' = _ := by lift_value [orR32Imm8Effect]

@[cfg_eval] theorem_by orR32Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR32Imm8Effect p len dst imm t) t' = _ := by lift_value [orR32Imm8Effect]

@[cfg_eval] theorem_by orR32Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR32Imm8Effect p len dst imm t) t' = _ := by lift_value [orR32Imm8Effect]

@[cfg_eval] theorem_by orR32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR32Imm8Effect p len dst imm t) t' = _ := by lift_value [orR32Imm8Effect]

@[cfg_eval] theorem orR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR32Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR32Imm8Effect_components])

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

@[cfg_eval] theorem_by adcR16Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR16Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR16Imm8Effect, atFlags]

@[cfg_eval] theorem adcR16Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR16Imm8Effect p len dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR16Imm8Effect_components])

@[cfg_eval] theorem_by adcR32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcR32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [adcR32Imm8Effect, atFlags]

@[cfg_eval] theorem adcR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (adcR32Imm8Effect p len dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, adcR32Imm8Effect_components])

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

@[cfg_eval] theorem_by sbbR16Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR16Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR16Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR16Imm8Effect, atFlags]

@[cfg_eval] theorem sbbR16Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR16Imm8Effect p len dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR16Imm8Effect_components])

@[cfg_eval] theorem_by sbbR32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR32Imm8Effect p len dst imm) t) t' = _ := by lift_value [sbbR32Imm8Effect, atFlags]

@[cfg_eval] theorem sbbR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR32Imm8Effect p len dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR32Imm8Effect_components])

@[cfg_eval] theorem_by sbbR64Imm8Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm8Effect_PF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm8Effect_AF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm8Effect_SF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbR64Imm8Effect_OF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm) t) t' = _ := by lift_value [sbbR64Imm8Effect, atFlags]

@[cfg_eval] theorem sbbR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (atFlags StatusFlags.CF (sbbR64Imm8Effect p dst imm)) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [atFlags, sbbR64Imm8Effect_components])

@[cfg_eval] theorem_by andR16Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR16Imm8Effect p len dst imm t) t' = _ := by lift_value [andR16Imm8Effect]

@[cfg_eval] theorem_by andR16Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR16Imm8Effect p len dst imm t) t' = _ := by lift_value [andR16Imm8Effect]

@[cfg_eval] theorem_by andR16Imm8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR16Imm8Effect p len dst imm t) t' = _ := by lift_value [andR16Imm8Effect]

@[cfg_eval] theorem_by andR16Imm8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR16Imm8Effect p len dst imm t) t' = _ := by lift_value [andR16Imm8Effect]

@[cfg_eval] theorem_by andR16Imm8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR16Imm8Effect p len dst imm t) t' = _ := by lift_value [andR16Imm8Effect]

@[cfg_eval] theorem_by andR16Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR16Imm8Effect p len dst imm t) t' = _ := by lift_value [andR16Imm8Effect]

@[cfg_eval] theorem andR16Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR16Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR16Imm8Effect_components])

end P256.Proofs.Lift
