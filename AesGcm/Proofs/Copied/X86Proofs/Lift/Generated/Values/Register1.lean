import AesGcm.Proofs.Copied.X86Proofs.Lift.Eval
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
import AesGcm.Proofs.Copied.X86Proofs.Lift.Rep

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG

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

@[cfg_eval] theorem_by callMemEffect_rsp (p : BitVec 64) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 4)).value (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am)) t) t' = _ := by lift_value [callEffect, pushEffect, callMemPtr, callMemLen]

@[cfg_eval ↓] theorem_by callMemEffect_rip (p : BitVec 64) (am : AddrMode) (t : RamState) :
    (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am)) t).rip = _ := by lift_value [callEffect, pushEffect, callMemPtr, callMemLen]

@[cfg_eval ↓] theorem_by callMemEffect_exec (code : CodeMap) (p : BitVec 64) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (CallMemPre p am) (callEffect (callMemPtr p am) (p + BitVec.ofNat 64 (callMemLen am))) R) args mem = _ := by lift_value [callEffect, pushEffect, callMemPtr, callMemLen, Op.eval_exec_callMem]

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

@[cfg_eval] theorem_by repStosbEffect_rdi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 7)).value (repStosbEffect p t) t' = _ := by lift_value [repStosbEffect, Nat.one_mul]

@[cfg_eval] theorem_by repStosbEffect_rcx (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 1)).value (repStosbEffect p t) t' = _ := by lift_value [repStosbEffect, Nat.one_mul]

@[cfg_eval] theorem_by repStosqEffect_rdi (p : BitVec 64) (t t' : RamState) :
    (EffectPart.reg (.gpr 7)).value (repStosqEffect p t) t' = _ := by lift_value [repStosqEffect, Nat.one_mul]

@[cfg_eval] theorem_by xorR16R16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR16R16Effect p len dst src t) t' = _ := by lift_value [xorR16R16Effect]

@[cfg_eval] theorem_by xorR16R16Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR16R16Effect p len dst src t) t' = _ := by lift_value [xorR16R16Effect]

@[cfg_eval] theorem xorR16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR16R16Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR16R16Effect_components])

@[cfg_eval] theorem_by xorR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR32R32Effect p len dst src t) t' = _ := by lift_value [xorR32R32Effect]

@[cfg_eval] theorem xorR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR32R32Effect_components])

@[cfg_eval] theorem_by xorR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (xorR64R64Effect p dst src t) t' = _ := by lift_value [xorR64R64Effect]

@[cfg_eval] theorem_by xorR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorR64R64Effect p dst src t) t' = _ := by lift_value [xorR64R64Effect]

@[cfg_eval] theorem xorR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (xorR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [xorR64R64Effect_components])

@[cfg_eval] theorem_by andR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR32R32Effect p len dst src t) t' = _ := by lift_value [andR32R32Effect]

@[cfg_eval] theorem andR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR32R32Effect_components])

@[cfg_eval] theorem_by andR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR64R64Effect p dst src t) t' = _ := by lift_value [andR64R64Effect]

@[cfg_eval] theorem_by andR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR64R64Effect p dst src t) t' = _ := by lift_value [andR64R64Effect]

@[cfg_eval] theorem andR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (andR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [andR64R64Effect_components])

@[cfg_eval] theorem_by addR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR32R32Effect p len dst src t) t' = _ := by lift_value [addR32R32Effect]

@[cfg_eval] theorem addR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR32R32Effect_components])

@[cfg_eval] theorem_by addR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR64R64Effect p dst src t) t' = _ := by lift_value [addR64R64Effect]

@[cfg_eval] theorem addR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR64R64Effect_components])

@[cfg_eval] theorem_by subR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR64R64Effect p dst src t) t' = _ := by lift_value [subR64R64Effect]

@[cfg_eval] theorem subR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (subR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [subR64R64Effect_components])

@[cfg_eval] theorem_by cmpR64R64Effect_CF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR64R64Effect p dst src t) t' = _ := by lift_value [cmpR64R64Effect]

@[cfg_eval] theorem_by cmpR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR64R64Effect p dst src t) t' = _ := by lift_value [cmpR64R64Effect]

@[cfg_eval] theorem cmpR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (cmpR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [cmpR64R64Effect_components])

@[cfg_eval] theorem_by testR64R64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testR64R64Effect p dst src t) t' = _ := by lift_value [testR64R64Effect]

@[cfg_eval] theorem testR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (testR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [testR64R64Effect_components])

@[cfg_eval] theorem_by orR32R32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR32R32Effect p len dst src t) t' = _ := by lift_value [orR32R32Effect]

@[cfg_eval] theorem orR32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR32R32Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR32R32Effect_components])

@[cfg_eval] theorem_by orR64R64Effect_dst (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR64R64Effect p dst src t) t' = _ := by lift_value [orR64R64Effect]

@[cfg_eval] theorem orR64R64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR64R64Effect p dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR64R64Effect_components])

@[cfg_eval] theorem_by orR8R8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR8R8Effect p len dst src t) t' = _ := by lift_value [orR8R8Effect]

@[cfg_eval] theorem_by orR8R8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR8R8Effect p len dst src t) t' = _ := by lift_value [orR8R8Effect]

@[cfg_eval] theorem orR8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (orR8R8Effect p len dst src) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [orR8R8Effect_components])

@[cfg_eval] theorem_by addR32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR32Imm8Effect p len dst imm t) t' = _ := by lift_value [addR32Imm8Effect]

@[cfg_eval] theorem addR32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR32Imm8Effect p len dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR32Imm8Effect_components])

@[cfg_eval] theorem_by addR64Imm8Effect_dst (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (addR64Imm8Effect p dst imm t) t' = _ := by lift_value [addR64Imm8Effect]

@[cfg_eval] theorem_by addR64Imm8Effect_ZF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addR64Imm8Effect p dst imm t) t' = _ := by lift_value [addR64Imm8Effect]

@[cfg_eval] theorem addR64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (fun s => s.RIP = p) (addR64Imm8Effect p dst imm) R) args mem = some (⟨1, 0⟩, mem) :=
  Op.eval_exec_rip (by lift_no_mem [addR64Imm8Effect_components])

end X86Proofs.Lift
