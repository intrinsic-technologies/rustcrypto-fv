import P256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Dec.Generated.M.Triple
import X86Proofs.Instructions.Inc.Generated.M.Triple
import X86Proofs.Instructions.Mov.Generated.M8R8.Triple
import X86Proofs.Instructions.Mov.Generated.MImm32C7.Triple
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Neg.Generated.M.Triple
import X86Proofs.Instructions.Not.Generated.M.Triple
import X86Proofs.Instructions.Rol.Generated.M.Triple
import X86Proofs.Instructions.Rol.Generated.MCl.Triple
import X86Proofs.Instructions.Ror.Generated.M.Triple
import X86Proofs.Instructions.Ror.Generated.MCl.Triple
import X86Proofs.Instructions.Sal.Generated.M.Triple
import X86Proofs.Instructions.Sal.Generated.MCl.Triple
import X86Proofs.Instructions.Sar.Generated.M.Triple
import X86Proofs.Instructions.Sar.Generated.MCl.Triple
import X86Proofs.Instructions.Shl.Generated.M.Triple
import X86Proofs.Instructions.Shl.Generated.MCl.Triple
import X86Proofs.Instructions.Shr.Generated.M.Triple
import X86Proofs.Instructions.Shr.Generated.MCl.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG

@[cfg_eval] theorem_by xorMImm32Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorMImm32Effect p len 64 am imm t) t' = _ := by lift_value [xorMImm32Effect]

@[cfg_eval] theorem_by xorMImm32Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorMImm32Effect p len 64 am imm t) t' = _ := by lift_value [xorMImm32Effect]

@[cfg_eval] theorem_by xorMImm32Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorMImm32Effect p len 64 am imm t) t' = _ := by lift_value [xorMImm32Effect]

@[cfg_eval] theorem_by xorMImm32Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorMImm32Effect p len 64 am imm t) t' = _ := by lift_value [xorMImm32Effect]

@[cfg_eval] theorem_by xorMImm32Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorMImm32Effect p len 64 am imm t) t' = _ := by lift_value [xorMImm32Effect]

@[cfg_eval ↓] theorem_by xorMImm32Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (xorMImm32Effect p len 64 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorMImm32Effect]
  · simp only [xorMImm32Effect_components]; rfl

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

@[cfg_eval] theorem_by decMEffect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (decMEffect p len 32 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (decMEffect p len 32 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (decMEffect p len 32 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (decMEffect p len 32 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (decMEffect p len 32 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (decMEffect p len 32 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval ↓] theorem_by decMEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (decMEffect p len 32 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [decMEffect, decSpec]
  · simp only [decMEffect_components]; rfl

@[cfg_eval] theorem_by decMEffect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (decMEffect p len 64 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (decMEffect p len 64 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (decMEffect p len 64 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (decMEffect p len 64 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (decMEffect p len 64 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (decMEffect p len 64 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval ↓] theorem_by decMEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (decMEffect p len 64 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [decMEffect, decSpec]
  · simp only [decMEffect_components]; rfl

@[cfg_eval ↓] theorem_by notMEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (notMEffect p len 32 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [notMEffect]
  · simp only [notMEffect_components]; rfl

@[cfg_eval ↓] theorem_by notMEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (notMEffect p len 64 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [notMEffect]
  · simp only [notMEffect_components]; rfl

@[cfg_eval] theorem_by negMEffect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (negMEffect p len 32 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (negMEffect p len 32 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (negMEffect p len 32 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (negMEffect p len 32 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (negMEffect p len 32 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (negMEffect p len 32 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval ↓] theorem_by negMEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (negMEffect p len 32 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [negMEffect]
  · simp only [negMEffect_components]; rfl

@[cfg_eval] theorem_by negMEffect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (negMEffect p len 64 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (negMEffect p len 64 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (negMEffect p len 64 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (negMEffect p len 64 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (negMEffect p len 64 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (negMEffect p len 64 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval ↓] theorem_by negMEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (negMEffect p len 64 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [negMEffect]
  · simp only [negMEffect_components]; rfl

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

@[cfg_eval] theorem_by decMEffect8_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (decMEffect p len 8 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect8_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (decMEffect p len 8 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect8_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (decMEffect p len 8 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect8_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (decMEffect p len 8 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect8_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (decMEffect p len 8 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval] theorem_by decMEffect8_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (decMEffect p len 8 am t) t' = _ := by lift_value [decMEffect, decSpec]

@[cfg_eval ↓] theorem_by decMEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (decMEffect p len 8 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [decMEffect, decSpec]
  · simp only [decMEffect_components]; rfl

@[cfg_eval ↓] theorem_by notMEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (notMEffect p len 8 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [notMEffect]
  · simp only [notMEffect_components]; rfl

@[cfg_eval] theorem_by negMEffect8_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (negMEffect p len 8 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect8_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (negMEffect p len 8 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect8_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (negMEffect p len 8 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect8_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (negMEffect p len 8 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect8_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (negMEffect p len 8 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval] theorem_by negMEffect8_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (negMEffect p len 8 am t) t' = _ := by lift_value [negMEffect]

@[cfg_eval ↓] theorem_by negMEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (negMEffect p len 8 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [negMEffect]
  · simp only [negMEffect_components]; rfl

@[cfg_eval] theorem_by rolMEffect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rolMEffect p len 32 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rolMEffect p len 32 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rolMEffect p len 32 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rolMEffect p len 32 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rolMEffect p len 32 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rolMEffect p len 32 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval ↓] theorem_by rolMEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (rolMEffect p len 32 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rolMEffect, rolFlags]
  · simp only [rolMEffect_components]; rfl

@[cfg_eval] theorem_by rolMEffect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rolMEffect p len 64 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rolMEffect p len 64 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rolMEffect p len 64 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rolMEffect p len 64 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rolMEffect p len 64 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rolMEffect p len 64 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval ↓] theorem_by rolMEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (rolMEffect p len 64 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rolMEffect, rolFlags]
  · simp only [rolMEffect_components]; rfl

@[cfg_eval] theorem_by rorMEffect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rorMEffect p len 32 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rorMEffect p len 32 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rorMEffect p len 32 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rorMEffect p len 32 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rorMEffect p len 32 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rorMEffect p len 32 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval ↓] theorem_by rorMEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (rorMEffect p len 32 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rorMEffect, rorFlags]
  · simp only [rorMEffect_components]; rfl

@[cfg_eval] theorem_by rorMEffect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rorMEffect p len 64 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rorMEffect p len 64 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rorMEffect p len 64 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rorMEffect p len 64 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rorMEffect p len 64 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rorMEffect p len 64 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval ↓] theorem_by rorMEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (rorMEffect p len 64 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rorMEffect, rorFlags]
  · simp only [rorMEffect_components]; rfl

@[cfg_eval] theorem_by shlMEffect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shlMEffect p len 32 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shlMEffect p len 32 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shlMEffect p len 32 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shlMEffect p len 32 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shlMEffect p len 32 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shlMEffect p len 32 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval ↓] theorem_by shlMEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (shlMEffect p len 32 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shlMEffect, shlFlags]
  · simp only [shlMEffect_components]; rfl

@[cfg_eval] theorem_by shlMEffect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shlMEffect p len 64 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shlMEffect p len 64 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shlMEffect p len 64 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shlMEffect p len 64 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shlMEffect p len 64 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shlMEffect p len 64 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval ↓] theorem_by shlMEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (shlMEffect p len 64 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shlMEffect, shlFlags]
  · simp only [shlMEffect_components]; rfl

@[cfg_eval] theorem_by salMEffect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (salMEffect p len 32 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (salMEffect p len 32 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (salMEffect p len 32 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (salMEffect p len 32 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (salMEffect p len 32 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (salMEffect p len 32 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval ↓] theorem_by salMEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (salMEffect p len 32 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [salMEffect, shlFlags]
  · simp only [salMEffect_components]; rfl

@[cfg_eval] theorem_by salMEffect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (salMEffect p len 64 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (salMEffect p len 64 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (salMEffect p len 64 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (salMEffect p len 64 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (salMEffect p len 64 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (salMEffect p len 64 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval ↓] theorem_by salMEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (salMEffect p len 64 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [salMEffect, shlFlags]
  · simp only [salMEffect_components]; rfl

@[cfg_eval] theorem_by shrMEffect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrMEffect p len 32 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrMEffect p len 32 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrMEffect p len 32 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrMEffect p len 32 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrMEffect p len 32 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrMEffect p len 32 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval ↓] theorem_by shrMEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (shrMEffect p len 32 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shrMEffect, shrFlags]
  · simp only [shrMEffect_components]; rfl

@[cfg_eval] theorem_by shrMEffect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrMEffect p len 64 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrMEffect p len 64 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrMEffect p len 64 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrMEffect p len 64 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrMEffect p len 64 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrMEffect p len 64 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval ↓] theorem_by shrMEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (shrMEffect p len 64 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shrMEffect, shrFlags]
  · simp only [shrMEffect_components]; rfl

@[cfg_eval] theorem_by sarMEffect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (sarMEffect p len 32 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (sarMEffect p len 32 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (sarMEffect p len 32 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (sarMEffect p len 32 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (sarMEffect p len 32 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (sarMEffect p len 32 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval ↓] theorem_by sarMEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (sarMEffect p len 32 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sarMEffect, sarFlags]
  · simp only [sarMEffect_components]; rfl

@[cfg_eval] theorem_by sarMEffect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (sarMEffect p len 64 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (sarMEffect p len 64 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (sarMEffect p len 64 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (sarMEffect p len 64 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (sarMEffect p len 64 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (sarMEffect p len 64 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval ↓] theorem_by sarMEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (sarMEffect p len 64 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sarMEffect, sarFlags]
  · simp only [sarMEffect_components]; rfl

@[cfg_eval ↓] theorem_by rolMClEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (rolMClEffect p len 32 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rolMClEffect, rolMEffect, rolFlags]
  · simp only [rolMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by rolMClEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (rolMClEffect p len 64 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rolMClEffect, rolMEffect, rolFlags]
  · simp only [rolMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by rorMClEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (rorMClEffect p len 32 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rorMClEffect, rorMEffect, rorFlags]
  · simp only [rorMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by rorMClEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (rorMClEffect p len 64 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rorMClEffect, rorMEffect, rorFlags]
  · simp only [rorMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by shlMClEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (shlMClEffect p len 32 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shlMClEffect, shlMEffect, shlFlags]
  · simp only [shlMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by shlMClEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (shlMClEffect p len 64 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shlMClEffect, shlMEffect, shlFlags]
  · simp only [shlMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by salMClEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (salMClEffect p len 32 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [salMClEffect, salMEffect, shlFlags]
  · simp only [salMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by salMClEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (salMClEffect p len 64 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [salMClEffect, salMEffect, shlFlags]
  · simp only [salMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by shrMClEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (shrMClEffect p len 32 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shrMClEffect, shrMEffect, shrFlags]
  · simp only [shrMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by shrMClEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (shrMClEffect p len 64 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shrMClEffect, shrMEffect, shrFlags]
  · simp only [shrMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by sarMClEffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (sarMClEffect p len 32 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sarMClEffect, sarMEffect, sarFlags]
  · simp only [sarMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by sarMClEffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (sarMClEffect p len 64 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sarMClEffect, sarMEffect, sarFlags]
  · simp only [sarMClEffect_components]; rfl

@[cfg_eval] theorem_by rolMEffect8_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rolMEffect p len 8 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect8_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rolMEffect p len 8 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect8_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rolMEffect p len 8 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect8_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rolMEffect p len 8 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect8_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rolMEffect p len 8 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval] theorem_by rolMEffect8_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rolMEffect p len 8 am c t) t' = _ := by lift_value [rolMEffect, rolFlags]

@[cfg_eval ↓] theorem_by rolMEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (rolMEffect p len 8 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rolMEffect, rolFlags]
  · simp only [rolMEffect_components]; rfl

@[cfg_eval] theorem_by rorMEffect8_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (rorMEffect p len 8 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect8_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (rorMEffect p len 8 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect8_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (rorMEffect p len 8 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect8_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (rorMEffect p len 8 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect8_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (rorMEffect p len 8 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval] theorem_by rorMEffect8_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (rorMEffect p len 8 am c t) t' = _ := by lift_value [rorMEffect, rorFlags]

@[cfg_eval ↓] theorem_by rorMEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (rorMEffect p len 8 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rorMEffect, rorFlags]
  · simp only [rorMEffect_components]; rfl

@[cfg_eval] theorem_by shlMEffect8_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shlMEffect p len 8 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect8_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shlMEffect p len 8 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect8_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shlMEffect p len 8 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect8_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shlMEffect p len 8 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect8_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shlMEffect p len 8 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval] theorem_by shlMEffect8_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shlMEffect p len 8 am c t) t' = _ := by lift_value [shlMEffect, shlFlags]

@[cfg_eval ↓] theorem_by shlMEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (shlMEffect p len 8 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shlMEffect, shlFlags]
  · simp only [shlMEffect_components]; rfl

@[cfg_eval] theorem_by salMEffect8_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (salMEffect p len 8 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect8_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (salMEffect p len 8 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect8_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (salMEffect p len 8 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect8_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (salMEffect p len 8 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect8_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (salMEffect p len 8 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval] theorem_by salMEffect8_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (salMEffect p len 8 am c t) t' = _ := by lift_value [salMEffect, shlFlags]

@[cfg_eval ↓] theorem_by salMEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (salMEffect p len 8 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [salMEffect, shlFlags]
  · simp only [salMEffect_components]; rfl

@[cfg_eval] theorem_by shrMEffect8_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrMEffect p len 8 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect8_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrMEffect p len 8 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect8_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrMEffect p len 8 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect8_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrMEffect p len 8 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect8_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrMEffect p len 8 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval] theorem_by shrMEffect8_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrMEffect p len 8 am c t) t' = _ := by lift_value [shrMEffect, shrFlags]

@[cfg_eval ↓] theorem_by shrMEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (shrMEffect p len 8 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shrMEffect, shrFlags]
  · simp only [shrMEffect_components]; rfl

@[cfg_eval] theorem_by sarMEffect8_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (sarMEffect p len 8 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect8_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (sarMEffect p len 8 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect8_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (sarMEffect p len 8 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect8_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (sarMEffect p len 8 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect8_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (sarMEffect p len 8 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval] theorem_by sarMEffect8_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (sarMEffect p len 8 am c t) t' = _ := by lift_value [sarMEffect, sarFlags]

@[cfg_eval ↓] theorem_by sarMEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (sarMEffect p len 8 am c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sarMEffect, sarFlags]
  · simp only [sarMEffect_components]; rfl

@[cfg_eval ↓] theorem_by rolMClEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (rolMClEffect p len 8 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rolMClEffect, rolMEffect, rolFlags]
  · simp only [rolMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by rorMClEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (rorMClEffect p len 8 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [rorMClEffect, rorMEffect, rorFlags]
  · simp only [rorMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by shlMClEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (shlMClEffect p len 8 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shlMClEffect, shlMEffect, shlFlags]
  · simp only [shlMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by salMClEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (salMClEffect p len 8 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [salMClEffect, salMEffect, shlFlags]
  · simp only [salMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by shrMClEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (shrMClEffect p len 8 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shrMClEffect, shrMEffect, shrFlags]
  · simp only [shrMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by sarMClEffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (sarMClEffect p len 8 am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sarMClEffect, sarMEffect, sarFlags]
  · simp only [sarMClEffect_components]; rfl

@[cfg_eval ↓] theorem_by movM16Imm16Effect_exec (code : CodeMap) (p : BitVec 64) (am : AddrMode) (imm : BitVec 16) (L : Nat) (hL : 5 + am.tail.length = L) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p L (fun s => am.addr s (p + BitVec.ofNat 64 L)) 2) (movM16Imm16Effect p am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM16Imm16Effect, storeEffect, storeAddrAt, hL]
  · subst hL; simp only [movM16Imm16Effect_components]; rfl

@[cfg_eval ↓] theorem_by movM32R32Effect_exec (code : CodeMap) (p : BitVec 64) (src : BitVec 5) (am : AddrMode) (L : Nat) (hL : 3 + am.tail.length = L) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p L (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (movM32R32Effect p src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM32R32Effect, storeEffect, storeAddrAt, hL]
  · subst hL; simp only [movM32R32Effect_components]; rfl

@[cfg_eval ↓] theorem_by movM64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (am : AddrMode) (imm : BitVec 32) (L : Nat) (hL : 7 + am.tail.length = L) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p L (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (movM64Imm32Effect p am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM64Imm32Effect, storeEffect, storeAddrAt, hL]
  · subst hL; simp only [movM64Imm32Effect_components]; rfl

@[cfg_eval ↓] theorem_by movM64R64Effect_exec (code : CodeMap) (p : BitVec 64) (src : BitVec 5) (am : AddrMode) (L : Nat) (hL : 3 + am.tail.length = L) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p L (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (movM64R64Effect p src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM64R64Effect, storeEffect, storeAddrAt, hL]
  · subst hL; simp only [movM64R64Effect_components]; rfl

@[cfg_eval ↓] theorem_by movM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) (L : Nat) (hL : 3 + am.tail.length = L) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p L (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (movM8Imm8Effect p am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM8Imm8Effect, storeEffect, storeAddrAt, hL]
  · subst hL; simp only [movM8Imm8Effect_components]; rfl

@[cfg_eval ↓] theorem_by movM8Imm8RexEffect_exec (code : CodeMap) (p : BitVec 64) (am : AddrMode) (imm : BitVec 8) (L : Nat) (hL : 4 + am.tail.length = L) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p L (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (movM8Imm8RexEffect p am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM8Imm8RexEffect, storeEffect, storeAddrAt, hL]
  · subst hL; simp only [movM8Imm8RexEffect_components]; rfl

@[cfg_eval ↓] theorem_by movM16R16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 2) (movM16R16Effect p len src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM16R16Effect, storeEffect]
  · simp only [movM16R16Effect, storeEffect_components]; rfl

@[cfg_eval ↓] theorem_by movM32R32LowEffect_exec (code : CodeMap) (p : BitVec 64) (src : BitVec 5) (am : AddrMode) (L : Nat) (hL : 2 + am.tail.length = L) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p L (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (movM32R32LowEffect p src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM32R32LowEffect, storeEffect, hL]
  · subst hL; simp only [movM32R32LowEffect, storeEffect_components]; rfl

@[cfg_eval ↓] theorem_by movM8R8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (movM8R8Effect p len src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM8R8Effect, storeEffect]
  · simp only [movM8R8Effect, storeEffect_components]; rfl

@[cfg_eval ↓] theorem_by movM32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (movM32Imm32Effect p len am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [movM32Imm32Effect, storeEffect]
  · simp only [movM32Imm32Effect, storeEffect_components]; rfl

end P256.Proofs.Lift
