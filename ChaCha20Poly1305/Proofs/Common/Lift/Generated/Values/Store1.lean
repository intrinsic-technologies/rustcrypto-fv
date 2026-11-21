import ChaCha20Poly1305.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple

namespace ChaCha20Poly1305.Proofs.Lift
open X86Proofs

open X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG

@[cfg_eval] theorem_by shldM32R32Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shldM32R32Effect p len am src c t) t' = _ := by lift_value [shldM32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldM32R32Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shldM32R32Effect p len am src c t) t' = _ := by lift_value [shldM32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldM32R32Effect_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shldM32R32Effect p len am src c t) t' = _ := by lift_value [shldM32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldM32R32Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shldM32R32Effect p len am src c t) t' = _ := by lift_value [shldM32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldM32R32Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shldM32R32Effect p len am src c t) t' = _ := by lift_value [shldM32R32Effect, shldFlags]

@[cfg_eval] theorem_by shldM32R32Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shldM32R32Effect p len am src c t) t' = _ := by lift_value [shldM32R32Effect, shldFlags]

@[cfg_eval ↓] theorem_by shldM32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (shldM32R32Effect p len am src c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shldM32R32Effect, shldFlags]
  · simp only [shldM32R32Effect_components]; rfl

@[cfg_eval] theorem_by shldM64R64Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shldM64R64Effect p len am src c t) t' = _ := by lift_value [shldM64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldM64R64Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shldM64R64Effect p len am src c t) t' = _ := by lift_value [shldM64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldM64R64Effect_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shldM64R64Effect p len am src c t) t' = _ := by lift_value [shldM64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldM64R64Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shldM64R64Effect p len am src c t) t' = _ := by lift_value [shldM64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldM64R64Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shldM64R64Effect p len am src c t) t' = _ := by lift_value [shldM64R64Effect, shldFlags]

@[cfg_eval] theorem_by shldM64R64Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shldM64R64Effect p len am src c t) t' = _ := by lift_value [shldM64R64Effect, shldFlags]

@[cfg_eval ↓] theorem_by shldM64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (shldM64R64Effect p len am src c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shldM64R64Effect, shldFlags]
  · simp only [shldM64R64Effect_components]; rfl

@[cfg_eval ↓] theorem_by shldM32R32ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (shldM32R32ClEffect p len am src) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shldM32R32ClEffect, shldM32R32Effect, shldFlags]
  · simp only [shldM32R32ClEffect_components]; rfl

@[cfg_eval ↓] theorem_by shldM64R64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (shldM64R64ClEffect p len am src) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shldM64R64ClEffect, shldM64R64Effect, shldFlags]
  · simp only [shldM64R64ClEffect_components]; rfl

@[cfg_eval] theorem_by shrdM32R32Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrdM32R32Effect p len am src c t) t' = _ := by lift_value [shrdM32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdM32R32Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrdM32R32Effect p len am src c t) t' = _ := by lift_value [shrdM32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdM32R32Effect_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrdM32R32Effect p len am src c t) t' = _ := by lift_value [shrdM32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdM32R32Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrdM32R32Effect p len am src c t) t' = _ := by lift_value [shrdM32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdM32R32Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrdM32R32Effect p len am src c t) t' = _ := by lift_value [shrdM32R32Effect, shrdFlags]

@[cfg_eval] theorem_by shrdM32R32Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrdM32R32Effect p len am src c t) t' = _ := by lift_value [shrdM32R32Effect, shrdFlags]

@[cfg_eval ↓] theorem_by shrdM32R32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (shrdM32R32Effect p len am src c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shrdM32R32Effect, shrdFlags]
  · simp only [shrdM32R32Effect_components]; rfl

@[cfg_eval] theorem_by shrdM64R64Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .CF).value (shrdM64R64Effect p len am src c t) t' = _ := by lift_value [shrdM64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdM64R64Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .PF).value (shrdM64R64Effect p len am src c t) t' = _ := by lift_value [shrdM64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdM64R64Effect_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .AF).value (shrdM64R64Effect p len am src c t) t' = _ := by lift_value [shrdM64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdM64R64Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .ZF).value (shrdM64R64Effect p len am src c t) t' = _ := by lift_value [shrdM64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdM64R64Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .SF).value (shrdM64R64Effect p len am src c t) t' = _ := by lift_value [shrdM64R64Effect, shrdFlags]

@[cfg_eval] theorem_by shrdM64R64Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (t t' : RamState) :
    (EffectPart.flag .OF).value (shrdM64R64Effect p len am src c t) t' = _ := by lift_value [shrdM64R64Effect, shrdFlags]

@[cfg_eval ↓] theorem_by shrdM64R64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (c : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (shrdM64R64Effect p len am src c) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shrdM64R64Effect, shrdFlags]
  · simp only [shrdM64R64Effect_components]; rfl

@[cfg_eval ↓] theorem_by shrdM32R32ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (shrdM32R32ClEffect p len am src) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shrdM32R32ClEffect, shrdM32R32Effect, shrdFlags]
  · simp only [shrdM32R32ClEffect_components]; rfl

@[cfg_eval ↓] theorem_by shrdM64R64ClEffect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (shrdM64R64ClEffect p len am src) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [shrdM64R64ClEffect, shrdM64R64Effect, shrdFlags]
  · simp only [shrdM64R64ClEffect_components]; rfl

@[cfg_eval ↓] theorem_by setccM8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (cc : BitVec 4) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (atFlags (condHolds cc) (setccM8Effect p len am)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [setccM8Effect, atFlags, storeEffect]
  · simp only [atFlags, setccM8Effect, storeEffect_components]; rfl

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

@[cfg_eval] theorem_by orMREffect32_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (orMREffect p len 32 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect32_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (orMREffect p len 32 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect32_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orMREffect p len 32 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect32_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (orMREffect p len 32 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect32_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (orMREffect p len 32 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval ↓] theorem_by orMREffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (orMREffect p len 32 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [orMREffect]
  · simp only [orMREffect_components]; rfl

@[cfg_eval] theorem_by orMREffect64_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (orMREffect p len 64 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect64_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (orMREffect p len 64 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect64_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orMREffect p len 64 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect64_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (orMREffect p len 64 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect64_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (orMREffect p len 64 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval ↓] theorem_by orMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (orMREffect p len 64 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [orMREffect]
  · simp only [orMREffect_components]; rfl

@[cfg_eval] theorem_by orMREffect8_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (orMREffect p len 8 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect8_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (orMREffect p len 8 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect8_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orMREffect p len 8 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect8_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (orMREffect p len 8 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval] theorem_by orMREffect8_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (orMREffect p len 8 src am t) t' = _ := by lift_value [orMREffect]

@[cfg_eval ↓] theorem_by orMREffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (orMREffect p len 8 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [orMREffect]
  · simp only [orMREffect_components]; rfl

@[cfg_eval] theorem_by adcMREffect32_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcMREffect p len 32 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect32_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcMREffect p len 32 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect32_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcMREffect p len 32 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect32_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcMREffect p len 32 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect32_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcMREffect p len 32 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect32_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcMREffect p len 32 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval ↓] theorem_by adcMREffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (atFlags StatusFlags.CF (adcMREffect p len 32 src am)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [adcMREffect, atFlags]
  · simp only [atFlags, adcMREffect_components]; rfl

@[cfg_eval] theorem_by adcMREffect64_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcMREffect p len 64 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect64_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcMREffect p len 64 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect64_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcMREffect p len 64 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect64_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcMREffect p len 64 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect64_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcMREffect p len 64 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect64_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcMREffect p len 64 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval ↓] theorem_by adcMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (atFlags StatusFlags.CF (adcMREffect p len 64 src am)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [adcMREffect, atFlags]
  · simp only [atFlags, adcMREffect_components]; rfl

@[cfg_eval] theorem_by adcMREffect8_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcMREffect p len 8 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect8_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcMREffect p len 8 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect8_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcMREffect p len 8 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect8_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcMREffect p len 8 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect8_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcMREffect p len 8 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval] theorem_by adcMREffect8_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcMREffect p len 8 src am) t) t' = _ := by lift_value [adcMREffect, atFlags]

@[cfg_eval ↓] theorem_by adcMREffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (atFlags StatusFlags.CF (adcMREffect p len 8 src am)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [adcMREffect, atFlags]
  · simp only [atFlags, adcMREffect_components]; rfl

@[cfg_eval] theorem_by sbbMREffect32_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbMREffect p len 32 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect32_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbMREffect p len 32 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect32_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbMREffect p len 32 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect32_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbMREffect p len 32 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect32_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbMREffect p len 32 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect32_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbMREffect p len 32 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval ↓] theorem_by sbbMREffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (atFlags StatusFlags.CF (sbbMREffect p len 32 src am)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sbbMREffect, atFlags]
  · simp only [atFlags, sbbMREffect_components]; rfl

@[cfg_eval] theorem_by sbbMREffect64_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbMREffect p len 64 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect64_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbMREffect p len 64 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect64_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbMREffect p len 64 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect64_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbMREffect p len 64 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect64_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbMREffect p len 64 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect64_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbMREffect p len 64 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval ↓] theorem_by sbbMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (atFlags StatusFlags.CF (sbbMREffect p len 64 src am)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sbbMREffect, atFlags]
  · simp only [atFlags, sbbMREffect_components]; rfl

@[cfg_eval] theorem_by sbbMREffect8_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbMREffect p len 8 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect8_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbMREffect p len 8 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect8_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbMREffect p len 8 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect8_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbMREffect p len 8 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect8_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbMREffect p len 8 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval] theorem_by sbbMREffect8_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbMREffect p len 8 src am) t) t' = _ := by lift_value [sbbMREffect, atFlags]

@[cfg_eval ↓] theorem_by sbbMREffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (atFlags StatusFlags.CF (sbbMREffect p len 8 src am)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sbbMREffect, atFlags]
  · simp only [atFlags, sbbMREffect_components]; rfl

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

@[cfg_eval] theorem_by subMREffect32_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (subMREffect p len 32 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect32_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (subMREffect p len 32 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect32_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (subMREffect p len 32 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect32_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subMREffect p len 32 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect32_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (subMREffect p len 32 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect32_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (subMREffect p len 32 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval ↓] theorem_by subMREffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (subMREffect p len 32 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [subMREffect]
  · simp only [subMREffect_components]; rfl

@[cfg_eval] theorem_by subMREffect64_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (subMREffect p len 64 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect64_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (subMREffect p len 64 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect64_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (subMREffect p len 64 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect64_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subMREffect p len 64 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect64_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (subMREffect p len 64 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect64_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (subMREffect p len 64 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval ↓] theorem_by subMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (subMREffect p len 64 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [subMREffect]
  · simp only [subMREffect_components]; rfl

@[cfg_eval] theorem_by subMREffect8_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (subMREffect p len 8 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect8_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (subMREffect p len 8 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect8_AF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (subMREffect p len 8 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect8_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subMREffect p len 8 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect8_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (subMREffect p len 8 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval] theorem_by subMREffect8_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (subMREffect p len 8 src am t) t' = _ := by lift_value [subMREffect]

@[cfg_eval ↓] theorem_by subMREffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (subMREffect p len 8 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [subMREffect]
  · simp only [subMREffect_components]; rfl

@[cfg_eval] theorem_by xorMREffect32_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorMREffect p len 32 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect32_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorMREffect p len 32 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect32_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorMREffect p len 32 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect32_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorMREffect p len 32 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect32_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorMREffect p len 32 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval ↓] theorem_by xorMREffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (xorMREffect p len 32 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorMREffect]
  · simp only [xorMREffect_components]; rfl

@[cfg_eval] theorem_by xorMREffect64_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorMREffect p len 64 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect64_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorMREffect p len 64 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect64_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorMREffect p len 64 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect64_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorMREffect p len 64 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect64_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorMREffect p len 64 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval ↓] theorem_by xorMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (xorMREffect p len 64 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorMREffect]
  · simp only [xorMREffect_components]; rfl

@[cfg_eval] theorem_by xorMREffect8_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorMREffect p len 8 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect8_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorMREffect p len 8 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect8_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorMREffect p len 8 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect8_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorMREffect p len 8 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval] theorem_by xorMREffect8_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorMREffect p len 8 src am t) t' = _ := by lift_value [xorMREffect]

@[cfg_eval ↓] theorem_by xorMREffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (xorMREffect p len 8 src am) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorMREffect]
  · simp only [xorMREffect_components]; rfl

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

@[cfg_eval] theorem_by orM8Imm8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (orM8Imm8Effect p len am imm t) t' = _ := by lift_value [orM8Imm8Effect]

@[cfg_eval] theorem_by orM8Imm8Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (orM8Imm8Effect p len am imm t) t' = _ := by lift_value [orM8Imm8Effect]

@[cfg_eval] theorem_by orM8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orM8Imm8Effect p len am imm t) t' = _ := by lift_value [orM8Imm8Effect]

@[cfg_eval] theorem_by orM8Imm8Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (orM8Imm8Effect p len am imm t) t' = _ := by lift_value [orM8Imm8Effect]

@[cfg_eval] theorem_by orM8Imm8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (orM8Imm8Effect p len am imm t) t' = _ := by lift_value [orM8Imm8Effect]

@[cfg_eval ↓] theorem_by orM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (orM8Imm8Effect p len am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [orM8Imm8Effect]
  · simp only [orM8Imm8Effect_components]; rfl

@[cfg_eval] theorem_by adcM8Imm8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcM8Imm8Effect p len am imm) t) t' = _ := by lift_value [adcM8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcM8Imm8Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcM8Imm8Effect p len am imm) t) t' = _ := by lift_value [adcM8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcM8Imm8Effect_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcM8Imm8Effect p len am imm) t) t' = _ := by lift_value [adcM8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcM8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcM8Imm8Effect p len am imm) t) t' = _ := by lift_value [adcM8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcM8Imm8Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcM8Imm8Effect p len am imm) t) t' = _ := by lift_value [adcM8Imm8Effect, atFlags]

@[cfg_eval] theorem_by adcM8Imm8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcM8Imm8Effect p len am imm) t) t' = _ := by lift_value [adcM8Imm8Effect, atFlags]

@[cfg_eval ↓] theorem_by adcM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (atFlags StatusFlags.CF (adcM8Imm8Effect p len am imm)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [adcM8Imm8Effect, atFlags]
  · simp only [atFlags, adcM8Imm8Effect_components]; rfl

@[cfg_eval] theorem_by sbbM8Imm8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbM8Imm8Effect p len am imm) t) t' = _ := by lift_value [sbbM8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbM8Imm8Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbM8Imm8Effect p len am imm) t) t' = _ := by lift_value [sbbM8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbM8Imm8Effect_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbM8Imm8Effect p len am imm) t) t' = _ := by lift_value [sbbM8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbM8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbM8Imm8Effect p len am imm) t) t' = _ := by lift_value [sbbM8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbM8Imm8Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbM8Imm8Effect p len am imm) t) t' = _ := by lift_value [sbbM8Imm8Effect, atFlags]

@[cfg_eval] theorem_by sbbM8Imm8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbM8Imm8Effect p len am imm) t) t' = _ := by lift_value [sbbM8Imm8Effect, atFlags]

@[cfg_eval ↓] theorem_by sbbM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (atFlags StatusFlags.CF (sbbM8Imm8Effect p len am imm)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sbbM8Imm8Effect, atFlags]
  · simp only [atFlags, sbbM8Imm8Effect_components]; rfl

@[cfg_eval] theorem_by andM8Imm8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (andM8Imm8Effect p len am imm t) t' = _ := by lift_value [andM8Imm8Effect]

@[cfg_eval] theorem_by andM8Imm8Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (andM8Imm8Effect p len am imm t) t' = _ := by lift_value [andM8Imm8Effect]

@[cfg_eval] theorem_by andM8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andM8Imm8Effect p len am imm t) t' = _ := by lift_value [andM8Imm8Effect]

@[cfg_eval] theorem_by andM8Imm8Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (andM8Imm8Effect p len am imm t) t' = _ := by lift_value [andM8Imm8Effect]

@[cfg_eval] theorem_by andM8Imm8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (andM8Imm8Effect p len am imm t) t' = _ := by lift_value [andM8Imm8Effect]

@[cfg_eval ↓] theorem_by andM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (andM8Imm8Effect p len am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [andM8Imm8Effect]
  · simp only [andM8Imm8Effect_components]; rfl

@[cfg_eval] theorem_by subM8Imm8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (subM8Imm8Effect p len am imm t) t' = _ := by lift_value [subM8Imm8Effect]

@[cfg_eval] theorem_by subM8Imm8Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (subM8Imm8Effect p len am imm t) t' = _ := by lift_value [subM8Imm8Effect]

@[cfg_eval] theorem_by subM8Imm8Effect_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (subM8Imm8Effect p len am imm t) t' = _ := by lift_value [subM8Imm8Effect]

@[cfg_eval] theorem_by subM8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subM8Imm8Effect p len am imm t) t' = _ := by lift_value [subM8Imm8Effect]

@[cfg_eval] theorem_by subM8Imm8Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (subM8Imm8Effect p len am imm t) t' = _ := by lift_value [subM8Imm8Effect]

@[cfg_eval] theorem_by subM8Imm8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (subM8Imm8Effect p len am imm t) t' = _ := by lift_value [subM8Imm8Effect]

@[cfg_eval ↓] theorem_by subM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 1) (subM8Imm8Effect p len am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [subM8Imm8Effect]
  · simp only [subM8Imm8Effect_components]; rfl

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

@[cfg_eval] theorem_by addMImm8Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (addMImm8Effect p len 32 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval] theorem_by addMImm8Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (addMImm8Effect p len 32 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval] theorem_by addMImm8Effect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (addMImm8Effect p len 32 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval] theorem_by addMImm8Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addMImm8Effect p len 32 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval] theorem_by addMImm8Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (addMImm8Effect p len 32 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval] theorem_by addMImm8Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (addMImm8Effect p len 32 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval ↓] theorem_by addMImm8Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (addMImm8Effect p len 32 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [addMImm8Effect]
  · simp only [addMImm8Effect_components]; rfl

@[cfg_eval] theorem_by addMImm8Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (addMImm8Effect p len 64 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval] theorem_by addMImm8Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (addMImm8Effect p len 64 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval] theorem_by addMImm8Effect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (addMImm8Effect p len 64 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval] theorem_by addMImm8Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addMImm8Effect p len 64 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval] theorem_by addMImm8Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (addMImm8Effect p len 64 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval] theorem_by addMImm8Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (addMImm8Effect p len 64 am imm t) t' = _ := by lift_value [addMImm8Effect]

@[cfg_eval ↓] theorem_by addMImm8Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (addMImm8Effect p len 64 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [addMImm8Effect]
  · simp only [addMImm8Effect_components]; rfl

@[cfg_eval] theorem_by orMImm8Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (orMImm8Effect p len 32 am imm t) t' = _ := by lift_value [orMImm8Effect]

@[cfg_eval] theorem_by orMImm8Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (orMImm8Effect p len 32 am imm t) t' = _ := by lift_value [orMImm8Effect]

@[cfg_eval] theorem_by orMImm8Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orMImm8Effect p len 32 am imm t) t' = _ := by lift_value [orMImm8Effect]

@[cfg_eval] theorem_by orMImm8Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (orMImm8Effect p len 32 am imm t) t' = _ := by lift_value [orMImm8Effect]

@[cfg_eval] theorem_by orMImm8Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (orMImm8Effect p len 32 am imm t) t' = _ := by lift_value [orMImm8Effect]

@[cfg_eval ↓] theorem_by orMImm8Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (orMImm8Effect p len 32 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [orMImm8Effect]
  · simp only [orMImm8Effect_components]; rfl

@[cfg_eval] theorem_by orMImm8Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (orMImm8Effect p len 64 am imm t) t' = _ := by lift_value [orMImm8Effect]

@[cfg_eval] theorem_by orMImm8Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (orMImm8Effect p len 64 am imm t) t' = _ := by lift_value [orMImm8Effect]

@[cfg_eval] theorem_by orMImm8Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orMImm8Effect p len 64 am imm t) t' = _ := by lift_value [orMImm8Effect]

@[cfg_eval] theorem_by orMImm8Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (orMImm8Effect p len 64 am imm t) t' = _ := by lift_value [orMImm8Effect]

@[cfg_eval] theorem_by orMImm8Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (orMImm8Effect p len 64 am imm t) t' = _ := by lift_value [orMImm8Effect]

@[cfg_eval ↓] theorem_by orMImm8Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (orMImm8Effect p len 64 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [orMImm8Effect]
  · simp only [orMImm8Effect_components]; rfl

@[cfg_eval] theorem_by adcMImm8Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval] theorem_by adcMImm8Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval] theorem_by adcMImm8Effect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval] theorem_by adcMImm8Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval] theorem_by adcMImm8Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval] theorem_by adcMImm8Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval ↓] theorem_by adcMImm8Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (atFlags StatusFlags.CF (adcMImm8Effect p len 32 am imm)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [adcMImm8Effect, atFlags]
  · simp only [atFlags, adcMImm8Effect_components]; rfl

@[cfg_eval] theorem_by adcMImm8Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval] theorem_by adcMImm8Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval] theorem_by adcMImm8Effect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval] theorem_by adcMImm8Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval] theorem_by adcMImm8Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval] theorem_by adcMImm8Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm8Effect, atFlags]

@[cfg_eval ↓] theorem_by adcMImm8Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (atFlags StatusFlags.CF (adcMImm8Effect p len 64 am imm)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [adcMImm8Effect, atFlags]
  · simp only [atFlags, adcMImm8Effect_components]; rfl

@[cfg_eval] theorem_by sbbMImm8Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm8Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm8Effect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm8Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm8Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm8Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval ↓] theorem_by sbbMImm8Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (atFlags StatusFlags.CF (sbbMImm8Effect p len 32 am imm)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sbbMImm8Effect, atFlags]
  · simp only [atFlags, sbbMImm8Effect_components]; rfl

@[cfg_eval] theorem_by sbbMImm8Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm8Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm8Effect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm8Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm8Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm8Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbMImm8Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm8Effect, atFlags]

@[cfg_eval ↓] theorem_by sbbMImm8Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (atFlags StatusFlags.CF (sbbMImm8Effect p len 64 am imm)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sbbMImm8Effect, atFlags]
  · simp only [atFlags, sbbMImm8Effect_components]; rfl

@[cfg_eval] theorem_by andMImm8Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (andMImm8Effect p len 32 am imm t) t' = _ := by lift_value [andMImm8Effect]

@[cfg_eval] theorem_by andMImm8Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (andMImm8Effect p len 32 am imm t) t' = _ := by lift_value [andMImm8Effect]

@[cfg_eval] theorem_by andMImm8Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andMImm8Effect p len 32 am imm t) t' = _ := by lift_value [andMImm8Effect]

@[cfg_eval] theorem_by andMImm8Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (andMImm8Effect p len 32 am imm t) t' = _ := by lift_value [andMImm8Effect]

@[cfg_eval] theorem_by andMImm8Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (andMImm8Effect p len 32 am imm t) t' = _ := by lift_value [andMImm8Effect]

@[cfg_eval ↓] theorem_by andMImm8Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (andMImm8Effect p len 32 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [andMImm8Effect]
  · simp only [andMImm8Effect_components]; rfl

@[cfg_eval] theorem_by andMImm8Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (andMImm8Effect p len 64 am imm t) t' = _ := by lift_value [andMImm8Effect]

@[cfg_eval] theorem_by andMImm8Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (andMImm8Effect p len 64 am imm t) t' = _ := by lift_value [andMImm8Effect]

@[cfg_eval] theorem_by andMImm8Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andMImm8Effect p len 64 am imm t) t' = _ := by lift_value [andMImm8Effect]

@[cfg_eval] theorem_by andMImm8Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (andMImm8Effect p len 64 am imm t) t' = _ := by lift_value [andMImm8Effect]

@[cfg_eval] theorem_by andMImm8Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (andMImm8Effect p len 64 am imm t) t' = _ := by lift_value [andMImm8Effect]

@[cfg_eval ↓] theorem_by andMImm8Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (andMImm8Effect p len 64 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [andMImm8Effect]
  · simp only [andMImm8Effect_components]; rfl

@[cfg_eval] theorem_by subMImm8Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (subMImm8Effect p len 32 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval] theorem_by subMImm8Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (subMImm8Effect p len 32 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval] theorem_by subMImm8Effect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (subMImm8Effect p len 32 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval] theorem_by subMImm8Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subMImm8Effect p len 32 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval] theorem_by subMImm8Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (subMImm8Effect p len 32 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval] theorem_by subMImm8Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (subMImm8Effect p len 32 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval ↓] theorem_by subMImm8Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (subMImm8Effect p len 32 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [subMImm8Effect]
  · simp only [subMImm8Effect_components]; rfl

@[cfg_eval] theorem_by subMImm8Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (subMImm8Effect p len 64 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval] theorem_by subMImm8Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (subMImm8Effect p len 64 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval] theorem_by subMImm8Effect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (subMImm8Effect p len 64 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval] theorem_by subMImm8Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subMImm8Effect p len 64 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval] theorem_by subMImm8Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (subMImm8Effect p len 64 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval] theorem_by subMImm8Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (subMImm8Effect p len 64 am imm t) t' = _ := by lift_value [subMImm8Effect]

@[cfg_eval ↓] theorem_by subMImm8Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (subMImm8Effect p len 64 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [subMImm8Effect]
  · simp only [subMImm8Effect_components]; rfl

@[cfg_eval] theorem_by xorMImm8Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorMImm8Effect p len 32 am imm t) t' = _ := by lift_value [xorMImm8Effect]

@[cfg_eval] theorem_by xorMImm8Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorMImm8Effect p len 32 am imm t) t' = _ := by lift_value [xorMImm8Effect]

@[cfg_eval] theorem_by xorMImm8Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorMImm8Effect p len 32 am imm t) t' = _ := by lift_value [xorMImm8Effect]

@[cfg_eval] theorem_by xorMImm8Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorMImm8Effect p len 32 am imm t) t' = _ := by lift_value [xorMImm8Effect]

@[cfg_eval] theorem_by xorMImm8Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorMImm8Effect p len 32 am imm t) t' = _ := by lift_value [xorMImm8Effect]

@[cfg_eval ↓] theorem_by xorMImm8Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (xorMImm8Effect p len 32 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorMImm8Effect]
  · simp only [xorMImm8Effect_components]; rfl

@[cfg_eval] theorem_by xorMImm8Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorMImm8Effect p len 64 am imm t) t' = _ := by lift_value [xorMImm8Effect]

@[cfg_eval] theorem_by xorMImm8Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorMImm8Effect p len 64 am imm t) t' = _ := by lift_value [xorMImm8Effect]

@[cfg_eval] theorem_by xorMImm8Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorMImm8Effect p len 64 am imm t) t' = _ := by lift_value [xorMImm8Effect]

@[cfg_eval] theorem_by xorMImm8Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorMImm8Effect p len 64 am imm t) t' = _ := by lift_value [xorMImm8Effect]

@[cfg_eval] theorem_by xorMImm8Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorMImm8Effect p len 64 am imm t) t' = _ := by lift_value [xorMImm8Effect]

@[cfg_eval ↓] theorem_by xorMImm8Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (xorMImm8Effect p len 64 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorMImm8Effect]
  · simp only [xorMImm8Effect_components]; rfl

@[cfg_eval] theorem_by addMImm32Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (addMImm32Effect p len 32 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval] theorem_by addMImm32Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (addMImm32Effect p len 32 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval] theorem_by addMImm32Effect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (addMImm32Effect p len 32 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval] theorem_by addMImm32Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addMImm32Effect p len 32 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval] theorem_by addMImm32Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (addMImm32Effect p len 32 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval] theorem_by addMImm32Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (addMImm32Effect p len 32 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval ↓] theorem_by addMImm32Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (addMImm32Effect p len 32 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [addMImm32Effect]
  · simp only [addMImm32Effect_components]; rfl

@[cfg_eval] theorem_by addMImm32Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (addMImm32Effect p len 64 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval] theorem_by addMImm32Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (addMImm32Effect p len 64 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval] theorem_by addMImm32Effect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (addMImm32Effect p len 64 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval] theorem_by addMImm32Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (addMImm32Effect p len 64 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval] theorem_by addMImm32Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (addMImm32Effect p len 64 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval] theorem_by addMImm32Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (addMImm32Effect p len 64 am imm t) t' = _ := by lift_value [addMImm32Effect]

@[cfg_eval ↓] theorem_by addMImm32Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (addMImm32Effect p len 64 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [addMImm32Effect]
  · simp only [addMImm32Effect_components]; rfl

@[cfg_eval] theorem_by orMImm32Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (orMImm32Effect p len 32 am imm t) t' = _ := by lift_value [orMImm32Effect]

@[cfg_eval] theorem_by orMImm32Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (orMImm32Effect p len 32 am imm t) t' = _ := by lift_value [orMImm32Effect]

@[cfg_eval] theorem_by orMImm32Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orMImm32Effect p len 32 am imm t) t' = _ := by lift_value [orMImm32Effect]

@[cfg_eval] theorem_by orMImm32Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (orMImm32Effect p len 32 am imm t) t' = _ := by lift_value [orMImm32Effect]

@[cfg_eval] theorem_by orMImm32Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (orMImm32Effect p len 32 am imm t) t' = _ := by lift_value [orMImm32Effect]

@[cfg_eval ↓] theorem_by orMImm32Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (orMImm32Effect p len 32 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [orMImm32Effect]
  · simp only [orMImm32Effect_components]; rfl

@[cfg_eval] theorem_by orMImm32Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (orMImm32Effect p len 64 am imm t) t' = _ := by lift_value [orMImm32Effect]

@[cfg_eval] theorem_by orMImm32Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (orMImm32Effect p len 64 am imm t) t' = _ := by lift_value [orMImm32Effect]

@[cfg_eval] theorem_by orMImm32Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orMImm32Effect p len 64 am imm t) t' = _ := by lift_value [orMImm32Effect]

@[cfg_eval] theorem_by orMImm32Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (orMImm32Effect p len 64 am imm t) t' = _ := by lift_value [orMImm32Effect]

@[cfg_eval] theorem_by orMImm32Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (orMImm32Effect p len 64 am imm t) t' = _ := by lift_value [orMImm32Effect]

@[cfg_eval ↓] theorem_by orMImm32Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (orMImm32Effect p len 64 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [orMImm32Effect]
  · simp only [orMImm32Effect_components]; rfl

@[cfg_eval] theorem_by adcMImm32Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval] theorem_by adcMImm32Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval] theorem_by adcMImm32Effect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval] theorem_by adcMImm32Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval] theorem_by adcMImm32Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval] theorem_by adcMImm32Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval ↓] theorem_by adcMImm32Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (atFlags StatusFlags.CF (adcMImm32Effect p len 32 am imm)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [adcMImm32Effect, atFlags]
  · simp only [atFlags, adcMImm32Effect_components]; rfl

@[cfg_eval] theorem_by adcMImm32Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval] theorem_by adcMImm32Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval] theorem_by adcMImm32Effect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval] theorem_by adcMImm32Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval] theorem_by adcMImm32Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval] theorem_by adcMImm32Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [adcMImm32Effect, atFlags]

@[cfg_eval ↓] theorem_by adcMImm32Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (atFlags StatusFlags.CF (adcMImm32Effect p len 64 am imm)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [adcMImm32Effect, atFlags]
  · simp only [atFlags, adcMImm32Effect_components]; rfl

@[cfg_eval] theorem_by sbbMImm32Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm32Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm32Effect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm32Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm32Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm32Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 32 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval ↓] theorem_by sbbMImm32Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (atFlags StatusFlags.CF (sbbMImm32Effect p len 32 am imm)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sbbMImm32Effect, atFlags]
  · simp only [atFlags, sbbMImm32Effect_components]; rfl

@[cfg_eval] theorem_by sbbMImm32Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm32Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm32Effect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm32Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm32Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval] theorem_by sbbMImm32Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbMImm32Effect p len 64 am imm) t) t' = _ := by lift_value [sbbMImm32Effect, atFlags]

@[cfg_eval ↓] theorem_by sbbMImm32Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (atFlags StatusFlags.CF (sbbMImm32Effect p len 64 am imm)) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [sbbMImm32Effect, atFlags]
  · simp only [atFlags, sbbMImm32Effect_components]; rfl

@[cfg_eval] theorem_by andMImm32Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (andMImm32Effect p len 32 am imm t) t' = _ := by lift_value [andMImm32Effect]

@[cfg_eval] theorem_by andMImm32Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (andMImm32Effect p len 32 am imm t) t' = _ := by lift_value [andMImm32Effect]

@[cfg_eval] theorem_by andMImm32Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andMImm32Effect p len 32 am imm t) t' = _ := by lift_value [andMImm32Effect]

@[cfg_eval] theorem_by andMImm32Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (andMImm32Effect p len 32 am imm t) t' = _ := by lift_value [andMImm32Effect]

@[cfg_eval] theorem_by andMImm32Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (andMImm32Effect p len 32 am imm t) t' = _ := by lift_value [andMImm32Effect]

@[cfg_eval ↓] theorem_by andMImm32Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (andMImm32Effect p len 32 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [andMImm32Effect]
  · simp only [andMImm32Effect_components]; rfl

@[cfg_eval] theorem_by andMImm32Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (andMImm32Effect p len 64 am imm t) t' = _ := by lift_value [andMImm32Effect]

@[cfg_eval] theorem_by andMImm32Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (andMImm32Effect p len 64 am imm t) t' = _ := by lift_value [andMImm32Effect]

@[cfg_eval] theorem_by andMImm32Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andMImm32Effect p len 64 am imm t) t' = _ := by lift_value [andMImm32Effect]

@[cfg_eval] theorem_by andMImm32Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (andMImm32Effect p len 64 am imm t) t' = _ := by lift_value [andMImm32Effect]

@[cfg_eval] theorem_by andMImm32Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (andMImm32Effect p len 64 am imm t) t' = _ := by lift_value [andMImm32Effect]

@[cfg_eval ↓] theorem_by andMImm32Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (andMImm32Effect p len 64 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [andMImm32Effect]
  · simp only [andMImm32Effect_components]; rfl

@[cfg_eval] theorem_by subMImm32Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (subMImm32Effect p len 32 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval] theorem_by subMImm32Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (subMImm32Effect p len 32 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval] theorem_by subMImm32Effect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (subMImm32Effect p len 32 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval] theorem_by subMImm32Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subMImm32Effect p len 32 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval] theorem_by subMImm32Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (subMImm32Effect p len 32 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval] theorem_by subMImm32Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (subMImm32Effect p len 32 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval ↓] theorem_by subMImm32Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (subMImm32Effect p len 32 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [subMImm32Effect]
  · simp only [subMImm32Effect_components]; rfl

@[cfg_eval] theorem_by subMImm32Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (subMImm32Effect p len 64 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval] theorem_by subMImm32Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (subMImm32Effect p len 64 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval] theorem_by subMImm32Effect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (subMImm32Effect p len 64 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval] theorem_by subMImm32Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subMImm32Effect p len 64 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval] theorem_by subMImm32Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (subMImm32Effect p len 64 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval] theorem_by subMImm32Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (subMImm32Effect p len 64 am imm t) t' = _ := by lift_value [subMImm32Effect]

@[cfg_eval ↓] theorem_by subMImm32Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 8) (subMImm32Effect p len 64 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [subMImm32Effect]
  · simp only [subMImm32Effect_components]; rfl

@[cfg_eval] theorem_by xorMImm32Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (xorMImm32Effect p len 32 am imm t) t' = _ := by lift_value [xorMImm32Effect]

@[cfg_eval] theorem_by xorMImm32Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (xorMImm32Effect p len 32 am imm t) t' = _ := by lift_value [xorMImm32Effect]

@[cfg_eval] theorem_by xorMImm32Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (xorMImm32Effect p len 32 am imm t) t' = _ := by lift_value [xorMImm32Effect]

@[cfg_eval] theorem_by xorMImm32Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (xorMImm32Effect p len 32 am imm t) t' = _ := by lift_value [xorMImm32Effect]

@[cfg_eval] theorem_by xorMImm32Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (xorMImm32Effect p len 32 am imm t) t' = _ := by lift_value [xorMImm32Effect]

@[cfg_eval ↓] theorem_by xorMImm32Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (StorePre p len (fun s => am.addr s (p + BitVec.ofNat 64 len)) 4) (xorMImm32Effect p len 32 am imm) R) args mem = _ := by
  rewrite [Op.eval_exec_store fun _ => ?_]
  · lift_value [xorMImm32Effect]
  · simp only [xorMImm32Effect_components]; rfl

end ChaCha20Poly1305.Proofs.Lift
