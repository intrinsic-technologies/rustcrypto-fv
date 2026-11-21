import K256.Proofs.Common.Lift.Eval
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
namespace K256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG

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

end K256.Proofs.Lift
