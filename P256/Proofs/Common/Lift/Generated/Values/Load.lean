import P256.Proofs.Common.Lift.Eval
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

namespace P256.Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG

@[cfg_eval] theorem_by imulR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR32M32Effect p len dst am t) t' = _ := by lift_value [imulR32M32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32M32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR32M32Effect p len dst am t) t' = _ := by lift_value [imulR32M32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32M32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR32M32Effect p len dst am t) t' = _ := by lift_value [imulR32M32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval ↓] theorem imulR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (imulR32M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [imulR32M32Effect_components])

@[cfg_eval] theorem_by imulR64M64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR64M64Effect p len dst am t) t' = _ := by lift_value [imulR64M64Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64M64Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR64M64Effect p len dst am t) t' = _ := by lift_value [imulR64M64Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64M64Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR64M64Effect p len dst am t) t' = _ := by lift_value [imulR64M64Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval ↓] theorem imulR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (imulR64M64Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [imulR64M64Effect_components])

@[cfg_eval] theorem_by imulR32M32Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR32M32Imm8Effect p len dst am imm t) t' = _ := by lift_value [imulR32M32Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32M32Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR32M32Imm8Effect p len dst am imm t) t' = _ := by lift_value [imulR32M32Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32M32Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR32M32Imm8Effect p len dst am imm t) t' = _ := by lift_value [imulR32M32Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval ↓] theorem imulR32M32Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (imulR32M32Imm8Effect p len dst am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [imulR32M32Imm8Effect_components])

@[cfg_eval] theorem_by imulR64M64Imm8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR64M64Imm8Effect p len dst am imm t) t' = _ := by lift_value [imulR64M64Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64M64Imm8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR64M64Imm8Effect p len dst am imm t) t' = _ := by lift_value [imulR64M64Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64M64Imm8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR64M64Imm8Effect p len dst am imm t) t' = _ := by lift_value [imulR64M64Imm8Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval ↓] theorem imulR64M64Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 8) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (imulR64M64Imm8Effect p len dst am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [imulR64M64Imm8Effect_components])

@[cfg_eval] theorem_by imulR32M32Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR32M32Imm32Effect p len dst am imm t) t' = _ := by lift_value [imulR32M32Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32M32Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR32M32Imm32Effect p len dst am imm t) t' = _ := by lift_value [imulR32M32Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR32M32Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR32M32Imm32Effect p len dst am imm t) t' = _ := by lift_value [imulR32M32Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval ↓] theorem imulR32M32Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 32) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (imulR32M32Imm32Effect p len dst am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [imulR32M32Imm32Effect_components])

@[cfg_eval] theorem_by imulR64M64Imm32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (imulR64M64Imm32Effect p len dst am imm t) t' = _ := by lift_value [imulR64M64Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64M64Imm32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulR64M64Imm32Effect p len dst am imm t) t' = _ := by lift_value [imulR64M64Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval] theorem_by imulR64M64Imm32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulR64M64Imm32Effect p len dst am imm t) t' = _ := by lift_value [imulR64M64Imm32Effect, imulFlags, ofInt_toInt_mul]

@[cfg_eval ↓] theorem imulR64M64Imm32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (imm : BitVec 32) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (imulR64M64Imm32Effect p len dst am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [imulR64M64Imm32Effect_components])

@[cfg_eval] theorem_by mulM32Effect_rax (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (mulM32Effect p len am t) t' = _ := by lift_value [mulM32Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulM32Effect_rdx (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 2)).value (mulM32Effect p len am t) t' = _ := by lift_value [mulM32Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulM32Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (mulM32Effect p len am t) t' = _ := by lift_value [mulM32Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulM32Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (mulM32Effect p len am t) t' = _ := by lift_value [mulM32Effect, mulFlags, mulResult_fst]

@[cfg_eval ↓] theorem mulM32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (mulM32Effect p len am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [mulM32Effect_components])

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

@[cfg_eval] theorem_by imulM32Effect_rax (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (imulM32Effect p len am t) t' = _ := by lift_value [imulM32Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulM32Effect_rdx (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 2)).value (imulM32Effect p len am t) t' = _ := by lift_value [imulM32Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulM32Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulM32Effect p len am t) t' = _ := by lift_value [imulM32Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulM32Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulM32Effect p len am t) t' = _ := by lift_value [imulM32Effect, imulWideFlags, mulResult_fst]

@[cfg_eval ↓] theorem imulM32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (imulM32Effect p len am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [imulM32Effect_components])

@[cfg_eval] theorem_by imulM64Effect_rax (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (imulM64Effect p len am t) t' = _ := by lift_value [imulM64Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulM64Effect_rdx (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 2)).value (imulM64Effect p len am t) t' = _ := by lift_value [imulM64Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulM64Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulM64Effect p len am t) t' = _ := by lift_value [imulM64Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulM64Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulM64Effect p len am t) t' = _ := by lift_value [imulM64Effect, imulWideFlags, mulResult_fst]

@[cfg_eval ↓] theorem imulM64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (imulM64Effect p len am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [imulM64Effect_components])

@[cfg_eval] theorem_by mulM8Effect_rax (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (mulM8Effect p len am t) t' = _ := by lift_value [mulM8Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulM8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (mulM8Effect p len am t) t' = _ := by lift_value [mulM8Effect, mulFlags, mulResult_fst]

@[cfg_eval] theorem_by mulM8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (mulM8Effect p len am t) t' = _ := by lift_value [mulM8Effect, mulFlags, mulResult_fst]

@[cfg_eval ↓] theorem mulM8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (mulM8Effect p len am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [mulM8Effect_components])

@[cfg_eval] theorem_by imulM8Effect_rax (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr 0)).value (imulM8Effect p len am t) t' = _ := by lift_value [imulM8Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulM8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (imulM8Effect p len am t) t' = _ := by lift_value [imulM8Effect, imulWideFlags, mulResult_fst]

@[cfg_eval] theorem_by imulM8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (imulM8Effect p len am t) t' = _ := by lift_value [imulM8Effect, imulWideFlags, mulResult_fst]

@[cfg_eval ↓] theorem imulM8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (imulM8Effect p len am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [imulM8Effect_components])

@[cfg_eval] theorem_by bsfR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsfR32M32Effect p len dst am t) t' = _ := by lift_value [bsfR32M32Effect]

@[cfg_eval] theorem_by bsfR32M32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsfR32M32Effect p len dst am t) t' = _ := by lift_value [bsfR32M32Effect]

@[cfg_eval ↓] theorem bsfR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (bsfR32M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [bsfR32M32Effect_components])

@[cfg_eval] theorem_by bsfR64M64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsfR64M64Effect p len dst am t) t' = _ := by lift_value [bsfR64M64Effect]

@[cfg_eval] theorem_by bsfR64M64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsfR64M64Effect p len dst am t) t' = _ := by lift_value [bsfR64M64Effect]

@[cfg_eval ↓] theorem bsfR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (bsfR64M64Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [bsfR64M64Effect_components])

@[cfg_eval] theorem_by bsrR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsrR32M32Effect p len dst am t) t' = _ := by lift_value [bsrR32M32Effect]

@[cfg_eval] theorem_by bsrR32M32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsrR32M32Effect p len dst am t) t' = _ := by lift_value [bsrR32M32Effect]

@[cfg_eval ↓] theorem bsrR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (bsrR32M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [bsrR32M32Effect_components])

@[cfg_eval] theorem_by bsrR64M64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (bsrR64M64Effect p len dst am t) t' = _ := by lift_value [bsrR64M64Effect]

@[cfg_eval] theorem_by bsrR64M64Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (bsrR64M64Effect p len dst am t) t' = _ := by lift_value [bsrR64M64Effect]

@[cfg_eval ↓] theorem bsrR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (bsrR64M64Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [bsrR64M64Effect_components])

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

@[cfg_eval] theorem_by movsxR32M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxR32M8Effect p len dst am t) t' = _ := by lift_value [movsxR32M8Effect]

@[cfg_eval ↓] theorem movsxR32M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (movsxR32M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movsxR32M8Effect_components])

@[cfg_eval] theorem_by movsxR64M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxR64M8Effect p len dst am t) t' = _ := by lift_value [movsxR64M8Effect]

@[cfg_eval ↓] theorem movsxR64M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (movsxR64M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movsxR64M8Effect_components])

@[cfg_eval] theorem_by movsxR32M16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxR32M16Effect p len dst am t) t' = _ := by lift_value [movsxR32M16Effect]

@[cfg_eval ↓] theorem movsxR32M16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 2) (movsxR32M16Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 2 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movsxR32M16Effect_components])

@[cfg_eval] theorem_by movsxR64M16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxR64M16Effect p len dst am t) t' = _ := by lift_value [movsxR64M16Effect]

@[cfg_eval ↓] theorem movsxR64M16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 2) (movsxR64M16Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 2 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movsxR64M16Effect_components])

@[cfg_eval] theorem_by movsxdR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxdR32M32Effect p len dst am t) t' = _ := by lift_value [movsxdR32M32Effect]

@[cfg_eval ↓] theorem movsxdR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (movsxdR32M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movsxdR32M32Effect_components])

@[cfg_eval] theorem_by movsxdR64M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movsxdR64M32Effect p len dst am t) t' = _ := by lift_value [movsxdR64M32Effect]

@[cfg_eval ↓] theorem movsxdR64M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (movsxdR64M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movsxdR64M32Effect_components])

@[cfg_eval] theorem_by cmovR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (cc : BitVec 4) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags (condHolds cc) (cmovR32M32Effect p len dst am) t) t' = _ := by lift_value [cmovR32M32Effect, atFlags]

@[cfg_eval ↓] theorem cmovR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (cc : BitVec 4) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (atFlags (condHolds cc) (cmovR32M32Effect p len dst am)) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [atFlags, cmovR32M32Effect_components])

@[cfg_eval] theorem_by cmovR64M64Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (cc : BitVec 4) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags (condHolds cc) (cmovR64M64Effect p len dst am) t) t' = _ := by lift_value [cmovR64M64Effect, atFlags]

@[cfg_eval ↓] theorem cmovR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (cc : BitVec 4) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (atFlags (condHolds cc) (cmovR64M64Effect p len dst am)) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [atFlags, cmovR64M64Effect_components])

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

@[cfg_eval] theorem_by orR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (orR32M32Effect p len dst am t) t' = _ := by lift_value [orR32M32Effect]

@[cfg_eval] theorem_by orR32M32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (orR32M32Effect p len dst am t) t' = _ := by lift_value [orR32M32Effect]

@[cfg_eval] theorem_by orR32M32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (orR32M32Effect p len dst am t) t' = _ := by lift_value [orR32M32Effect]

@[cfg_eval] theorem_by orR32M32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (orR32M32Effect p len dst am t) t' = _ := by lift_value [orR32M32Effect]

@[cfg_eval] theorem_by orR32M32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (orR32M32Effect p len dst am t) t' = _ := by lift_value [orR32M32Effect]

@[cfg_eval] theorem_by orR32M32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (orR32M32Effect p len dst am t) t' = _ := by lift_value [orR32M32Effect]

@[cfg_eval ↓] theorem orR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (orR32M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [orR32M32Effect_components])

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

@[cfg_eval] theorem_by adcR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR32M32Effect p len dst am) t) t' = _ := by lift_value [adcR32M32Effect, atFlags]

@[cfg_eval] theorem_by adcR32M32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR32M32Effect p len dst am) t) t' = _ := by lift_value [adcR32M32Effect, atFlags]

@[cfg_eval] theorem_by adcR32M32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR32M32Effect p len dst am) t) t' = _ := by lift_value [adcR32M32Effect, atFlags]

@[cfg_eval] theorem_by adcR32M32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR32M32Effect p len dst am) t) t' = _ := by lift_value [adcR32M32Effect, atFlags]

@[cfg_eval] theorem_by adcR32M32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR32M32Effect p len dst am) t) t' = _ := by lift_value [adcR32M32Effect, atFlags]

@[cfg_eval] theorem_by adcR32M32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR32M32Effect p len dst am) t) t' = _ := by lift_value [adcR32M32Effect, atFlags]

@[cfg_eval] theorem_by adcR32M32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR32M32Effect p len dst am) t) t' = _ := by lift_value [adcR32M32Effect, atFlags]

@[cfg_eval ↓] theorem adcR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (atFlags StatusFlags.CF (adcR32M32Effect p len dst am)) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [atFlags, adcR32M32Effect_components])

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

@[cfg_eval] theorem_by adcR8M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (adcR8M8Effect p len dst am) t) t' = _ := by lift_value [adcR8M8Effect, atFlags]

@[cfg_eval] theorem_by adcR8M8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (adcR8M8Effect p len dst am) t) t' = _ := by lift_value [adcR8M8Effect, atFlags]

@[cfg_eval] theorem_by adcR8M8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (adcR8M8Effect p len dst am) t) t' = _ := by lift_value [adcR8M8Effect, atFlags]

@[cfg_eval] theorem_by adcR8M8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (adcR8M8Effect p len dst am) t) t' = _ := by lift_value [adcR8M8Effect, atFlags]

@[cfg_eval] theorem_by adcR8M8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (adcR8M8Effect p len dst am) t) t' = _ := by lift_value [adcR8M8Effect, atFlags]

@[cfg_eval] theorem_by adcR8M8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (adcR8M8Effect p len dst am) t) t' = _ := by lift_value [adcR8M8Effect, atFlags]

@[cfg_eval] theorem_by adcR8M8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (adcR8M8Effect p len dst am) t) t' = _ := by lift_value [adcR8M8Effect, atFlags]

@[cfg_eval ↓] theorem adcR8M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (atFlags StatusFlags.CF (adcR8M8Effect p len dst am)) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [atFlags, adcR8M8Effect_components])

@[cfg_eval] theorem_by sbbR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR32M32Effect p len dst am) t) t' = _ := by lift_value [sbbR32M32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32M32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR32M32Effect p len dst am) t) t' = _ := by lift_value [sbbR32M32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32M32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR32M32Effect p len dst am) t) t' = _ := by lift_value [sbbR32M32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32M32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR32M32Effect p len dst am) t) t' = _ := by lift_value [sbbR32M32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32M32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR32M32Effect p len dst am) t) t' = _ := by lift_value [sbbR32M32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32M32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR32M32Effect p len dst am) t) t' = _ := by lift_value [sbbR32M32Effect, atFlags]

@[cfg_eval] theorem_by sbbR32M32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR32M32Effect p len dst am) t) t' = _ := by lift_value [sbbR32M32Effect, atFlags]

@[cfg_eval ↓] theorem sbbR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (atFlags StatusFlags.CF (sbbR32M32Effect p len dst am)) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [atFlags, sbbR32M32Effect_components])

@[cfg_eval] theorem_by sbbR64M64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR64M64Effect p dst am) t) t' = _ := by lift_value [sbbR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by sbbR64M64Effect_CF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR64M64Effect p dst am) t) t' = _ := by lift_value [sbbR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by sbbR64M64Effect_PF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR64M64Effect p dst am) t) t' = _ := by lift_value [sbbR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by sbbR64M64Effect_AF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR64M64Effect p dst am) t) t' = _ := by lift_value [sbbR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by sbbR64M64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR64M64Effect p dst am) t) t' = _ := by lift_value [sbbR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by sbbR64M64Effect_SF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR64M64Effect p dst am) t) t' = _ := by lift_value [sbbR64M64Effect, atFlags, movLoadLen]

@[cfg_eval] theorem_by sbbR64M64Effect_OF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR64M64Effect p dst am) t) t' = _ := by lift_value [sbbR64M64Effect, atFlags, movLoadLen]

@[cfg_eval ↓] theorem sbbR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (atFlags StatusFlags.CF (sbbR64M64Effect p dst am)) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [atFlags, sbbR64M64Effect_components])

@[cfg_eval] theorem_by sbbR8M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (atFlags StatusFlags.CF (sbbR8M8Effect p len dst am) t) t' = _ := by lift_value [sbbR8M8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8M8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (atFlags StatusFlags.CF (sbbR8M8Effect p len dst am) t) t' = _ := by lift_value [sbbR8M8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8M8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (atFlags StatusFlags.CF (sbbR8M8Effect p len dst am) t) t' = _ := by lift_value [sbbR8M8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8M8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (atFlags StatusFlags.CF (sbbR8M8Effect p len dst am) t) t' = _ := by lift_value [sbbR8M8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8M8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (atFlags StatusFlags.CF (sbbR8M8Effect p len dst am) t) t' = _ := by lift_value [sbbR8M8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8M8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (atFlags StatusFlags.CF (sbbR8M8Effect p len dst am) t) t' = _ := by lift_value [sbbR8M8Effect, atFlags]

@[cfg_eval] theorem_by sbbR8M8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (atFlags StatusFlags.CF (sbbR8M8Effect p len dst am) t) t' = _ := by lift_value [sbbR8M8Effect, atFlags]

@[cfg_eval ↓] theorem sbbR8M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (atFlags StatusFlags.CF (sbbR8M8Effect p len dst am)) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [atFlags, sbbR8M8Effect_components])

@[cfg_eval] theorem_by andR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (andR32M32Effect p len dst am t) t' = _ := by lift_value [andR32M32Effect]

@[cfg_eval] theorem_by andR32M32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (andR32M32Effect p len dst am t) t' = _ := by lift_value [andR32M32Effect]

@[cfg_eval] theorem_by andR32M32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (andR32M32Effect p len dst am t) t' = _ := by lift_value [andR32M32Effect]

@[cfg_eval] theorem_by andR32M32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (andR32M32Effect p len dst am t) t' = _ := by lift_value [andR32M32Effect]

@[cfg_eval] theorem_by andR32M32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (andR32M32Effect p len dst am t) t' = _ := by lift_value [andR32M32Effect]

@[cfg_eval] theorem_by andR32M32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (andR32M32Effect p len dst am t) t' = _ := by lift_value [andR32M32Effect]

@[cfg_eval ↓] theorem andR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (andR32M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [andR32M32Effect_components])

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

@[cfg_eval] theorem_by subR32M32Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR32M32Effect p len dst am t) t' = _ := by lift_value [subR32M32Effect]

@[cfg_eval] theorem_by subR32M32Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR32M32Effect p len dst am t) t' = _ := by lift_value [subR32M32Effect]

@[cfg_eval] theorem_by subR32M32Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR32M32Effect p len dst am t) t' = _ := by lift_value [subR32M32Effect]

@[cfg_eval] theorem_by subR32M32Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR32M32Effect p len dst am t) t' = _ := by lift_value [subR32M32Effect]

@[cfg_eval] theorem_by subR32M32Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR32M32Effect p len dst am t) t' = _ := by lift_value [subR32M32Effect]

@[cfg_eval] theorem_by subR32M32Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR32M32Effect p len dst am t) t' = _ := by lift_value [subR32M32Effect]

@[cfg_eval] theorem_by subR32M32Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR32M32Effect p len dst am t) t' = _ := by lift_value [subR32M32Effect]

@[cfg_eval ↓] theorem subR32M32Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (subR32M32Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [subR32M32Effect_components])

@[cfg_eval] theorem_by subR64M64Effect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR64M64Effect p dst am t) t' = _ := by lift_value [subR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by subR64M64Effect_CF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR64M64Effect p dst am t) t' = _ := by lift_value [subR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by subR64M64Effect_PF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR64M64Effect p dst am t) t' = _ := by lift_value [subR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by subR64M64Effect_AF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR64M64Effect p dst am t) t' = _ := by lift_value [subR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by subR64M64Effect_ZF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR64M64Effect p dst am t) t' = _ := by lift_value [subR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by subR64M64Effect_SF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR64M64Effect p dst am t) t' = _ := by lift_value [subR64M64Effect, movLoadLen]

@[cfg_eval] theorem_by subR64M64Effect_OF (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR64M64Effect p dst am t) t' = _ := by lift_value [subR64M64Effect, movLoadLen]

@[cfg_eval ↓] theorem subR64M64Effect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (subR64M64Effect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [subR64M64Effect_components])

@[cfg_eval] theorem_by subR8M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (subR8M8Effect p len dst am t) t' = _ := by lift_value [subR8M8Effect]

@[cfg_eval] theorem_by subR8M8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (subR8M8Effect p len dst am t) t' = _ := by lift_value [subR8M8Effect]

@[cfg_eval] theorem_by subR8M8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (subR8M8Effect p len dst am t) t' = _ := by lift_value [subR8M8Effect]

@[cfg_eval] theorem_by subR8M8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (subR8M8Effect p len dst am t) t' = _ := by lift_value [subR8M8Effect]

@[cfg_eval] theorem_by subR8M8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (subR8M8Effect p len dst am t) t' = _ := by lift_value [subR8M8Effect]

@[cfg_eval] theorem_by subR8M8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (subR8M8Effect p len dst am t) t' = _ := by lift_value [subR8M8Effect]

@[cfg_eval] theorem_by subR8M8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (subR8M8Effect p len dst am t) t' = _ := by lift_value [subR8M8Effect]

@[cfg_eval ↓] theorem subR8M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (subR8M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [subR8M8Effect_components])

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

@[cfg_eval] theorem_by cmpR8M8Effect_CF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpR8M8Effect p len dst am t) t' = _ := by lift_value [cmpR8M8Effect]

@[cfg_eval] theorem_by cmpR8M8Effect_PF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpR8M8Effect p len dst am t) t' = _ := by lift_value [cmpR8M8Effect]

@[cfg_eval] theorem_by cmpR8M8Effect_AF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpR8M8Effect p len dst am t) t' = _ := by lift_value [cmpR8M8Effect]

@[cfg_eval] theorem_by cmpR8M8Effect_ZF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpR8M8Effect p len dst am t) t' = _ := by lift_value [cmpR8M8Effect]

@[cfg_eval] theorem_by cmpR8M8Effect_SF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpR8M8Effect p len dst am t) t' = _ := by lift_value [cmpR8M8Effect]

@[cfg_eval] theorem_by cmpR8M8Effect_OF (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpR8M8Effect p len dst am t) t' = _ := by lift_value [cmpR8M8Effect]

@[cfg_eval ↓] theorem cmpR8M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (cmpR8M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpR8M8Effect_components])

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

@[cfg_eval] theorem_by testMREffect32_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (testMREffect p len 32 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect32_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (testMREffect p len 32 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect32_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testMREffect p len 32 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect32_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (testMREffect p len 32 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect32_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (testMREffect p len 32 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval ↓] theorem testMREffect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (testMREffect p len 32 src am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [testMREffect_components])

@[cfg_eval] theorem_by testMREffect64_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (testMREffect p len 64 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect64_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (testMREffect p len 64 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect64_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testMREffect p len 64 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect64_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (testMREffect p len 64 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect64_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (testMREffect p len 64 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval ↓] theorem testMREffect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (testMREffect p len 64 src am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [testMREffect_components])

@[cfg_eval] theorem_by testMREffect8_CF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .CF).value (testMREffect p len 8 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect8_PF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .PF).value (testMREffect p len 8 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect8_ZF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testMREffect p len 8 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect8_SF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .SF).value (testMREffect p len 8 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval] theorem_by testMREffect8_OF (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.flag .OF).value (testMREffect p len 8 src am t) t' = _ := by lift_value [testMREffect]

@[cfg_eval ↓] theorem testMREffect8_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (src : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (testMREffect p len 8 src am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [testMREffect_components])

@[cfg_eval] theorem_by cmpM8Imm8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpM8Imm8Effect p len am imm t) t' = _ := by lift_value [cmpM8Imm8Effect]

@[cfg_eval] theorem_by cmpM8Imm8Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpM8Imm8Effect p len am imm t) t' = _ := by lift_value [cmpM8Imm8Effect]

@[cfg_eval] theorem_by cmpM8Imm8Effect_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpM8Imm8Effect p len am imm t) t' = _ := by lift_value [cmpM8Imm8Effect]

@[cfg_eval] theorem_by cmpM8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpM8Imm8Effect p len am imm t) t' = _ := by lift_value [cmpM8Imm8Effect]

@[cfg_eval] theorem_by cmpM8Imm8Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpM8Imm8Effect p len am imm t) t' = _ := by lift_value [cmpM8Imm8Effect]

@[cfg_eval] theorem_by cmpM8Imm8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpM8Imm8Effect p len am imm t) t' = _ := by lift_value [cmpM8Imm8Effect]

@[cfg_eval ↓] theorem cmpM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (cmpM8Imm8Effect p len am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpM8Imm8Effect_components])

@[cfg_eval] theorem_by testM8Imm8Effect_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (testM8Imm8Effect p len am imm t) t' = _ := by lift_value [testM8Imm8Effect]

@[cfg_eval] theorem_by testM8Imm8Effect_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (testM8Imm8Effect p len am imm t) t' = _ := by lift_value [testM8Imm8Effect]

@[cfg_eval] theorem_by testM8Imm8Effect_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testM8Imm8Effect p len am imm t) t' = _ := by lift_value [testM8Imm8Effect]

@[cfg_eval] theorem_by testM8Imm8Effect_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (testM8Imm8Effect p len am imm t) t' = _ := by lift_value [testM8Imm8Effect]

@[cfg_eval] theorem_by testM8Imm8Effect_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (testM8Imm8Effect p len am imm t) t' = _ := by lift_value [testM8Imm8Effect]

@[cfg_eval ↓] theorem testM8Imm8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (testM8Imm8Effect p len am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [testM8Imm8Effect_components])

@[cfg_eval] theorem_by cmpMImm8Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpMImm8Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval] theorem_by cmpMImm8Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpMImm8Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval] theorem_by cmpMImm8Effect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpMImm8Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval] theorem_by cmpMImm8Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpMImm8Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval] theorem_by cmpMImm8Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpMImm8Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval] theorem_by cmpMImm8Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpMImm8Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval ↓] theorem cmpMImm8Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (cmpMImm8Effect p len 32 am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpMImm8Effect_components])

@[cfg_eval] theorem_by cmpMImm8Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpMImm8Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval] theorem_by cmpMImm8Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpMImm8Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval] theorem_by cmpMImm8Effect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpMImm8Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval] theorem_by cmpMImm8Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpMImm8Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval] theorem_by cmpMImm8Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpMImm8Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval] theorem_by cmpMImm8Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpMImm8Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm8Effect]

@[cfg_eval ↓] theorem cmpMImm8Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 8) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (cmpMImm8Effect p len 64 am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpMImm8Effect_components])

@[cfg_eval] theorem_by cmpMImm32Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpMImm32Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval] theorem_by cmpMImm32Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpMImm32Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval] theorem_by cmpMImm32Effect32_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpMImm32Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval] theorem_by cmpMImm32Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpMImm32Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval] theorem_by cmpMImm32Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpMImm32Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval] theorem_by cmpMImm32Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpMImm32Effect p len 32 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval ↓] theorem cmpMImm32Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (cmpMImm32Effect p len 32 am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpMImm32Effect_components])

@[cfg_eval] theorem_by cmpMImm32Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (cmpMImm32Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval] theorem_by cmpMImm32Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (cmpMImm32Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval] theorem_by cmpMImm32Effect64_AF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .AF).value (cmpMImm32Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval] theorem_by cmpMImm32Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (cmpMImm32Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval] theorem_by cmpMImm32Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (cmpMImm32Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval] theorem_by cmpMImm32Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (cmpMImm32Effect p len 64 am imm t) t' = _ := by lift_value [cmpMImm32Effect]

@[cfg_eval ↓] theorem cmpMImm32Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (cmpMImm32Effect p len 64 am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [cmpMImm32Effect_components])

@[cfg_eval] theorem_by testMImm32Effect32_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (testMImm32Effect p len 32 am imm t) t' = _ := by lift_value [testMImm32Effect]

@[cfg_eval] theorem_by testMImm32Effect32_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (testMImm32Effect p len 32 am imm t) t' = _ := by lift_value [testMImm32Effect]

@[cfg_eval] theorem_by testMImm32Effect32_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testMImm32Effect p len 32 am imm t) t' = _ := by lift_value [testMImm32Effect]

@[cfg_eval] theorem_by testMImm32Effect32_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (testMImm32Effect p len 32 am imm t) t' = _ := by lift_value [testMImm32Effect]

@[cfg_eval] theorem_by testMImm32Effect32_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (testMImm32Effect p len 32 am imm t) t' = _ := by lift_value [testMImm32Effect]

@[cfg_eval ↓] theorem testMImm32Effect32_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (testMImm32Effect p len 32 am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [testMImm32Effect_components])

@[cfg_eval] theorem_by testMImm32Effect64_CF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .CF).value (testMImm32Effect p len 64 am imm t) t' = _ := by lift_value [testMImm32Effect]

@[cfg_eval] theorem_by testMImm32Effect64_PF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .PF).value (testMImm32Effect p len 64 am imm t) t' = _ := by lift_value [testMImm32Effect]

@[cfg_eval] theorem_by testMImm32Effect64_ZF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .ZF).value (testMImm32Effect p len 64 am imm t) t' = _ := by lift_value [testMImm32Effect]

@[cfg_eval] theorem_by testMImm32Effect64_SF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .SF).value (testMImm32Effect p len 64 am imm t) t' = _ := by lift_value [testMImm32Effect]

@[cfg_eval] theorem_by testMImm32Effect64_OF (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (t t' : RamState) :
    (EffectPart.flag .OF).value (testMImm32Effect p len 64 am imm t) t' = _ := by lift_value [testMImm32Effect]

@[cfg_eval ↓] theorem testMImm32Effect64_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (am : AddrMode) (imm : BitVec 32) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 8) (testMImm32Effect p len 64 am imm) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 8 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [testMImm32Effect_components])

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

@[cfg_eval] theorem_by movR16M16Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR16M16Effect p len dst am t) t' = _ := by lift_value [movR16M16Effect]

@[cfg_eval ↓] theorem movR16M16Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 2) (movR16M16Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 2 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movR16M16Effect_components])

@[cfg_eval] theorem_by movR32M32LowEffect_dst (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR32M32LowEffect p dst am t) t' = _ := by lift_value [movR32M32LowEffect]

@[cfg_eval ↓] theorem movR32M32LowEffect_exec (code : CodeMap) (p : BitVec 64) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 4) (movR32M32LowEffect p dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 4 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movR32M32LowEffect_components])

@[cfg_eval] theorem_by movR8M8Effect_dst (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (t t' : RamState) :
    (EffectPart.reg (.gpr dst)).value (movR8M8Effect p len dst am t) t' = _ := by lift_value [movR8M8Effect]

@[cfg_eval ↓] theorem movR8M8Effect_exec (code : CodeMap) (p : BitVec 64) (len : Nat) (dst : BitVec 5) (am : AddrMode) (L : Nat) (R : List Reg) (args : Values Value R.length) (mem : Ram) :
    Op.eval code (.exec p (LoadPre p (fun s => am.addr s (p + BitVec.ofNat 64 L)) 1) (movR8M8Effect p len dst am) R) args mem =
      if LoadOk mem (am.addr (Op.state p R args mem) (p + BitVec.ofNat 64 L)) 1 then
        some (⟨1, 0⟩, mem) else none :=
  Op.eval_exec_load (by lift_no_mem [movR8M8Effect_components])

end P256.Proofs.Lift
