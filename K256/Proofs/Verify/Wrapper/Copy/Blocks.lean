import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Verify.Wrapper.Copy.Key
import K256.Proofs.Common.Tactic
import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Common.Lift.Generated.Values.Load

namespace K256.Proofs.Verify.Wrapper

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Verify.LIR

variable {code : CodeMap} {args : Values Value Reg.count} {mem : Ram} {sp : BitVec 64}

local macro "copy_regs" : tactic =>
  `(tactic| (congr 2
             apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
               fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
             intro i
             finite_cases i <;> simp only [Vector.getElem_set] <;> rfl))

theorem keyTag (rsp : args[4].get 64 = sp) (read : LoadOk mem (sp + 8) 1) :
    let ok := memLoad mem (sp + 8) 8 == 0
    program.runBlock (dialect code) ⟨.l102fe9, args, mem⟩ =
      .jump ⟨if ok then .l102ff4 else .l103408, args.set 19 (.ofBool ok), mem⟩ := by
  dsimp only
  cfg_eval [rsp, read, cmpSpec_ZF]
  cases (memLoad mem (sp + 8) 8 == 0) <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> copy_regs

theorem signatureTag (rsp : args[4].get 64 = sp) (read : LoadOk mem (sp + 8) 4) :
    let reject := memLoad mem (sp + 8) 32 == 1
    program.runBlock (dialect code) ⟨.l10302c, args, mem⟩ =
      .jump ⟨if reject then .l103432 else .l103037, args.set 19 (.ofBool reject), mem⟩ := by
  dsimp only
  cfg_eval [rsp, read, cmpSpec_ZF]
  cases (memLoad mem (sp + 8) 32 == 1) <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;> copy_regs

def signatureCallArgs (args : Values Value Reg.count) (sp : BitVec 64) :=
  let a := (args.set 0 ⟨64, sp + 256⟩).set 4 ⟨64, sp - 8⟩
  (a.set 6 ⟨64, args[15].get 64⟩).set 7 ⟨64, sp + 8⟩

theorem signatureCall (rsp : args[4].get 64 = sp)
    (firstCopy : RepMovsOk code mem (args[22].get 1) (sp + 16) (sp + 256) 11 8 0x103009 3)
    (secondCopy : RepMovsOk code (memCopy mem (sp + 256) (sp + 16) 88) (args[22].get 1)
      (sp + 256) (sp + 416) 11 8 0x10301c 3)
    (push : StoreOk code (copiedKey mem sp) (sp - 8) 8 0x103027 5) :
    program.runBlock (dialect code) ⟨.l102ff4, args, mem⟩ =
      .call ⟨.l103ac0, signatureCallArgs args sp,
        memStore (copiedKey mem sp) (sp - 8) (0x10302c : BitVec 64)⟩
        ⟨.l10302c, #v[], rfl, some ⟨64, 0x10302c⟩⟩ := by
  unfold copiedKey at push ⊢
  cfg_eval [rsp, firstCopy, secondCopy, push, Nat.reduceMul, or_true, false_or]
  unfold signatureCallArgs
  copy_regs

def verificationCallArgs (args : Values Value Reg.count) (sp : BitVec 64) :=
  let a := (args.set 1 ⟨64, 32⟩).set 2 ⟨64, sp + 128⟩
  let a := (a.set 4 ⟨64, sp - 8⟩).set 6 ⟨64, args[3].get 64⟩
  (a.set 7 ⟨64, sp + 160⟩).set 8 ⟨64, sp + 352⟩

theorem verificationCall (rsp : args[4].get 64 = sp)
    (push : StoreOk code mem (sp - 8) 8 0x1033c2 5) :
    program.runBlock (dialect code) ⟨.l1033a2, args, mem⟩ =
      .call ⟨.l104f20, verificationCallArgs args sp, memStore mem (sp - 8) (0x1033c7 : BitVec 64)⟩
        ⟨.l1033c7, #v[], rfl, some ⟨64, 0x1033c7⟩⟩ := by
  cfg_eval [rsp, push]
  unfold verificationCallArgs
  copy_regs

end K256.Proofs.Verify.Wrapper
