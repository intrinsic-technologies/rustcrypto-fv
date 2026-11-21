import AesGcm.Proofs.AES16.KeySchedule.Generation.State
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.Runtime.Call

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def copyLabel (use256 odd : Bool) : LIR.Label :=
  match use256, odd with
  | false, _ => .l104424
  | true, false => .l105870
  | true, true => .l1058d4

def subLabel (use256 odd : Bool) : LIR.Label :=
  match use256, odd with
  | false, _ => .l104434
  | true, false => .l105880
  | true, true => .l1058e4

def subReturn (use256 odd : Bool) : BitVec 64 :=
  match use256, odd with
  | false, _ => 0x104434
  | true, false => 0x105880
  | true, true => 0x1058e4

def callFrame (target : LIR.Label) (ret : BitVec 64) :
    StackFrame Value LIR.Label signature Reg.count :=
  { target := target, kept := #v[], arity := rfl, guard := some ⟨64, ret⟩ }

set_option maxHeartbeats 1000000 in
theorem copy_setup (use256 odd : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hsp : args[4].get 64 = sp) (hTypes : GPRsTyped args)
    (hstack : Writable code mem (sp - 8) 8) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨copyLabel use256 odd, args, mem⟩ =
        .call ⟨.l103f30, nextArgs, memStore mem (sp - 8) (subReturn use256 odd)⟩
          (callFrame (subLabel use256 odd) (subReturn use256 odd)) ∧
      nextArgs[4] = ⟨64, sp - 8⟩ ∧
      nextArgs[7] = ⟨64, args[14].get 64⟩ ∧
      nextArgs[6] = ⟨64, if use256 then 120 else 88⟩ ∧
      nextArgs[2] = ⟨64, args[15].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        nextArgs[r] = args[r]) ∧ GPRsTyped nextArgs := by
  have hs0 : StoreOk code mem (sp - 8) 8 0x10442f 5 := by
    apply storeOk_of_writable hstack
    exact RangeApart.right_sub (storeOk_of_codeRange hstack
      (fun x hx => hcode x (LIR.code_l104424 x hx))).apart (off := 11) (by decide)
  have hs1 : StoreOk code mem (sp - 8) 8 0x10587b 5 := by
    apply storeOk_of_writable hstack
    exact RangeApart.right_sub (storeOk_of_codeRange hstack
      (fun x hx => hcode x (LIR.code_l105870 x hx))).apart (off := 11) (by decide)
  have hs2 : StoreOk code mem (sp - 8) 8 0x1058df 5 := by
    apply storeOk_of_writable hstack
    exact RangeApart.right_sub (storeOk_of_codeRange hstack
      (fun x hx => hcode x (LIR.code_l1058d4 x hx))).apart (off := 11) (by decide)
  cases use256 <;> cases odd
  all_goals simp only [copyLabel, subLabel, subReturn, Bool.false_eq_true, ↓reduceIte]
  all_goals cfg_eval [hsp]
  all_goals try first | simp only [hs0, ite_true] | simp only [hs1, ite_true] | simp only [hs2, ite_true]
  all_goals refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals first
    | (rintro ⟨r, hr⟩ hin
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
       rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    | runtime_typed

def notLabel (use256 odd : Bool) : LIR.Label :=
  match use256, odd with
  | false, _ => .l104446
  | true, false => .l105892
  | true, true => .l1058f6

def notReturn (use256 odd : Bool) : BitVec 64 :=
  match use256, odd with
  | false, _ => 0x104446
  | true, false => 0x105892
  | true, true => 0x1058f6

def subDestination (use256 odd : Bool) (sp : BitVec 64)
    (args : Values Value Reg.count) : BitVec 64 :=
  sp + (if use256 && !odd then args[3].get 64 else args[12].get 64) +
    (if use256 then 12 else 8)

set_option maxHeartbeats 1000000 in
theorem sub_setup (use256 odd : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hsp : args[4].get 64 = sp) (hTypes : GPRsTyped args)
    (hstack : Writable code mem (sp - 8) 8) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨subLabel use256 odd, args, mem⟩ =
        .call ⟨.l100b10, nextArgs, memStore mem (sp - 8) (notReturn use256 odd)⟩
          (callFrame (notLabel use256 odd) (notReturn use256 odd)) ∧
      nextArgs[4] = ⟨64, sp - 8⟩ ∧
      nextArgs[7] = ⟨64, subDestination use256 odd sp args⟩ ∧
      nextArgs[6] = ⟨64, 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        nextArgs[r] = args[r]) ∧ GPRsTyped nextArgs := by
  have hs0 : StoreOk code mem (sp - 8) 8 0x104441 5 := by
    apply storeOk_of_writable hstack
    exact RangeApart.right_sub (storeOk_of_codeRange hstack
      (fun x hx => hcode x (LIR.code_l104434 x hx))).apart (off := 13) (by decide)
  have hs1 : StoreOk code mem (sp - 8) 8 0x10588d 5 := by
    apply storeOk_of_writable hstack
    exact RangeApart.right_sub (storeOk_of_codeRange hstack
      (fun x hx => hcode x (LIR.code_l105880 x hx))).apart (off := 13) (by decide)
  have hs2 : StoreOk code mem (sp - 8) 8 0x1058f1 5 := by
    apply storeOk_of_writable hstack
    exact RangeApart.right_sub (storeOk_of_codeRange hstack
      (fun x hx => hcode x (LIR.code_l1058e4 x hx))).apart (off := 13) (by decide)
  cases use256 <;> cases odd
  all_goals simp only [subLabel, notLabel, notReturn, subDestination,
    Bool.false_eq_true, Bool.and_self, Bool.true_and, Bool.false_and, Bool.not_false,
    Bool.not_true, ↓reduceIte]
  all_goals cfg_eval [hsp]
  all_goals try first | simp only [hs0, ite_true] | simp only [hs1, ite_true] | simp only [hs2, ite_true]
  all_goals refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  all_goals first
    | (rintro ⟨r, hr⟩ hin
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
       rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    | runtime_typed

def afterLabel (use256 odd : Bool) : LIR.Label :=
  match use256, odd with
  | false, _ => .l104413
  | true, false => .l1058cb
  | true, true => .l105929

def afterReturn (use256 odd : Bool) : BitVec 64 :=
  match use256, odd with
  | false, _ => 0x104413
  | true, false => 0x1058cb
  | true, true => 0x105929

def oddRound (round : Nat) : Bool := decide (round % 2 ≠ 0)

def substitutedRound (use256 : Bool) (round : Nat) (x : Fixslice16.Planes16) :
    Fixslice16.Planes16 :=
  let c := if Nat.mod (4 * round) (variant use256).Nk = 0 then
    (rcon (Nat.div (4 * round) (variant use256).Nk))[0] else 0
  fun p ↦ Fixslice16.subBytesNots x p ^^^
    (if c.toBitVec.getLsbD p.val then (0x80 : BitVec 16) else 0)

theorem caller_reaches {code : CodeMap}
    {caller callee : LIR.lifted.Location}
    {target : LIR.Label} {ret : BitVec 64}
    {output : Output Value Ram Reg.count}
    (hcall : LIR.program.runBlock (dialect code) caller =
      .call callee (callFrame target ret))
    (hexec : LIR.program.Exec (dialect code) ⟨callee, []⟩ output)
    (htag : output.tag = some ⟨64, ret⟩) :
    (LIR.program.sem (dialect code)).Reaches
      ⟨caller, []⟩ ⟨⟨target, output.values, output.store⟩, []⟩ := by
  have hresume := CFGCall.exec_reaches_resume hexec (callFrame target ret) []
    (by rw [htag]; change decide (_ = _) = true; simp only [decide_true])
  exact (Semantics.Reaches.single (by
    change LIR.program.step (dialect code) _ = _
    rw [Program.step, hcall]
    rfl)).trans hresume

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation
