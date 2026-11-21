import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Fn104370.Frame
import AesGcm.Proofs.Machine.LIR.Fn1057c0.Frame

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

attribute [local irreducible] memLoad memStore

set_option maxHeartbeats 800000 in
theorem return_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hRead : Readable mem (args[4].get 64 + (if use256 then 312 else 216)) 56)
    (hRetLow : (memLoad mem (args[4].get 64 + (if use256 then 360 else 264)) 64).toNat <
      2 ^ 32) :
    ∃ output : Output Value Ram Reg.count,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l10693d else .l1050df), args, mem⟩ = .returned output ∧
      output.store = mem ∧
      output.tag = some ⟨64, memLoad mem (args[4].get 64 + (if use256 then 360 else 264)) 64⟩ ∧
      output.values[4] = ⟨64, args[4].get 64 + (if use256 then 368 else 272)⟩ ∧
      output.values[0] = ⟨64, args[3].get 64⟩ ∧
      output.values[3] = ⟨64, memLoad mem
        (args[4].get 64 + (if use256 then 312 else 216)) 64⟩ ∧
      output.values[12] = ⟨64, memLoad mem
        (args[4].get 64 + (if use256 then 320 else 224)) 64⟩ ∧
      output.values[13] = ⟨64, memLoad mem
        (args[4].get 64 + (if use256 then 328 else 232)) 64⟩ ∧
      output.values[14] = ⟨64, memLoad mem
        (args[4].get 64 + (if use256 then 336 else 240)) 64⟩ ∧
      output.values[15] = ⟨64, memLoad mem
        (args[4].get 64 + (if use256 then 344 else 248)) 64⟩ ∧
      output.values[5] = ⟨64, memLoad mem
        (args[4].get 64 + (if use256 then 352 else 256)) 64⟩ ∧
      output.values[22] = args[22] ∧
      output.values[39] = args[39] ∧
      output.values[50] = args[50] ∧
      output.values[51] = args[51] ∧
      (GPRsTyped args → GPRsTyped output.values) := by
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hRead hRetLow ⊢
  · refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l1050df, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards returned
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish []
  · refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l10693d, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards returned
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish []

theorem return_exec (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (hsp : args[4].get 64 + (if use256 then 360 else 264) = fr.rsp)
    (hTypes : GPRsTyped args) (hDF : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, fr.mxcsr⟩)
    (h50 : args[50] = ⟨16, fr.ftw⟩) (h51 : args[51] = ⟨16, fr.fcw⟩)
    (hRead : Readable mem (fr.rsp - 48) 56)
    (hRet : memLoad mem fr.rsp 64 = fr.ret) (hRetLow : fr.ret.toNat < 2 ^ 32)
    (h3 : memLoad mem (fr.rsp - 48) 64 = fr.rbx)
    (h12 : memLoad mem (fr.rsp - 40) 64 = fr.r12)
    (h13 : memLoad mem (fr.rsp - 32) 64 = fr.r13)
    (h14 : memLoad mem (fr.rsp - 24) 64 = fr.r14)
    (h15 : memLoad mem (fr.rsp - 16) 64 = fr.r15)
    (h5 : memLoad mem (fr.rsp - 8) 64 = fr.rbp) :
    ∃ output : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code)
        ⟨⟨(if use256 then .l10693d else .l1050df), args, mem⟩, []⟩ output ∧
      output.store = mem ∧ output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Fn1057c0.frameInfo else LIR.Fn104370.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values := by
  have a3 : args[4].get 64 + (if use256 then 312 else 216) = fr.rsp - 48 := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have a12 : args[4].get 64 + (if use256 then 320 else 224) = fr.rsp - 40 := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have a13 : args[4].get 64 + (if use256 then 328 else 232) = fr.rsp - 32 := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have a14 : args[4].get 64 + (if use256 then 336 else 240) = fr.rsp - 24 := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have a15 : args[4].get 64 + (if use256 then 344 else 248) = fr.rsp - 16 := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have a5 : args[4].get 64 + (if use256 then 352 else 256) = fr.rsp - 8 := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  have a4 : args[4].get 64 + (if use256 then 368 else 272) = fr.rsp + 8 := by
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> bv_omega
  obtain ⟨output, hex, hm, ht, ho4, _, ho3, ho12, ho13, ho14, ho15, ho5,
      ho22, ho39, ho50, ho51, hoTypes⟩ := return_runBlock use256 code args mem
        (by rw [a3]; exact hRead) (by rw [hsp, hRet]; exact hRetLow)
  rw [hsp, hRet] at ht
  rw [a4] at ho4
  rw [a3, h3] at ho3
  rw [a12, h12] at ho12
  rw [a13, h13] at ho13
  rw [a14, h14] at ho14
  rw [a15, h15] at ho15
  rw [a5, h5] at ho5
  refine ⟨output, ?_, hm, ht, ?_, hoTypes hTypes⟩
  · apply Program.Exec.done
    change (LIR.program.runBlock (dialect code) _).next (dialect code) [] = _
    rw [hex]
    rfl
  · have hd : output.values[4] = ⟨64, fr.rsp + 8⟩ ∧
        output.values[22] = ⟨1, 0⟩ ∧ output.values[3] = ⟨64, fr.rbx⟩ ∧
        output.values[5] = ⟨64, fr.rbp⟩ ∧ output.values[12] = ⟨64, fr.r12⟩ ∧
        output.values[13] = ⟨64, fr.r13⟩ ∧ output.values[14] = ⟨64, fr.r14⟩ ∧
        output.values[15] = ⟨64, fr.r15⟩ ∧ output.values[39] = ⟨32, fr.mxcsr⟩ ∧
        output.values[50] = ⟨16, fr.ftw⟩ ∧ output.values[51] = ⟨16, fr.fcw⟩ ∧ True :=
      ⟨ho4, ho22.trans hDF, ho3, ho5, ho12, ho13, ho14, ho15,
        ho39.trans h39, ho50.trans h50, ho51.trans h51, trivial⟩
    cases use256 <;> exact hd

end AesGcm.Proofs.Machine.AES16.KeySchedule
