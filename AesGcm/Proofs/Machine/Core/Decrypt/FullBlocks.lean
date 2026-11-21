import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime


def fullCtrMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let descriptor := memLoad mem (sp + 0x40) 64
  let destination := memLoad mem (descriptor + 8) 64
  let delta := (args[3].get 64 + 16) &&& args[14].get 64
  let mem := memStore mem (descriptor + 8) (delta + destination)
  let mem := memStore mem (sp + 0x10) (args[15].get 64)
  let mem := memStore mem (sp + 0x18) (args[12].get 64)
  let mem := memStore mem (sp + 0x20) destination
  let mem := memStore mem (sp + 0x28) (args[14].get 64 >>> 4)
  memStore mem (sp - 8) (if use256 then (0x1028d0 : BitVec 64) else 0x102470)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem full_ctr_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 56)
    (hread : Readable mem (args[4].get 64 + 0x40) 8)
    (hdescriptor : Writable code mem (memLoad mem (args[4].get 64 + 0x40) 64 + 8) 8) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102885 else .l102425), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l1084e0 else .l107050) ∧
      continuation.target = (if use256 then .l1028d0 else .l102470) ∧
      continuation.guard = some ⟨64, (if use256 then 0x1028d0 else 0x102470)⟩ ∧
      callee.store = fullCtrMemory use256 args mem ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 0x58⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[4].get 64 + 0x10⟩ ∧
      callee.arguments[1]'(by change 1 < 53; decide) = ⟨64, args[14].get 64 >>> 4⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, memLoad mem (memLoad mem (args[4].get 64 + 0x40) 64 + 8) 64⟩ ∧
      callee.arguments[3]'(by change 3 < 53; decide) = ⟨64, (args[0].get 32).setWidth 64⟩ ∧
      callee.arguments[13]'(by change 13 < 53; decide) = ⟨64, args[12].get 64 + ((args[3].get 64 + 16) &&& args[14].get 64)⟩ ∧
      callee.arguments[14]'(by change 14 < 53; decide) = ⟨64, (args[14].get 32 &&& 15).setWidth 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [0,5,12,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hdescriptorRead := hdescriptor.readable
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102885 else 0x102425) 75 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l102425 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l102885 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l102425, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102885, args, mem⟩ = _
      cfg_eval []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [fullCtrMemory]

end AesGcm.Proofs.Machine.Core.Decrypt
