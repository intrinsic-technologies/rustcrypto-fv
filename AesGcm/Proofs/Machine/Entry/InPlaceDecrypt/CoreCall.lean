import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def coreMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let tail := args[12].get 64 + args[13].get 64 - 16
  let lo := memLoad mem tail 64
  let hi := memLoad mem (args[12].get 64 + args[13].get 64 - 8) 64
  let mem := memStore mem (sp + 8) hi
  let mem := memStore mem sp lo
  let mem := memStore mem (sp + 16) (args[12].get 64)
  let mem := memStore mem (sp + 24) (args[12].get 64)
  let mem := memStore mem (sp + 32) (args[13].get 64 - 16)
  memStore mem (sp - 8) (if use256 then (0x1015af : BitVec 64) else 0x1012cf)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem core_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (hTypes : GPRsTyped args)
    (hw : Writable code mem (args[4].get 64 - 8) 48)
    (hr : Readable mem (args[12].get 64 + args[13].get 64 - 16) 16) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l10156b else .l10128b), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l102720 else .l1022c0) ∧
      continuation.target = (if use256 then .l1015af else .l1012cf) ∧
      continuation.guard = some ⟨64, if use256 then 0x1015af else 0x1012cf⟩ ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) =
        ⟨64, args[4].get 64 + (if use256 then 256 else 192)⟩ ∧
      callee.arguments[8]'(by change 8 < 53; decide) = ⟨64, args[4].get 64 + 16⟩ ∧
      callee.arguments[9]'(by change 9 < 53; decide) = ⟨64, args[4].get 64⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[15].get 64⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, args[14].get 64⟩ ∧
      callee.arguments[1]'(by change 1 < 53; decide) = ⟨64, args[3].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
        callee.arguments[r] = args[r]) ∧
      GPRsTyped callee.arguments ∧ callee.store = coreMemory use256 args mem := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x10156b else 0x10128b) 68 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10128b x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10156b x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l10128b, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l10156b, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | runtime_typed
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [coreMemory]

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
