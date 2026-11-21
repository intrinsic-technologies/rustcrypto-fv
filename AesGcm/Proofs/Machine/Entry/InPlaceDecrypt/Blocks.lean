import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def frameBytes (use256 : Bool) : Nat := if use256 then 0x248 else 0x1c8

def entryMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp - 8) (args[5].get 64)
  let mem := memStore mem (sp - 16) (args[15].get 64)
  let mem := memStore mem (sp - 24) (args[14].get 64)
  let mem := memStore mem (sp - 32) (args[13].get 64)
  let mem := memStore mem (sp - 40) (args[12].get 64)
  let mem := memStore mem (sp - 48) (args[3].get 64)
  memStore mem (sp - (if use256 then 592 else 464))
    (if use256 then (0x101550 : BitVec 64) else 0x101270)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem entry_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (hTypes : GPRsTyped args)
    (hw : Writable code mem (args[4].get 64 - (if use256 then 592 else 464))
      (if use256 then 592 else 464)) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101520 else .l101240), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l1057c0 else .l104370) ∧
      continuation.target = (if use256 then .l101550 else .l101270) ∧
      continuation.guard = some ⟨64, if use256 then 0x101550 else 0x101270⟩ ∧
      callee.arguments[4]'(by change 4 < 53; decide) =
        ⟨64, args[4].get 64 - (if use256 then 592 else 464)⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) =
        ⟨64, args[4].get 64 - (if use256 then 568 else 440)⟩ ∧
      callee.arguments[5]'(by change 5 < 53; decide) =
        ⟨64, args[4].get 64 - (if use256 then 568 else 440)⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[7].get 64⟩ ∧
      callee.arguments[3]'(by change 3 < 53; decide) = ⟨64, args[1].get 64⟩ ∧
      callee.arguments[12]'(by change 12 < 53; decide) = ⟨64, args[8].get 64⟩ ∧
      callee.arguments[13]'(by change 13 < 53; decide) = ⟨64, args[9].get 64⟩ ∧
      callee.arguments[14]'(by change 14 < 53; decide) = ⟨64, args[2].get 64⟩ ∧
      callee.arguments[15]'(by change 15 < 53; decide) = ⟨64, args[6].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [22,39,50,51] → callee.arguments[r] = args[r]) ∧
      GPRsTyped callee.arguments ∧ callee.store = entryMemory use256 args mem := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x101520 else 0x101240) 48 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101240 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101520 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart hw
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l101240, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101520, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | runtime_typed
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [entryMemory]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem initialize_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (hTypes : GPRsTyped args)
    (hw : Writable code mem (args[4].get 64 - 8) 8) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101550 else .l101270), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l102180 else .l102040) ∧
      continuation.target = (if use256 then .l101560 else .l101280) ∧
      continuation.guard = some ⟨64, if use256 then 0x101560 else 0x101280⟩ ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) =
        ⟨64, args[4].get 64 + (if use256 then 256 else 192)⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[5].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
        callee.arguments[r] = args[r]) ∧
      GPRsTyped callee.arguments ∧
      callee.store = memStore mem (args[4].get 64 - 8)
        (if use256 then (0x101560 : BitVec 64) else 0x101280) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x101550 else 0x101270) 16 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101270 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101550 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l101270, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101550, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | runtime_typed
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem exit_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hr : Readable mem (args[4].get 64) (if use256 then 592 else 464))
    (hret : (memLoad mem (args[4].get 64 + (if use256 then 584 else 456)) 64).toNat <
      2^32) :
    ∃ output,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1015b2 else .l1012d2), args, mem⟩ = .returned output ∧
      output.store = mem ∧
      output.tag = some ⟨64,
        memLoad mem (args[4].get 64 + (if use256 then 584 else 456)) 64⟩ ∧
      output.values[4] = ⟨64, args[4].get 64 + (if use256 then 592 else 464)⟩ ∧
      output.values[3] = ⟨64,
        memLoad mem (args[4].get 64 + (if use256 then 536 else 408)) 64⟩ ∧
      output.values[12] = ⟨64,
        memLoad mem (args[4].get 64 + (if use256 then 544 else 416)) 64⟩ ∧
      output.values[13] = ⟨64,
        memLoad mem (args[4].get 64 + (if use256 then 552 else 424)) 64⟩ ∧
      output.values[14] = ⟨64,
        memLoad mem (args[4].get 64 + (if use256 then 560 else 432)) 64⟩ ∧
      output.values[15] = ⟨64,
        memLoad mem (args[4].get 64 + (if use256 then 568 else 440)) 64⟩ ∧
      output.values[5] = ⟨64,
        memLoad mem (args[4].get 64 + (if use256 then 576 else 448)) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [0,22,39,50,51] → output.values[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped output.values) := by
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hr hret
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1012d2, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1015b2, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards returned
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
