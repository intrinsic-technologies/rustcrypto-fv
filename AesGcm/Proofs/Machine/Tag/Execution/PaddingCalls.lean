import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Tag.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem copy_runBlock (use256 isCipher : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 8)
    (hslotRead : Readable mem 0x201208 8)
    (hslot : memLoad mem 0x201208 64 = 0x103f00) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then (if isCipher then .l101da7 else .l101cbb)
          else (if isCipher then .l101987 else .l10189b)), args, mem⟩ =
        .call callee continuation ∧
      callee.label = .l103f00 ∧
      continuation.target = (if use256 then (if isCipher then .l101db8 else .l101ccc)
          else (if isCipher then .l101998 else .l1018ac)) ∧
      continuation.guard = some ⟨64, if use256 then (if isCipher then 0x101db8 else 0x101ccc)
          else (if isCipher then 0x101998 else 0x1018ac)⟩ ∧
      callee.store = memStore mem (args[4].get 64 - 8)
        (if use256 then (if isCipher then (0x101db8 : BitVec 64) else 0x101ccc)
          else (if isCipher then 0x101998 else 0x1018ac)) ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 64⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) =
        ⟨64, if isCipher then args[14].get 64 else args[12].get 64⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) =
        ⟨64, if isCipher then args[12].get 64 else args[13].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n
        (if use256 then (if isCipher then 0x101da7 else 0x101cbb)
          else (if isCipher then 0x101987 else 0x10189b)) 17 := by
    cases use256 <;> cases isCipher
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10189b x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101987 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101cbb x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101da7 x hx))).apart
  cases use256 <;> cases isCipher
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l10189b, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101987, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101cbb, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101da7, args, mem⟩ = _
      cfg_eval [hslot]
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem zero_runBlock (use256 isCipher : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 8)
    (hslotRead : Readable mem 0x201228 8)
    (hslot : memLoad mem 0x201228 64 = 0x103eb0) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then (if isCipher then .l101d7f else .l101c93)
          else (if isCipher then .l10195f else .l101873)), args, mem⟩ =
        .call callee continuation ∧
      callee.label = .l103eb0 ∧
      continuation.target = (if use256 then (if isCipher then .l101da7 else .l101cbb)
          else (if isCipher then .l101987 else .l10189b)) ∧
      continuation.guard = some ⟨64, if use256 then (if isCipher then 0x101da7 else 0x101cbb)
          else (if isCipher then 0x101987 else 0x10189b)⟩ ∧
      callee.store = memStore mem (args[4].get 64 - 8)
        (if use256 then (if isCipher then (0x101da7 : BitVec 64) else 0x101cbb)
          else (if isCipher then 0x101987 else 0x10189b)) ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + (if isCipher then args[12].get 64 else args[13].get 64) + 64⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) =
        ⟨64, 0⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) =
        ⟨64, 16 - (if isCipher then args[12].get 64 else args[13].get 64)⟩ ∧
      callee.arguments[12]'(by change 12 < 53; decide) =
        (if isCipher then args[12] else ⟨64, args[12].get 64 +
          (0x1ffffffffffffff0 &&& args[3].get 64)⟩) ∧
      callee.arguments[14]'(by change 14 < 53; decide) =
        (if isCipher then ⟨64, args[14].get 64 +
          (0xffffffff0 &&& args[15].get 64)⟩ else args[14]) ∧
      (∀ r : Fin 53, r.val ∈ [3,5,13,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n
        (if use256 then (if isCipher then 0x101d7f else 0x101c93)
          else (if isCipher then 0x10195f else 0x101873)) 40 := by
    cases use256 <;> cases isCipher
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101873 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10195f x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101c93 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101d7f x hx))).apart
  cases use256 <;> cases isCipher
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l101873, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l10195f, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101c93, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101d7f, args, mem⟩ = _
      cfg_eval [hslot]
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

end AesGcm.Proofs.Machine.Tag.Execution
