import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def tagMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp + 0x40) (args[15].get 64)
  let mem := memStore mem sp (args[14].get 64)
  memStore mem (sp - 8) (if use256 then (0x1027e8 : BitVec 64) else 0x102388)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem tag_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 176)
    (hread : Readable mem (args[4].get 64) 168)
    (hdescriptor : Readable mem (args[15].get 64) 8) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1027bc else .l10235c), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l101c20 else .l101800) ∧
      continuation.target = (if use256 then .l1027e8 else .l102388) ∧
      continuation.guard = some ⟨64, if use256 then 0x1027e8 else 0x102388⟩ ∧
      callee.store = tagMemory use256 args mem ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 0x88⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[12].get 64⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, args[4].get 64 + 0x78⟩ ∧
      callee.arguments[1]'(by change 1 < 53; decide) =
        ⟨64, memLoad mem (args[4].get 64 + 0x50) 64⟩ ∧
      callee.arguments[8]'(by change 8 < 53; decide) = ⟨64, args[5].get 64⟩ ∧
      callee.arguments[9]'(by change 9 < 53; decide) =
        ⟨64, memLoad (memStore mem (args[4].get 64 + 0x40) (args[15].get 64))
          (args[15].get 64) 64⟩ ∧
      callee.arguments[12]'(by change 12 < 53; decide) = callee.arguments[9]'(by change 9 < 53; decide) ∧
      (∀ r : Fin 53, r.val ∈ [3,5,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x1027bc else 0x10235c) 44 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l10235c x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1027bc x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l10235c, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1027bc, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [tagMemory]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem tail_copy_in_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 8) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l10290b else .l1024ab), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103f00 ∧
      continuation.target = (if use256 then .l102926 else .l1024c6) ∧
      continuation.guard = some ⟨64, (if use256 then 0x102926 else 0x1024c6)⟩ ∧
      callee.store = memStore mem (args[4].get 64 - 8) (if use256 then (0x102926 : BitVec 64) else 0x1024c6) ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 0x98⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[13].get 64⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, args[14].get 64⟩ ∧
      callee.arguments[3]'(by change 3 < 53; decide) = ⟨64, args[4].get 64 + 0x98⟩ ∧
      callee.arguments[12]'(by change 12 < 53; decide) = ⟨64, 0x103f00⟩ ∧
      (∀ r : Fin 53, r.val ∈ [0,5,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x10290b else 0x1024ab) 27 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1024ab x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l10290b x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1024ab, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l10290b, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

def tailCtrMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp + 0x10) (args[15].get 64)
  let mem := memStore mem (sp + 0x18) (args[3].get 64)
  let mem := memStore mem (sp + 0x20) (args[3].get 64)
  let mem := memStore mem (sp + 0x28) (1 : BitVec 64)
  memStore mem (sp - 8) (if use256 then (0x10294d : BitVec 64) else 0x1024ed)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem tail_ctr_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 56) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102926 else .l1024c6), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l1084e0 else .l107050) ∧
      continuation.target = (if use256 then .l10294d else .l1024ed) ∧
      continuation.guard = some ⟨64, (if use256 then 0x10294d else 0x1024ed)⟩ ∧
      callee.store = tailCtrMemory use256 args mem ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 0x58⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[4].get 64 + 0x10⟩ ∧
      (∀ r : Fin 53, r.val ∈ [0,3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102926 else 0x1024c6) 39 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1024c6 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l102926 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1024c6, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102926, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [tailCtrMemory]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem tail_copy_out_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 8)
    (hread : Readable mem (args[4].get 64 + 0x40) 8)
    (hdescriptor : Readable mem (memLoad mem (args[4].get 64 + 0x40) 64 + 8) 8)
    (htarget : args[12].get 64 = 0x103f00) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l10294d else .l1024ed), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103f00 ∧
      continuation.target = (if use256 then .l10295f else .l1024ff) ∧
      continuation.guard = some ⟨64, (if use256 then 0x10295f else 0x1024ff)⟩ ∧
      callee.store = memStore mem (args[4].get 64 - 8) (if use256 then (0x10295f : BitVec 64) else 0x1024ff) ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, memLoad mem (memLoad mem (args[4].get 64 + 0x40) 64 + 8) 64⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[3].get 64⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, args[14].get 64⟩ ∧
      callee.arguments[0]'(by change 0 < 53; decide) = ⟨64, memLoad mem (args[4].get 64 + 0x40) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x10294d else 0x1024ed) 18 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1024ed x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l10294d x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1024ed, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l10294d, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      simp only [htarget]
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
theorem tail_zero_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 8)
    (hslotRead : Readable mem 0x201228 8)
    (hslot : memLoad mem 0x201228 64 = 0x103eb0) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1028e4 else .l102484), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103eb0 ∧
      continuation.target = (if use256 then .l10290b else .l1024ab) ∧
      continuation.guard = some ⟨64, (if use256 then 0x10290b else 0x1024ab)⟩ ∧
      callee.store = memStore mem (args[4].get 64 - 8) (if use256 then (0x10290b : BitVec 64) else 0x1024ab) ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + args[14].get 64 + 0x98⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, 0⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, if args[14].get 64 < 16 then 16 - args[14].get 64 else 0⟩ ∧
      callee.arguments[5]'(by change 5 < 53; decide) = ⟨64, (args[0].get 32).setWidth 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [0,3,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x1028e4 else 0x102484) 39 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l102484 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1028e4 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l102484, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1028e4, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      simp only [hslot]
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

def maskMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let nonce := args[6].get 64
  let w0 := memLoad mem nonce 32
  let w1 := memLoad mem (nonce + 4) 32
  let mem := memStore mem (sp + 0x50) (args[2].get 64)
  let w2 := memLoad mem (nonce + 8) 32
  let mem := memStore mem (sp + 0x80) (0 : BitVec 64)
  let mem := memStore mem (sp + 0x78) (0 : BitVec 64)
  let mem := memStore mem (sp + 0x3c) w0
  let mem := memStore mem (sp + 0x10) w0
  let mem := memStore mem (sp + 0x38) w1
  let mem := memStore mem (sp + 0x14) w1
  let mem := memStore mem (sp + 0x34) w2
  let mem := memStore mem (sp + 0x18) w2
  let mem := memStore mem (sp + 0x1c) (0x1000000 : BitVec 32)
  let mem := memStore mem (sp + 0x48) (args[7].get 64 + 0x20)
  memStore mem (sp - 8) (if use256 then (0x1027bc : BitVec 64) else 0x10235c)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem mask_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 176)
    (hnonce : Readable mem (args[6].get 64) 12) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102759 else .l1022f9), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l106960 else .l105100) ∧
      continuation.target = (if use256 then .l1027bc else .l10235c) ∧
      continuation.guard = some ⟨64, (if use256 then 0x1027bc else 0x10235c)⟩ ∧
      callee.store = maskMemory use256 args mem ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + 0x78⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[7].get 64 + 0x20⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, args[4].get 64 + 0x10⟩ ∧
      callee.arguments[12]'(by change 12 < 53; decide) = ⟨64, args[7].get 64⟩ ∧
      callee.arguments[13]'(by change 13 < 53; decide) = ⟨64, args[9].get 64⟩ ∧
      callee.arguments[15]'(by change 15 < 53; decide) = ⟨64, args[8].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,14,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102759 else 0x1022f9) 99 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1022f9 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l102759 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1022f9, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102759, args, mem⟩ = _
      cfg_eval []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [maskMemory]

end AesGcm.Proofs.Machine.Core.Decrypt
