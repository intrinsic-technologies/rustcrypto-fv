import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.Runtime.SavedRegisters
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def frameBytes (use256 : Bool) : Nat := if use256 then 0x258 else 0x1d8

abbrev savedMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  saveSixRegisters args mem

def entryMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  memStore (savedMemory args mem)
    (args[4].get 64 - BitVec.ofNat 64 (frameBytes use256 + 8))
    (if use256 then (0x101690 : BitVec 64) else 0x1013b0)

set_option maxHeartbeats 1600000 in
theorem entry_schedule_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem
      (args[4].get 64 - BitVec.ofNat 64 (frameBytes use256 + 8)) (frameBytes use256 + 8)) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101660 else .l101380), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l1057c0 else .l104370) ∧
      continuation.target = (if use256 then .l101690 else .l1013b0) ∧
      continuation.guard = some ⟨64, if use256 then 0x101690 else 0x1013b0⟩ ∧
      callee.store = entryMemory use256 args mem ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 =
        args[4].get 64 - BitVec.ofNat 64 (frameBytes use256 + 8) ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 =
        args[4].get 64 - BitVec.ofNat 64 (frameBytes use256 - 32) ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = args[7].get 64 ∧
      (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = args[9].get 64 ∧
      (callee.arguments[5]'(by change 5 < 53; decide)).get 64 =
        args[4].get 64 - BitVec.ofNat 64 (frameBytes use256 - 32) ∧
      (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = args[2].get 64 ∧
      (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = args[6].get 64 ∧
      (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = args[8].get 64 ∧
      (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = args[1].get 64 ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hstackRead := hstack.readable
  cases use256
  all_goals simp only [frameBytes, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd, Nat.reduceSub] at hstack hstackRead ⊢
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x101380 48 := by
      have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l101380 x hx))
      have hl : LIR.bytes_l101380.length = 48 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l101380, args, mem⟩ = _
      cfg_eval
      refine_norm []
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish [entryMemory, savedMemory, saveSixRegisters, frameBytes]
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x101660 48 := by
      have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l101660 x hx))
      have hl : LIR.bytes_l101660.length = 48 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l101660, args, mem⟩ = _
      cfg_eval
      refine_norm []
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish [entryMemory, savedMemory, saveSixRegisters, frameBytes]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem context_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 8) 8)
    (hcapacity : Readable mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 + 8)) 8) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101690 else .l1013b0), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l102180 else .l102040) ∧
      continuation.target = (if use256 then .l1016a8 else .l1013c8) ∧
      continuation.guard = some ⟨64, if use256 then 0x1016a8 else 0x1013c8⟩ ∧
      callee.store = memStore mem (args[4].get 64 - 8)
        (if use256 then (0x1016a8 : BitVec 64) else 0x1013c8) ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) =
        ⟨64, args[4].get 64 + (if use256 then 0x110 else 0xd0)⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[5].get 64⟩ ∧
      callee.arguments[5]'(by change 5 < 53; decide) =
        ⟨64, memLoad mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 + 8)) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,12,13,14,15,22,39,50,51] →
        callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x101690 else 0x1013b0) 24 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1013b0 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l101690 x hx))).apart
  cases use256
  all_goals
    simp only [frameBytes, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd] at hcapacity hhelperApart ⊢
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1013b0, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101690, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem exit_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hr : Readable mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 48)) 56)
    (hbase : (memLoad mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256)) 64).toNat < 2^32) :
    ∃ output,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101739 else .l101459), args, mem⟩ = .returned output ∧
      output.store = mem ∧
      output.tag = some ⟨64, memLoad mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256)) 64⟩ ∧
      output.values[4] = ⟨64, args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 + 8)⟩ ∧
      output.values[3] = ⟨64, memLoad mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 48)) 64⟩ ∧
      output.values[12] = ⟨64, memLoad mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 40)) 64⟩ ∧
      output.values[13] = ⟨64, memLoad mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 32)) 64⟩ ∧
      output.values[14] = ⟨64, memLoad mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 24)) 64⟩ ∧
      output.values[15] = ⟨64, memLoad mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 16)) 64⟩ ∧
      output.values[5] = ⟨64, memLoad mem (args[4].get 64 + BitVec.ofNat 64 (frameBytes use256 - 8)) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [0,22,39,50,51] → output.values[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped output.values) := by
  generalize hsp : args[4].get 64 = sp at *
  cases use256
  all_goals
    simp only [frameBytes, Bool.false_eq_true, ↓reduceIte, Nat.reduceAdd, Nat.reduceSub] at hr hbase ⊢
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l101459, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101739, args, mem⟩ = _
      cfg_eval []
      refine_norm [hsp]
      runtime_guards returned
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [hsp]

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
