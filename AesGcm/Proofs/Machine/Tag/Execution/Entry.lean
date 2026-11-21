import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Tag.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def savedMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp - 8) (args[5].get 64)
  let mem := memStore mem (sp - 16) (args[15].get 64)
  let mem := memStore mem (sp - 24) (args[14].get 64)
  let mem := memStore mem (sp - 32) (args[13].get 64)
  let mem := memStore mem (sp - 40) (args[12].get 64)
  let mem := memStore mem (sp - 48) (args[3].get 64)
  let mem := memStore mem (sp - 64) (args[2].get 64)
  memStore mem (sp - 56) (args[7].get 64)

def entryMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := savedMemory args mem
  let v := memLoad mem (args[6].get 64 + 24) 64
  let mem := memStore mem (sp - 80) v
  let v := memLoad mem (args[6].get 64 + 16) 64
  let mem := memStore mem (sp - 88) v
  let lo := memLoad mem (args[6].get 64) 64
  let hi := memLoad mem (args[6].get 64 + 8) 64
  let mem := memStore mem (sp - 96) hi
  let mem := memStore mem (sp - 104) lo
  memStore mem (sp - 192) (if use256 then (0x101c86 : BitVec 64) else 0x101866)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem entry_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 192) 192)
    (hstate : Readable mem (args[6].get 64) 32)
    (hlength : Readable mem (args[4].get 64 + 8) 8) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101c20 else .l101800), args, mem⟩ = .call callee continuation ∧
      callee.label = .l109980 ∧
      continuation.target = (if use256 then .l101c86 else .l101866) ∧
      continuation.guard = some ⟨64, if use256 then 0x101c86 else 0x101866⟩ ∧
      callee.store = entryMemory use256 args mem ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 192⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 - 104⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[1].get 64⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, args[8].get 64 >>> 4⟩ ∧
      callee.arguments[3]'(by change 3 < 53; decide) = ⟨64, args[8].get 64⟩ ∧
      callee.arguments[12]'(by change 12 < 53; decide) = ⟨64, args[1].get 64⟩ ∧
      callee.arguments[14]'(by change 14 < 53; decide) = ⟨64, args[9].get 64⟩ ∧
      callee.arguments[15]'(by change 15 < 53; decide) =
        ⟨64, memLoad (savedMemory args mem) (args[4].get 64 + 8) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [5,8,9,13,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x101c20 else 0x101800) 102 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101800 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l101c20 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l101800, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101c20, args, mem⟩ = _
      cfg_eval []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [entryMemory, savedMemory]

theorem savedMemory_frame (args : Values Value Reg.count) (mem : Ram)
    (hroom : 192 ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (savedMemory args mem) [span (args[4].get 64 - 192) 192] := by
  dsimp only [savedMemory]
  runtime_finish [span]

theorem entryMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : 192 ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (entryMemory use256 args mem) [span (args[4].get 64 - 192) 192] := by
  dsimp only [entryMemory, savedMemory]
  runtime_finish [span]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem entryMemory_saved (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) :
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 192) 64 =
      (if use256 then 0x101c86 else 0x101866) ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 64) 64 = args[2].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 56) 64 = args[7].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 48) 64 = args[3].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 40) 64 = args[12].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 32) 64 = args[13].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 24) 64 = args[14].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 16) 64 = args[15].get 64 ∧
    memLoad (entryMemory use256 args mem) (args[4].get 64 - 8) 64 = args[5].get 64 := by
  repeat' apply And.intro
  all_goals
    simp only [entryMemory, savedMemory]
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | (rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_diff
          simp only [sub_sub_sub_left]
          decide +kernel)])

end AesGcm.Proofs.Machine.Tag.Execution
