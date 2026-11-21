import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Fn102040.Frame
import AesGcm.Proofs.Machine.LIR.Fn102180.Frame

namespace AesGcm.Proofs.Machine.GCM
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def savedMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  memStore (memStore mem (args[4].get 64 - 8) (args[14].get 64))
    (args[4].get 64 - 16) (args[3].get 64)

def zeroMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  memStore (memStore (savedMemory args mem) (args[4].get 64 - 24) (0#64))
    (args[4].get 64 - 32) (0#64)

def entryMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  memStore (zeroMemory args mem) (args[4].get 64 - 64)
    (if use256 then 0x1021ac#64 else 0x10206c#64)

set_option maxHeartbeats 1600000 in
theorem entry_encrypt_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 64) 64) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102180 else .l102040), args, mem⟩ = .call callee continuation ∧
      callee.label = (if use256 then .l106960 else .l105100) ∧
      continuation.target = (if use256 then .l1021ac else .l10206c) ∧
      continuation.guard = some ⟨64, if use256 then 0x1021ac else 0x10206c⟩ ∧
      callee.store = entryMemory use256 args mem ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 64⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 - 56⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, args[4].get 64 - 32⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = args[6] ∧
      callee.arguments[3]'(by change 3 < 53; decide) = ⟨64, args[7].get 64⟩ ∧
      callee.arguments[14]'(by change 14 < 53; decide) = ⟨64, args[6].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [5,12,13,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  cases use256
  all_goals
    have hstackRead := hstack.readable
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x102040 44 := by
      have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l102040 x hx))
      have hl : LIR.bytes_l102040.length = 44 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l102040, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [entryMemory, zeroMemory, savedMemory]
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x102180 44 := by
      have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l102180 x hx))
      have hl : LIR.bytes_l102180.length = 44 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?_, ?exec256, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec256 =>
      change LIR.program.runBlock (dialect code) ⟨.l102180, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [entryMemory, zeroMemory, savedMemory]
end AesGcm.Proofs.Machine.GCM
