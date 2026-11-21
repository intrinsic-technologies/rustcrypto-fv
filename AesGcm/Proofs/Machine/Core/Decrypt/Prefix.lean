import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def entryMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp - 8) (args[5].get 64)
  let mem := memStore mem (sp - 16) (args[15].get 64)
  let mem := memStore mem (sp - 24) (args[14].get 64)
  let mem := memStore mem (sp - 32) (args[13].get 64)
  let mem := memStore mem (sp - 40) (args[12].get 64)
  memStore mem (sp - 48) (args[3].get 64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem entry_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 48) 48)
    (hr : Readable mem (args[8].get 64 + 16) 8)
    (length : BitVec 64)
    (hload : memLoad (entryMemory args mem) (args[8].get 64 + 16) 64 = length)
    (hlen : length.toNat ≤ 2^32)
    (haad : (args[1].get 64).toNat ≤ 2^32) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102720 else .l1022c0), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l102759 else .l1022f9) ∧
      next.store = entryMemory args mem ∧
      next.arguments[0].get 8 = 1 ∧
      next.arguments[1]'(by change 1 < 53; decide) = ⟨64, 0⟩ ∧
      next.arguments[3]'(by change 3 < 53; decide) = ⟨64, 0xfffffffe0⟩ ∧
      next.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 216⟩ ∧
      next.arguments[5]'(by change 5 < 53; decide) = ⟨64, args[1].get 64⟩ ∧
      next.arguments[14]'(by change 14 < 53; decide) = ⟨64, length⟩ ∧
      (∀ r : Fin 53, r.val ∈ [2,6,7,8,9,12,13,15,22,39,50,51] →
        next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  have hshift : args[1].get 64 >>> 61 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change (args[1].get 64).toNat / 2^61 = 0
    omega
  have hsmall : length.toNat < 68719476704 := by omega
  simp only [entryMemory] at hload
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102720 else 0x1022c0) 57 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1022c0 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102720 x hx))).apart
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l1022c0, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102720, args, mem⟩ = _
      cfg_eval [hshift]
      refine_norm [hshift, hload]
      simp only [hsmall, not_true_eq_false, false_and, ite_false,
        setWidth_mergeGPR8, orFlags, Option.getD_some]
      runtime_guards transfer
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl <;> rfl)
      | runtime_finish [entryMemory, hload, setWidth_mergeGPR8]

theorem entryMemory_frame (args : Values Value Reg.count) (mem : Ram)
    (hroom : 48 ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (entryMemory args mem) [span (args[4].get 64 - 48) 48] := by
  simp only [entryMemory]
  runtime_finish [span]

end AesGcm.Proofs.Machine.Core.Decrypt
