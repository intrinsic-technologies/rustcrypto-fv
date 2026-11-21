import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def counterMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp + 0x58) (memLoad mem (sp + 0x48) 64)
  let mem := memStore mem (sp + 0x60) (memLoad mem (sp + 0x3c) 32)
  let mem := memStore mem (sp + 0x64) (memLoad mem (sp + 0x38) 32)
  let mem := memStore mem (sp + 0x68) (memLoad mem (sp + 0x34) 32)
  memStore mem (sp + 0x6c) (0x100000001 : BitVec 64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem counter_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 + 0x58) 28)
    (hread : Readable mem (args[4].get 64) 168) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102849 else .l1023e9), args, mem⟩ = .jump next ∧
      next.label = (if (args[14].get 64).toNat < 17
        then (if use256 then .l1028dc else .l10247c)
        else (if use256 then .l102885 else .l102425)) ∧
      next.store = counterMemory args mem ∧
      next.arguments[1]'(by change 1 < 53; decide) = ⟨64, 0x100000001⟩ ∧
      next.arguments[15]'(by change 15 < 53; decide) = ⟨64, args[4].get 64 + 0x60⟩ ∧
      (∀ r : Fin 53, r.val ∈ [0,3,4,5,12,13,14,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102849 else 0x1023e9) 60 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1023e9 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l102849 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    by_cases hsmall : (args[14].get 64).toNat < 17
    all_goals
      simp only [hsmall, ↓reduceIte]
      runtime_context [hsmall]
      refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_⟩
      case exec =>
        first
          | change LIR.program.runBlock (dialect code) ⟨.l1023e9, args, mem⟩ = _
          | change LIR.program.runBlock (dialect code) ⟨.l102849, args, mem⟩ = _
        cfg_eval []
        simp only [cmpSpec_CF, show ((17 : BitVec 64).toNat) = 17 by rfl,
          hsmall, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
        runtime_guards transfer
        rfl
      all_goals first
        | rfl
        | (intro hTypes; runtime_typed)
        | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
            rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        | runtime_finish [counterMemory]

theorem counterMemory_frame (args : Values Value Reg.count) (mem : Ram)
    (hbound : (args[4].get 64).toNat + 116 ≤ 2^64) :
    RamWriteFrame mem (counterMemory args mem) [span (args[4].get 64 + 88) 28] := by
  simp only [counterMemory]
  runtime_finish [span]

theorem counterMemory_loads (args : Values Value Reg.count) (mem : Ram) :
    memLoad (counterMemory args mem) (args[4].get 64 + 88) 64 =
      memLoad mem (args[4].get 64 + 72) 64 ∧
    memLoad (counterMemory args mem) (args[4].get 64 + 96) 32 =
      memLoad mem (args[4].get 64 + 60) 32 ∧
    memLoad (counterMemory args mem) (args[4].get 64 + 100) 32 =
      memLoad mem (args[4].get 64 + 56) 32 ∧
    memLoad (counterMemory args mem) (args[4].get 64 + 104) 32 =
      memLoad mem (args[4].get 64 + 52) 32 ∧
    memLoad (counterMemory args mem) (args[4].get 64 + 108) 32 = 1 ∧
    memLoad (counterMemory args mem) (args[4].get 64 + 112) 32 = 1 := by
  repeat' apply And.intro
  all_goals
    simp only [counterMemory]
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | (rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_diff
          simp only [add_sub_add_left']
          decide +kernel)])
  · rw [memLoad_memStore_within _ _ 32 0 (by bv_omega) (by decide) (by decide) (by decide)]
    rfl
  · rw [memLoad_memStore_within _ _ 32 4 (by bv_omega) (by decide) (by decide) (by decide)]
    rfl

end AesGcm.Proofs.Machine.Core.Decrypt
