import AesGcm.Proofs.Machine.CTR.KeyLoop
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def entryMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let m1 := memStore mem (sp - 8) (args[5].get 64)
  let m2 := memStore m1 (sp - 16) (args[15].get 64)
  let m3 := memStore m2 (sp - 24) (args[14].get 64)
  let m4 := memStore m3 (sp - 32) (args[13].get 64)
  let m5 := memStore m4 (sp - 40) (args[12].get 64)
  memStore m5 (sp - 48) (args[3].get 64)

set_option maxHeartbeats 1200000 in
theorem entry_widening (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (schedule : BitVec 64)
    (hTypes : GPRsTyped args)
    (hStack : Writable code mem (args[4].get 64 - 48) 48)
    (hSlot : Readable mem (args[7].get 64) 8)
    (hWord : memLoad mem (args[7].get 64) 64 = schedule)
    (hApart : (args[7].get 64).toNat + 8 ≤ (args[4].get 64 - 48).toNat ∨
      (args[4].get 64).toNat ≤ (args[7].get 64).toNat) :
    ∃ next : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1084e0 else .l107050), args, mem⟩ = .jump next ∧
      next.label = wideningLabel use256 ∧
      next.store = entryMemory args mem ∧
      wideningRegisters next.arguments schedule
        (args[4].get 64 - (if use256 then 0x908 else 0x708)) 0 = next.arguments ∧
      next.arguments[3]'(by change 3 < 53; decide) = ⟨64, args[6].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [5,8,9,10,11,12,13,14,15,22,39,50,51] →
        next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store [span (args[4].get 64 - 48) 48] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hSlotLow := hSlot.low
  have hStackBase : (args[4].get 64 - 48).toNat + 48 = (args[4].get 64).toNat := by
    bv_omega
  have hRoom : 48 ≤ (args[4].get 64).toNat := by omega
  have hApartNat : (args[7].get 64).toNat + 8 ≤ (args[4].get 64).toNat - 48 ∨
      (args[4].get 64).toNat ≤ (args[7].get 64).toNat := by omega
  have hSaved : RamWriteFrame mem (entryMemory args mem)
      [span (args[4].get 64 - 48) 48] := by
    unfold entryMemory
    runtime_finish [span]
  have hSlotSaved : memLoad (entryMemory args mem) (args[7].get 64) 64 = schedule := by
    rw [hSaved.memLoad_eq]
    · exact hWord
    · refine ⟨by omega, ?_⟩
      intro region hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl
      change (args[7].get 64).toNat + 8 ≤ (args[4].get 64 - 48).toNat ∨
        (args[4].get 64 - 48).toNat + 48 ≤ (args[7].get 64).toNat
      omega
  runtime_context [hWord, hSlotSaved]
  cases use256
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x107050 64 := by
      have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107050 x hx))
      have hl : LIR.bytes_l107050.length = 64 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l107050, args, mem⟩ = _
      cfg_eval []
      runtime_guards transfer
      rfl
    all_goals first
      | rfl
      | runtime_typed
      | (apply wideningRegisters_eq <;> first | rfl | (apply congrArg (fun x ↦ Value.mk 64 x); exact hSlotSaved))
      | (rintro ⟨r,hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [entryMemory, span]
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x1084e0 64 := by
      have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1084e0 x hx))
      have hl : LIR.bytes_l1084e0.length = 64 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l1084e0, args, mem⟩ = _
      cfg_eval []
      runtime_guards transfer
      rfl
    all_goals first
      | rfl
      | runtime_typed
      | (apply wideningRegisters_eq <;> first | rfl | (apply congrArg (fun x ↦ Value.mk 64 x); exact hSlotSaved))
      | (rintro ⟨r,hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [entryMemory, span]

end AesGcm.Proofs.Machine.CTR
