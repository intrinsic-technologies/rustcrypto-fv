import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Fn109980.Frame

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem driver_batch_prepare_runBlock (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (sp src : BitVec 64) (hsp : args[4].get 64 = sp)
    (hsrc : args[3].get 64 = src) (htypes : GPRsTyped args) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l1099b4, args, mem⟩ =
        .jump ⟨.l1099c0, nextArgs, mem⟩ ∧
      nextArgs[12] = ⟨64, sp + 32⟩ ∧ nextArgs[6] = ⟨64, src⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 4, 5, 7, 13, 14, 15, 22, 39, 50, 51] → nextArgs[r] = args[r]) ∧ GPRsTyped nextArgs := by
  cfg_eval [hsp, hsrc]
  refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩
  · rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · apply GPRsTyped.of_updates htypes [6, 12]
    · rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl <;> rfl
    · rintro ⟨r,hr⟩ hout
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
      have hc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 7 ∨ r = 8 ∨
          r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

def driverBatchFrame : StackFrame Value LIR.Label signature Reg.count :=
  { target := .l1099cc, kept := #v[], arity := rfl, guard := some ⟨64, 0x1099cc⟩ }

set_option maxHeartbeats 400000 in
theorem driver_batch_call_runBlock (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp src ptr : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsrc : args[6].get 64 = src)
    (hptr : args[12].get 64 = ptr) (htypes : GPRsTyped args)
    (hw : Writable code mem (sp - 8) 8) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l1099c0, args, mem⟩ =
        .call ⟨.l109ac0, nextArgs, memStore mem (sp - 8) (0x1099cc#64)⟩ driverBatchFrame ∧
      nextArgs[4] = ⟨64, sp - 8⟩ ∧ nextArgs[7] = ⟨64, ptr⟩ ∧
      nextArgs[15] = ⟨64, src + 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 6, 12, 13, 14, 22, 39, 50, 51] → nextArgs[r] = args[r]) ∧
      GPRsTyped nextArgs := by
  have hs := storeOk_of_codeRange hw (fun x hx => hcode x (LIR.code_l1099c0 x hx))
  have hlen : LIR.bytes_l1099c0.length = 12 := by decide +kernel
  rw [hlen] at hs
  have hretStore : StoreOk code mem (sp - 8) 8 0x1099c7 5 :=
    storeOk_of_writable hw (RangeApart.right_sub hs.apart (off := 7) (by decide))
  cfg_eval [hsp, hsrc, hptr]
  simp only [BitVec.ofNat_eq_ofNat] at hretStore ⊢
  simp only [hretStore, ite_true]
  refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · apply GPRsTyped.of_updates htypes [4, 7, 15]
    · rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl <;> rfl
    · rintro ⟨r,hr⟩ hout
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
      have hc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 6 ∨ r = 8 ∨
          r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 400000 in
theorem driver_batch_return_runBlock (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (remaining nextSrc : BitVec 64) (h5 : args[5].get 64 = remaining)
    (h15 : args[15].get 64 = nextSrc) (hTypes : GPRsTyped args) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l1099cc, args, mem⟩ =
        (if remaining - 64 = 0 then .jump ⟨.l1099d5, nextArgs, mem⟩
          else .jump ⟨.l1099c0, nextArgs, mem⟩) ∧
      nextArgs[5] = ⟨64, remaining - 64⟩ ∧ nextArgs[6] = ⟨64, nextSrc⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 4, 7, 12, 13, 14, 15, 22, 39, 50, 51] → nextArgs[r] = args[r]) ∧
      GPRsTyped nextArgs := by
  have he : remaining + 0xffffffffffffffc0 = remaining - 64 := by bv_omega
  by_cases hz : remaining - 64 = 0
  all_goals
    cfg_eval [h5, h15, he, addSpec]
    simp only [BitVec.ofNat_eq_ofNat] at hz he ⊢
    simp only [hz, Bool.not_eq_true', beq_eq_false_iff_ne, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
    try rw [ite_eq_left hz]
    refine ⟨_, rfl, ?_, rfl, ?_, ?_⟩
    · rfl
    · rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed

theorem driver_tail_dispatch_runBlock (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (bytes : BitVec 64) (h13 : args[13].get 64 = bytes)
    (hTypes : GPRsTyped args) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l1099d5, args, mem⟩ =
        (if bytes &&& 0x30 = 0 then .jump ⟨.l109aaa, nextArgs, mem⟩
          else .jump ⟨.l1099df, nextArgs, mem⟩) ∧
      nextArgs[13] = ⟨64, bytes &&& 0x30⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 4, 5, 6, 7, 12, 14, 15, 22, 39, 50, 51] → nextArgs[r] = args[r]) ∧
      GPRsTyped nextArgs := by
  by_cases hz : bytes &&& 0x30 = 0
  all_goals
    cfg_eval [h13, andFlags]
    simp only [BitVec.ofNat_eq_ofNat] at hz ⊢
    simp only [hz, beq_iff_eq, beq_self_eq_true, ite_true, ite_false]
    try rw [ite_eq_left hz]
    refine ⟨_, rfl, rfl, ?_, ?_⟩
    · rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed

theorem driver_tail_prepare_runBlock (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (sp src : BitVec 64) (hsp : args[4].get 64 = sp)
    (hsrc : args[3].get 64 = src) (hTypes : GPRsTyped args)
    (hr : Readable mem (sp + 24) 8) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l1099df, args, mem⟩ = .jump ⟨.l109a00, nextArgs, mem⟩ ∧
      nextArgs[3] = ⟨64, src + ((memLoad mem (sp + 24) 64 &&& 0x7fffffffffffffc) <<< 4)⟩ ∧
      nextArgs[12] = ⟨64, 0⟩ ∧ nextArgs[15] = ⟨64, sp + 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [4, 5, 6, 7, 13, 14, 22, 39, 50, 51] → nextArgs[r] = args[r]) ∧
      GPRsTyped nextArgs := by
  have hload : LoadOk mem (sp + 24) 8 := LoadOk.of_offsets hr (addr_self _) (addr_self _) (by decide)
  cfg_eval [hsp, hsrc]
  simp only [BitVec.ofNat_eq_ofNat] at hload ⊢
  simp only [hload, ite_true]
  refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · runtime_typed

set_option maxHeartbeats 400000 in
theorem driver_tail_return_runBlock (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (offset limit : BitVec 64) (h12 : args[12].get 64 = offset)
    (h13 : args[13].get 64 = limit) (hTypes : GPRsTyped args) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l109a9d, args, mem⟩ =
        (if limit - (offset + 16) = 0 then .jump ⟨.l109aaa, nextArgs, mem⟩
          else .jump ⟨.l109a00, nextArgs, mem⟩) ∧
      nextArgs[12] = ⟨64, offset + 16⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 4, 5, 6, 7, 13, 14, 15, 22, 39, 50, 51] → nextArgs[r] = args[r]) ∧
      GPRsTyped nextArgs := by
  by_cases hz : limit - (offset + 16) = 0
  all_goals
    cfg_eval [h12, h13, addSpec, cmpSpec, subSpec]
    simp only [BitVec.ofNat_eq_ofNat] at hz ⊢
    simp only [hz, Bool.not_eq_true', beq_eq_false_iff_ne, beq_self_eq_true, Bool.true_eq_false, ite_true, ite_false]
    try rw [ite_eq_left hz]
    refine ⟨_, rfl, rfl, ?_, ?_⟩
    · rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed

end AesGcm.Proofs.Machine.GHASHUpdate
