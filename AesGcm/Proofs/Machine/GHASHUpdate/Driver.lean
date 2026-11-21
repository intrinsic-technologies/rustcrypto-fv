import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Fn109980.Frame

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem driverEntry_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x109980 52 := by
  have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l109980 x hx))
  have hlen : LIR.bytes_l109980.length = 52 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

abbrev driverBatchBytes (count : BitVec 64) := 0x7fffffffffffffc0#64 &&& (count <<< 4)

def driverEntryArgs (args : Values Value Reg.count) (rsp src dst count : BitVec 64) :
    Values Value Reg.count :=
  #v[args[0], args[1], args[2], ⟨64, src⟩, ⟨64, rsp - 88⟩,
    ⟨64, driverBatchBytes count⟩, args[6], args[7], args[8], args[9],
    args[10], args[11], args[12], ⟨64, count <<< 4⟩, ⟨64, dst⟩,
    args[15], args[16], args[17], args[18], Value.ofBool (driverBatchBytes count == 0),
    args[20], args[21], args[22], args[23], args[24],
    args[25], args[26], args[27], args[28], args[29],
    args[30], args[31], args[32], args[33], args[34],
    args[35], args[36], args[37], args[38], args[39],
    args[40], args[41], args[42], args[43], args[44],
    args[45], args[46], args[47], args[48], args[49],
    args[50], args[51], args[52]]

def driverEntryMemory (args : Values Value Reg.count) (mem : Ram) (rsp dst count : BitVec 64) : Ram :=
  let mem := memStore mem (rsp - 8) (args[5].get 64)
  let mem := memStore mem (rsp - 16) (args[15].get 64)
  let mem := memStore mem (rsp - 24) (args[14].get 64)
  let mem := memStore mem (rsp - 32) (args[13].get 64)
  let mem := memStore mem (rsp - 40) (args[12].get 64)
  let mem := memStore mem (rsp - 48) (args[3].get 64)
  let mem := memStore mem (rsp - 56) dst
  memStore mem (rsp - 64) count

set_option maxHeartbeats 800000 in
theorem driver_entry_runBlock (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (rsp src dst count : BitVec 64)
    (hsp : args[4].get 64 = rsp) (hsrc : args[6].get 64 = src)
    (hdst : args[7].get 64 = dst) (hcount : args[2].get 64 = count)
    (htypes : GPRsTyped args) (hw : Writable code mem (rsp - 88) 88)
    (hroom : 88 ≤ rsp.toNat) :
    ∃ nextArgs : Values Value Reg.count, ∃ outMem : Ram,
      LIR.program.runBlock (dialect code) ⟨.l109980, args, mem⟩ =
        (if driverBatchBytes count = 0 then .jump ⟨.l1099d5, nextArgs, outMem⟩
          else .jump ⟨.l1099b4, nextArgs, outMem⟩) ∧
      nextArgs[4] = ⟨64, rsp - 88⟩ ∧ nextArgs[3] = ⟨64, src⟩ ∧
      nextArgs[14] = ⟨64, dst⟩ ∧ nextArgs[13] = ⟨64, count <<< 4⟩ ∧
      nextArgs[5] = ⟨64, driverBatchBytes count⟩ ∧
      (∀ r : Fin 53, r.val ∈ [2, 6, 7, 12, 15, 22, 39, 50, 51] → nextArgs[r] = args[r]) ∧
      GPRsTyped nextArgs ∧ RamWriteFrame mem outMem [span (rsp - 88) 88] ∧
      memLoad outMem (rsp - 64) 64 = count ∧ memLoad outMem (rsp - 56) 64 = dst ∧
      memLoad outMem (rsp - 48) 64 = args[3].get 64 ∧
      memLoad outMem (rsp - 40) 64 = args[12].get 64 ∧
      memLoad outMem (rsp - 32) 64 = args[13].get 64 ∧
      memLoad outMem (rsp - 24) 64 = args[14].get 64 ∧
      memLoad outMem (rsp - 16) 64 = args[15].get 64 ∧
      memLoad outMem (rsp - 8) 64 = args[5].get 64 := by
  have hhelperApart := @driverEntry_rangeApart code hcode
  have hsr := hw.readable
  have hsl := hsr.low
  runtime_context [hsp, hsrc, hdst, hcount]
  refine ⟨driverEntryArgs args rsp src dst count, driverEntryMemory args mem rsp dst count, ?execution, ?sp, ?src, ?dst, ?count, ?batch, ?preserved,
    ?typed, ?frame, ?words⟩
  all_goals dsimp only [driverEntryArgs, driverEntryMemory]
  case execution =>
    by_cases hz : driverBatchBytes count = 0
    all_goals
      simp only [hz, ite_true, ite_false]
      simp only [driverBatchBytes, BitVec.ofNat_eq_ofNat] at hz
      cfg_eval [hsp, hsrc, hdst, hcount, andFlags]
      simp only [driverBatchBytes, BitVec.ofNat_eq_ofNat, beq_iff_eq, hz, beq_self_eq_true, ite_true, ite_false]
      runtime_guards transfer
      rfl
  case sp => runtime_finish []
  case src => runtime_finish []
  case dst => runtime_finish []
  case count => runtime_finish []
  case batch => runtime_finish [driverBatchBytes]
  case preserved =>
    rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case typed =>
    apply GPRsTyped.of_updates htypes [3, 4, 5, 13, 14]
    · rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨r,hr⟩ hout
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
      have hc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨
          r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 15 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case frame => runtime_finish [span]
  case words =>
    repeat' apply And.intro
    all_goals runtime_finish []

set_option maxHeartbeats 400000 in
theorem driver_exit_runBlock (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (sp : BitVec 64) (hsp : args[4].get 64 = sp)
    (htypes : GPRsTyped args) (hr : Readable mem (sp + 40) 56)
    (hret : (memLoad mem (sp + 88) 64).toNat < 2^32) :
    ∃ o : Output Value Ram Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l109aaa, args, mem⟩ = .returned o ∧
      o.tag = some ⟨64, memLoad mem (sp + 88) 64⟩ ∧ o.store = mem ∧
      o.values[4] = ⟨64, sp + 96⟩ ∧
      o.values[3] = ⟨64, memLoad mem (sp + 40) 64⟩ ∧
      o.values[12] = ⟨64, memLoad mem (sp + 48) 64⟩ ∧
      o.values[13] = ⟨64, memLoad mem (sp + 56) 64⟩ ∧
      o.values[14] = ⟨64, memLoad mem (sp + 64) 64⟩ ∧
      o.values[15] = ⟨64, memLoad mem (sp + 72) 64⟩ ∧
      o.values[5] = ⟨64, memLoad mem (sp + 80) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [0, 1, 2, 6, 7, 8, 9, 10, 11, 22, 39, 50, 51] →
        o.values[r] = args[r]) ∧ GPRsTyped o.values := by
  have hlow := hr.low
  runtime_context [hsp]
  refine ⟨?out, ?execution, ?tag, ?store, ?sp, ?r3, ?r12, ?r13, ?r14, ?r15, ?r5,
    ?preserved, ?typed⟩
  case execution =>
    cfg_eval [hsp]
    runtime_guards returned
    rfl
  case tag => runtime_finish []
  case store => rfl
  case sp => runtime_finish []
  case r3 => runtime_finish []
  case r12 => runtime_finish []
  case r13 => runtime_finish []
  case r14 => runtime_finish []
  case r15 => runtime_finish []
  case r5 => runtime_finish []
  case preserved =>
    rintro ⟨r,hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case typed =>
    apply GPRsTyped.of_updates htypes [3, 4, 5, 12, 13, 14, 15]
    · rintro ⟨r,hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · rintro ⟨r,hr⟩ hout
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hout
      have hc : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨
          r = 10 ∨ r = 11 := by omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end AesGcm.Proofs.Machine.GHASHUpdate
