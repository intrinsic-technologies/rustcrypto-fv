import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def counterMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp + 48) (args[5].get 64)
  let mem := memStore mem (sp + 56) (args[13].get 32)
  let mem := memStore mem (sp + 60) (args[15].get 32)
  let mem := memStore mem (sp + 64) (args[3].get 32)
  memStore mem (sp + 68) (0x100000001#64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem counter_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 + 48) 28)
    (hr : Readable mem (args[14].get 64) 16) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102a22 else .l1025c2), args, mem⟩ = .jump next ∧
      next.label = (if (args[12].get 64).toNat < 17 then
        (if use256 then .l102aaf else .l10264f) else
        (if use256 then .l102a59 else .l1025f9)) ∧
      next.store = counterMemory args mem ∧
      (next.arguments[0]'(by change 0 < 53; decide)).get 64 = 0x100000001 ∧
      (next.arguments[1]'(by change 1 < 53; decide)).get 64 = args[4].get 64 + 56 ∧
      (next.arguments[5]'(by change 5 < 53; decide)).get 64 = args[12].get 64 ∧
      (next.arguments[13]'(by change 13 < 53; decide)).get 64 =
        memLoad (counterMemory args mem) (args[14].get 64 + 8) 64 ∧
      (next.arguments[15]'(by change 15 < 53; decide)).get 64 =
        memLoad (counterMemory args mem) (args[14].get 64) 64 ∧
      (∀ r : Fin 53, r.val ∈ [2,3,4,6,7,8,9,10,11,12,14,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  revert hstack hr
  refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 ↦ ?_) args
  clear args
  intro hstack hr
  let args : Values Value Reg.count := #v[a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52]
  change Writable code mem (a4.get 64 + 48) 28 at hstack
  change Readable mem (a14.get 64) 16 at hr
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102a22 else 0x1025c2) 55 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1025c2 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102a22 x hx))).apart
  have hget (v : Value) : (v.get 64).setWidth 32 = v.get 32 := setWidth_get v (by decide)
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    by_cases hsmall : (a12.get 64).toNat < 17
    all_goals
      runtime_context [hsmall]
      refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      case exec =>
        first
          | change LIR.program.runBlock (dialect code) ⟨.l1025c2, args, mem⟩ = _
          | change LIR.program.runBlock (dialect code) ⟨.l102a22, args, mem⟩ = _
        cfg_eval [cmpSpec_CF, hsmall]
        runtime_guards transfer
        rfl
      all_goals first
        | (intro hTypes; runtime_typed)
        | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
            rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
              rfl | rfl | rfl | rfl | rfl <;> rfl)
        | (try simp only [counterMemory, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, hsmall, Bool.false_eq_true, ↓reduceIte, hget] <;> runtime_finish [])

theorem counterMemory_frame (args : Values Value Reg.count) (mem : Ram)
    (hbound : (args[4].get 64).toNat + 76 ≤ 2^64) :
    RamWriteFrame mem (counterMemory args mem) [span (args[4].get 64 + 48) 28] := by
  simp only [counterMemory]
  runtime_finish [span]

theorem counterMemory_loads (args : Values Value Reg.count) (mem : Ram) :
    memLoad (counterMemory args mem) (args[4].get 64 + 48) 64 = args[5].get 64 ∧
    memLoad (counterMemory args mem) (args[4].get 64 + 56) 32 = args[13].get 32 ∧
    memLoad (counterMemory args mem) (args[4].get 64 + 60) 32 = args[15].get 32 ∧
    memLoad (counterMemory args mem) (args[4].get 64 + 64) 32 = args[3].get 32 ∧
    memLoad (counterMemory args mem) (args[4].get 64 + 68) 32 = 1 ∧
    memLoad (counterMemory args mem) (args[4].get 64 + 72) 32 = 1 := by
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

end AesGcm.Proofs.Machine.Core.Encrypt
