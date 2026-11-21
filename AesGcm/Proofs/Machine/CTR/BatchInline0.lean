import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.AES64.MixColumns

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice AES64

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
theorem batch_inline0 (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp index : BitVec 64)
    (planes keys : Planes)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hIndex : args[5].get 64 = index)
    (hStack : Writable code mem (sp + 8) (if use256 then 128 else 64))
    (hKeyRead : Readable mem (sp + (index <<< 3) + (if use256 then 536 else 600)) 64)
    (hApart : (sp + 8).toNat + (if use256 then 128 else 64) ≤
        (sp + (index <<< 3) + (if use256 then 536 else 600)).toNat ∨
      (sp + (index <<< 3) + (if use256 then 536 else 600)).toNat + 64 ≤ (sp + 8).toNat)
    (hWords : WordsAt mem (sp + 8) 64 (Vector.ofFn planes))
    (hKeys : WordsAt mem (sp + (index <<< 3) + (if use256 then 536 else 600)) 64 (Vector.ofFn keys)) :
    ∃ next : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1093a3 else .l107f13), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l109010 else .l107b80) ∧
      (∀ i (hi : i < 7), memLoad next.store (sp + 8 + BitVec.ofNat 64 (8 * i)) 64 =
        mixColumns0 planes ⟨i, by omega⟩ ^^^ keys ⟨i, by omega⟩) ∧
      (next.arguments[if use256 then 15 else 14]'(by change (if use256 then 15 else 14) < 53; cases use256 <;> decide)).get 64 = mixColumns0 planes 7 ∧
      memLoad next.store (sp + 64) 64 = mixColumns0 planes 7 ∧
      next.arguments[5]'(by change 5 < 53; decide) = ⟨64, index + 32⟩ ∧
      (∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store
        (if use256 then [span (sp + 8) 64, span (sp + 120) 16] else [span (sp + 8) 64]) := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hKeyLow := hKeyRead.low
  have hw0 := hWords 0 (by decide)
  have hw1 := hWords 1 (by decide)
  have hw2 := hWords 2 (by decide)
  have hw3 := hWords 3 (by decide)
  have hw4 := hWords 4 (by decide)
  have hw5 := hWords 5 (by decide)
  have hw6 := hWords 6 (by decide)
  have hw7 := hWords 7 (by decide)
  have hk0 := hKeys 0 (by decide)
  have hk1 := hKeys 1 (by decide)
  have hk2 := hKeys 2 (by decide)
  have hk3 := hKeys 3 (by decide)
  have hk4 := hKeys 4 (by decide)
  have hk5 := hKeys 5 (by decide)
  have hk6 := hKeys 6 (by decide)
  have hk7 := hKeys 7 (by decide)
  simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, Vector.getElem_ofFn,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
  have hRange {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n
        (if use256 then 0x1093a3 else 0x107f13) (if use256 then 358 else 332) := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107f13 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1093a3 x hx))).apart
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart hStack hStackRead hStackLow hApart hKeyRead hKeyLow hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    simp only [BitVec.reduceAdd] at hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    simp only [← BitVec.ofNat_eq_ofNat] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    runtime_context [hsp, hIndex, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l107f13, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l1093a3, args, mem⟩ = _
      cfg_eval [LIR.program, hsp, hIndex]
      runtime_guards jump
      rfl
    · rfl
    · intro i hi
      have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      runtime_finish_all [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd,
        Fixslice.mixColumns0, mixColumnsCircuit_machine, ← rotateRows1_machine, ← rotateRows2_machine]
      all_goals first | rfl | ac_rfl
    · dsimp only [Value.get, getElem, Vector.get, Array.getInternal, List.get, Fin.cast]
      runtime_finish [Fixslice.mixColumns0, mixColumnsCircuit_machine, ← rotateRows1_machine, ← rotateRows2_machine]
      all_goals first | rfl | ac_rfl
    · runtime_finish [Fixslice.mixColumns0, mixColumnsCircuit_machine, ← rotateRows1_machine, ← rotateRows2_machine]
      all_goals first | rfl | ac_rfl
    · rfl
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

end AesGcm.Proofs.Machine.CTR
