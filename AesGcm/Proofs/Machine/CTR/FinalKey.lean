import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.Fixslice.Operations

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice

def batchFinalKeyFrame (use256 : Bool) : StackFrame Value LIR.Label signature Reg.count :=
  { target := if use256 then .l1087a5 else .l107315, kept := #v[], arity := rfl,
    guard := some ⟨64, if use256 then 0x1087a5 else 0x107315⟩ }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
theorem batch_final_key (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (planes keys : Planes)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hBase : args[3].get 64 = sp + 8)
    (hStack : Writable code mem (sp - 8) 80)
    (hKeyRead : Readable mem (sp + (if use256 then 1240 else 984)) 64)
    (hApart : (sp - 8).toNat + 80 ≤
        (sp + (if use256 then 1240 else 984)).toNat ∨
      (sp + (if use256 then 1240 else 984)).toNat + 64 ≤ (sp - 8).toNat)
    (hWords : WordsAt mem (sp + 8) 64 (Vector.ofFn planes))
    (hKeys : WordsAt mem (sp + (if use256 then 1240 else 984)) 64 (Vector.ofFn keys)) :
    ∃ callee : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l108728 else .l107298), args, mem⟩ = .call callee (batchFinalKeyFrame use256) ∧
      callee.label = .l10a210 ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, sp + 152⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, sp + 8⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, 8⟩ ∧
      WordsAt callee.store (sp + 8) 64 (Vector.ofFn (xorPlanes planes keys)) ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      GPRsTyped callee.arguments ∧
      RamWriteFrame mem callee.store [span (sp - 8) 8, span (sp + 8) 64] ∧
      memLoad callee.store (sp - 8) 64 = (if use256 then 0x1087a5 else 0x107315) := by
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
        (if use256 then 0x108728 else 0x107298) 125 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107298 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l108728 x hx))).apart
  cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart hApart hKeyRead hKeyLow hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    simp only [BitVec.reduceAdd] at hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    simp only [BitVec.ofNat_eq_ofNat] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    runtime_context [hsp, hBase, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l107298, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l108728, args, mem⟩ = _
      cfg_eval [LIR.program, batchFinalKeyFrame, hsp, hBase]
      runtime_guards call
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro i hi
      rw [Vector.getElem_ofFn]
      change memLoad (_ : Ram) ((sp + 8) + BitVec.ofNat 64 (8 * i)) 64 =
        planes ⟨i, by omega⟩ ^^^ keys ⟨i, by omega⟩
      have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      runtime_finish_all [wordAddr, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
        BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, xorPlanes]
      all_goals
        simp only [← BitVec.ofNat_eq_ofNat] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
        simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]

    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]
    · exact memLoad_memStore_eq _ _ rfl (by decide) (by decide)

end AesGcm.Proofs.Machine.CTR
