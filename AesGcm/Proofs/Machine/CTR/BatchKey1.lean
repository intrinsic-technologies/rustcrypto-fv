import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.Fixslice.Operations

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice

def batchPlaneRegister (p : Fin 8) : Fin 53 :=
  (#v[10, 9, 8, 7, 6, 2, 1, 0] : Vector (Fin 53) 8)[p]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 3200000 in
theorem batch_key1 (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp index : BitVec 64)
    (planes keys : Planes)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hIndex : args[5].get 64 = index)
    (hStack : Writable code mem (sp + 8) 64)
    (hKeyRead : Readable mem (sp + (index <<< 3) + (if use256 then 344 else 408)) 64)
    (hApart : (sp + 8).toNat + 64 ≤
        (sp + (index <<< 3) + (if use256 then 344 else 408)).toNat ∨
      (sp + (index <<< 3) + (if use256 then 344 else 408)).toNat + 64 ≤ (sp + 8).toNat)
    (hWords : WordsAt mem (sp + 8) 64 (Vector.ofFn planes))
    (hKeys : WordsAt mem (sp + (index <<< 3) + (if use256 then 344 else 408)) 64 (Vector.ofFn keys)) :
    ∃ next : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l109037 else .l107ba7), args, mem⟩ = .jump next ∧
      next.label = (if index = (if use256 then 104 else 64) then
        (if use256 then .l108600 else .l107170)
        else (if use256 then .l1090d1 else .l107c41)) ∧
      WordsAt next.store (sp + 8) 64 (Vector.ofFn (xorPlanes planes keys)) ∧
      (∀ p : Fin 8, (next.arguments[batchPlaneRegister p]).get 64 = xorPlanes planes keys p) ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store [span (sp + 8) 64] := by
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
        (if use256 then 0x109037 else 0x107ba7) 154 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107ba7 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l109037 x hx))).apart
  by_cases hLast : index = (if use256 then 104 else 64)
  all_goals cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart hLast hApart hKeyRead hKeyLow hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    simp only [BitVec.reduceAdd] at hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    simp only [BitVec.ofNat_eq_ofNat] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    runtime_context [hsp, hIndex, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l107ba7, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l109037, args, mem⟩ = _
      cfg_eval [LIR.program, hsp, hIndex]
      runtime_guards branch
      runtime_finish [hLast]
      rfl
    · simp only [Bool.false_eq_true, ↓reduceIte, hLast]
      rfl
    · intro i hi
      rw [Vector.getElem_ofFn]
      change memLoad (_ : Ram) ((sp + 8) + BitVec.ofNat 64 (8 * i)) 64 =
        planes ⟨i, by omega⟩ ^^^ keys ⟨i, by omega⟩
      have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [Nat.reduceMul, BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.add_zero]
      runtime_finish_all []
      all_goals
        simp only [← BitVec.ofNat_eq_ofNat] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
        simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
      all_goals rfl
    · intro p
      rcases p with ⟨p, hp⟩
      have he : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      runtime_finish_all [batchPlaneRegister, xorPlanes]
      all_goals
        simp only [hLast, BitVec.add_assoc] at hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7 ⊢
        simp only [← BitVec.ofNat_eq_ofNat] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
        simp only [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

end AesGcm.Proofs.Machine.CTR
