import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.Fixslice.Operations

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem batch_key0 (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (planes keys : Planes)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hStack : Writable code mem (sp + 8) 64)
    (hKeyRead : Readable mem (sp + 344) 64)
    (hWords : WordsAt mem (sp + 8) 64 (Vector.ofFn planes))
    (hKeys : WordsAt mem (sp + 344) 64 (Vector.ofFn keys)) :
    ∃ next : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l108fa2 else .l107b12), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l109010 else .l107b80) ∧
      next.arguments[5]'(by change 5 < 53; decide) = ⟨64, if use256 then 8 else 0⟩ ∧
      (next.arguments[if use256 then 15 else 14]'(by change (if use256 then 15 else 14) < 53; cases use256 <;> decide)).get 64 = planes 7 ∧
      WordsAt next.store (sp + 8) 64
        (Vector.ofFn fun p : Fin 7 ↦ xorPlanes planes keys ⟨p.val, by omega⟩) ∧
      (∀ r : Fin 53, r.val ∈ [4,12,13,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store [span (sp + 8) 56] := by
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
  runtime_context [hsp, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
  have hRange {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n
        (if use256 then 0x108fa2 else 0x107b12) 110 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107b12 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l108fa2 x hx))).apart
  cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l107b12, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l108fa2, args, mem⟩ = _
      cfg_eval [LIR.program, hsp]
      runtime_guards transfer
      rfl
    · rfl
    · rfl
    · simp only [Bool.false_eq_true, ↓reduceIte]
      runtime_finish []
      exact hw7
    · intro i hi
      rw [Vector.getElem_ofFn]
      change memLoad (_ : Ram) ((sp + 8) + BitVec.ofNat 64 (8 * i)) 64 =
        planes ⟨i, by omega⟩ ^^^ keys ⟨i, by omega⟩
      have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [Nat.reduceMul, BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.add_zero]
      runtime_finish_all []
      all_goals first
        | exact congr (congrArg (fun a b : BitVec 64 ↦ a ^^^ b) hw0) hk0
        | exact congr (congrArg (fun a b : BitVec 64 ↦ a ^^^ b) hw1) hk1
        | exact congr (congrArg (fun a b : BitVec 64 ↦ a ^^^ b) hw2) hk2
        | exact congr (congrArg (fun a b : BitVec 64 ↦ a ^^^ b) hw3) hk3
        | exact congr (congrArg (fun a b : BitVec 64 ↦ a ^^^ b) hw4) hk4
        | exact congr (congrArg (fun a b : BitVec 64 ↦ a ^^^ b) hw5) hk5
        | exact congr (congrArg (fun a b : BitVec 64 ↦ a ^^^ b) hw6) hk6
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

end AesGcm.Proofs.Machine.CTR
