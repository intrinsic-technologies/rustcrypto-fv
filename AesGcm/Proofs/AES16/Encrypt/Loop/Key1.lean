import AesGcm.Proofs.AES16.Encrypt.State
import AesGcm.Proofs.AES16.MixColumns
import AesGcm.Proofs.Machine.LIR.Fn105100
import AesGcm.Proofs.Machine.LIR.Fn106960
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16 AES16

attribute [local irreducible] memStore memLoad

set_option hygiene false in
local macro "key1_proof" entry:term "," stop:num "," exitLabel:term "," nextLabel:term "," pc:num "," len:num "," codeLemma:ident : tactic => `(tactic| (
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n $pc $len := by
    have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x ($codeLemma:ident x hx))
    change StoreOk code m a n $pc $len at hx
    exact hx.apart
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hReadLow := hRead.low
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
  simp (config := { bitVecOfNat := false }) only
    [wordAddr, Nat.reduceDiv, Nat.reduceMul, Vector.getElem_ofFn, BitVec.reduceOfNat,
      BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit]
    at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
  simp (config := { bitVecOfNat := false }) only [← BitVec.add_assoc]
    at hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
  runtime_context [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
    hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
  refine ⟨⟨(if a12.get 64 = $stop then $exitLabel else $nextLabel),?_,?_⟩, ?_, ?_, ?_⟩
  rotate_left 2
  · change LIR.program.runBlock (dialect code) ⟨$entry, _, mem⟩ = _
    cfg_eval []
    runtime_guards branch
    simp only [cmpSpec_ZF,beq_iff_eq]
    split
    · rename_i hc
      rw [ite_eq_left hc]
    · rename_i hc
      rw [ite_eq_right hc]
  · rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨r, hrBound⟩ hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · aes16_words
      all_goals runtime_finish [Vector.getElem_ofFn, xorPlanes, setWidth_mergeGPR16,
        BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
      all_goals rfl
    · intro p
      have hp : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals runtime_finish [planeReg, Vector.getElem_ofFn, xorPlanes,
        show (0 : Fin 53).val = 0 from rfl,
        show (1 : Fin 53).val = 1 from rfl,
        show (2 : Fin 53).val = 2 from rfl,
        show (6 : Fin 53).val = 6 from rfl,
        show (7 : Fin 53).val = 7 from rfl,
        show (8 : Fin 53).val = 8 from rfl,
        show (9 : Fin 53).val = 9 from rfl,
        show (10 : Fin 53).val = 10 from rfl,
        setWidth_mergeGPR16, BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le,
        BitVec.setWidth_eq]
      all_goals rfl
    · runtime_finish [span]
    ))

set_option maxHeartbeats 2400000 in
theorem key1_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (planes keys : Planes16)
    (hTypes : GPRsTyped args)
    (hStack : Writable code mem (args[4].get 64) (if use256 then 24 else 16))
    (hRead : Readable mem
      (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 2 else 16)) 16)
    (hApart : (args[4].get 64).toNat + (if use256 then 24 else 16) ≤
        (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 2 else 16)).toNat ∨
      (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 2 else 16)).toNat + 16 ≤
        (args[4].get 64).toNat)
    (hWords : WordsAt mem (args[4].get 64 + (if use256 then 8 else 0)) 16
      (Vector.ofFn planes))
    (hKeys : WordsAt mem
      (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 2 else 16)) 16
      (Vector.ofFn keys)) :
    ∃ next : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l106a19 else .l1051a8), args, mem⟩ = .jump next ∧
      next.label = (if args[12].get 64 = (if use256 then 103 else 64)
        then (if use256 then .l106ebc else .l105636)
        else (if use256 then .l106aa9 else .l105236)) ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      WordsAt next.store (args[4].get 64 + (if use256 then 8 else 0)) 16
        (Vector.ofFn (xorPlanes planes keys)) ∧
      (∀ p : Fin 8, ((next.arguments[(planeReg p).val]'(planeReg p).isLt).get 64).setWidth 16 =
        xorPlanes planes keys p) ∧
      RamWriteFrame mem next.store [span (args[4].get 64 + (if use256 then 8 else 0)) 16] := by
  dsimp only [LIR.lifted]
  revert hTypes hStack hRead hApart hWords hKeys
  refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
    a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
  clear args
  intro hTypes hStack hRead hApart hWords hKeys
  change Writable code mem (a4.get 64) (if use256 then 24 else 16) at hStack
  change Readable mem (a3.get 64 + (a12.get 64 <<< 1) + (if use256 then 2 else 16)) 16 at hRead
  change (a4.get 64).toNat + (if use256 then 24 else 16) ≤
      (a3.get 64 + (a12.get 64 <<< 1) + (if use256 then 2 else 16)).toNat ∨
    (a3.get 64 + (a12.get 64 <<< 1) + (if use256 then 2 else 16)).toNat + 16 ≤
      (a4.get 64).toNat at hApart
  change WordsAt mem (a4.get 64 + (if use256 then 8 else 0)) 16 (Vector.ofFn planes) at hWords
  change WordsAt mem (a3.get 64 + (a12.get 64 <<< 1) + (if use256 then 2 else 16)) 16
    (Vector.ofFn keys) at hKeys
  cases use256
  all_goals simp (config := { bitVecOfNat := false }) only
    [Bool.false_eq_true, ↓reduceIte, add_zero_lit] at *
  · key1_proof (.l1051a8), 64, (.l105636), (.l105236), 0x1051a8, 142, LIR.code_l1051a8
  · key1_proof (.l106a19), 103, (.l106ebc), (.l106aa9), 0x106a19, 144, LIR.code_l106a19

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
