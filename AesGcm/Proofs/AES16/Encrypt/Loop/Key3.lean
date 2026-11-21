import AesGcm.Proofs.AES16.MixColumns
import AesGcm.Proofs.Machine.LIR.Fn105100
import AesGcm.Proofs.Machine.LIR.Fn106960
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16 AES16

attribute [local irreducible] memStore memLoad

set_option hygiene false in
local macro "key3_proof" entry:term "," pc:num "," len:num "," hc:ident "," bytes:ident : tactic => `(tactic| (
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hReadLow := hRead.low
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n $pc $len := by
    have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x ($hc:ident x hx))
    have hl : ($bytes:ident).length = $len := by decide +kernel
    rw [hl] at hx
    exact hx.apart
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
      BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
  simp (config := { bitVecOfNat := false }) only [← BitVec.add_assoc]
    at hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
  runtime_context [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · change LIR.program.runBlock (dialect code) ⟨$entry, _, mem⟩ = _
    cfg_eval
    runtime_guards call
    rfl
  · refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · change (⟨64, a14.get 64⟩ : Value) = ⟨64, _⟩
      rw [hBuffer]
      rfl
    · rintro ⟨r, hrBound⟩ hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · aes16_words
      all_goals runtime_finish [Vector.getElem_ofFn, xorPlanes,
        BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
      all_goals rfl
    · runtime_finish []
    · runtime_finish [span]
  ))

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem key3_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (planes keys : Planes16)
    (hTypes : GPRsTyped args)
    (hStack : Writable code mem (args[4].get 64 - 8) (if use256 then 32 else 24))
    (hRead : Readable mem
      (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 34 else 48)) 16)
    (hApart : (args[4].get 64 - 8).toNat + (if use256 then 32 else 24) ≤
        (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 34 else 48)).toNat ∨
      (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 34 else 48)).toNat + 16 ≤
        (args[4].get 64 - 8).toNat)
    (hBuffer : args[14].get 64 = args[4].get 64 + (if use256 then 8 else 0))
    (hWords : WordsAt mem (args[4].get 64 + (if use256 then 8 else 0)) 16
      (Vector.ofFn planes))
    (hKeys : WordsAt mem
      (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 34 else 48)) 16
      (Vector.ofFn keys)) :
    ∃ (next : LIR.lifted.Location) (frame : LIR.lifted.StackFrame),
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l106ceb else .l105472), args, mem⟩ = .call next frame ∧
      next.label = .l100b10 ∧
      frame = { target := (if use256 then .l106d50 else .l1054d6), kept := #v[], arity := rfl, guard := some ⟨64, (if use256 then 0x106d50 else 0x1054d6)⟩ } ∧
      next.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      next.arguments[7]'(by change 7 < 53; decide) =
        ⟨64, args[4].get 64 + (if use256 then 8 else 0)⟩ ∧
      next.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
        next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      WordsAt next.store (args[4].get 64 + (if use256 then 8 else 0)) 16
        (Vector.ofFn (xorPlanes planes keys)) ∧
      memLoad next.store (args[4].get 64 - 8) 64 =
        (if use256 then 0x106d50 else 0x1054d6) ∧
      RamWriteFrame mem next.store
        [span (args[4].get 64 - 8) (if use256 then 32 else 24)] := by
  dsimp only [LIR.lifted]
  revert hTypes hStack hRead hApart hBuffer hWords hKeys
  refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
    a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
  clear args
  intro hTypes hStack hRead hApart hBuffer hWords hKeys
  change Writable code mem (a4.get 64 - 8) (if use256 then 32 else 24) at hStack
  change Readable mem (a3.get 64 + (a12.get 64 <<< 1) + (if use256 then 34 else 48)) 16 at hRead
  change (a4.get 64 - 8).toNat + (if use256 then 32 else 24) ≤
      (a3.get 64 + (a12.get 64 <<< 1) + (if use256 then 34 else 48)).toNat ∨
    (a3.get 64 + (a12.get 64 <<< 1) + (if use256 then 34 else 48)).toNat + 16 ≤
      (a4.get 64 - 8).toNat at hApart
  change a14.get 64 = a4.get 64 + (if use256 then 8 else 0) at hBuffer
  change WordsAt mem (a4.get 64 + (if use256 then 8 else 0)) 16 (Vector.ofFn planes) at hWords
  change WordsAt mem (a3.get 64 + (a12.get 64 <<< 1) + (if use256 then 34 else 48)) 16
    (Vector.ofFn keys) at hKeys
  cases use256
  all_goals simp (config := { bitVecOfNat := false }) only
    [Bool.false_eq_true, ↓reduceIte, add_zero_lit] at *
  · key3_proof (.l105472), 0x105472, 100, LIR.code_l105472, LIR.bytes_l105472
  · key3_proof (.l106ceb), 0x106ceb, 101, LIR.code_l106ceb, LIR.bytes_l106ceb

set_option hygiene false in
local macro "key1_sbox_proof" entry:term "," pc:num "," len:num "," hc:ident "," bytes:ident : tactic => `(tactic| (
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n $pc $len := by
    have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x ($hc:ident x hx))
    have hl : ($bytes:ident).length = $len := by decide +kernel
    rw [hl] at hx
    exact hx.apart
  have hw0 := hWords 0 (by decide)
  have hw1 := hWords 1 (by decide)
  have hw2 := hWords 2 (by decide)
  have hw3 := hWords 3 (by decide)
  have hw4 := hWords 4 (by decide)
  have hw5 := hWords 5 (by decide)
  have hw6 := hWords 6 (by decide)
  have hw7 := hWords 7 (by decide)
  simp (config := { bitVecOfNat := false }) only
    [wordAddr, Nat.reduceDiv, Nat.reduceMul, Vector.getElem_ofFn, BitVec.reduceOfNat,
      BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit]
    at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7
  runtime_context [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · change LIR.program.runBlock (dialect code) ⟨$entry, _, mem⟩ = _
    cfg_eval
    runtime_guards call
    rfl
  · refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · first | rfl | (change (⟨64, a4.get 64⟩ : Value) = ⟨64, a4.get 64 + 0⟩; rw [add_zero_lit])
    · rintro ⟨r, hrBound⟩ hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · aes16_words
      all_goals runtime_finish [Vector.getElem_ofFn]
    · runtime_finish []
    · runtime_finish [span]
  ))

set_option maxHeartbeats 800000 in
theorem key1_sbox_call_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (planes : Planes16)
    (hTypes : GPRsTyped args)
    (hStack : Writable code mem (args[4].get 64 - 8) (if use256 then 32 else 24))
    (hWords : WordsAt mem (args[4].get 64 + (if use256 then 8 else 0)) 16
      (Vector.ofFn planes)) :
    ∃ (next : LIR.lifted.Location) (frame : LIR.lifted.StackFrame),
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l106aa9 else .l105236), args, mem⟩ = .call next frame ∧
      next.label = .l100b10 ∧
      frame = { target := (if use256 then .l106ab8 else .l105243), kept := #v[], arity := rfl, guard := some ⟨64, (if use256 then 0x106ab8 else 0x105243)⟩ } ∧
      next.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      next.arguments[7]'(by change 7 < 53; decide) =
        ⟨64, args[4].get 64 + (if use256 then 8 else 0)⟩ ∧
      next.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
        next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      WordsAt next.store (args[4].get 64 + (if use256 then 8 else 0)) 16
        (Vector.ofFn planes) ∧
      memLoad next.store (args[4].get 64 - 8) 64 =
        (if use256 then 0x106ab8 else 0x105243) ∧
      RamWriteFrame mem next.store [span (args[4].get 64 - 8) 8] := by
  dsimp only [LIR.lifted]
  revert hTypes hStack hWords
  refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
    a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
  clear args
  intro hTypes hStack hWords
  change Writable code mem (a4.get 64 - 8) (if use256 then 32 else 24) at hStack
  change WordsAt mem (a4.get 64 + (if use256 then 8 else 0)) 16 (Vector.ofFn planes) at hWords
  cases use256
  all_goals simp (config := { bitVecOfNat := false }) only
    [Bool.false_eq_true, ↓reduceIte, add_zero_lit] at *
  · key1_sbox_proof (.l105236), 0x105236, 13, LIR.code_l105236, LIR.bytes_l105236
  · key1_sbox_proof (.l106aa9), 0x106aa9, 15, LIR.code_l106aa9, LIR.bytes_l106aa9

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
