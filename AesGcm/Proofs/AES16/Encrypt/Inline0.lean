import AesGcm.Proofs.AES16.MixColumns
import AesGcm.Proofs.AES16.Encrypt.Memory
import AesGcm.Proofs.Machine.LIR.Fn105100
import AesGcm.Proofs.Machine.LIR.Fn106960
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

private theorem inline0_128_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x1054d6 352 := by
  have hx := storeOk_of_codeRange h
    (fun x hx => hcode x (LIR.code_l1054d6 x hx))
  have hlen : LIR.bytes_l1054d6.length = 352 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

private theorem inline0_256_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x106d50 364 := by
  have hx := storeOk_of_codeRange h
    (fun x hx => hcode x (LIR.code_l106d50 x hx))
  have hlen : LIR.bytes_l106d50.length = 364 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

set_option hygiene false in
local macro "inline0_proof" entry:term "," stack:num "," off:num "," key:num ","
    apart:ident : tactic =>
  `(tactic| (
    revert hTypes hStack hRead hApart hWords hKeys
    refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
      a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
    clear args
    intro hTypes hStack hRead hApart hWords hKeys
    change Writable code mem (a4.get 64) $stack at hStack
    change Readable mem (a3.get 64 + (a12.get 64 <<< 1) + $key) 16 at hRead
    change (a4.get 64).toNat + $stack ≤ (a3.get 64 + (a12.get 64 <<< 1) + $key).toNat ∨
      (a3.get 64 + (a12.get 64 <<< 1) + $key).toNat + 16 ≤ (a4.get 64).toNat at hApart
    have hStackRead := hStack.readable
    have hStackLow := hStackRead.low
    have hReadLow := hRead.low
    have hw0 := hWords 0 (by decide)
    change memLoad mem (a4.get 64 + $off + 0) 16 = planes 0 at hw0
    simp (config := { bitVecOfNat := false }) only
      [BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit] at hw0
    have hw1 := hWords 1 (by decide)
    change memLoad mem (a4.get 64 + $off + 2) 16 = planes 1 at hw1
    simp (config := { bitVecOfNat := false }) only
      [BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit] at hw1
    have hw2 := hWords 2 (by decide)
    change memLoad mem (a4.get 64 + $off + 4) 16 = planes 2 at hw2
    simp (config := { bitVecOfNat := false }) only
      [BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit] at hw2
    have hw3 := hWords 3 (by decide)
    change memLoad mem (a4.get 64 + $off + 6) 16 = planes 3 at hw3
    simp (config := { bitVecOfNat := false }) only
      [BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit] at hw3
    have hw4 := hWords 4 (by decide)
    change memLoad mem (a4.get 64 + $off + 8) 16 = planes 4 at hw4
    simp (config := { bitVecOfNat := false }) only
      [BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit] at hw4
    have hw5 := hWords 5 (by decide)
    change memLoad mem (a4.get 64 + $off + 10) 16 = planes 5 at hw5
    simp (config := { bitVecOfNat := false }) only
      [BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit] at hw5
    have hw6 := hWords 6 (by decide)
    change memLoad mem (a4.get 64 + $off + 12) 16 = planes 6 at hw6
    simp (config := { bitVecOfNat := false }) only
      [BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit] at hw6
    have hw7 := hWords 7 (by decide)
    change memLoad mem (a4.get 64 + $off + 14) 16 = planes 7 at hw7
    simp (config := { bitVecOfNat := false }) only
      [BitVec.add_assoc, BitVec.reduceAdd, add_zero_lit] at hw7
    have hk0 := hKeys 0 (by decide)
    change memLoad mem (a3.get 64 + (a12.get 64 <<< 1) + $key + 0) 16 = keys 0 at hk0
    have hk1 := hKeys 1 (by decide)
    change memLoad mem (a3.get 64 + (a12.get 64 <<< 1) + $key + 2) 16 = keys 1 at hk1
    have hk2 := hKeys 2 (by decide)
    change memLoad mem (a3.get 64 + (a12.get 64 <<< 1) + $key + 4) 16 = keys 2 at hk2
    have hk3 := hKeys 3 (by decide)
    change memLoad mem (a3.get 64 + (a12.get 64 <<< 1) + $key + 6) 16 = keys 3 at hk3
    have hk4 := hKeys 4 (by decide)
    change memLoad mem (a3.get 64 + (a12.get 64 <<< 1) + $key + 8) 16 = keys 4 at hk4
    have hk5 := hKeys 5 (by decide)
    change memLoad mem (a3.get 64 + (a12.get 64 <<< 1) + $key + 10) 16 = keys 5 at hk5
    have hk6 := hKeys 6 (by decide)
    change memLoad mem (a3.get 64 + (a12.get 64 <<< 1) + $key + 12) 16 = keys 6 at hk6
    have hk7 := hKeys 7 (by decide)
    change memLoad mem (a3.get 64 + (a12.get 64 <<< 1) + $key + 14) 16 = keys 7 at hk7
    simp (config := { bitVecOfNat := false }) only [BitVec.add_assoc,
      BitVec.reduceAdd, add_zero_lit] at hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    simp (config := { bitVecOfNat := false }) only [← BitVec.add_assoc]
      at hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    have hhelperApart := @$apart:ident code hcode
    runtime_context [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩
    rotate_left
    ·
      change LIR.program.runBlock (dialect code) ⟨$entry, _, _⟩ = .jump _
      cfg_eval
      runtime_guards transfer
      rfl
    · rfl
    · rfl
    · rfl
    · runtime_finish []
    ·
      runtime_finish [mixColumns0, mixColumnsCircuit_machine, rotateRows1,
      rotateRows2, setWidth_mergeGPR16, BitVec.setWidth_xor,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, setWidth16_memLoad32]
      all_goals simp (config := { bitVecOfNat := false }) only [BitVec.rotateLeft,
        BitVec.rotateRight, BitVec.rotateLeftAux,
        BitVec.rotateRightAux, Nat.reduceMod, Nat.reduceSub]
      all_goals ac_rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · runtime_typed
    ·
      aes16_words
      all_goals simp (config := { bitVecOfNat := false }) only [Vector.getElem_ofFn,
        Fin.reduceFinMk, Nat.reduceEqDiff, ite_true, ite_false]
      all_goals runtime_finish [setWidth_mergeGPR16, BitVec.setWidth_xor,
        BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, setWidth16_memLoad32]
      all_goals simp (config := { bitVecOfNat := false }) only [mixColumns0,
        mixColumnsCircuit_machine, rotateRows1, rotateRows2,
        BitVec.rotateLeft, BitVec.rotateRight, BitVec.rotateLeftAux,
        BitVec.rotateRightAux, Nat.reduceMod, Nat.reduceSub,
        show (0 : Fin 8).val = 0 from rfl,
        show (1 : Fin 8).val = 1 from rfl,
        show (2 : Fin 8).val = 2 from rfl,
        show (3 : Fin 8).val = 3 from rfl,
        show (4 : Fin 8).val = 4 from rfl,
        show (5 : Fin 8).val = 5 from rfl,
        show (6 : Fin 8).val = 6 from rfl,
        show (7 : Fin 8).val = 7 from rfl]
      all_goals ac_rfl
    · runtime_finish [span]
  ))

set_option maxHeartbeats 1600000 in
theorem inline_mixColumns0 (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (planes keys : Planes16)
    (hTypes : GPRsTyped args)
    (hStack : Writable code mem (args[4].get 64) (if use256 then 64 else 40))
    (hRead : Readable mem
      (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 50 else 64)) 16)
    (hApart : (args[4].get 64).toNat + (if use256 then 64 else 40) ≤
        (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 50 else 64)).toNat ∨
      (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 50 else 64)).toNat + 16 ≤
        (args[4].get 64).toNat)
    (hWords : WordsAt mem (args[4].get 64 + (if use256 then 8 else 0)) 16
      (Vector.ofFn planes))
    (hKeys : WordsAt mem
      (args[3].get 64 + (args[12].get 64 <<< 1) + (if use256 then 50 else 64)) 16
      (Vector.ofFn keys)) :
    ∃ loc : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l106d50 else .l1054d6), args, mem⟩ = .jump loc ∧
      loc.label = (if use256 then .l1069f0 else .l105180) ∧
      loc.arguments[4]'(by change 4 < 53; decide) = args[4] ∧
      loc.arguments[3]'(by change 3 < 53; decide) = args[3] ∧
      loc.arguments[12]'(by change 12 < 53; decide) = ⟨64, args[12].get 64 + 32⟩ ∧
      ((loc.arguments[0]'(by change 0 < 53; decide)).get 64).setWidth 16 = mixColumns0 planes 7 ∧
      loc.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      loc.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      loc.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      loc.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      GPRsTyped loc.arguments ∧
      WordsAt loc.store (args[4].get 64 + (if use256 then 8 else 0)) 16
        (Vector.ofFn fun p : Fin 8 ↦ if p.val = 7 then mixColumns0 planes p
          else mixColumns0 planes p ^^^ keys p) ∧
      RamWriteFrame mem loc.store (if use256 then
        [span (args[4].get 64) 48, span (args[4].get 64 + 60) 4]
        else [span (args[4].get 64) 40]) := by
  dsimp only [LIR.lifted]
  cases use256
  · simp (config := { bitVecOfNat := false }) only [Bool.false_eq_true, ite_false]
      at hStack hRead hApart hWords hKeys ⊢
    inline0_proof LIR.Label.l1054d6, 40, 0, 64, inline0_128_rangeApart
  · simp (config := { bitVecOfNat := false }) only [ite_true]
      at hStack hRead hApart hWords hKeys ⊢
    inline0_proof LIR.Label.l106d50, 64, 8, 50, inline0_256_rangeApart

end AesGcm.Proofs.Machine.AES16.Encrypt
