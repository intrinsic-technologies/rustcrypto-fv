import AesGcm.Proofs.AES16.MixColumns
import AesGcm.Proofs.Machine.LIR.Fn105100
import AesGcm.Proofs.Machine.LIR.Fn106960
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

set_option hygiene false in
local macro "key0_proof" result:ident apart:ident "at" lab:term "with" len:num "," buf:num "," _slot:num : tactic => `(tactic| (
    revert hTypes hStack hRead hApart hWords hKeys
    refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
      a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
      a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
    clear args
    intro hTypes hRead hKeys hStack hApart hWords
    simp only [Bool.false_eq_true, ↓reduceIte] at hStack hApart hWords ⊢
    let inputs : Values Value Reg.count := #v[a0, a1, a2, a3, a4, a5, a6, a7, a8,
      a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23, a24,
      a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39,
      a40, a41, a42, a43, a44, a45, a46, a47, a48, a49, a50, a51, a52]
    change Writable code mem (a4.get 64) $len at hStack
    change Readable mem (a3.get 64) 16 at hRead
    change (a4.get 64).toNat + $len ≤ (a3.get 64).toNat ∨
      (a3.get 64).toNat + 16 ≤ (a4.get 64).toNat at hApart
    change WordsAt mem (a4.get 64 + $buf) 16 (Vector.ofFn planes) at hWords
    change WordsAt mem (a3.get 64) 16 (Vector.ofFn keys) at hKeys
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
    simp (config := { bitVecOfNat := false }) only [wordAddr, Nat.reduceDiv, Vector.getElem_ofFn, Nat.reduceMul,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, add_zero_lit, BitVec.ofNat_eq_ofNat] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    first
    | (change memLoad mem (a4.get 64) 16 = planes 0 at hw0
       change memLoad mem (a4.get 64 + 2) 16 = planes 1 at hw1
       change memLoad mem (a4.get 64 + 4) 16 = planes 2 at hw2
       change memLoad mem (a4.get 64 + 6) 16 = planes 3 at hw3
       change memLoad mem (a4.get 64 + 8) 16 = planes 4 at hw4
       change memLoad mem (a4.get 64 + 10) 16 = planes 5 at hw5
       change memLoad mem (a4.get 64 + 12) 16 = planes 6 at hw6
       change memLoad mem (a4.get 64 + 14) 16 = planes 7 at hw7)
    | (change memLoad mem (a4.get 64 + 8) 16 = planes 0 at hw0
       change memLoad mem (a4.get 64 + 10) 16 = planes 1 at hw1
       change memLoad mem (a4.get 64 + 12) 16 = planes 2 at hw2
       change memLoad mem (a4.get 64 + 14) 16 = planes 3 at hw3
       change memLoad mem (a4.get 64 + 16) 16 = planes 4 at hw4
       change memLoad mem (a4.get 64 + 18) 16 = planes 5 at hw5
       change memLoad mem (a4.get 64 + 20) 16 = planes 6 at hw6
       change memLoad mem (a4.get 64 + 22) 16 = planes 7 at hw7)
    change memLoad mem (a3.get 64) 16 = keys 0 at hk0
    change memLoad mem (a3.get 64 + 2) 16 = keys 1 at hk1
    change memLoad mem (a3.get 64 + 4) 16 = keys 2 at hk2
    change memLoad mem (a3.get 64 + 6) 16 = keys 3 at hk3
    change memLoad mem (a3.get 64 + 8) 16 = keys 4 at hk4
    change memLoad mem (a3.get 64 + 10) 16 = keys 5 at hk5
    change memLoad mem (a3.get 64 + 12) 16 = keys 6 at hk6
    change memLoad mem (a3.get 64 + 14) 16 = keys 7 at hk7
    runtime_context [hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
    refine ⟨?$result:ident, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    ·
      have hhelperApart := @$apart:ident
      change LIR.program.runBlock (dialect code) ⟨$lab, _, mem⟩ = _
      cfg_eval
      runtime_guards transfer
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · runtime_finish [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
      all_goals exact hw7
    · rfl
    · rfl
    · rfl
    · rfl
    · runtime_typed
    ·
      aes16_words
      all_goals runtime_finish [Vector.getElem_ofFn, BitVec.setWidth_setWidth_of_le,
        BitVec.setWidth_eq, BitVec.setWidth_xor, ↓reduceIte]
      all_goals rfl
    · runtime_finish []
    · runtime_finish [span]

))

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem key0_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (planes keys : Planes16)
    (hTypes : GPRsTyped args)
    (hStack : Writable code mem (args[4].get 64) (if use256 then 56 else 48))
    (hRead : Readable mem (args[3].get 64) 16)
    (hApart : (args[4].get 64).toNat + (if use256 then 56 else 48) ≤
        (args[3].get 64).toNat ∨ (args[3].get 64).toNat + 16 ≤ (args[4].get 64).toNat)
    (hWords : WordsAt mem (args[4].get 64 + (if use256 then 8 else 0)) 16
      (Vector.ofFn planes))
    (hKeys : WordsAt mem (args[3].get 64) 16 (Vector.ofFn keys)) :
    ∃ loc : LIR.lifted.Location,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l106997 else .l105134), args, mem⟩ = .jump loc ∧
      loc.label = (if use256 then .l1069f0 else .l105180) ∧
      loc.arguments[4]'(by change 4 < 53; decide) = args[4] ∧
      loc.arguments[3]'(by change 3 < 53; decide) = args[3] ∧
      loc.arguments[12]'(by change 12 < 53; decide) = ⟨64, (if use256 then 7 else 0)⟩ ∧
      ((loc.arguments[0]'(by change 0 < 53; decide)).get 64).setWidth 16 = planes 7 ∧
      loc.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      loc.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      loc.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      loc.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      GPRsTyped loc.arguments ∧
      WordsAt loc.store (args[4].get 64 + (if use256 then 8 else 0)) 16
        (Vector.ofFn fun p : Fin 8 ↦ if p.val = 7 then planes p else planes p ^^^ keys p) ∧
      memLoad loc.store (args[4].get 64 + (if use256 then 48 else 40)) 64 = args[3].get 64 ∧
      RamWriteFrame mem loc.store [span (args[4].get 64) (if use256 then 56 else 48)] := by
  have apart128 {mem : Ram} {a : BitVec 64} {n : Nat} (h : Writable code mem a n) :
      RangeApart a n 0x105134 76 := by
    have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l105134 x hx))
    have hl : LIR.bytes_l105134.length = 76 := by decide +kernel
    rw [hl] at hx
    exact hx.apart
  have apart256 {mem : Ram} {a : BitVec 64} {n : Nat} (h : Writable code mem a n) :
      RangeApart a n 0x106997 89 := by
    have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l106997 x hx))
    have hl : LIR.bytes_l106997.length = 89 := by decide +kernel
    rw [hl] at hx
    exact hx.apart
  cases use256
  · key0_proof loc128 apart128 at (.l105134) with 48, 0, 40
  · key0_proof loc256 apart256 at (.l106997) with 56, 8, 48

end AesGcm.Proofs.Machine.AES16.Encrypt
