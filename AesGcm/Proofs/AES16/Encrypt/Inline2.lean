import AesGcm.Proofs.AES16.MixColumns
import AesGcm.Proofs.AES16.Encrypt.Memory
import AesGcm.Proofs.Machine.LIR.Fn105100
import AesGcm.Proofs.Machine.LIR.Fn106960
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

attribute [local irreducible] memStore memLoad

private theorem rotateRowsAndColumns12_machine (x : BitVec 16) :
    (x.rotateLeft 14 &&& 0xcccc ||| x.rotateLeft 10 &&& 0x3333) =
      rotateRowsAndColumns12 x := by
  have h14 : x.rotateLeft 14 = x.rotateRight 2 := BitVec.or_comm _ _
  have h10 : x.rotateLeft 10 = x.rotateRight 6 := BitVec.or_comm _ _
  rw [h14, h10]
  exact BitVec.or_comm _ _

private theorem inline2_rangeApart128 {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x105243 551 := by
  have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l105243 x hx))
  have hlen : LIR.bytes_l105243.length = 551 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

private theorem inline2_rangeApart256 {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x106ab8 555 := by
  have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l106ab8 x hx))
  have hlen : LIR.bytes_l106ab8.length = 555 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

set_option hygiene false in
local macro "inline2_post" : tactic =>
  `(tactic| (
  refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · first
    | rfl
    | (change (⟨64, a4.get 64⟩ : Value) = ⟨64, a4.get 64 + 0⟩; rw [add_zero_lit])
  · change (⟨64, _⟩ : Value) = ⟨64, base⟩
    runtime_finish []
  · first
    | rfl
    | (change (⟨64, a4.get 64⟩ : Value) = ⟨64, a4.get 64 + 0⟩; rw [add_zero_lit])
  · runtime_typed
  · aes16_words
    runtime_finish_all [Vector.getElem_ofFn, setWidth_mergeGPR16,
      BitVec.setWidth_and, BitVec.setWidth_or, BitVec.setWidth_xor,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, setWidth16_memLoad32,
      xorPlanes, AES16.mixColumns2, mixColumnsCircuit_machine,
      rotateRowsAndColumns12_machine, rotateRows2, hrotate8]
    all_goals ac_rfl
  · runtime_finish []
  · runtime_finish [span]
  ))

set_option maxHeartbeats 1600000 in
theorem inline_mixColumns2 (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (planes keys : Planes16)
    (base : BitVec 64)
    (hTypes : GPRsTyped args)
    (hStack : Writable code mem (args[4].get 64 - 8) (if use256 then 64 else 56))
    (hSlot : memLoad mem (args[4].get 64 + (if use256 then 48 else 40)) 64 = base)
    (hRead : Readable mem
      (base + (args[12].get 64 <<< 1) + (if use256 then 18 else 32)) 16)
    (hApart : (args[4].get 64).toNat + (if use256 then 48 else 40) ≤
        (base + (args[12].get 64 <<< 1) + (if use256 then 18 else 32)).toNat ∨
      (base + (args[12].get 64 <<< 1) + (if use256 then 18 else 32)).toNat + 16 ≤
        (args[4].get 64 - 8).toNat)
    (hWords : WordsAt mem (args[4].get 64 + (if use256 then 8 else 0)) 16
      (Vector.ofFn planes))
    (hKeys : WordsAt mem
      (base + (args[12].get 64 <<< 1) + (if use256 then 18 else 32)) 16
      (Vector.ofFn keys)) :
    ∃ (loc : LIR.lifted.Location) (frame : LIR.lifted.StackFrame),
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l106ab8 else .l105243), args, mem⟩ = .call loc frame ∧
      loc.label = .l100b10 ∧
      frame = { target := (if use256 then .l106ce3 else .l10546a), kept := #v[], arity := rfl, guard := some ⟨64, (if use256 then 0x106ce3 else 0x10546a)⟩ } ∧
      loc.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      loc.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + (if use256 then 8 else 0)⟩ ∧
      loc.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩ ∧
      loc.arguments[3]'(by change 3 < 53; decide) = ⟨64, base⟩ ∧
      loc.arguments[12]'(by change 12 < 53; decide) = args[12] ∧
      loc.arguments[14]'(by change 14 < 53; decide) = ⟨64, args[4].get 64 + (if use256 then 8 else 0)⟩ ∧
      loc.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      loc.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      loc.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      loc.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      GPRsTyped loc.arguments ∧
      WordsAt loc.store (args[4].get 64 + (if use256 then 8 else 0)) 16
        (Vector.ofFn (xorPlanes (mixColumns2 planes) keys)) ∧
      memLoad loc.store (args[4].get 64 - 8) 64 = (if use256 then 0x106ce3 else 0x10546a) ∧
      RamWriteFrame mem loc.store [span (args[4].get 64 - 8) (if use256 then 56 else 48)] := by
  dsimp only [LIR.lifted]
  revert hTypes hStack hSlot hRead hApart hWords hKeys
  refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
    a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
  clear args
  intro hTypes hStack hSlot hRead hApart hWords hKeys
  change Writable code mem (a4.get 64 - 8) (if use256 then 64 else 56) at hStack
  change memLoad mem (a4.get 64 + (if use256 then 48 else 40)) 64 = base at hSlot
  change Readable mem (base + (a12.get 64 <<< 1) + (if use256 then 18 else 32)) 16 at hRead
  change (a4.get 64).toNat + (if use256 then 48 else 40) ≤
      (base + (a12.get 64 <<< 1) + (if use256 then 18 else 32)).toNat ∨
    (base + (a12.get 64 <<< 1) + (if use256 then 18 else 32)).toNat + 16 ≤
      (a4.get 64 - 8).toNat at hApart
  change WordsAt mem (a4.get 64 + (if use256 then 8 else 0)) 16
    (Vector.ofFn planes) at hWords
  change WordsAt mem (base + (a12.get 64 <<< 1) + (if use256 then 18 else 32)) 16
    (Vector.ofFn keys) at hKeys
  have hrotate8 (x : BitVec 16) : x.rotateLeft 8 = x.rotateRight 8 := BitVec.or_comm _ _
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ite_false, ite_true] at *
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
      [wordAddr, Vector.getElem_ofFn, Nat.reduceMul, Nat.reduceDiv, BitVec.reduceOfNat,
       add_zero_lit, BitVec.add_assoc, BitVec.reduceAdd]
      at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    simp (config := { bitVecOfNat := false }) only [← BitVec.add_assoc]
      at hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7
    runtime_context [hSlot, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
      hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
  · have hhelperApart := @inline2_rangeApart128 code hcode
    refine ⟨?loc128, ?frame128, ?execution128, ?rest128⟩
    case execution128 =>
      change LIR.program.runBlock (dialect code) ⟨.l105243, _, mem⟩ = _
      cfg_eval
      runtime_guards call
      rfl
    case rest128 =>
      inline2_post
  · have hhelperApart := @inline2_rangeApart256 code hcode
    refine ⟨?loc256, ?frame256, ?execution256, ?rest256⟩
    case execution256 =>
      change LIR.program.runBlock (dialect code) ⟨.l106ab8, _, mem⟩ = _
      cfg_eval
      runtime_guards call
      rfl
    case rest256 =>
      inline2_post

end AesGcm.Proofs.Machine.AES16.Encrypt
