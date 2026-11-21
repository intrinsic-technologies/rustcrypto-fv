import AesGcm.Proofs.AES16.Encrypt.State
import AesGcm.Proofs.AES16.MixColumns
import AesGcm.Proofs.Machine.LIR.Fn105100
import AesGcm.Proofs.Machine.LIR.Fn106960
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.AES16.Encrypt.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16 AES16

attribute [local irreducible] memStore memLoad

private theorem header128_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x105180 32 := by
  have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l105180 x hx))
  have hlen : LIR.bytes_l105180.length = 32 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

private theorem header256_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x1069f0 33 := by
  have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1069f0 x hx))
  have hlen : LIR.bytes_l1069f0.length = 33 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

set_option hygiene false in
local macro "header_proof" entry:term "," apart:ident : tactic => `(tactic| (
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hReadLow := hRead.low
  have hhelperApart := @$apart:ident code hcode
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
  have hTail16 : a0.get 16 = planes 7 := by
    simpa only [setWidth_get (n := 16) (m := 64) a0 (by decide)] using hTail
  runtime_context [hSlot, hKey, hTail16, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7]
  refine ⟨?_, ?_, ?_, ?_⟩
  rotate_left 2
  · change LIR.program.runBlock (dialect code) ⟨$entry, _, mem⟩ = _
    cfg_eval
    runtime_guards call
    rfl
  · refine ⟨rfl, rfl, rfl, ?_, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · first | rfl | (change (⟨64, a4.get 64⟩ : Value) = ⟨64, a4.get 64 + 0⟩; rw [add_zero_lit])
    · change (⟨64, _⟩ : Value) = ⟨64, base⟩
      runtime_finish []
    · first | rfl | (change (⟨64, a4.get 64⟩ : Value) = ⟨64, a4.get 64 + 0⟩; rw [add_zero_lit])
    · rintro ⟨r, hrBound⟩ hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · aes16_words
      all_goals runtime_finish [Vector.getElem_ofFn, setWidth_mergeGPR16,
        BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
        show (0 : Fin 8).val = 0 from rfl, show (1 : Fin 8).val = 1 from rfl,
        show (2 : Fin 8).val = 2 from rfl, show (3 : Fin 8).val = 3 from rfl,
        show (4 : Fin 8).val = 4 from rfl, show (5 : Fin 8).val = 5 from rfl,
        show (6 : Fin 8).val = 6 from rfl, show (7 : Fin 8).val = 7 from rfl]
      all_goals rfl
    · runtime_finish []
    · runtime_finish [span]
  ))

set_option maxHeartbeats 800000 in
theorem header_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (base : BitVec 64)
    (planes : Planes16) (keyTail : BitVec 16)
    (hTypes : GPRsTyped args)
    (hStack : Writable code mem (args[4].get 64 - 8) (if use256 then 64 else 56))
    (hSlot : memLoad mem (args[4].get 64 + (if use256 then 48 else 40)) 64 = base)
    (hRead : Readable mem (base + (args[12].get 64 <<< 1) + (if use256 then 0 else 14)) 2)
    (hKey : memLoad mem (base + (args[12].get 64 <<< 1) + (if use256 then 0 else 14)) 16 = keyTail)
    (hTail : (args[0].get 64).setWidth 16 = planes 7)
    (hWords : WordsAt mem (args[4].get 64 + (if use256 then 8 else 0)) 16
      (Vector.ofFn planes)) :
    ∃ (next : LIR.lifted.Location) (frame : LIR.lifted.StackFrame),
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1069f0 else .l105180), args, mem⟩ = .call next frame ∧
      next.label = .l100b10 ∧
      frame = { target := (if use256 then .l106a11 else .l1051a0), kept := #v[], arity := rfl, guard := some ⟨64, (if use256 then 0x106a11 else 0x1051a0)⟩ } ∧
      next.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      next.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[4].get 64 + (if use256 then 8 else 0)⟩ ∧
      next.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩ ∧
      next.arguments[3]'(by change 3 < 53; decide) = ⟨64, base⟩ ∧
      next.arguments[12]'(by change 12 < 53; decide) = args[12] ∧
      next.arguments[14]'(by change 14 < 53; decide) = ⟨64, args[4].get 64 + (if use256 then 8 else 0)⟩ ∧
      (∀ r : Fin 53, r.val ∈ [5,12,13,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      WordsAt next.store (args[4].get 64 + (if use256 then 8 else 0)) 16
        (Vector.ofFn fun p : Fin 8 ↦ if p.val = 7 then planes p ^^^ keyTail else planes p) ∧
      memLoad next.store (args[4].get 64 - 8) 64 = (if use256 then 0x106a11 else 0x1051a0) ∧
      RamWriteFrame mem next.store [span (args[4].get 64 - 8) (if use256 then 32 else 24)] := by
  dsimp only [LIR.lifted]
  revert hTypes hStack hSlot hRead hKey hTail hWords
  refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
    a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
  clear args
  intro hTypes hStack hSlot hRead hKey hTail hWords
  change Writable code mem (a4.get 64 - 8) (if use256 then 64 else 56) at hStack
  change memLoad mem (a4.get 64 + (if use256 then 48 else 40)) 64 = base at hSlot
  change Readable mem (base + (a12.get 64 <<< 1) + (if use256 then 0 else 14)) 2 at hRead
  change memLoad mem (base + (a12.get 64 <<< 1) + (if use256 then 0 else 14)) 16 = keyTail at hKey
  change (a0.get 64).setWidth 16 = planes 7 at hTail
  change WordsAt mem (a4.get 64 + (if use256 then 8 else 0)) 16
    (Vector.ofFn planes) at hWords
  cases use256
  all_goals simp (config := { bitVecOfNat := false }) only [Bool.false_eq_true, ↓reduceIte, add_zero_lit] at *
  · header_proof (.l105180), header128_rangeApart
  · header_proof (.l1069f0), header256_rangeApart

end AesGcm.Proofs.Machine.AES16.Encrypt.Loop
