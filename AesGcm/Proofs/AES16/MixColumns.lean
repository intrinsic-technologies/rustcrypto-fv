import AesGcm.Proofs.Common.Bitwise
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.LIR.Fn100000.Frame
import AesGcm.Proofs.Machine.LIR.Fn100580.Frame
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values
import AesGcm.Proofs.AES16.MixColumnsAlgebra
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Copied.X86Proofs.Refine.Tactic

namespace AesGcm.Proofs.Machine.AES16

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open Lean Meta Elab Tactic
open AesGcm.Proofs.Machine.Fixslice16

theorem rotateRowsAndColumns11_machine (x : BitVec 16) :
    (x.rotateRight 1 &&& 0x8888 ||| x.rotateLeft 11 &&& 0x7777) =
      rotateRowsAndColumns11 x := by
  have h : x.rotateLeft 11 = x.rotateRight 5 := BitVec.or_comm _ _
  simp only [h, rotateRowsAndColumns11, BitVec.or_comm]

theorem rotateRowsAndColumns13_machine (x : BitVec 16) :
    (x.rotateLeft 13 &&& 0xeeee ||| x.rotateLeft 9 &&& 0x1111) =
      rotateRowsAndColumns13 x := by
  have h₁ : x.rotateLeft 13 = x.rotateRight 3 := BitVec.or_comm _ _
  have h₂ : x.rotateLeft 9 = x.rotateRight 7 := BitVec.or_comm _ _
  simp only [h₁, h₂, rotateRowsAndColumns13, BitVec.or_comm]

theorem rotateRowsAndColumns22_machine (x : BitVec 16) :
    (x.rotateLeft 10 &&& 0xcccc ||| x.rotateLeft 6 &&& 0x3333) =
      rotateRowsAndColumns22 x := by
  have h₁ : x.rotateLeft 10 = x.rotateRight 6 := BitVec.or_comm _ _
  have h₂ : x.rotateLeft 6 = x.rotateRight 10 := BitVec.or_comm _ _
  simp only [h₁, h₂, rotateRowsAndColumns22, BitVec.or_comm]

elab "aes16_words" : tactic => withMainContext do
  let g ← getMainGoal
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  unless ty.isAppOfArity ``WordsAt 5 do throwError "expected WordsAt"
  let args := ty.getAppArgs
  let some n := (← instantiateMVars args[3]!).nat? | throwError "expected literal length"
  let mut proof := mkAppN (mkConst ``WordsAt.from_end) args
  let mut goals := #[]
  for k in (List.range n).reverse do
    let hk ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit k, args[3]!])
    let f := mkAppN (mkConst ``WordsAt.from_succ) (args ++ #[mkNatLit k, hk])
    let w ← mkFreshExprSyntheticOpaqueMVar (← inferType f).bindingDomain!
    goals := goals.push w.mvarId!
    proof := mkApp2 f w proof
  let S ← Refine.Tactic.Shared.new #[]
  g.assign (mkAppN (mkConst ``WordsAt.of_from) (args.push proof))
  let mut remaining := []
  for w in goals.reverse do
    if let some w ← Refine.Tactic.simpShallow S.words w then
      remaining := remaining ++ [w]
  replaceMainGoal remaining

theorem mixColumnsCircuit_machine (first second : BitVec 16 → BitVec 16)
    (a : Planes16) (p : Fin 8) :
    mixColumnsCircuit first second a p =
      match p.val with
      | 0 => ((first (a 0)) ^^^ ((a 7) ^^^ (first (a 7)))) ^^^ (second ((a 0) ^^^ (first (a 0))))
      | 1 => ((((a 0) ^^^ (first (a 0))) ^^^ (first (a 1))) ^^^ ((a 7) ^^^ (first (a 7)))) ^^^ (second ((a 1) ^^^ (first (a 1))))
      | 2 => (((a 1) ^^^ (first (a 1))) ^^^ (first (a 2))) ^^^ (second ((a 2) ^^^ (first (a 2))))
      | 3 => (((first (a 3)) ^^^ ((a 2) ^^^ (first (a 2)))) ^^^ ((a 7) ^^^ (first (a 7)))) ^^^ (second ((a 3) ^^^ (first (a 3))))
      | 4 => (((first (a 4)) ^^^ ((a 3) ^^^ (first (a 3)))) ^^^ ((a 7) ^^^ (first (a 7)))) ^^^ (second ((a 4) ^^^ (first (a 4))))
      | 5 => (second ((a 5) ^^^ (first (a 5)))) ^^^ ((first (a 5)) ^^^ ((a 4) ^^^ (first (a 4))))
      | 6 => (second ((a 6) ^^^ (first (a 6)))) ^^^ ((first (a 6)) ^^^ ((a 5) ^^^ (first (a 5))))
      | _ => (second ((a 7) ^^^ (first (a 7)))) ^^^ ((first (a 7)) ^^^ ((a 6) ^^^ (first (a 6))))
    := by
  have hp : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by
    have := p.isLt
    omega
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (((first (a 0)) ^^^ ((a 7) ^^^ (first (a 7)))) ^^^ (second ((a 0) ^^^ (first (a 0))))) = (((first (a 0)) ^^^ ((a 7) ^^^ (first (a 7)))) ^^^ (second ((a 0) ^^^ (first (a 0)))))
    ac_rfl
  · change (((first (a 1)) ^^^ (((a 0) ^^^ (first (a 0))) ^^^ ((a 7) ^^^ (first (a 7))))) ^^^ (second ((a 1) ^^^ (first (a 1))))) = (((((a 0) ^^^ (first (a 0))) ^^^ (first (a 1))) ^^^ ((a 7) ^^^ (first (a 7)))) ^^^ (second ((a 1) ^^^ (first (a 1)))))
    ac_rfl
  · change (((first (a 2)) ^^^ ((a 1) ^^^ (first (a 1)))) ^^^ (second ((a 2) ^^^ (first (a 2))))) = ((((a 1) ^^^ (first (a 1))) ^^^ (first (a 2))) ^^^ (second ((a 2) ^^^ (first (a 2)))))
    ac_rfl
  · change (((first (a 3)) ^^^ (((a 2) ^^^ (first (a 2))) ^^^ ((a 7) ^^^ (first (a 7))))) ^^^ (second ((a 3) ^^^ (first (a 3))))) = ((((first (a 3)) ^^^ ((a 2) ^^^ (first (a 2)))) ^^^ ((a 7) ^^^ (first (a 7)))) ^^^ (second ((a 3) ^^^ (first (a 3)))))
    ac_rfl
  · change (((first (a 4)) ^^^ (((a 3) ^^^ (first (a 3))) ^^^ ((a 7) ^^^ (first (a 7))))) ^^^ (second ((a 4) ^^^ (first (a 4))))) = ((((first (a 4)) ^^^ ((a 3) ^^^ (first (a 3)))) ^^^ ((a 7) ^^^ (first (a 7)))) ^^^ (second ((a 4) ^^^ (first (a 4)))))
    ac_rfl
  · change (((first (a 5)) ^^^ ((a 4) ^^^ (first (a 4)))) ^^^ (second ((a 5) ^^^ (first (a 5))))) = ((second ((a 5) ^^^ (first (a 5)))) ^^^ ((first (a 5)) ^^^ ((a 4) ^^^ (first (a 4)))))
    ac_rfl
  · change (((first (a 6)) ^^^ ((a 5) ^^^ (first (a 5)))) ^^^ (second ((a 6) ^^^ (first (a 6))))) = ((second ((a 6) ^^^ (first (a 6)))) ^^^ ((first (a 6)) ^^^ ((a 5) ^^^ (first (a 5)))))
    ac_rfl
  · change (((first (a 7)) ^^^ ((a 6) ^^^ (first (a 6)))) ^^^ (second ((a 7) ^^^ (first (a 7))))) = ((second ((a 7) ^^^ (first (a 7)))) ^^^ ((first (a 7)) ^^^ ((a 6) ^^^ (first (a 6)))))
    ac_rfl

private theorem mixColumns1_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x100000 666 := by
  have hx := storeOk_of_codeRange h
    (fun x hx => hcode x (LIR.code_l100000 x hx))
  have hlen : LIR.bytes_l100000.length = 666 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

private theorem mixColumns3_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x100580 674 := by
  have hx := storeOk_of_codeRange h
    (fun x hx => hcode x (LIR.code_l100580 x hx))
  have hlen : LIR.bytes_l100580.length = 674 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

set_option hygiene false in
local macro "mixColumnsForward_proof" apart:ident : tactic =>
  `(tactic| (
  simp only [projectPlanes_mixColumns1, projectPlanes_mixColumns3, projectPlanes_widenPlanes]
  dsimp only [CallContract, LIR.lifted]
  intro fr ⟨lab, args, mem⟩ hl hs hf hTypes hpre
  dsimp only at hl hs hf hTypes hpre
  subst lab mem
  rcases hpre with ⟨hWords, hWrite, hApart⟩
  have hRead := hWrite.readable
  revert hf hTypes
  refine args_cases (fun a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
    a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34 a35
    a36 a37 a38 a39 a40 a41 a42 a43 a44 a45 a46 a47 a48 a49 a50 a51 a52 => ?_) args
  clear args
  intro hTypes hf
  change a4 = ⟨64, fr.rsp⟩ ∧ a22 = ⟨1, 0⟩ ∧ a1 = ⟨64, fr.rcx⟩ ∧
    a2 = ⟨64, fr.rdx⟩ ∧ a3 = ⟨64, fr.rbx⟩ ∧ a5 = ⟨64, fr.rbp⟩ ∧
    a6 = ⟨64, fr.rsi⟩ ∧ a7 = ⟨64, fr.rdi⟩ ∧ a8 = ⟨64, fr.r8⟩ ∧ a9 = ⟨64, fr.r9⟩ ∧
    a12 = ⟨64, fr.r12⟩ ∧ a13 = ⟨64, fr.r13⟩ ∧ a14 = ⟨64, fr.r14⟩ ∧ a15 = ⟨64, fr.r15⟩ ∧
    a39 = ⟨32, fr.mxcsr⟩ ∧ a50 = ⟨16, fr.ftw⟩ ∧ a51 = ⟨16, fr.fcw⟩ ∧
    Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 64) 64 ∧
    fr.low.toNat + 64 ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True at hf
  rcases hf with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    h39, h50, h51, hRetRead, hRet, hRetLow, hStack, hRoom, hAlign, _⟩
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hReadLow := hRead.low
  have hRetReadLow := hRetRead.low
  have hApartNum : fr.rsp.toNat + 8 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 16 ≤ fr.low.toNat := by
    have h := hApart (max fr.low.toNat fr.rdi.toNat)
    simp only [callStack, span, MemoryRegion.Disjoint, MemoryRegion.Contains] at hApart
    dsimp only [callStack, span, MemoryRegion.Contains] at h
    omega
  have hw0 := hWords 0 (by decide)
  change memLoad fr.original (fr.rdi + 0) 16 = planes 0 at hw0
  rw [add_zero_lit] at hw0
  have hw1 : memLoad fr.original (fr.rdi + 2) 16 = planes 1 := hWords 1 (by decide)
  have hw2 : memLoad fr.original (fr.rdi + 4) 16 = planes 2 := hWords 2 (by decide)
  have hw3 : memLoad fr.original (fr.rdi + 6) 16 = planes 3 := hWords 3 (by decide)
  have hw4 : memLoad fr.original (fr.rdi + 8) 16 = planes 4 := hWords 4 (by decide)
  have hw5 : memLoad fr.original (fr.rdi + 10) 16 = planes 5 := hWords 5 (by decide)
  have hw6 : memLoad fr.original (fr.rdi + 12) 16 = planes 6 := hWords 6 (by decide)
  have hw7 : memLoad fr.original (fr.rdi + 14) 16 = planes 7 := hWords 7 (by decide)
  have hhelperApart := @$apart:ident code hcode
  dsimp only [Activation.original] at *
  runtime_context [hRet, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7]
  refine ⟨?output, .done ?execution, ?tag, ?atoms, ?typed, ?frame, ?words⟩
  case execution =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    runtime_guards returned
    rfl
  case tag => runtime_finish []
  case atoms =>
    change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
    repeat' apply And.intro
    all_goals first | trivial | (runtime_finish [Activation.entryReg, Activation.entryValue]; all_goals first | rfl | exact h39 | exact h50 | exact h51)
  case typed => runtime_typed
  case frame => runtime_finish [Activation.region, span]
  case words =>
    aes16_words
    all_goals runtime_finish [Vector.getElem_ofFn, setWidth_mergeGPR16, BitVec.setWidth_and, BitVec.setWidth_or, BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
      AES16.mixColumns1, AES16.mixColumns3, mixColumnsCircuit_machine,
      rotateRowsAndColumns11_machine, rotateRowsAndColumns13_machine,
      rotateRowsAndColumns22_machine]
    all_goals ac_rfl
  ))

set_option maxHeartbeats 1600000 in
theorem mixColumns1_call (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (planes : Fixslice16.Planes16) :
    CallContract LIR.lifted code .l100000 LIR.Fn100000.frameInfo
      (fun fr => [span fr.rdi 16])
      (fun fr mem => WordsAt mem fr.rdi 16 (Vector.ofFn planes) ∧
        Writable code mem fr.rdi 16 ∧
        (callStack fr).Disjoint (span fr.rdi 16))
      (fun fr mem => WordsAt mem fr.rdi 16 (Vector.ofFn
        (projectPlanes (Fixslice.mixColumns1 (widenPlanes planes)) 0))) := by
  mixColumnsForward_proof mixColumns1_rangeApart

set_option maxHeartbeats 1600000 in
theorem mixColumns3_call (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (planes : Fixslice16.Planes16) :
    CallContract LIR.lifted code .l100580 LIR.Fn100580.frameInfo
      (fun fr => [span fr.rdi 16])
      (fun fr mem => WordsAt mem fr.rdi 16 (Vector.ofFn planes) ∧
        Writable code mem fr.rdi 16 ∧
        (callStack fr).Disjoint (span fr.rdi 16))
      (fun fr mem => WordsAt mem fr.rdi 16 (Vector.ofFn
        (projectPlanes (Fixslice.mixColumns3 (widenPlanes planes)) 0))) := by
  mixColumnsForward_proof mixColumns3_rangeApart

end AesGcm.Proofs.Machine.AES16
