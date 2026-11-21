import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.AES16.Input
import AesGcm.Proofs.Machine.LIR.Fn100b10.Frame
import AesGcm.Proofs.Machine.Fixslice16.Sbox

namespace AesGcm.Proofs.Machine.AES16

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice16

private theorem sboxEntry_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x100b10 23 := by
  have hx := storeOk_of_codeRange h
    (fun x hx => hcode x (LIR.code_l100b10 x hx))
  have hlen : LIR.bytes_l100b10.length = 23 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

private theorem sboxBody_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x100b6d 633 := by
  have hx := storeOk_of_codeRange h
    (fun x hx => hcode x (LIR.code_l100b6d x hx))
  have hlen : LIR.bytes_l100b6d.length = 633 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

open Lean Meta Elab Tactic

elab "aes16_boolean_circuit" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let collect : StateT (Array Expr) MetaM Unit := ty.forEach' fun e => do
    if e.isAppOf ``BitVec.getLsbD then
      modify fun xs => if xs.contains e then xs else xs.push e
      return false
    return true
  let (_, atoms) ← collect.run #[]
  let mut representatives : Array Expr := #[]
  let mut indices : Array Nat := #[]
  for atom in atoms do
    let mut found : Option Nat := none
    for i in [:representatives.size] do
      if ← isDefEq atom representatives[i]! then
        found := some i
        break
    match found with
    | some i => indices := indices.push i
    | none =>
      indices := indices.push representatives.size
      representatives := representatives.push atom
  unless representatives.size ≤ 8 do
    throwError "expected at most eight bit inputs, found {representatives.size}: {representatives}"
  let closed ← withLocalDeclsDND
      (representatives.mapIdx fun i _ => (Name.mkSimple s!"b{i}", mkConst ``Bool)) fun vars => do
    let body := ty.replace fun e => (atoms.findIdx? (· == e)).map fun i => vars[indices[i]!]!
    mkForallFVars vars body
  if closed.hasFVar then throwError "circuit still depends on a non-bit variable"
  let proof ← mkFreshExprSyntheticOpaqueMVar closed
  let gs ← Refine.Tactic.runOn proof.mvarId! (evalTactic (← `(tactic| decide +kernel)))
  unless gs.isEmpty do throwError "Boolean circuit did not close"
  g.assign (mkAppN proof representatives)
  replaceMainGoal []

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem subBytes_callContract (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) :
    CallContract LIR.lifted code .l100b10 LIR.Fn100b10.frameInfo
      (fun fr ↦ [span fr.rdi 16])
      (fun fr mem ↦ fr.rsi = 8 ∧ Writable code mem fr.rdi 16 ∧
        (callStack fr).Disjoint (span fr.rdi 16))
      (fun fr mem ↦ WordsAt mem fr.rdi 16 (Vector.ofFn (Fixslice16.subBytes
        (fun p ↦ memLoad fr.original (fr.rdi + BitVec.ofNat 64 (2 * p.val)) 16)))) := by
  dsimp only [CallContract, LIR.lifted]
  intro fr ⟨lab, args, mem⟩ hl hs hf hTypes hpre
  dsimp only at hl hs hf hTypes hpre
  subst lab mem
  rcases hpre with ⟨hlen, hWrite, hApart⟩
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
    fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 240) 240 ∧
    fr.low.toNat + 240 ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ _ at hf
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
  dsimp only [Activation.original] at *
  runtime_context [hRet]
  refine ⟨?output, .next (next := ?middle0) ?entry0 (.next (next := ?middle1) ?entry1 (.next (next := ?middle2) ?entry2 (.next (next := ?middle3) ?entry3 (.next (next := ?middle4) ?entry4 (.next (next := ?middle5) ?entry5 (.next (next := ?middle6) ?entry6 (.next (next := ?middle7) ?entry7 (.done ?execution)))))))), ?tag, ?atoms, ?typed, ?frame, ?words⟩
  case entry0 =>
    have hhelperApart := @sboxEntry_rangeApart code hcode
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ (testFlags (fr.rsi &&& fr.rsi)).ZF.getD false = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
    runtime_guards next
    rfl
  case entry1 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ (cmpSpec fr.rsi (1 : BitVec 64)).ZF = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry2 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ ((cmpSpec fr.rsi (2 : BitVec 64)).CF || (cmpSpec fr.rsi (2 : BitVec 64)).ZF) = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry3 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ (cmpSpec fr.rsi (3 : BitVec 64)).ZF = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry4 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ ((cmpSpec fr.rsi (4 : BitVec 64)).CF || (cmpSpec fr.rsi (4 : BitVec 64)).ZF) = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry5 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ (cmpSpec fr.rsi (5 : BitVec 64)).ZF = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry6 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ ((cmpSpec fr.rsi (6 : BitVec 64)).CF || (cmpSpec fr.rsi (6 : BitVec 64)).ZF) = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry7 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ (cmpSpec fr.rsi (7 : BitVec 64)).ZF = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case execution =>
    have hhelperApart := @sboxBody_rangeApart code hcode
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
    all_goals runtime_finish [Vector.getElem_ofFn, setWidth_mergeGPR16,
      BitVec.setWidth_and, BitVec.setWidth_or, BitVec.setWidth_xor,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    all_goals
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp only [Fixslice16.subBytes, Fixslice.subBytesCircuit, BitVec.getLsbD_xor,
        BitVec.getLsbD_and, Fin.val_zero, Fin.isValue, Nat.reduceMul, BitVec.add_zero]
      aes16_boolean_circuit

end AesGcm.Proofs.Machine.AES16
