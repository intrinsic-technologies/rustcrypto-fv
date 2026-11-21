import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Common.Bitwise
import AesGcm.Proofs.AES16.Input
import AesGcm.Proofs.Machine.LIR.Fn109d90.Frame

namespace AesGcm.Proofs.Machine.AES16

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice16

private theorem outputEntry_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x109d90 12 := by
  have hx := storeOk_of_codeRange h
    (fun x hx => hcode x (LIR.code_l109d90 x hx))
  have hlen : LIR.bytes_l109d90.length = 12 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

private theorem outputBody_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x109de2 351 := by
  have hx := storeOk_of_codeRange h
    (fun x hx => hcode x (LIR.code_l109de2 x hx))
  have hlen : LIR.bytes_l109de2.length = 351 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

theorem memoryBlock_eq_of_words {mem : Ram} {a : BitVec 64} {bytes : Fixslice16.Block}
    (h : WordsAt mem a 8 (Vector.ofFn bytes)) : Fixslice.memoryBlock mem a = bytes := by
  funext j
  have hj := h j.val j.isLt
  simpa only [wordAddr, Nat.reduceDiv, Nat.one_mul, memLoad_8, Vector.getElem_ofFn,
    Fixslice.memoryBlock] using hj

set_option maxHeartbeats 1600000 in
theorem output_call (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) :
    CallContract LIR.lifted code .l109d90 LIR.Fn109d90.frameInfo
      (fun fr ↦ [span fr.rdi 16])
      (fun fr mem ↦ fr.rdx = 8 ∧ Readable mem fr.rsi 16 ∧ Writable code mem fr.rdi 16 ∧
        (callStack fr).Disjoint (span fr.rdi 16) ∧
        (callStack fr).Disjoint (span fr.rsi 16) ∧
        (span fr.rdi 16).Disjoint (span fr.rsi 16))
      (fun fr mem ↦ Fixslice.memoryBlock mem fr.rdi =
        Fixslice16.decode (fun p ↦ memLoad fr.original
          (fr.rsi + BitVec.ofNat 64 (2 * p.val)) 16)) := by
  dsimp only [CallContract, LIR.lifted]
  intro fr ⟨lab, args, mem⟩ hl hs hf hTypes hpre
  dsimp only at hl hs hf hTypes hpre
  subst lab mem
  rcases hpre with ⟨hlen, hRead, hWrite, hApart, hInputApart, hDataApart⟩
  have hOutRead := hWrite.readable
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
    fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 160) 160 ∧
    fr.low.toNat + 160 ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ _ at hf
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
  have hInputApartNum : fr.rsp.toNat + 8 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 16 ≤ fr.low.toNat := by
    have h := hInputApart (max fr.low.toNat fr.rsi.toNat)
    simp only [callStack, span, MemoryRegion.Disjoint, MemoryRegion.Contains] at hInputApart
    dsimp only [callStack, span, MemoryRegion.Contains] at h
    omega
  have hDataApartNum : fr.rdi.toNat + 16 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 16 ≤ fr.rdi.toNat := by
    have h := hDataApart (max fr.rdi.toNat fr.rsi.toNat)
    simp only [span, MemoryRegion.Disjoint, MemoryRegion.Contains] at hDataApart
    dsimp only [span, MemoryRegion.Contains] at h
    omega
  have hOutReadLow := hOutRead.low
  dsimp only [Activation.original] at *
  runtime_context [hRet]
  refine ⟨?output, .next (next := ?middle0) ?entry0 (.next (next := ?middle1) ?entry1 (.next (next := ?middle2) ?entry2 (.next (next := ?middle3) ?entry3 (.next (next := ?middle4) ?entry4 (.next (next := ?middle5) ?entry5 (.next (next := ?middle6) ?entry6 (.next (next := ?middle7) ?entry7 (.done ?execution)))))))), ?tag, ?atoms, ?typed, ?frame, ?words⟩
  case entry0 =>
    have hhelperApart := @outputEntry_rangeApart code hcode
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ (testFlags (fr.rdx &&& fr.rdx)).ZF.getD false = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
    runtime_guards next
    rfl
  case entry1 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ (cmpSpec fr.rdx (1 : BitVec 64)).ZF = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry2 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ ((cmpSpec fr.rdx (2 : BitVec 64)).CF || (cmpSpec fr.rdx (2 : BitVec 64)).ZF) = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry3 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ (cmpSpec fr.rdx (3 : BitVec 64)).ZF = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry4 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ ((cmpSpec fr.rdx (4 : BitVec 64)).CF || (cmpSpec fr.rdx (4 : BitVec 64)).ZF) = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry5 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ (cmpSpec fr.rdx (5 : BitVec 64)).ZF = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry6 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ ((cmpSpec fr.rdx (6 : BitVec 64)).CF || (cmpSpec fr.rdx (6 : BitVec 64)).ZF) = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case entry7 =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    have hbranch : ¬ (cmpSpec fr.rdx (7 : BitVec 64)).ZF = true := by
      rw [hlen]
      decide +kernel
    rw [ite_eq_right hbranch]
  case execution =>
    have hhelperApart := @outputBody_rangeApart code hcode
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
    apply memoryBlock_eq_of_words
    aes16_words
    all_goals runtime_finish [Vector.getElem_ofFn, setWidth_mergeGPR16,
      BitVec.setWidth_and, BitVec.setWidth_or, BitVec.setWidth_xor,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    all_goals
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [getLsbD_decode _ _ ⟨i, hi⟩]
      have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases h with h | h | h | h | h | h | h | h
      all_goals simp only [BitVec.ofNat_eq_ofNat, add_self_eq_shift, h, Nat.zero_lt_succ,
        BitVec.getLsbD_eq_getElem, BitVec.getElem_xor, xor, BitVec.getElem_shiftLeft, decide_true,
        Bool.not_true, Nat.zero_le, Nat.sub_eq_zero_of_le, BitVec.getElem_and,
        BitVec.getElem_setWidth, BitVec.getElem_ushiftRight, Nat.add_zero, Nat.reduceLT,
        decide_false, Bool.not_false, Nat.reduceSub, Nat.reduceAdd, Nat.lt_one_iff, reduceCtorEq,
        Nat.add_one_sub_one, BitVec.reduceGetElem, Bool.and_false, Bool.false_bne, Nat.lt_add_one,
        Bool.and_true, Bool.false_and, Nat.mul_zero, BitVec.add_zero, transposeIndex, Nat.zero_mod,
        Nat.zero_div, Fin.zero_eta, Fin.isValue, Fin.val_zero, Nat.reduceLeDiff, Nat.lt_irrefl, Bool.true_and, Bool.bne_assoc, Nat.mul_one, Nat.reduceMul,
        Bool.xor_left_comm, bne_self_eq_false, Bool.bne_false, Nat.one_mod,
        Nat.reduceDiv, Fin.reduceFinMk, Fin.is_lt, ↓reduceIte, and_true, not_false_eq_true,
        BitVec.setWidth_setWidth, BitVec.getElem_extractLsb', Nat.reduceMod,
        BitVec.setWidth_ushiftRight, BitVec.setWidth_xor, Nat.mod_succ, Std.le_refl,
        BitVec.getLsbD_of_ge, Bool.and_self, Nat.mod_self, Nat.div_self, Nat.zero_add, Fin.mk_one,
        Fin.val_one, BitVec.setWidth_and, Nat.reducePow, BitVec.setWidth_ofNat_of_le_of_lt,
        Fin.val_two, bne_cancel_middle]
      all_goals rfl


end AesGcm.Proofs.Machine.AES16
