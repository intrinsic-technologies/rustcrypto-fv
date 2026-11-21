import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.ParseSignature

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

theorem serializeBlock {code : CodeMap} (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    {args : Vector Value 53} {mem : Ram} {sp dst : BitVec 64}
    (hsp : args[4] = ⟨64, sp⟩) (hdst : args[3] = ⟨64, dst⟩)
    (hr : Readable mem (sp + 16) 64) (hw : Writable code mem dst 64) :
    ∃ (next : Vector Value 53) (after : Ram),
      LIR.program.runBlock (dialect code) ⟨.l10246f, args, mem⟩ =
        .jump ⟨.l1024d0, next, after⟩ ∧
      next[0] = ⟨64, 0⟩ ∧
      (∀ i : Fin 53, i.val ∈ [4, 5, 12, 13, 14, 15, 22] → next[i] = args[i]) ∧
      RamWriteFrame mem after [buffer dst 64] ∧
      ∀ i < 8, memLoad after (wordAddr dst 64 i) 64 =
        bswapSpec (memLoad mem (wordAddr (sp + 16) 64 (4 * (i / 4) + (3 - i % 4))) 64) := by
  let words (i : Nat) := bswapSpec (memLoad mem
    (sp + BitVec.ofNat 64 (16 + 8 * (4 * (i / 4) + (3 - i % 4)))) 64)
  let writeAddr (i : Nat) := if i = 0 then dst else wordAddr dst 64 i
  have writeAddr_eq (i : Nat) : writeAddr i = wordAddr dst 64 i := by
    by_cases hi : i = 0
    · subst i
      exact (BitVec.add_zero dst).symm
    · simp only [writeAddr, hi, ite_false]
  let writeWords : Nat → Ram := fun n => Nat.rec mem
    (fun i acc => memStore acc (writeAddr i) (words i)) n
  have hwLow := hw.readable.low
  have haddr (i : Nat) (hi : i < 8) : (wordAddr dst 64 i).toNat = dst.toNat + 8 * i := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 8 * i) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hframe (n : Nat) (hn : n ≤ 8) : RamWriteFrame mem (writeWords n) [buffer dst 64] := by
    induction n with
    | zero => exact RamWriteFrame.refl _ _
    | succ n ih =>
      apply (ih (by omega)).memStore
      refine ⟨buffer dst 64, List.mem_singleton_self _, ?_⟩
      change dst.toNat ≤ (writeAddr n).toNat ∧
        (writeAddr n).toNat + 8 ≤ dst.toNat + 64 ∧ (writeAddr n).toNat + 8 ≤ 2 ^ 64
      rw [writeAddr_eq, haddr n (by omega)]
      omega
  have hwords (n : Nat) (hn : n ≤ 8) (i : Nat) (hi : i < n) :
      memLoad (writeWords n) (wordAddr dst 64 i) 64 = words i := by
    induction n with
    | zero => omega
    | succ n ih =>
      change memLoad (memStore (writeWords n) (writeAddr n) (words n))
        (wordAddr dst 64 i) 64 = words i
      rw [writeAddr_eq]
      by_cases he : i = n
      · subst i
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_toNat <;>
            simp only [haddr n (by omega), haddr i (by omega), Nat.reduceDiv] <;> omega)]
        exact ih (by omega) (by omega)
  have hload (off : Nat) (hoff : off + 8 ≤ 64) :
      LoadOk mem (sp + BitVec.ofNat 64 (16 + off)) 8 := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    change LoadOk mem (sp + 16 + BitVec.ofNat 64 off) 8
    have hl := hr.low
    have ha : (sp + 16 + BitVec.ofNat 64 off).toNat = (sp + 16).toNat + off := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    exact LoadOk.of_region hr (by rw [ha]; omega) (by rw [ha]; omega)
  have hstore (i off len : Nat) (hi : i < 8) (hoff : off + len ≤ LIR.bytes_l10246f.length) :
      StoreOk code (writeWords i) (writeAddr i) 8 (0x10246f + BitVec.ofNat 64 off) len := by
    rw [writeAddr_eq]
    have hw' : Writable code (writeWords i) (wordAddr dst 64 i) 8 :=
      (hw.of_frame (hframe i (by omega))).sub
        (by rw [haddr i hi]; omega) (by rw [haddr i hi]; omega)
    refine ⟨hw'.readable.low, hw'.readable.present, hw'.tables, ?_, hw'.notCode⟩
    apply RangeApart.right_sub (m := LIR.bytes_l10246f.length) ?_ hoff
    intro k hk j hj he
    have hm := hcode _ (LIR.code_l10246f _ (mem_codeRange 0x10246f LIR.bytes_l10246f j hj))
    exact hw'.notCode _ hm k hk he.symm
  have hspBits : Value.get 64 args[4] = sp := congrArg (Value.get 64) hsp
  have hdstBits : Value.get 64 args[3] = dst := congrArg (Value.get 64) hdst
  refine ⟨?next, writeWords 8, ?eval, ?post⟩
  case eval =>
    cfg_eval [LIR.b_l10246f_1, hspBits, hdstBits]
    refine (ite_eq_left (hload 24 (by decide))).trans ?_
    refine (ite_eq_left (hload 16 (by decide))).trans ?_
    refine (ite_eq_left (hload 0 (by decide))).trans ?_
    refine (ite_eq_left (hload 8 (by decide))).trans ?_
    refine (ite_eq_left (hload 56 (by decide))).trans ?_
    refine (ite_eq_left (hload 48 (by decide))).trans ?_
    refine (ite_eq_left (hload 40 (by decide))).trans ?_
    refine (ite_eq_left (hload 32 (by decide))).trans ?_
    refine (ite_eq_left (hstore 0 64 3 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (hstore 1 67 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (hstore 2 71 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (hstore 3 75 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (hstore 4 79 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (hstore 5 83 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (hstore 6 87 4 (by decide) (by decide))).trans ?_
    refine (ite_eq_left (hstore 7 91 4 (by decide) (by decide))).trans ?_
    rfl
  case post =>
    refine ⟨rfl, ?regs, hframe 8 (by decide), ?words⟩
    · intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · intro i hi
      rw [hwords 8 (by decide) i hi]
      dsimp only [words, wordAddr, Nat.reduceDiv]
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl

end K256.Proofs.ParseSignature
