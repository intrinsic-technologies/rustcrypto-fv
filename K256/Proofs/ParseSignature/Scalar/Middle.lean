import K256.Proofs.ParseSignature.Contract
import K256.Proofs.ParseSignature.Scalar.Borrow
import K256.Proofs.Common.Refine.Lemma.Store
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

namespace K256.Proofs.ParseSignature.Scalar

open K256.Proofs.Common Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

def borrowResume : StackFrame Value Label signature Reg.count :=
  { target := .l107880, kept := #v[], arity := rfl, guard := some ⟨64, 0x107880⟩ }

theorem borrow_block {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    {mem : Ram} {args : Values Value Reg.count} {sp : BitVec 64}
    {regions : List MemoryRegion}
    (htmp : InRegions regions (sp + 8) 8) (hret : InRegions regions (sp - 8) 8)
    (hsp : args[4] = ⟨64, sp⟩) (hwtmp : Writable code mem (sp + 8) 8)
    (hwret : Writable code mem (sp - 8) 8)
    (hl0 : LoadOk mem (sp + 40) 8) (hl1 : LoadOk mem (sp + 48) 8)
    (hl2 : LoadOk mem (sp + 56) 8) (hl3 : LoadOk mem (sp + 64) 8)
    (widths : ArgumentWidths args)
    (a0 a1 a2 a3 : BitVec 64)
    (h0 : memLoad mem (sp + 40) 64 = a0) (h1 : memLoad mem (sp + 48) 64 = a1)
    (h2 : memLoad mem (sp + 56) 64 = a2) (h3 : memLoad mem (sp + 64) 64 = a3) :
    ∃ (next : Values Value Reg.count) (testMem : Ram),
      program.runBlock (dialect code) ⟨.l1077c7, args, mem⟩ =
        .call ⟨.l127d50, next, testMem⟩ borrowResume ∧
      next[7] = ⟨64, borrowChain a0 a1 a2 a3⟩ ∧ next[4] = ⟨64, sp - 8⟩ ∧
      next[15] = ⟨64, a0⟩ ∧ next[12] = ⟨64, a1⟩ ∧
      next[13] = ⟨64, a2⟩ ∧ next[5] = ⟨64, a3⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 14, 22, 39, 50, 51] → next[i] = args[i]) ∧
      ArgumentWidths next ∧
      RamWriteFrame mem testMem regions ∧ memLoad testMem (sp - 8) 64 = 0x107880 := by
  have hspBits : args[4].get 64 = sp := by rw [hsp]; rfl
  have carryLoad {m : Ram} {b a : BitVec 64} {n k : Nat} {v : BitVec k}
      (h : LoadOk m a n) : LoadOk (memStore m b v) a n :=
    ⟨h.low, fun i hi => memStore_isSome m b v _ (h.present i hi)⟩
  have carryStore {m : Ram} {b a p : BitVec 64} {n k len : Nat} {v : BitVec k}
      (h : StoreOk code m a n p len) : StoreOk code (memStore m b v) a n p len :=
    ⟨h.low, fun i hi => memStore_isSome m b v _ (h.present i hi), h.tables, h.apart, h.notCode⟩
  have loadTmp : LoadOk mem (sp + 8) 8 := ⟨hwtmp.readable.low, hwtmp.readable.present⟩
  have loadByte : LoadOk mem (sp + 8) 1 := LoadOk.of_region hwtmp.readable (Nat.le_refl _) (by omega)
  have storeGuard {a : BitVec 64} (h : Writable code mem a 8) (off : Nat)
      (hoff : off + 5 ≤ bytes_l1077c7.length) :
      StoreOk code mem a 8 (0x1077c7 + BitVec.ofNat 64 off) 5 := by
    refine ⟨h.readable.low, h.readable.present, h.tables, ?_, h.notCode⟩
    intro i hi j hj he
    have byte := mem_codeRange 0x1077c7 bytes_l1077c7 (off + j) (by omega)
    apply h.notCode _ (hcode _ (code_l1077c7 _ byte)) i hi
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he.symm
  have sto1 : StoreOk code mem (sp + 8) 8 0x1077f5 5 := storeGuard hwtmp 46 (by decide +kernel)
  have sto2 : StoreOk code mem (sp + 8) 8 0x107829 5 := storeGuard hwtmp 98 (by decide +kernel)
  have sto3 : StoreOk code mem (sp + 8) 8 0x10784b 5 := storeGuard hwtmp 132 (by decide +kernel)
  have sto4 : StoreOk code mem (sp + 8) 8 0x10786c 5 := storeGuard hwtmp 165 (by decide +kernel)
  have sto5 : StoreOk code mem (sp - 8) 8 0x10787b 5 := storeGuard hwret 180 (by decide +kernel)
  have readWord (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (sp + 8) v) (sp + 8) 64 = v :=
    memLoad_memStore_same m _ v (by decide) (by decide)
  have readByte (m : Ram) (v : BitVec 64) :
      memLoad (memStore m (sp + 8) v) (sp + 8) 8 = v.extractLsb' 0 8 :=
    memLoad_memStore_within m v 8 0 (BitVec.add_zero _).symm (by decide) (by decide) (by decide)
  refine ⟨?next, ?mem, ?eval, ?post⟩
  case eval =>
    cfg_eval [hspBits, hl0, hl1, hl2, hl3, h0, h1, h2, h3, sto1, sto2, sto3, sto4, sto5,
      carryLoad, carryStore, loadTmp, loadByte, readWord, readByte]
    simp (config := { maxDischargeDepth := 16 }) only [carryLoad, carryStore, loadTmp, loadByte,
      sto4, sto5, ite_true]
    rfl
  case post =>
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · have hb := borrowChain_eq a0 a1 a2 a3
      change (⟨64, (mergeGPR 8 ((borrowChain a0 a1 a2 a3).extractLsb' 0 8 &&& 1)
        (((borrowChain a0 a1 a2 a3).extractLsb' 0 8).setWidth 64)).setWidth 8 |>.setWidth 64⟩ : Value) =
          ⟨64, borrowChain a0 a1 a2 a3⟩
      rw [hb]
      split <;> rfl
    · intro ⟨i, hi⟩ h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · have h8 := widths 8 (by decide)
      have h9 := widths 9 (by decide)
      intro ⟨i, hi⟩ h
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | rfl | exact h8 | exact h9
    · apply RamWriteFrame.memStore _ _ hret
      iterate 4 apply RamWriteFrame.memStore _ _ htmp
      exact RamWriteFrame.refl _ _
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem branch_after_fill {code : CodeMap} {mem : Ram} {args : Values Value Reg.count}
    (hresult : args[0].get 8 = 255) (widths : ArgumentWidths args) :
    ∃ (next : Values Value Reg.count),
      program.runBlock (dialect code) ⟨.l1077bf, args, mem⟩ = .jump ⟨.l1077c7, next, mem⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 4, 14, 22, 39, 50, 51] → next[i] = args[i]) ∧
      ArgumentWidths next := by
  refine ⟨?next, ?eval, ?regs, ?widths⟩
  case eval =>
    have hlow : (args[0].get 64).setWidth 8 = 255 := by
      simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using hresult
    cfg_eval [hlow]
    rfl
  case regs =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case widths =>
    intro ⟨i, hi⟩ h
    have hw := widths ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

end K256.Proofs.ParseSignature.Scalar
