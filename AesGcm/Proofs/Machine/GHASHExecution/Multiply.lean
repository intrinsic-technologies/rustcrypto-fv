import AesGcm.Proofs.Machine.LIR.Fn102bd0.Frame
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.GHASHExecution.Memory
import AesGcm.Proofs.Machine.GHASHExecution.Run
import AesGcm.Proofs.Machine.GHASHExecution.ProductTactics
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.GHASH.WideProduct
import AesGcm.Proofs.Machine.GHASH.Reduction
import AesGcm.Proofs.Machine.GHASH.WordMultiplication

namespace AesGcm.Proofs.Machine.GHASHExecution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASH

section WordProof

attribute [local irreducible] memStore memLoad bswapSpec polyvalMultiplyWords wideMul64 high64
  BitVec.mul BitVec.and BitVec.or BitVec.xor BitVec.shiftLeft BitVec.ushiftRight
  BitVec.setWidth BitVec.reverse

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem multiplyRam_words (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (hRead : Readable mem (args[7].get 64) 32)
    (hStack : Readable mem (args[4].get 64 - 128) 128)
    (hApart : (args[7].get 64).toNat + 32 ≤ (args[4].get 64 - 128).toNat ∨
      (args[4].get 64).toNat ≤ (args[7].get 64).toNat) :
    let result := polyvalMultiplyWords
      (args[6].get 64 ^^^ memLoad mem (args[7].get 64 + 16) 64)
      (args[2].get 64 ^^^ memLoad mem (args[7].get 64 + 24) 64)
      (memLoad mem (args[7].get 64) 64)
      (memLoad mem (args[7].get 64 + 8) 64)
    memLoad (multiplyRam code args mem) (args[7].get 64 + 16) 64 = result.1 ∧
      memLoad (multiplyRam code args mem) (args[7].get 64 + 24) 64 = result.2 := by
  generalize hbase : args[7].get 64 = base at *
  generalize hstackBase : args[4].get 64 = sp at *
  generalize hk0 : memLoad mem base 64 = k0
  generalize hk1 : memLoad mem (base + 8) 64 = k1
  generalize ha0 : memLoad mem (base + 16) 64 = acc0
  generalize ha1 : memLoad mem (base + 24) 64 = acc1
  have hReadLow := hRead.low
  have hStackLow := hStack.low
  runtime_context [hbase, hstackBase, hk0, hk1, ha0, ha1]
  unfold multiplyRam
  extract_lets result m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19
  dsimp only [result]
  constructor
  all_goals runtime_local_memory_norm [hstackBase, hk0, hk1, ha0, ha1]
  all_goals simp only [BitVec.ofNat_eq_ofNat, reverseBits64_machine, reverseBits64_machine_clear]
  all_goals ghash_fold_products
  all_goals try simp only [mask5555_comm, reverseBits64_machine_clear]
  all_goals try simp only [← reverse_xor]
  all_goals try simp only [reverse_xor_shift, ← wideMul64_high_masked]
  all_goals try simp only [maskedMul64_machine_lowTwo_shift, maskedMul64_machine_bit0_shift]
  all_goals simp only [wideMul64_high_double_half, ← wideMul64_low_masked]
  all_goals simp only [polyvalMultiplyWords, polyvalReduceWords, reductionCarry, reductionHigh,
    BitVec.shiftLeft_xor_distrib, BitVec.ushiftRight_xor_distrib,
    wideMul64_high_double_half]
  all_goals ac_nf0
  all_goals ac_rfl

end WordProof

def multiplyWords (x0 x1 y0 y1 : BitVec 64) : BitVec 64 × BitVec 64 :=
  polyvalMultiplyWords x0 x1 y0 y1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem multiply_call (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) :
    CallContract LIR.lifted code .l102bd0 LIR.Fn102bd0.frameInfo
      (fun fr ↦ [span (fr.rdi + 16) 16])
      (fun fr mem ↦ Writable code mem fr.rdi 32 ∧
        (callStack fr).Disjoint (span fr.rdi 32))
      (fun fr mem ↦
        let result := multiplyWords
          (fr.rsi ^^^ memLoad fr.original (fr.rdi + 16) 64)
          (fr.rdx ^^^ memLoad fr.original (fr.rdi + 24) 64)
          (memLoad fr.original fr.rdi 64)
          (memLoad fr.original (fr.rdi + 8) 64)
        memLoad mem (fr.rdi + 16) 64 = result.1 ∧
        memLoad mem (fr.rdi + 24) 64 = result.2) := by
  intro fr loc hlabel hstore hentry htyped hpre
  rcases loc with ⟨l, args, mem⟩
  change l = _ at hlabel
  change mem = _ at hstore
  subst l
  subst mem
  change Values Value Reg.count at args
  rcases hpre with ⟨hstate, hdis⟩
  simp only [↓reduceIte, LIR.Fn102bd0.frameInfo,
    FrameInfo.entryAtoms, FrameInfo.frameAtoms, FrameInfo.entryFrame, FrameInfo.entryRegs,
    FrameInfo.stackAtoms, FrameInfo.window, FrameInfo.callSlotAtoms, Activation.below,
    Activation.entryReg, Activation.entryValue, Option.getD, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.append_nil, Atom.All, Atom.Holds, Atom.gpr,
    Nat.reduceEqDiff, ↓reduceIte] at hentry
  rcases hentry with ⟨h4, h22, h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, h14, h15,
    h39, h50, h51, hretRead, hretWord, hretLow, hstack, hroom, halign, _⟩
  have hsp : args[4].get 64 = fr.rsp :=
    (congrArg (Value.get 64) h4).trans (by rfl)
  have hdi : args[7].get 64 = fr.rdi :=
    (congrArg (Value.get 64) h7).trans (by rfl)
  have hstack136 : Readable fr.original (fr.rsp - 128) 136 := by
    have hend : Readable fr.original (fr.rsp - 128#64 + 128#64) 8 := by
      simpa only [BitVec.sub_add_cancel] using hretRead
    exact readable_append hstack.readable hend
  have hap : fr.rsp.toNat + 8 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 32 ≤ fr.low.toNat := by
    have h := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
      fr.rdi.toNat 32 (by omega) (by decide) hdis
    omega
  have hsub : (fr.rsp - 128).toNat = fr.rsp.toNat - 128 := by
    rw [BitVec.toNat_sub_of_le (by change 128 ≤ fr.rsp.toNat; omega)]
    rfl
  have hApart : fr.rdi.toNat + 32 ≤ (fr.rsp - 128).toNat ∨
      fr.rsp.toNat + 8 ≤ fr.rdi.toNat := by omega
  obtain ⟨out, hrun⟩ := multiply_returns code hcode args fr hsp hdi hstack hstate
    hretRead hretWord hretLow hroom hap
  have hout := multiply_returned_output code args fr.original out hrun
  have hsaved (j : Fin 6) : out.values[
      (match j.val with | 0 => 3 | 1 => 12 | 2 => 13 | 3 => 14 | 4 => 15 | _ => 5)]'(by split <;> decide) =
      args[(match j.val with | 0 => 3 | 1 => 12 | 2 => 13 | 3 => 14 | 4 => 15 | _ => 5)]'(by split <;> decide) := by
    let rj : Nat := match j.val with | 0 => 3 | 1 => 12 | 2 => 13 | 3 => 14 | 4 => 15 | _ => 5
    have hrj : rj < 16 := by dsimp only [rj]; split <;> decide
    have hrj53 : rj < Reg.count := by change rj < 53; omega
    have hval := multiplyOutput_saved code args fr.original j
    have h := multiplyRam_saved code args fr.original
      (by simpa only [hdi] using hstate.readable)
      (by simpa only [hsp] using hstack136)
      (by simpa only [hsp, hdi] using hApart) ⟨j.val, by have := j.isLt; omega⟩
    have hm : memLoad (multiplyRam code args fr.original)
        (args[4].get 64 - BitVec.ofNat 64 (48 - 8 * j.val)) 64 = args[rj].get 64 := by
      rcases j with ⟨j, hj⟩
      have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
      rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa only [rj, Nat.reduceMul, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte] using h
    have ho : out.values[rj] = (multiplyOutput code args fr.original).values[rj] :=
      congrArg (fun o : Output Value Ram Reg.count => o.values[rj]) hout
    exact ho.trans (hval.trans ((congrArg (Value.mk 64) hm).trans
      (htyped.value ⟨rj, hrj⟩).symm))
  have oregs := multiplyOutput_registers code args fr.original
  refine ⟨out, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Program.Exec.of_sem
    apply Semantics.Exec.ret
    change LIR.program.step (dialect code) _ = .done out
    change Transfer.next (dialect code) []
      (LIR.program.runBlock (dialect code) ⟨.l102bd0, args, fr.original⟩) = .done out
    exact congrArg (Transfer.next (dialect code) []) hrun
  · rw [hout, multiplyOutput_tag]
    have h := multiplyRam_saved code args fr.original
      (by simpa only [hdi] using hstate.readable)
      (by simpa only [hsp] using hstack136)
      (by simpa only [hsp, hdi] using hApart) (6 : Fin 7)
    have hs : memLoad (multiplyRam code args fr.original) (args[4].get 64) 64 =
        memLoad fr.original (args[4].get 64) 64 := by
      have hj : (6 : Fin 7).val = 6 := by decide +kernel
      simpa only [hj, Nat.reduceMul, Nat.reduceSub,
        show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.sub_zero, ↓reduceIte] using h
    rw [hs, hsp, hretWord]
  · have s3 := hsaved 0
    have s12 := hsaved 1
    have s13 := hsaved 2
    have s14 := hsaved 3
    have s15 := hsaved 4
    have s5 := hsaved 5
    simp only [LIR.Fn102bd0.frameInfo, FrameInfo.doneAtoms, List.map_cons, List.map_nil,
      Activation.entryReg, Activation.entryValue]
    rw [hout]
    exact ⟨by exact oregs.1.trans (congrArg (fun x => Value.mk 64 (x + 8)) hsp),
      oregs.2.1.trans h22, (by rw [← hout]; exact s3.trans h3),
      (by rw [← hout]; exact s5.trans h5), (by rw [← hout]; exact s12.trans h12),
      (by rw [← hout]; exact s13.trans h13), (by rw [← hout]; exact s14.trans h14),
      (by rw [← hout]; exact s15.trans h15), oregs.2.2.1.trans h39,
      oregs.2.2.2.1.trans h50, oregs.2.2.2.2.trans h51, trivial⟩
  · rw [hout]
    exact multiplyOutput_typed code args fr.original
  · rw [hout, multiplyOutput_store]
    have hf := multiplyRam_frame code args fr.original
      (by simpa only [hdi] using hstate.readable)
      (by simpa only [hsp] using hstack136) (by rw [hsp]; omega)
    apply (RamWriteFrame.refl fr.original [fr.region, span (fr.rdi + 16) 16]).trans hf
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨fr.region, by simp, ?_, ?_⟩
      all_goals simp only [hsp, Activation.region]
      all_goals omega
    · rw [hdi]
      exact ⟨span (fr.rdi + 16) 16, by simp, Nat.le_refl _, Nat.le_refl _⟩
  · rw [hout, multiplyOutput_store]
    have hsi : args[6].get 64 = fr.rsi :=
      (congrArg (Value.get 64) h6).trans (by rfl)
    have hdx : args[2].get 64 = fr.rdx :=
      (congrArg (Value.get 64) h2).trans (by rfl)
    have hw := multiplyRam_words code args fr.original
      (by simpa only [hdi] using hstate.readable)
      (by simpa only [hsp, BitVec.ofNat_eq_ofNat] using hstack.readable)
      (by rw [hdi, hsp]; omega)
    simpa only [multiplyWords, hdi, hsi, hdx] using hw

end AesGcm.Proofs.Machine.GHASHExecution
