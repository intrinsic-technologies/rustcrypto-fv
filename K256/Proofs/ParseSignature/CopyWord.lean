import K256.Proofs.ParseSignature.Contract
import K256.Proofs.LIR.Fn12a820.Frame
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
import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Common.Refine.Lemma.Layout
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.ParseSignature

open K256.Spec K256.Proofs.Common Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

theorem memcpy_word_call {code : CodeMap} (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (hn : fr.rdx = 8) (ha : fr.rdi.toNat % 8 = 0)
    (hr : Readable fr.original fr.rsi 8) (hw : Writable code fr.original fr.rdi 8)
    (hapart : Outside [buffer fr.rdi 8] fr.rsi 8)
    (hret : Outside [buffer fr.rdi 8] fr.rsp 8) :
    Call code .l12a820 LIR.Fn12a820.frameInfo fr [buffer fr.rdi 8] fun out =>
      memLoad out.store fr.rdi 64 = memLoad fr.original fr.rsi 64 := by
  intro args hentry
  change Atom.All code args fr.original (LIR.Fn12a820.frameAt .l12a820 fr) at hentry
  simp only [LIR.Fn12a820.frameAt, LIR.Fn12a820.frameAtG0,
    Atom.All, Atom.Holds, Atom.gpr] at hentry
  rcases hentry with ⟨hsp, hdf, -, hdx, hbx, hbp, hsi, hdi, -, h9, h12, h13, h14, h15,
    h39, h50, h51, hreadret, hretword, hretlow, -, -, -⟩
  have hap : fr.rsi.toNat + 8 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 8 ≤ fr.rsi.toNat :=
    hapart.2 _ (List.mem_cons_self ..)
  have hmovsq : RepMovsOk code fr.original 0 fr.rsi fr.rdi 1 8 0x12a843 3 := by
    refine ⟨rfl, hr.low, hw.readable.low, hr.present, hw.readable.present, hap, hw.tables, ?_,
      hw.notCode⟩
    intro i hi j hj hij
    have hj' : 35 + j < LIR.bytes_l12a820.length := by
      change 35 + j < 47
      omega
    have hx := hcode _ (LIR.code_l12a820 _ (mem_codeRange 0x12a820 LIR.bytes_l12a820 _ hj'))
    apply hw.notCode _ hx i hi
    change (0x12a820 : BitVec 64) + BitVec.ofNat 64 (35 + j) = _
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact hij.symm
  let copied := memCopy fr.original fr.rdi fr.rsi 8
  have hins : InRegion (buffer fr.rdi 8) fr.rdi 8 :=
    ⟨Nat.le_refl _, Nat.le_refl _, by
      have hdst := hw.readable.low
      omega⟩
  have hf : RamWriteFrame fr.original copied [buffer fr.rdi 8] :=
    (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_cons_self .., hins⟩
  have hretok : LoadOk copied fr.rsp 8 :=
    LoadOk.of_region (hreadret.of_frame hf) (Nat.le_refl _) (Nat.le_refl _)
  have htarget : memLoad copied fr.rsp 64 = fr.ret :=
    (hf.memLoad_eq hret).trans hretword
  have htargetLow : (memLoad copied fr.rsp 64).toNat < 2^32 := by rwa [htarget]
  have hspBits : (args[4]).get 64 = fr.rsp := congrArg (Value.get 64) hsp
  have hdfBits : (args[22]).get 1 = 0 := congrArg (Value.get 1) hdf
  have hdxBits : (args[2]).get 64 = 8 := (congrArg (Value.get 64) hdx).trans hn
  have hsiBits : (args[6]).get 64 = fr.rsi := congrArg (Value.get 64) hsi
  have hdiBits : (args[7]).get 64 = fr.rdi := congrArg (Value.get 64) hdi
  have hprefix : (-(fr.rdi.setWidth 32) &&& 7) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_neg, BitVec.toNat_setWidth]
    change (((2^32 - fr.rdi.toNat % 2^32) % 2^32) &&& (2^3 - 1)) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hcopyZero (m : Ram) (dst src : BitVec 64) : memCopy m dst src 0 = m := rfl
  have hwidth : (0 : BitVec 32).setWidth 64 = 0 := rfl
  have hcarry : (cmpSpec (8 : BitVec 64) 0).CF = false := by decide +kernel
  have hshift : ((8 : BitVec 64) - 0) >>> 3 = 1 := by decide +kernel
  have htail : ((((8 : BitVec 64) - 0).setWidth 32) &&& 7).setWidth 64 = 0 := by
    decide +kernel
  dsimp only [copied] at hretok htargetLow
  have hshow : ∃ out, LIR.program.runBlock (dialect code) ⟨.l12a820, args, fr.original⟩ =
      .returned out ∧ out.store = copied ∧ out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code out.values out.store (LIR.Fn12a820.frameInfo.doneAtoms fr) ∧ ArgumentWidths out.values := by
    refine ⟨?out, ?eval, ?post⟩
    case eval =>
      cfg_eval
      simp only [hspBits, hdfBits, hdxBits, hsiBits, hdiBits, hprefix,
        hwidth, hcarry, Bool.false_eq_true, ite_false, hshift, htail,
        BitVec.reduceToNat, BitVec.add_zero, hcopyZero, Nat.reduceMul,
        hmovsq, or_true, true_or, ite_true, hretok, htargetLow, and_self]
      rfl
    case post =>
      refine ⟨rfl, ?_, ?_, ?_⟩
      · exact congrArg (fun w => some (⟨64, w⟩ : Value)) htarget
      · exact ⟨rfl, hdf, hbx, hbp, h12, h13, h14, h15, h39, h50, h51, trivial⟩
      · intro ⟨i, hi⟩ harg
        simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at harg
        rcases harg with rfl | rfl | rfl | rfl | rfl | rfl <;> try rfl
        exact congrArg Value.width h9
  obtain ⟨out, heval, hstore, htag, hdone, hwidths⟩ := hshow
  refine ⟨out, .done ?_, htag, hdone, ?_, hwidths, ?_⟩
  · rw [Program.step, heval]
    rfl
  · rw [hstore]
    exact (RamWriteFrame.refl _ _).memStore _ ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), hins⟩
  · change memLoad out.store fr.rdi 64 = memLoad fr.original fr.rsi 64
    rw [hstore]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.ParseSignature
