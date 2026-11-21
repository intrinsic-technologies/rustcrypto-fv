import K256.Proofs.ParseSignature.Memory
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.LIR.Fn127d50.Frame
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

namespace K256.Proofs.ParseSignature

open K256.Spec K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

theorem blackBox_call {code : CodeMap} (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) :
    Call code .l127d50 LIR.Fn127d50.frameInfo fr [] fun out =>
      out.values[0] = ⟨64, (fr.rdi.setWidth 8).zeroExtend 64⟩ := by
  intro args hentry
  simp only [LIR.Fn127d50.frameInfo, FrameInfo.entryAtoms, FrameInfo.entryFrame,
    FrameInfo.frameAtoms, FrameInfo.entryRegs, FrameInfo.stackAtoms, FrameInfo.callSlotAtoms,
    FrameInfo.window, Activation.below, Activation.entryValue, Activation.entryReg, ite_eq_left,
    Option.getD_some, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, List.append_nil, Atom.All, Atom.Holds] at hentry
  rcases hentry with ⟨hsp, hdf, hcx, hdx, hbx, hbp, hsi, hdi, h8, h9, h12, h13, h14, h15,
    hmxcsr, hftw, hfcw, hread, hret, hretLow, hwrite, hroom, _, _⟩
  change fr.low.toNat + 1 ≤ fr.rsp.toNat at hroom
  let slot := fr.rsp - 1
  let byte := fr.rdi.setWidth 8
  have hstore : StoreOk code fr.original slot 1 0x127d54 4 := by
    exact storeOk_of_codeRange (off := 4) hwrite
      (fun x hx => hcode x (LIR.code_l127d50 x hx)) (by decide)
  have hslotLoad : LoadOk (memStore fr.original slot byte) slot 1 := by
    let h := hwrite.readable.memStore slot byte
    exact ⟨h.low, h.present⟩
  have hretLoad : LoadOk (memStore fr.original slot byte) fr.rsp 8 := by
    let h := hread.memStore slot byte
    exact ⟨h.low, h.present⟩
  have hslotValue := memLoad_memStore_same fr.original slot byte (by decide) (by decide)
  have hslotNat : slot.toNat + 1 = fr.rsp.toNat := by
    dsimp only [slot]
    bv_omega
  have hframe : RamWriteFrame fr.original (memStore fr.original slot byte) [fr.region] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨fr.region, List.mem_singleton_self _, ?_⟩
    change fr.low.toNat ≤ slot.toNat ∧
      slot.toNat + 1 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧
      slot.toNat + 1 ≤ 2 ^ 64
    have := fr.rsp.isLt
    omega
  have hretAddr : memLoad (memStore fr.original slot byte) fr.rsp 64 = fr.ret := by
    rw [hframe.memLoad_eq, hret]
    refine ⟨by have := hread.low; omega, ?_⟩
    intro r hr
    have hr' := List.mem_singleton.mp hr
    subst r
    right
    change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ fr.rsp.toNat
    omega
  have hspBits : Value.get 64 args[4] = fr.rsp := congrArg (Value.get 64) hsp
  have hdiBits : Value.get 64 args[7] = fr.rdi := congrArg (Value.get 64) hdi
  dsimp only [Activation.original, slot, byte] at hstore hslotLoad hretLoad hretAddr hslotValue
  refine ⟨?out, .done ?execution, ?tag, ?atoms, ?frame, ?widths, ?post⟩
  case execution =>
    change LIR.program.step (dialect code) _ = _
    cfg_eval
    simp only [hspBits, hdiBits, hstore, hslotLoad, hretLoad, hretAddr, hretLow, hslotValue,
      and_self, ite_true]
    rfl
  case tag => rfl
  case atoms =>
    simp only [LIR.Fn127d50.frameInfo, FrameInfo.doneAtoms, Activation.entryReg,
      Activation.entryValue, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      Atom.All, Atom.Holds]
    exact ⟨rfl, hdf, hbx, hbp, h12, h13, h14, h15, hmxcsr, hftw, hfcw, trivial⟩
  case frame => exact hframe
  case widths =>
    intro ⟨i, bound⟩ hi
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact congrArg Value.width hdi
      | exact congrArg Value.width hsi
      | exact congrArg Value.width hdx
      | exact congrArg Value.width hcx
      | exact congrArg Value.width h8
      | exact congrArg Value.width h9
      | rfl
  case post => rfl

end K256.Proofs.ParseSignature
