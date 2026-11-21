import K256.Proofs.ParseSignature.Contract
import K256.Proofs.LIR.Fn127d70.Frame
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

open Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

def FillSavedWord (mem : Ram) (addr value : BitVec 64) : Prop :=
  Readable mem addr 8 ∧ memLoad mem addr 64 = value

theorem FillSavedWord.of_frame {mem next : Ram} {regions : List MemoryRegion}
    {addr value : BitVec 64} (h : FillSavedWord mem addr value)
    (hf : RamWriteFrame mem next regions) (hout : Outside regions addr 8) :
    FillSavedWord next addr value :=
  ⟨h.1.of_frame hf, (hf.memLoad_eq hout).trans h.2⟩

structure FillSavedStack (fr : Activation) (mem : Ram) : Prop where
  rbx : FillSavedWord mem (fr.rsp - 48) fr.rbx
  r12 : FillSavedWord mem (fr.rsp - 40) fr.r12
  r13 : FillSavedWord mem (fr.rsp - 32) fr.r13
  r14 : FillSavedWord mem (fr.rsp - 24) fr.r14
  r15 : FillSavedWord mem (fr.rsp - 16) fr.r15
  rbp : FillSavedWord mem (fr.rsp - 8) fr.rbp
  ret : FillSavedWord mem fr.rsp fr.ret

theorem FillSavedStack.of_frame {fr : Activation} {mem next : Ram} {regions : List MemoryRegion}
    (h : FillSavedStack fr mem) (hf : RamWriteFrame mem next regions)
    (hout : ∀ off ∈ ([48, 40, 32, 24, 16, 8, 0] : List (BitVec 64)),
      Outside regions (fr.rsp - off) 8) :
    FillSavedStack fr next := by
  refine ⟨h.rbx.of_frame hf (hout 48 (by decide)), h.r12.of_frame hf (hout 40 (by decide)),
    h.r13.of_frame hf (hout 32 (by decide)), h.r14.of_frame hf (hout 24 (by decide)),
    h.r15.of_frame hf (hout 16 (by decide)), h.rbp.of_frame hf (hout 8 (by decide)),
    h.ret.of_frame hf ?_⟩
  have hs := hout 0 (by decide)
  change Outside regions (fr.rsp - (0 : BitVec 64)) 8 at hs
  have hz : fr.rsp - (0 : BitVec 64) = fr.rsp := BitVec.sub_zero _
  rwa [hz] at hs

private theorem FillSavedWord.loadOk {mem : Ram} {addr value : BitVec 64}
    (h : FillSavedWord mem addr value) : LoadOk mem addr 8 :=
  ⟨h.1.low, h.1.present⟩

set_option maxHeartbeats 600000 in
theorem fill_return {code : CodeMap} (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hbx : args[3] = ⟨64, 256⟩) (hsp : args[4] = ⟨64, fr.rsp - 72⟩)
    (hwidths : ArgumentWidths args)
    (hdf : args[22] = ⟨1, 0⟩) (hmxcsr : args[39] = ⟨32, fr.mxcsr⟩)
    (hftw : args[50] = ⟨16, fr.ftw⟩) (hfcw : args[51] = ⟨16, fr.fcw⟩)
    (hsaved : FillSavedStack fr mem) (hretLow : fr.ret.toNat < 2 ^ (32 : Nat)) :
    ∃ out : Output Value Ram Reg.count,
      program.Exec (dialect code) ⟨⟨.l127e50, args, mem⟩, []⟩ out ∧
      out.store = mem ∧ out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code out.values out.store (Fn127d70.frameInfo.doneAtoms fr) ∧
      ArgumentWidths out.values ∧ out.values[0].get 8 = 255 := by
  have hb : Value.get 64 args[3] = 256 := congrArg (Value.get 64) hbx
  let nextArgs : Values Value Reg.count :=
    #v[⟨64, mergeGPR 8 255 (args[0].get 64)⟩, ⟨64, 0⟩, args[2], args[3], args[4], args[5], args[6],
    args[7], args[8], args[9], args[10], args[11], args[12], args[13], args[14], args[15],
    args[16], args[17], args[18], Value.ofBool true, args[20], args[21], args[22], args[23],
    args[24], args[25], args[26], args[27], args[28], args[29], args[30], args[31], args[32],
    args[33], args[34], args[35], args[36], args[37], args[38], args[39], args[40], args[41],
    args[42], args[43], args[44], args[45], args[46], args[47], args[48], args[49], args[50],
    args[51], args[52]]
  have hbranch : program.step (dialect code) ⟨⟨.l127e50, args, mem⟩, []⟩ =
      .next ⟨⟨.l127e76, nextArgs, mem⟩, []⟩ := by
    cfg_eval
    rw [hb]
    have hz : (andFlags ((256 : BitVec 64).setWidth 32 &&& 63)).ZF.getD false = true := rfl
    simp only [hz, ite_true]
    rfl
  let outArgs : Values Value Reg.count :=
    #v[⟨64, mergeGPR 8 255 (args[0].get 64)⟩, ⟨64, 0⟩, args[2], ⟨64, fr.rbx⟩, ⟨64, fr.rsp + 8⟩,
    ⟨64, fr.rbp⟩, args[6], args[7], args[8], args[9], args[10], args[11], ⟨64, fr.r12⟩, ⟨64, fr.r13⟩,
    ⟨64, fr.r14⟩, ⟨64, fr.r15⟩, args[16], args[17], args[18], Value.ofBool true, args[20],
    args[21], args[22], args[23], args[24], args[25], args[26], args[27], args[28], args[29],
    args[30], args[31], args[32], args[33], args[34], args[35], args[36], args[37], args[38],
    args[39], args[40], args[41], args[42], args[43], args[44], args[45], args[46], args[47],
    args[48], args[49], args[50], args[51], args[52]]
  refine ⟨⟨outArgs, some ⟨64, fr.ret⟩, mem⟩, .next hbranch (.done ?_), rfl, rfl, ?_, ?_, ?_⟩
  · have hs : Value.get 64 args[4] = fr.rsp - 72 := congrArg (Value.get 64) hsp
    have a24 : fr.rsp - 72 + 24 = fr.rsp - 48 := by bv_omega
    have a32 : fr.rsp - 72 + 32 = fr.rsp - 40 := by bv_omega
    have a40 : fr.rsp - 72 + 40 = fr.rsp - 32 := by bv_omega
    have a48 : fr.rsp - 72 + 48 = fr.rsp - 24 := by bv_omega
    have a56 : fr.rsp - 72 + 56 = fr.rsp - 16 := by bv_omega
    have a64 : fr.rsp - 72 + 64 = fr.rsp - 8 := by bv_omega
    have a72 : fr.rsp - 72 + 72 = fr.rsp := by bv_omega
    have a80 : fr.rsp - 72 + 80 = fr.rsp + 8 := by bv_omega
    cfg_eval
    simp only [hs, a24, a32, a40, a48, a56, a64, a72, a80, hsaved.rbx.loadOk,
      hsaved.r12.loadOk, hsaved.r13.loadOk, hsaved.r14.loadOk, hsaved.r15.loadOk,
      hsaved.rbp.loadOk, hsaved.ret.loadOk, hsaved.rbx.2, hsaved.r12.2, hsaved.r13.2,
      hsaved.r14.2, hsaved.r15.2, hsaved.rbp.2, hsaved.ret.2, hretLow, and_self, ↓reduceIte]
    rfl
  · simp only [Fn127d70.frameInfo, FrameInfo.doneAtoms, Activation.entryReg,
      Activation.entryValue, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      Atom.All, Atom.Holds]
    exact ⟨rfl, hdf, rfl, rfl, rfl, rfl, rfl, rfl, hmxcsr, hftw, hfcw, trivial⟩
  · intro ⟨i, bound⟩ hi
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hwidths 7 (by decide)
    · exact hwidths 6 (by decide)
    · exact hwidths 2 (by decide)
    · rfl
    · exact hwidths 8 (by decide)
    · exact hwidths 9 (by decide)
  · change (mergeGPR 8 255 (args[0].get 64)).setWidth 8 = 255
    exact setWidth_mergeGPR8 _ _

end K256.Proofs.ParseSignature
