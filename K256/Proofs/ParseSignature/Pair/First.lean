import K256.Proofs.ParseSignature.Pair.Preparation.Atoms
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

namespace K256.Proofs.ParseSignature.Pair

open Standards.SECG.DomainParameters K256.Proofs.Common X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

theorem firstScalarEntry {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count)
    (hentry : Atom.All code args fr.original (Fn103ac0.frameInfo.entryAtoms fr))
    (hr : Readable fr.original fr.rsi 64) (hin : Outside [callStack fr] fr.rsi 64) :
    ∃ regs mem, program.runBlock (dialect code) ⟨.l103ac0, args, fr.original⟩ =
      .call ⟨.l107730, regs, mem⟩ (resumeAt .l103b07 0x103b07) ∧
      ScalarEntry code fr 0x103b07 fr.rsi regs mem := by
  change Atom.All code args fr.original (Fn103ac0.frameAt .l103ac0 fr) at hentry
  simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds] at hentry
  obtain ⟨hsp, df, _, _, bx, bp, si, di, h8, h9, h12, h13, h14, h15, mx, ftw, fcw, read,
    ret, small, win, room, align, s1, v1, s2, v2, s3, v3, apart, _⟩ := hentry
  change fr.low.toNat + 560 ≤ fr.rsp.toNat at room
  change Writable code fr.original (fr.rsp - 560) 560 at win
  have guard {m : Ram} (f : RamWriteFrame fr.original m (topWrites fr)) (off pc n : Nat)
      (ho : off ≤ 560 := by decide) (hw : 8 ≤ off := by decide)
      (hlen : pc + n ≤ bytes_l103ac0.length := by decide) :
      StoreOk code m (fr.rsp - BitVec.ofNat 64 off) 8 (0x103ac0 + BitVec.ofNat 64 pc) n :=
    storeOk_of_codeRange (stackWordWritable (win.of_frame f) off ho hw)
      (fun x hx => hcode x (code_l103ac0 x hx)) hlen
  have originalFrame {m : Ram} (frame : RamWriteFrame fr.original m (topWrites fr)) :
      RamWriteFrame fr.original m [fr.region] :=
    (RamWriteFrame.refl _ _).trans frame (topWritesWithin room)
  have f0 : RamWriteFrame fr.original fr.original (topWrites fr) := .refl _ _
  let m1 := memStore fr.original (fr.rsp - 8) fr.r14
  let m2 := memStore m1 (fr.rsp - 16) fr.rbx
  let m3 := memStore m2 (fr.rsp - 88) (memLoad fr.original (fr.rsi + 24) 64)
  let m4 := memStore m3 (fr.rsp - 96) (memLoad fr.original (fr.rsi + 16) 64)
  let m5 := memStore m4 (fr.rsp - 104) (memLoad fr.original (fr.rsi + 8) 64)
  let m6 := memStore m5 (fr.rsp - 112) (memLoad fr.original fr.rsi 64)
  have f1 : RamWriteFrame fr.original m1 (topWrites fr) := topWordFrame room f0 8 _ (by decide) (by decide)
  have f2 : RamWriteFrame fr.original m2 (topWrites fr) := topWordFrame room f1 16 _ (by decide) (by decide)
  have f3 : RamWriteFrame fr.original m3 (topWrites fr) := topWordFrame room f2 88 _ (by decide) (by decide)
  have f4 : RamWriteFrame fr.original m4 (topWrites fr) := topWordFrame room f3 96 _ (by decide) (by decide)
  have f5 : RamWriteFrame fr.original m5 (topWrites fr) := topWordFrame room f4 104 _ (by decide) (by decide)
  have f6 : RamWriteFrame fr.original m6 (topWrites fr) := topWordFrame room f5 112 _ (by decide) (by decide)
  have g1 : StoreOk code fr.original (fr.rsp - 8) 8 0x103ac0 2 := guard f0 8 0 2
  have g2 : StoreOk code m1 (fr.rsp - 16) 8 0x103ac2 1 := guard f1 16 2 1
  have g3 : StoreOk code m2 (fr.rsp - 88) 8 0x103ad4 5 := guard f2 88 20 5
  have g4 : StoreOk code m3 (fr.rsp - 96) 8 0x103add 5 := guard f3 96 29 5
  have g5 : StoreOk code m4 (fr.rsp - 104) 8 0x103ae9 5 := guard f4 104 41 5
  have g6 : StoreOk code m5 (fr.rsp - 112) 8 0x103aee 5 := guard f5 112 46 5
  have g7 : StoreOk code m6 (fr.rsp - 192) 8 0x103b02 5 := guard f6 192 66 5
  obtain ⟨l24, w24⟩ : LoadOk m2 (fr.rsi + 24) 8 ∧
      memLoad m2 (fr.rsi + 24) 64 = memLoad fr.original (fr.rsi + 24) 64 := inputWord room hr hin (originalFrame f2) 24 (by decide)
  obtain ⟨l16, w16⟩ : LoadOk m3 (fr.rsi + 16) 8 ∧
      memLoad m3 (fr.rsi + 16) 64 = memLoad fr.original (fr.rsi + 16) 64 := inputWord room hr hin (originalFrame f3) 16 (by decide)
  have lw0 := inputWord room hr hin (originalFrame f4) 0 (by decide)
  change LoadOk m4 (fr.rsi + 0) 8 ∧ memLoad m4 (fr.rsi + 0) 64 = memLoad _ (fr.rsi + 0) 64 at lw0
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at lw0
  obtain ⟨l0, w0⟩ := lw0
  obtain ⟨l8, w8⟩ : LoadOk m4 (fr.rsi + 8) 8 ∧
      memLoad m4 (fr.rsi + 8) 64 = memLoad fr.original (fr.rsi + 8) 64 := inputWord room hr hin (originalFrame f4) 8 (by decide)
  have rsp : args[4].get 64 = fr.rsp := congrArg (Value.get 64) hsp
  have r14 : args[14].get 64 = fr.r14 := congrArg (Value.get 64) h14
  have rbx : args[3].get 64 = fr.rbx := congrArg (Value.get 64) bx
  have rsi : args[6].get 64 = fr.rsi := congrArg (Value.get 64) si
  have rdi : args[7].get 64 = fr.rdi := congrArg (Value.get 64) di
  let after := putScalar fr m2 fr.rsi 0x103b07
  refine ⟨?regs, after, ?block, ?result⟩
  case block =>
    cfg_eval
    dsimp only [m1, m2, m3, m4, m5, m6] at g1 g2 g3 g4 g5 g6 g7 l24 w24 l16 w16 l8 w8 l0 w0
    simp only [rsp, r14, rbx, rsi, rdi, g1, g2, g3, g4, g5, g6, g7,
      l24, w24, l16, w16, l8, w8, l0, w0, ↓reduceIte]
    rfl
  case result =>
    apply scalarEntry_of_copy fr.rsi 0x103b07 room (originalFrame f2)
    · have tail : Atom.All code args fr.original ((callerLayout fr).drop 13) :=
        ⟨read, ret, small, win, room, align, s1, v1, s2, v2, s3, v3, apart, trivial⟩
      apply callerAtoms tail _ _ _ (putScalar_top room f2 fr.rsi 0x103b07)
      · exact ⟨rfl, df, rfl, bp, h12, h13, rfl, h15, mx, ftw, fcw, trivial⟩
      · rw [show memLoad (putScalar fr m2 fr.rsi 0x103b07) (fr.rsp - 16) 64 = _ from
          putScalar_keep fr m2 fr.rsi 0x103b07 16 (by decide) (by decide) (by decide)]
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · rw [show memLoad (putScalar fr m2 fr.rsi 0x103b07) (fr.rsp - 8) 64 = _ from
          putScalar_keep fr m2 fr.rsi 0x103b07 8 (by decide) (by decide) (by decide)]
        have keep : memLoad m2 (fr.rsp - 8) 64 = memLoad m1 (fr.rsp - 8) 64 :=
          stackWordKeep fr m1 16 8 _ (by decide) (by decide) (by decide)
        exact keep.trans (memLoad_memStore_same _ _ _ (by decide) (by decide))
    · intro i hi
      obtain ⟨i, bound⟩ := i
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | exact congrArg Value.width h8 | exact congrArg Value.width h9
    · rfl
    · exact congrArg (Value.mk 64) (show fr.rsp - 176 = fr.rsp - 184 + 8 by bv_omega)
    · exact congrArg (Value.mk 64) (show fr.rsp - 112 = fr.rsp - 184 + 72 by bv_omega)
    · rfl
    · decide

end K256.Proofs.ParseSignature.Pair
