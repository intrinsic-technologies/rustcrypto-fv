import AesGcm.Proofs.Machine.Core.Decrypt.Counter
import AesGcm.Proofs.Machine.Core.Decrypt.Branches
import AesGcm.Proofs.Machine.Core.Decrypt.Finish

namespace AesGcm.Proofs.Machine.Core.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 800000 in
theorem empty_exec (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (hworking : Atom.All code args mem
      (if use256 then LIR.Fn102720.frameAt .l102849 fr else LIR.Fn1022c0.frameAt .l1023e9 fr))
    (hTypes : GPRsTyped args) (hlen : args[14].get 64 = 0) :
    ∃ output : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code)
        ⟨⟨(if use256 then .l102849 else .l1023e9),args,mem⟩,[]⟩ output ∧
      output.tag = some ⟨64,fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Fn102720.frameInfo else LIR.Fn1022c0.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values ∧ RamWriteFrame mem output.store [span (fr.rsp - 128) 28] ∧
      output.values[0].get 8 = args[0].get 8 := by
  obtain ⟨counter,cRun,cLabel,cFrame,cTyped,cWrites,cKeep,c15,cWords⟩ :=
    counter_reaches use256 code hcode fr args mem hworking hTypes
  have cLabel' : counter.label = (if use256 then .l1028dc else .l10247c) := by
    have small : (args[14].get 64).toNat < 17 := by rw [hlen]; decide
    simpa only [small, ↓reduceIte] using cLabel
  rw [cLabel'] at cFrame
  have cLength : (counter.arguments[14]'(by change 14 < 53; decide)).get 64 = 0 :=
    (congrArg (Value.get 64) (cKeep 14 (by decide))).trans hlen
  obtain ⟨last,lRun,lLabel,lMemory,l13,lKeep,lTyped⟩ :=
    small_runBlock use256 code counter.arguments counter.store
  have lLabel' : last.label = (if use256 then .l102961 else .l102501) := by
    simpa only [cLength, ↓reduceIte] using lLabel
  let window : Nat := if use256 then 2912 else 2384
  have facts : counter.arguments[4]'(by change 4 < 53; decide) = ⟨64, fr.rsp - 216⟩ ∧
      counter.arguments[22]'(by change 22 < 53; decide) = ⟨1,0⟩ ∧
      counter.arguments[5]'(by change 5 < 53; decide) = ⟨64,fr.rcx⟩ ∧
      counter.arguments[13]'(by change 13 < 53; decide) = ⟨64,fr.r9⟩ ∧
      counter.arguments[39]'(by change 39 < 53; decide) = ⟨32,fr.mxcsr⟩ ∧
      counter.arguments[50]'(by change 50 < 53; decide) = ⟨16,fr.ftw⟩ ∧
      counter.arguments[51]'(by change 51 < 53; decide) = ⟨16,fr.fcw⟩ ∧
      memLoad counter.store (fr.rsp - 152) 64 = fr.r8 ∧
      memLoad counter.store (fr.rsp - 136) 64 = fr.rdx ∧
      memLoad counter.store (fr.rsp - 48) 64 = fr.rbx ∧
      memLoad counter.store (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad counter.store (fr.rsp - 32) 64 = fr.r13 ∧
      memLoad counter.store (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad counter.store (fr.rsp - 16) 64 = fr.r15 ∧
      memLoad counter.store (fr.rsp - 8) 64 = fr.rbp ∧
      Readable counter.store fr.rsp 8 ∧ memLoad counter.store fr.rsp 64 = fr.ret ∧
      fr.ret.toNat < 2^32 ∧ Writable code counter.store (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Atom.All code counter.arguments counter.store
        ((if use256 then LIR.Fn102720.frameInfo else LIR.Fn1022c0.frameInfo).callSlotAtoms
          (if use256 then LIR.Fn102720.frameInfo else LIR.Fn1022c0.frameInfo).callSlots fr) := by
    cases use256 <;> exact cFrame
  obtain ⟨a4,a22,a5,a13,a39,a50,a51,hd,ha,s3,s12,s13,s14,s15,s5,hr,hret,hrl,hw,hroom,halign,hslots⟩ := facts
  have lsp : (last.arguments[4]'(by change 4 < 53; decide)).get 64 = fr.rsp - 216 :=
    congrArg (Value.get 64) ((lKeep 4 (by decide)).trans a4)
  have readable : Readable last.store ((last.arguments[4]'(by change 4 < 53; decide)).get 64 + 168) 56 := by
    have addr : (last.arguments[4]'(by change 4 < 53; decide)).get 64 + 168 = fr.rsp - 48 := by
      rw [lsp]; bv_omega
    rw [lMemory,addr]
    apply readable_append (n := 48) (k := 8)
    · apply hw.readable.of_offsets (addr_sub _ _) (addr_sub _ _)
      cases use256 <;> decide +kernel
    · change Readable counter.store (fr.rsp - 48 + 48) 8
      rw [BitVec.sub_add_cancel]
      exact hr
  obtain ⟨output,hexec,htag,hdone,ht,hm,h0⟩ := finish_exec use256 code fr
    last.arguments last.store (lTyped cTyped) lsp readable
    (by rw [lMemory]; exact hret) hrl
    (by rw [lMemory]; exact s3) (by rw [lMemory]; exact s12)
    (by rw [lMemory]; exact s13) (by rw [lMemory]; exact s14)
    (by rw [lMemory]; exact s15) (by rw [lMemory]; exact s5)
    ((lKeep 22 (by decide)).trans a22) ((lKeep 39 (by decide)).trans a39)
    ((lKeep 50 (by decide)).trans a50) ((lKeep 51 (by decide)).trans a51)
  have smallStep : LIR.program.step (dialect code)
      ⟨⟨(if use256 then .l1028dc else .l10247c),counter.arguments,counter.store⟩,[]⟩ =
      .next ⟨last,[]⟩ := by
    rw [Program.step,lRun]
    rfl
  have step : (LIR.program.sem (dialect code)).Reaches ⟨counter,[]⟩ ⟨last,[]⟩ := by
    change (LIR.program.sem (dialect code)).Reaches
      ⟨⟨counter.label,counter.arguments,counter.store⟩,[]⟩ ⟨last,[]⟩
    rw [cLabel']
    exact Semantics.Reaches.single smallStep
  have exec : LIR.program.Exec (dialect code)
      ⟨⟨(if use256 then .l102849 else .l1023e9),args,mem⟩,[]⟩ output := by
    apply Program.Exec.of_sem
    apply (cRun.trans step).exec
    change (LIR.program.sem (dialect code)).Exec
      ⟨⟨last.label,last.arguments,last.store⟩,[]⟩ output
    rw [lLabel']
    exact hexec.sem
  refine ⟨output,exec,htag,hdone,ht,?_,?_⟩
  · rw [hm,lMemory]
    exact cWrites
  · rw [h0]
    exact congrArg (Value.get 8) ((lKeep 0 (by decide)).trans (cKeep 0 (by decide)))

end AesGcm.Proofs.Machine.Core.Decrypt
