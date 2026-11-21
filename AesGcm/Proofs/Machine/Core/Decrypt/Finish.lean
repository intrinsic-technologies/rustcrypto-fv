import AesGcm.Proofs.Machine.Core.Decrypt.Native
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102720.Frame

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem finish_exec (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (hTypes : GPRsTyped args)
    (hsp : args[4].get 64 = fr.rsp - 216)
    (hr : Readable mem (args[4].get 64 + 168) 56)
    (hret : memLoad mem fr.rsp 64 = fr.ret) (hretLow : fr.ret.toNat < 2^32)
    (h3 : memLoad mem (fr.rsp - 48) 64 = fr.rbx)
    (h12 : memLoad mem (fr.rsp - 40) 64 = fr.r12)
    (h13 : memLoad mem (fr.rsp - 32) 64 = fr.r13)
    (h14 : memLoad mem (fr.rsp - 24) 64 = fr.r14)
    (h15 : memLoad mem (fr.rsp - 16) 64 = fr.r15)
    (h5 : memLoad mem (fr.rsp - 8) 64 = fr.rbp)
    (h22 : args[22] = ⟨1, 0⟩) (h39 : args[39] = ⟨32, fr.mxcsr⟩)
    (h50 : args[50] = ⟨16, fr.ftw⟩) (h51 : args[51] = ⟨16, fr.fcw⟩) :
    ∃ output,
      LIR.program.Exec (dialect code)
        ⟨⟨(if use256 then .l102961 else .l102501), args, mem⟩, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Fn102720.frameInfo else
          LIR.Fn1022c0.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values ∧ output.store = mem ∧ output.values[0] = args[0] := by
  have he : args[4].get 64 + 216 = fr.rsp := by
    rw [hsp]
    bv_omega
  obtain ⟨output, hx, hm, ht, o4, o3, o12, o13, o14, o15, o5, keep, typed⟩ :=
    exit_runBlock use256 code args mem hr (by rw [he, hret]; exact hretLow)
  refine ⟨output, .done ?_, ?_, ?_, typed hTypes, hm, keep 0 (by decide)⟩
  · change (LIR.program.runBlock (dialect code) _).next (dialect code) [] = .done output
    rw [hx]
    rfl
  · rw [ht, he, hret]
  · have h4' : output.values[4] = ⟨64, fr.rsp + 8⟩ := by
      rw [o4, hsp]
      congr 1
      bv_omega
    have h3' : output.values[3] = ⟨64, fr.rbx⟩ := by
      rw [o3, hsp]
      have he' : fr.rsp - 216 +
          168 = fr.rsp - 48 := by bv_omega
      rw [he', h3]
    have h12' : output.values[12] = ⟨64, fr.r12⟩ := by
      rw [o12, hsp]
      have he' : fr.rsp - 216 +
          176 = fr.rsp - 40 := by bv_omega
      rw [he', h12]
    have h13' : output.values[13] = ⟨64, fr.r13⟩ := by
      rw [o13, hsp]
      have he' : fr.rsp - 216 +
          184 = fr.rsp - 32 := by bv_omega
      rw [he', h13]
    have h14' : output.values[14] = ⟨64, fr.r14⟩ := by
      rw [o14, hsp]
      have he' : fr.rsp - 216 +
          192 = fr.rsp - 24 := by bv_omega
      rw [he', h14]
    have h15' : output.values[15] = ⟨64, fr.r15⟩ := by
      rw [o15, hsp]
      have he' : fr.rsp - 216 +
          200 = fr.rsp - 16 := by bv_omega
      rw [he', h15]
    have h5' : output.values[5] = ⟨64, fr.rbp⟩ := by
      rw [o5, hsp]
      have he' : fr.rsp - 216 +
          208 = fr.rsp - 8 := by bv_omega
      rw [he', h5]
    have hd : Atom.All code output.values output.store
        (LIR.Fn1022c0.frameInfo.doneAtoms fr) := by
      exact ⟨h4', (keep 22 (by decide)).trans h22, h3', h5', h12', h13', h14', h15',
        (keep 39 (by decide)).trans h39, (keep 50 (by decide)).trans h50,
        (keep 51 (by decide)).trans h51, trivial⟩
    cases use256 <;> exact hd

end AesGcm.Proofs.Machine.Core.Decrypt
