import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Blocks
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Branch
import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Frames
import AesGcm.Proofs.Machine.Runtime.Preservation
import AesGcm.Proofs.Machine.LIR.Aes128gcmDecryptInPlace.Frame
import AesGcm.Proofs.Machine.LIR.Aes256gcmDecryptInPlace.Frame

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem finish_exec (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (hTypes : GPRsTyped args)
    (hsp : args[4].get 64 = fr.rsp - (if use256 then 584 else 456))
    (hr : Readable mem (args[4].get 64) (if use256 then 592 else 464))
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
        ⟨⟨(if use256 then .l1015b2 else .l1012d2), args, mem⟩, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Aes256gcmDecryptInPlace.frameInfo else
          LIR.Aes128gcmDecryptInPlace.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values ∧ output.store = mem ∧ output.values[0] = args[0] := by
  have he : args[4].get 64 + (if use256 then 584 else 456) = fr.rsp := by
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
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
    have h3' : output.values[3] = ⟨64, fr.rbx⟩ := by
      rw [o3, hsp]
      have he' : fr.rsp - (if use256 then 584 else 456) +
          (if use256 then 536 else 408) = fr.rsp - 48 := by cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
      rw [he', h3]
    have h12' : output.values[12] = ⟨64, fr.r12⟩ := by
      rw [o12, hsp]
      have he' : fr.rsp - (if use256 then 584 else 456) +
          (if use256 then 544 else 416) = fr.rsp - 40 := by cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
      rw [he', h12]
    have h13' : output.values[13] = ⟨64, fr.r13⟩ := by
      rw [o13, hsp]
      have he' : fr.rsp - (if use256 then 584 else 456) +
          (if use256 then 552 else 424) = fr.rsp - 32 := by cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
      rw [he', h13]
    have h14' : output.values[14] = ⟨64, fr.r14⟩ := by
      rw [o14, hsp]
      have he' : fr.rsp - (if use256 then 584 else 456) +
          (if use256 then 560 else 432) = fr.rsp - 24 := by cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
      rw [he', h14]
    have h15' : output.values[15] = ⟨64, fr.r15⟩ := by
      rw [o15, hsp]
      have he' : fr.rsp - (if use256 then 584 else 456) +
          (if use256 then 568 else 440) = fr.rsp - 16 := by cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
      rw [he', h15]
    have h5' : output.values[5] = ⟨64, fr.rbp⟩ := by
      rw [o5, hsp]
      have he' : fr.rsp - (if use256 then 584 else 456) +
          (if use256 then 576 else 448) = fr.rsp - 8 := by cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
      rw [he', h5]
    have hd : Atom.All code output.values output.store
        (LIR.Aes128gcmDecryptInPlace.frameInfo.doneAtoms fr) := by
      exact ⟨h4', (keep 22 (by decide)).trans h22, h3', h5', h12', h13', h14', h15',
        (keep 39 (by decide)).trans h39, (keep 50 (by decide)).trans h50,
        (keep 51 (by decide)).trans h51, trivial⟩
    cases use256 <;> exact hd


set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem reject_exec (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram) (hTypes : GPRsTyped args)
    (hworking : Atom.All code args mem
      (if use256 then LIR.Aes256gcmDecryptInPlace.frameAt .l101560 fr else
        LIR.Aes128gcmDecryptInPlace.frameAt .l101280 fr))
    (hshort : fr.r9.toNat < 16) :
    ∃ output,
      LIR.program.Exec (dialect code)
        ⟨⟨(if use256 then .l101560 else .l101280), args, mem⟩, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Aes256gcmDecryptInPlace.frameInfo else
          LIR.Aes128gcmDecryptInPlace.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values ∧ output.store = mem ∧ output.values[0] = ⟨64, 1⟩ := by
  have hworking' :
      args[4] = ⟨64, fr.rsp - (if use256 then 584 else 456)⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[3] = ⟨64, fr.rcx⟩ ∧ args[12] = ⟨64, fr.r8⟩ ∧ args[13] = ⟨64, fr.r9⟩ ∧
      args[14] = ⟨64, fr.rdx⟩ ∧ args[15] = ⟨64, fr.rsi⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧ memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧ memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧ memLoad mem (fr.rsp - 8) 64 = fr.rbp ∧
      Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code mem (fr.rsp - (if use256 then 3504 else 2848))
        (if use256 then 3504 else 2848) := by
    cases use256
    all_goals
      rcases hworking with ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, rest⟩
      exact ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19⟩
  rcases hworking' with ⟨hsp, h22, -, -, hlen, -, -, h39, h50, h51,
    h3, h12, h13, h14, h15, h5, hreturnRead, hret, hretLow, hstack⟩
  obtain ⟨next, hbranch, hlabel, hmem, hstatus, keep, typed⟩ :=
    length_runBlock use256 code args mem hTypes
  have hlabel' : next.label = (if use256 then .l1015b2 else .l1012d2) := by
    rw [hlabel, hlen]
    simp only [Value.get, BitVec.setWidth_eq, hshort, ↓reduceIte]
  have localRead : Readable mem (args[4].get 64) (if use256 then 592 else 464) := by
    have hr : Readable mem (fr.rsp - (if use256 then 584 else 456))
        (if use256 then 584 else 456) := by
      apply hstack.readable.of_offsets (addr_sub _ _) (addr_sub _ _)
      cases use256 <;> decide +kernel
    have hsum : fr.rsp - (if use256 then 584 else 456) +
        BitVec.ofNat 64 (if use256 then 584 else 456) = fr.rsp := by
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> bv_omega
    have hr' := readable_append hr (by rw [hsum]; exact hreturnRead)
    rw [hsp]
    cases use256 <;> exact hr'
  have nsp : next.arguments[4]'(by change 4 < 53; decide) = args[4] := keep 4 (by decide)
  obtain ⟨output, hx, ht, hd, htypes, hm, hzero⟩ := finish_exec use256 code fr
    next.arguments mem typed
    (by rw [nsp, hsp]; rfl) (by rw [nsp]; exact localRead)
    hret hretLow h3 h12 h13 h14 h15 h5
    ((keep 22 (by decide)).trans h22) ((keep 39 (by decide)).trans h39)
    ((keep 50 (by decide)).trans h50) ((keep 51 (by decide)).trans h51)
  refine ⟨output, ?_, ht, hd, htypes, hm, hzero.trans hstatus⟩
  apply Program.Exec.next (next := ⟨next, []⟩)
  · simp only [Program.step, hbranch, Transfer.next]
  · have hloc : next = ⟨(if use256 then .l1015b2 else .l1012d2), next.arguments, mem⟩ := by
      cases next with
      | mk label arguments store =>
        dsimp only at hlabel' hmem ⊢
        subst label store
        rfl
    rw [hloc]
    exact hx

theorem status_exec (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (hTypes : GPRsTyped args)
    (hsp : args[4].get 64 = fr.rsp - (if use256 then 584 else 456))
    (hr : Readable mem (args[4].get 64) (if use256 then 592 else 464))
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
        ⟨⟨(if use256 then .l1015af else .l1012cf), args, mem⟩, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Aes256gcmDecryptInPlace.frameInfo else
          LIR.Aes128gcmDecryptInPlace.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values ∧ output.store = mem ∧
      output.values[0] = ⟨64, (args[0].get 8).setWidth 64⟩ := by
  obtain ⟨next, hstep, hlabel, hmem, hstatus, keep, typed⟩ :=
    status_runBlock use256 code args mem hTypes
  have nsp : next.arguments[4]'(by change 4 < 53; decide) = args[4] := keep 4 (by decide)
  obtain ⟨output, hx, ht, hd, htypes, hm, hzero⟩ := finish_exec use256 code fr
    next.arguments mem typed
    (by rw [nsp]; exact hsp) (by rw [nsp]; exact hr)
    hret hretLow h3 h12 h13 h14 h15 h5
    ((keep 22 (by decide)).trans h22) ((keep 39 (by decide)).trans h39)
    ((keep 50 (by decide)).trans h50) ((keep 51 (by decide)).trans h51)
  refine ⟨output, ?_, ht, hd, htypes, hm, hzero.trans hstatus⟩
  apply Program.Exec.next (next := ⟨next, []⟩)
  · simp only [Program.step, hstep, Transfer.next]
  · have hloc : next = ⟨(if use256 then .l1015b2 else .l1012d2), next.arguments, mem⟩ := by
      cases next with
      | mk label arguments store =>
        dsimp only at hlabel hmem ⊢
        subst label store
        rfl
    rw [hloc]
    exact hx

theorem status_exec_of_frame (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (before mem : Ram)
    (regions : List MemoryRegion) (hf : RamWriteFrame before mem regions)
    (hout : Outside regions (fr.rsp - 48) 56)
    (hTypes : GPRsTyped args)
    (hsp : args[4].get 64 = fr.rsp - (if use256 then 584 else 456))
    (hr : Readable before (args[4].get 64) (if use256 then 592 else 464))
    (hret : memLoad before fr.rsp 64 = fr.ret) (hretLow : fr.ret.toNat < 2^32)
    (h3 : memLoad before (fr.rsp - 48) 64 = fr.rbx)
    (h12 : memLoad before (fr.rsp - 40) 64 = fr.r12)
    (h13 : memLoad before (fr.rsp - 32) 64 = fr.r13)
    (h14 : memLoad before (fr.rsp - 24) 64 = fr.r14)
    (h15 : memLoad before (fr.rsp - 16) 64 = fr.r15)
    (h5 : memLoad before (fr.rsp - 8) 64 = fr.rbp)
    (h22 : args[22] = ⟨1, 0⟩) (h39 : args[39] = ⟨32, fr.mxcsr⟩)
    (h50 : args[50] = ⟨16, fr.ftw⟩) (h51 : args[51] = ⟨16, fr.fcw⟩) :
    ∃ output,
      LIR.program.Exec (dialect code)
        ⟨⟨(if use256 then .l1015af else .l1012cf), args, mem⟩, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Aes256gcmDecryptInPlace.frameInfo else
          LIR.Aes128gcmDecryptInPlace.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values ∧ output.store = mem ∧
      output.values[0] = ⟨64, (args[0].get 8).setWidth 64⟩ := by
  have hload (offset : Nat) (hoffset : offset ≤ 48) :
      memLoad mem (fr.rsp - 48 + BitVec.ofNat 64 offset) 64 =
      memLoad before (fr.rsp - 48 + BitVec.ofNat 64 offset) 64 :=
    hf.memLoad_eq (outside_subregion hout (by omega) (by omega))
  have he (offset : Nat) (hoffset : offset ≤ 48) :
      fr.rsp - (48 : BitVec 64) + BitVec.ofNat 64 offset =
        fr.rsp - BitVec.ofNat 64 (48 - offset) := by
    rw [← BitVec.ofNat_sub_ofNat_of_le 48 offset (by omega) hoffset]
    bv_omega
  have hload' (offset : Nat) (hoffset : offset ≤ 48) :
      memLoad mem (fr.rsp - BitVec.ofNat 64 (48 - offset)) 64 =
      memLoad before (fr.rsp - BitVec.ofNat 64 (48 - offset)) 64 := by
    simpa only [he offset hoffset] using hload offset hoffset
  apply status_exec use256 code fr args mem hTypes hsp (hr.of_frame hf)
  · have hh := hload' 48 (by decide)
    simp only [Nat.sub_self, BitVec.sub_zero] at hh
    exact hh.trans hret
  · exact hretLow
  · exact (hload' 0 (by decide)).trans h3
  · exact (hload' 8 (by decide)).trans h12
  · exact (hload' 16 (by decide)).trans h13
  · exact (hload' 24 (by decide)).trans h14
  · exact (hload' 32 (by decide)).trans h15
  · exact (hload' 40 (by decide)).trans h5
  · exact h22
  · exact h39
  · exact h50
  · exact h51

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
