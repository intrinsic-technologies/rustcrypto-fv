import AesGcm.Proofs.Machine.CTR.Outer.Prefix
import AesGcm.Proofs.Machine.CTR.Outer.Step
import AesGcm.Proofs.Machine.CTR.Outer.Tail
import AesGcm.Proofs.Machine.CTR.OuterLoop

namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem crypt_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (input : ByteArray) (blockCount : Nat)
    (hsize : input.size = 16 * blockCount)
    (schedule counter source destination : BitVec 64) :
    CallContract LIR.lifted code (if use256 then .l1084e0 else .l107050)
      (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo)
      (fun _ ↦ [span (counter + 16) 4, span destination input.size])
      (fun fr mem ↦
        Readable mem fr.rdi 8 ∧ memLoad mem fr.rdi 64 = schedule ∧
        AES16.ScheduleIn (AES16.variant use256) key schedule mem ∧
        Readable mem schedule (16 * ((AES16.variant use256).Nr + 1)) ∧
        Readable mem fr.rsi 32 ∧ memLoad mem fr.rsi 64 = counter ∧
        memLoad mem (fr.rsi + 8) 64 = source ∧ memLoad mem (fr.rsi + 16) 64 = destination ∧
        (memLoad mem (fr.rsi + 24) 64).toNat = blockCount ∧
        Writable code mem counter 20 ∧ Readable mem source input.size ∧
        (span source input.size).HasBytes mem input ∧ Writable code mem destination input.size ∧
        (source = destination ∨ (span source input.size).Disjoint (span destination input.size)) ∧
        (∀ slot ∈ ([0x201208, 0x201210, 0x201230] : List (BitVec 64)),
          (span destination input.size).Disjoint (span slot 8) ∧
          (span counter 20).Disjoint (span slot 8)) ∧
        (∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
          span schedule (16 * ((AES16.variant use256).Nr + 1)), span counter 20,
          span source input.size, span destination input.size],
          (callStack fr).Disjoint region) ∧
        (∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
          span schedule (16 * ((AES16.variant use256).Nr + 1)), span counter 20],
          (span destination input.size).Disjoint region) ∧
        (∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
          span schedule (16 * ((AES16.variant use256).Nr + 1)),
          span source input.size, span destination input.size],
          (span counter 20).Disjoint region))
      (fun fr mem ↦ memLoad mem (counter + 16) 32 =
          memLoad fr.original (counter + 16) 32 + BitVec.ofNat 32 blockCount ∧
        (span destination input.size).HasBytes mem
          (AesGcm.Spec.GCM.byteArrayOfBits
            (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
              (Standards.NIST.GCM.bitsOfBytes (initialCounterBlock fr.original counter))
              (AesGcm.Spec.GCM.bitsOfByteArray input)))) := by
  intro fr loc hlabel hstore hAtoms hTypes hPre
  cases loc with
  | mk label args mem =>
    change label = _ at hlabel
    change mem = fr.original at hstore
    subst label
    subst mem
    change Values Value Reg.count at args
    have hentry :
        args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧
        args[1] = ⟨64, fr.rcx⟩ ∧ args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧
        args[5] = ⟨64, fr.rbp⟩ ∧ args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧
        args[8] = ⟨64, fr.r8⟩ ∧ args[9] = ⟨64, fr.r9⟩ ∧
        args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
        args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
        args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
        Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
        fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - (if use256 then 0xa80 else 0x870))
          (if use256 then 0xa80 else 0x870) ∧
        fr.low.toNat + (if use256 then 0xa80 else 0x870) ≤ fr.rsp.toNat ∧
        fr.rsp.toNat % 16 = 8 ∧ Readable fr.original 0x201208 8 ∧
        memLoad fr.original 0x201208 64 = 0x103f00 ∧ Readable fr.original 0x201210 8 ∧
        memLoad fr.original 0x201210 64 = 0x103880 ∧ Readable fr.original 0x201230 8 ∧
        memLoad fr.original 0x201230 64 = 0x101230 ∧
        ((if use256 then 0x201cb8 else 0x201aa8) ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
      cases use256 <;> exact hAtoms
    rcases hentry with ⟨h4, h22, h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, h14, h15,
      h39, h50, h51, hread, hret, hretLow, hstack, hroom, halign,
      hs0r, hs0, hs1r, hs1, hs2r, hs2, hslotBound, _⟩
    rcases hPre with ⟨hrdi, hrdiVal, hSchedule, hSchedRead, hrsi, hcounter,
      hsource, hdest, hcount, hcounterW, hsourceRead, hsourceBytes, hdestW,
      hdestApart, hslotApart, hstackSep, hdestSep, hcounterSep⟩
    have hprefix := crypt_prefix use256 code fr hcode args hTypes
      ⟨h4, h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, h14, h15⟩ key input blockCount
      hsize schedule counter source destination
      ⟨hrdi, hrdiVal, hSchedule, hSchedRead, hrsi, hcounter, hsource, hdest,
        hcount, hcounterW, hsourceRead, hsourceBytes, hdestW, hdestApart⟩
      hslotApart ⟨hread, hret, hretLow⟩ hstack hroom halign
      hs0r hs0 hs1r hs1 hs2r hs2 hslotBound hstackSep hdestSep hcounterSep
      ⟨h22, h39, h50, h51⟩
    obtain ⟨start, hstart, hcase⟩ := hprefix
    have hOuter : ∃ exit, (LIR.program.sem (dialect code)).Reaches
        ⟨start, []⟩ ⟨exit, []⟩ ∧
        OuterExit use256 code fr key input blockCount schedule counter source destination exit := by
      rcases hcase with ⟨_, hInv⟩ | ⟨_, hExit⟩
      · have hpos := hInv.count_lt
        obtain ⟨last, hReach, hLast⟩ := outer_loop
          (fun c (q : LIR.lifted.Location) =>
            (LIR.program.sem (dialect code)).Reaches ⟨start, []⟩ ⟨q, []⟩ ∧
            OuterInvariant use256 code fr key input (blockCount / 4) c
              schedule counter source destination q)
          (blockCount / 4 - 1)
          (fun c q hc ⟨hq, inv⟩ => by
            obtain ⟨next, hr, hs⟩ := batch_step use256 code fr hcode key input
              (blockCount / 4) c blockCount hsize rfl schedule counter source destination q inv (by omega)
            rcases hs with ⟨_, hn⟩ | ⟨he, _⟩
            · exact ⟨next, hq.trans hr, hn⟩
            · omega)
          start ⟨.refl _, hInv⟩
        obtain ⟨exit, hStep, hs⟩ := batch_step use256 code fr hcode key input
          (blockCount / 4) (blockCount / 4 - 1) blockCount hsize rfl schedule counter source destination
          last hLast (by omega)
        rcases hs with ⟨hlt, _⟩ | ⟨_, hExit⟩
        · omega
        · exact ⟨exit, hReach.trans hStep, hExit⟩
      · exact ⟨start, .refl _, hExit⟩
    obtain ⟨exit, hOuterReach, hExit⟩ := hOuter
    obtain ⟨next, hTail, hlabelNext, output, hrun, houtputStore, htag, hdone, htypes,
      hcounterFinal, hbytes, hTailFrame⟩ :=
      crypt_tail use256 code fr hcode key input blockCount hsize schedule counter source destination exit hExit
    have hExec : LIR.program.Exec (dialect code) ⟨next, []⟩ output := by
      apply Program.Exec.done
      change (LIR.program.runBlock (dialect code) next).next (dialect code) [] = .done output
      rw [hrun]
      rfl
    refine ⟨output, Program.Exec.of_sem ((hstart.trans (hOuterReach.trans hTail)).exec hExec.sem), ?_, ?_, ?_, ?_, ?_⟩
    · exact htag
    · exact hdone
    · exact htypes
    · exact hTailFrame
    · exact ⟨hcounterFinal, hbytes⟩

end AesGcm.Proofs.Machine.CTR
