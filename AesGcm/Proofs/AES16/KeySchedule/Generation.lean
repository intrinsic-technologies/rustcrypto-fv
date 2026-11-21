import AesGcm.Proofs.AES16.KeySchedule.Generation.Memory
import AesGcm.Proofs.AES16.KeySchedule.Generation.Start
import AesGcm.Proofs.AES16.KeySchedule.Generation.Native

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess
  X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem generation_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (hsp : args[4].get 64 = sp) (hTypes : GPRsTyped args)
    (hDF : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hbuffer : args[14].get 64 = sp + (if use256 then 12 else 8))
    (hindex : args[15].get 64 = (if use256 then 8 else 0))
    (hstack : Writable code mem (sp - 248) (if use256 then 608 else 512))
    (hroom : 248 ≤ sp.toNat) (hAlign : sp.toNat % 16 = 0)
    (hreadPanic : Readable mem 0x201210 8)
    (hpanic : memLoad mem 0x201210 64 = 0x103880)
    (hreadBounds : Readable mem 0x201230 8)
    (hbounds : memLoad mem 0x201230 64 = 0x101230)
    (hslotsApart : 0x201330 ≤ sp.toNat ∨
      sp.toNat + (if use256 then 360 else 264) ≤ 0x201210)
    (hkeys : RawSchedulePrefix (variant use256) key ((variant use256).Nk / 4)
      (sp + (if use256 then 12 else 8)) mem) :
    ∃ (finalArgs : Values Value Reg.count) (finalMem : Ram),
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l105856 else .l1043d2), args, mem⟩, []⟩
        ⟨⟨(if use256 then .l10593a else .l10446f), finalArgs, finalMem⟩, []⟩ ∧
      finalArgs[4].get 64 = sp ∧
      finalArgs[22] = args[22] ∧ finalArgs[39] = args[39] ∧
      finalArgs[50] = args[50] ∧ finalArgs[51] = args[51] ∧
      GPRsTyped finalArgs ∧
      RamWriteFrame mem finalMem [span (sp - 248) 248,
        span (sp + (if use256 then 12 else 8)) (if use256 then 240 else 176)] ∧
      RawSchedulePrefix (variant use256) key ((variant use256).Nr + 1)
        (sp + (if use256 then 12 else 8)) finalMem := by
  have hmemory : Generation.MemoryReady use256 code mem sp :=
    ⟨hstack, hroom, hAlign, hreadPanic, hpanic, hreadBounds, hbounds, hslotsApart⟩
  obtain ⟨startArgs, hstart, hstartReady, hstartFP⟩ := Generation.start_reaches use256 code
    args mem sp hsp hTypes hDF h39 h50 h51 hbuffer hindex
  let firstRound := (variant use256).Nk / 4
  have hfirst : firstRound ≤ (variant use256).Nr + 1 := by
    cases use256 <;> decide
  have iterate : ∀ n : Nat, firstRound + n ≤ (variant use256).Nr + 1 →
      ∃ (nextArgs : Values Value Reg.count) (nextMem : Ram),
        (LIR.program.sem (dialect code)).Reaches
          ⟨⟨Generation.label use256 firstRound, startArgs, mem⟩, []⟩
          ⟨⟨Generation.label use256 (firstRound + n), nextArgs, nextMem⟩, []⟩ ∧
        Generation.Ready use256 (firstRound + n) sp nextArgs ∧
        Generation.SameFP startArgs nextArgs ∧
        RamWriteFrame mem nextMem (Generation.regions use256 sp) ∧
        RawSchedulePrefix (variant use256) key (firstRound + n)
          (Generation.base use256 sp) nextMem := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨startArgs, mem, .refl _, hstartReady, ⟨rfl, rfl, rfl⟩,
        RamWriteFrame.refl _ _, hkeys⟩
    | succ n ih =>
      intro hn
      obtain ⟨priorArgs, priorMem, hreach, hready, hfp, hframe, hprefix⟩ := ih (by omega)
      have hpriorMemory := Generation.memoryReady_of_frame hmemory hframe
        (Generation.regions_within_stack hmemory)
      obtain ⟨nextArgs, nextMem, hstep, hnextReady, hnextFP, hnextFrame, hnew⟩ :=
        Generation.step_reaches use256 code hcode key (firstRound + n) (by omega)
          (by omega) priorArgs priorMem sp hready hpriorMemory hprefix
      refine ⟨nextArgs, nextMem, hreach.trans hstep, hnextReady,
        ⟨hnextFP.1.trans hfp.1, hnextFP.2.1.trans hfp.2.1,
          hnextFP.2.2.trans hfp.2.2⟩,
        hframe.trans hnextFrame (Generation.roundRegions_within hpriorMemory (firstRound + n) (by omega)),
        Generation.prefix_of_round hpriorMemory key (firstRound + n) (by omega) hprefix hnextFrame hnew⟩
  let count := (variant use256).Nr + 1 - firstRound
  have hcount : firstRound + count = (variant use256).Nr + 1 := by omega
  obtain ⟨finalArgs, finalMem, hreach, hready, hfp, hframe, hprefix⟩ :=
    iterate count (by omega)
  rw [hcount] at hreach hready hprefix
  have hlabel : Generation.label use256 ((variant use256).Nr + 1) =
      (if use256 then .l10593a else .l10446f) := by
    simp only [Generation.label, ite_true]
  rw [hlabel] at hreach
  exact ⟨finalArgs, finalMem, hstart.trans hreach, hready.hsp,
    hready.hDF.trans hDF.symm, hfp.1.trans hstartFP.1,
    hfp.2.1.trans hstartFP.2.1, hfp.2.2.trans hstartFP.2.2, hready.hTypes,
    hframe, hprefix⟩

end AesGcm.Proofs.Machine.AES16.KeySchedule
