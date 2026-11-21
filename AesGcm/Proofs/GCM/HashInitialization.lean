import AesGcm.Proofs.GCM.AuthenticationKey
import AesGcm.Proofs.Machine.GHASHUpdate.Initialize
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn102040.Frame
import AesGcm.Proofs.Machine.LIR.Fn102180.Frame

namespace AesGcm.Proofs.Machine.GCM
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem authenticationMemory_load (use256 : Bool) (mem : Ram) (sp : BitVec 64)
    (block : Standards.NIST.AES.Block) :
    let k := GHASH.polyvalKeyWords (GcmContext.blockWord block 1) (GcmContext.blockWord block 0)
    memLoad (authenticationMemory use256 mem sp block) sp 64 = k.1 ∧
    memLoad (authenticationMemory use256 mem sp block) (sp + 8) 64 = k.2 ∧
    memLoad (authenticationMemory use256 mem sp block) (sp - 8) 64 =
      (if use256 then 0x10229c else 0x10215c) := by
  dsimp only
  constructor
  · runtime_finish [authenticationMemory]
  constructor
  · runtime_finish [authenticationMemory]
  · runtime_finish [authenticationMemory]

set_option maxHeartbeats 1600000 in
theorem initializeHash (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (block : Standards.NIST.AES.Block) (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = (if use256 then .l1021ac else .l10206c))
    (hworking : Atom.All code loc.arguments loc.store
      (if use256 then LIR.Fn102180.frameAt .l1021ac fr else LIR.Fn102040.frameAt .l10206c fr))
    (hTypes : GPRsTyped loc.arguments)
    (hw : Writable code loc.store fr.rdi 32)
    (hdstsep : (callStack fr).Disjoint (span fr.rdi 32))
    (hslotsep : fr.rdi.toNat + 32 ≤ 0x201208 ∨ 0x201210 ≤ fr.rdi.toNat)
    (hblock : Fixslice.memoryBlock loc.store (fr.rsp - 56) = Fixslice16.fromStandard block) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l10229c else .l10215c) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102180.frameAt .l10229c fr else LIR.Fn102040.frameAt .l10215c fr) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame loc.store next.store [fr.region, span fr.rdi 32] ∧
      (let k := GHASH.polyvalKeyWords (GcmContext.blockWord block 1) (GcmContext.blockWord block 0)
       memLoad next.store fr.rdi 64 = k.1 ∧ memLoad next.store (fr.rdi + 8) 64 = k.2 ∧
       memLoad next.store (fr.rdi + 16) 64 = 0 ∧ memLoad next.store (fr.rdi + 24) 64 = 0) := by
  rcases loc with ⟨label, args, mem⟩
  dsimp only at hlabel hworking hTypes hw hblock ⊢
  subst label
  change Values Value Reg.count at args
  let window := if use256 then 432 else 416
  have working : args[4] = ⟨64, fr.rsp - 56⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[3] = ⟨64, fr.rdi⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
      args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
      args[14] = ⟨64, fr.rsi⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 16) 64 = fr.rbx ∧ memLoad mem (fr.rsp - 8) 64 = fr.r14 ∧
      Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code mem (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      ((if use256 then 0x2013c0 else 0x2013b0) ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hworking
  rcases working with ⟨hsp, hdf, h3, h5, h12, h13, h14, h15, h39, h50, h51,
    hs3, hs14, hreadret, hret, hretlow, hstack, hroom, halign, hslotRead, hslot, hslotStack, -⟩
  have hwindow : 104 ≤ window := by cases use256 <;> decide
  have hsub (off : Nat) (hoff : off ≤ window) :
      (fr.rsp - BitVec.ofNat 64 off).toNat = fr.rsp.toNat - off := by
    have hle : BitVec.ofNat 64 off ≤ fr.rsp := by
      have hoff64 : off < 2^64 := by cases use256 <;> simp only [window, ↓reduceIte] at hoff <;> omega
      change (BitVec.ofNat 64 off).toNat ≤ fr.rsp.toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff64]
      omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat]
    have hoff64 : off < 2^64 := by cases use256 <;> simp only [window, ↓reduceIte] at hoff <;> omega
    rw [Nat.mod_eq_of_lt hoff64]
  have n64 : (fr.rsp - 64).toNat = fr.rsp.toNat - 64 := by
    simpa only [BitVec.ofNat_eq_ofNat] using hsub 64 (by omega)
  have n104 : (fr.rsp - 104).toNat = fr.rsp.toNat - 104 := by
    simpa only [BitVec.ofNat_eq_ofNat] using hsub 104 (by omega)
  have n56 : (fr.rsp - 56).toNat = fr.rsp.toNat - 56 := by
    simpa only [BitVec.ofNat_eq_ofNat] using hsub 56 (by omega)
  let sp := fr.rsp - 56
  have argsSp : args[4].get 64 = sp := by rw [hsp]; rfl
  have stackLocal : Writable code mem (args[4].get 64 - 8) 24 := by
    rw [argsSp, show sp - 8 = fr.rsp - 64 by dsimp only [sp]; bv_omega]
    apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  have readLocal : Readable mem (args[4].get 64) 16 := by
    rw [argsSp]
    apply hstack.readable.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  obtain ⟨callee, continuation, hcall, hcallee, htarget, hguard, hmemory,
      hcsp, hcdst, hcsrc, hkeep, hctypes⟩ := authenticationKey_call use256 code hcode args mem block
        stackLocal readLocal (by rw [argsSp]; exact hblock)
  rcases callee with ⟨clabel, cargs, cmem⟩
  dsimp only at hcallee hmemory hcsp hcdst hcsrc hkeep hctypes hcall
  subst clabel
  change Values Value Reg.count at cargs
  have hcsp' : (cargs[4]'(by change 4 < 53; decide)).get 64 = fr.rsp - 64 := by
    rw [hcsp, argsSp]
    change sp - 8 = fr.rsp - 64
    dsimp only [sp]
    bv_omega
  have hcdst' : (cargs[7]'(by change 7 < 53; decide)).get 64 = fr.rdi := by rw [hcdst, h3]; rfl
  have hcsrc' : (cargs[6]'(by change 6 < 53; decide)).get 64 = sp := by rw [hcsrc, argsSp]; rfl
  let original := authenticationMemory use256 mem sp block
  have hmem : cmem = original := by rw [hmemory, argsSp]
  clear hmemory
  subst cmem
  have loadKey := authenticationMemory_load use256 mem sp block
  have freshFrame : RamWriteFrame mem original [span (fr.rsp - 64) 24] := by
    have hin : InRegions [span (fr.rsp - 64) 24] (fr.rsp - 64) 24 := by
      refine ⟨span (fr.rsp - 64) 24, by simp, ?_⟩
      simp only [InRegion, span, n64]
      have := fr.rsp.isLt
      omega
    have hi0 : InRegions [span (fr.rsp - 64) 24] sp 8 := by
      have h := GHASHUpdate.inRegions_add_offset (off := 8) hin (by decide : 0 < 8) (by decide)
      simpa only [show fr.rsp - 64 + BitVec.ofNat 64 8 = sp by dsimp only [sp]; bv_omega] using h
    have hi8 : InRegions [span (fr.rsp - 64) 24] (sp + 8) 8 := by
      have h := GHASHUpdate.inRegions_add_offset (off := 16) hin (by decide : 0 < 8) (by decide)
      simpa only [show fr.rsp - 64 + BitVec.ofNat 64 16 = sp + 8 by dsimp only [sp]; bv_omega] using h
    have hir : InRegions [span (fr.rsp - 64) 24] (sp - 8) 8 := by
      have h := GHASHUpdate.inRegions_add_offset (off := 0) hin (by decide : 0 < 8) (by decide)
      simpa only [BitVec.add_zero, show sp - 8 = fr.rsp - 64 by dsimp only [sp]; bv_omega] using h
    dsimp only [original, authenticationMemory]
    exact (((RamWriteFrame.refl mem _).memStore _ hi0).memStore _ hi8).memStore _ hir
  have originalRead := hstack.readable.of_frame freshFrame
  have originalWrite := hstack.of_frame freshFrame
  have orig64 : Readable original (fr.rsp - 64) 8 := by
    apply originalRead.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  have origWin : Writable code original (fr.rsp - 104) 40 := by
    apply originalWrite.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  have origLocal : Readable original sp 16 := by
    rw [← argsSp]
    exact readLocal.of_frame freshFrame
  let low := fr.rsp - 104
  let ret := if use256 then 0x10229c#64 else 0x10215c#64
  have originalRet : memLoad original (fr.rsp - 64) 64 = ret := by
    have he : sp - 8 = fr.rsp - 64 := by dsimp only [sp]; bv_omega
    have hh := loadKey.2.2
    rw [he] at hh
    cases use256 <;> exact hh
  have keep3 : cargs[3] = args[3] := hkeep 3 (by decide)
  have keep5 : cargs[5] = args[5] := hkeep 5 (by decide)
  have keep12 : cargs[12] = args[12] := hkeep 12 (by decide)
  have keep13 : cargs[13] = args[13] := hkeep 13 (by decide)
  have keep14 : cargs[14] = args[14] := hkeep 14 (by decide)
  have keep15 : cargs[15] = args[15] := hkeep 15 (by decide)
  have keep22 : cargs[22] = args[22] := hkeep 22 (by decide)
  have keep39 : cargs[39] = args[39] := hkeep 39 (by decide)
  have keep50 : cargs[50] = args[50] := hkeep 50 (by decide)
  have keep51 : cargs[51] = args[51] := hkeep 51 (by decide)
  obtain ⟨o, hexec, htag, hdone, houtTypes, hcallFrame, hpost⟩ :=
    callContract_exec_values LIR.lifted code .l102b80 LIR.Fn102b80.frameInfo
      (fun cfr ↦ [span cfr.rdi 32]) _ _ (GHASHUpdate.initialize_call code hcode)
      original cargs ret low (hctypes hTypes)
      (by rw [keep39, h39]; rfl)
      (by rw [keep50, h50]; rfl)
      (by rw [keep51, h51]; rfl)
      ((keep22).trans hdf)
      (by rw [hcsp']; exact orig64)
      (by rw [hcsp']; exact originalRet)
      (by dsimp only [ret]; cases use256 <;> decide)
      (by intro _; rw [hcsp'];
          rw [show fr.rsp - 64 - BitVec.ofNat 64 LIR.Fn102b80.frameInfo.window = fr.rsp - 104
            by change fr.rsp - 64 - 40 = fr.rsp - 104; bv_omega]; exact origWin)
      (by rw [hcsp', n64]; change low.toNat + 40 ≤ _; dsimp only [low]; rw [n104]; omega)
      (by rw [hcsp', n64]; omega)
      (by trivial)
      (by
        change Readable original ((cargs[6]'(by change 6 < 53; decide)).get 64) 16 ∧
          Writable code original ((cargs[7]'(by change 7 < 53; decide)).get 64) 32 ∧
          (callStack (activationOfValues original cargs ret low)).Disjoint
            (span ((cargs[6]'(by change 6 < 53; decide)).get 64) 16) ∧
          (callStack (activationOfValues original cargs ret low)).Disjoint
            (span ((cargs[7]'(by change 7 < 53; decide)).get 64) 32)
        rw [hcsrc', hcdst']
        refine ⟨origLocal, hw.of_frame freshFrame, ?_, ?_⟩
        · change (⟨low.toNat, ((cargs[4]'(by change 4 < 53; decide)).get 64).toNat + 8 - low.toNat⟩ : MemoryRegion).Disjoint
            (span sp 16)
          rw [hcsp', n64]
          intro x hx hs
          simp only [MemoryRegion.Contains, span, sp, low, n104, n56] at hx hs
          omega
        · have bounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
            fr.rdi.toNat 32 (by omega) (by decide) hdstsep
          change (⟨low.toNat, ((cargs[4]'(by change 4 < 53; decide)).get 64).toNat + 8 - low.toNat⟩ : MemoryRegion).Disjoint
            (span fr.rdi 32)
          rw [hcsp', n64]
          intro x hx hs
          simp only [MemoryRegion.Contains, span, low, n104] at hx hs
          omega)
  let work : List MemoryRegion :=
    [span low 64, span fr.rdi 32]
  have firstWithin : RegionsWithin [span (fr.rsp - 64) 24] work := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst r
    refine ⟨span low 64, by simp [work], ?_, ?_⟩
    all_goals simp only [span, low, n104, n64]; omega
  have callWithin : RegionsWithin
      ((activationOfValues original cargs ret low).region ::
        [span (activationOfValues original cargs ret low).rdi 32]) work := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · refine ⟨span low 64, by simp [work], ?_, ?_⟩
      all_goals simp only [activationOfValues, Activation.region, span, low, hcsp', n104, n64]; omega
    · refine ⟨span fr.rdi 32, by simp [work], ?_, ?_⟩
      all_goals simp only [activationOfValues, hcdst']; omega
  have workFrame : RamWriteFrame mem o.store work :=
    ((RamWriteFrame.refl mem work).trans freshFrame firstWithin).trans hcallFrame callWithin
  have finalFrame : RamWriteFrame mem o.store [fr.region, span fr.rdi 32] := by
    apply (RamWriteFrame.refl mem [fr.region, span fr.rdi 32]).trans workFrame
    intro r hr'
    simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · refine ⟨fr.region, by simp, ?_, ?_⟩
      all_goals simp only [Activation.region, span, low, n104]; omega
    · exact ⟨span fr.rdi 32, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have dstBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdi.toNat 32 (by omega) (by decide) hdstsep
  have savedOutside (off : Nat) (ho : off ≤ 16) :
      Outside work (fr.rsp - BitVec.ofNat 64 off) 8 := by
    refine ⟨?_, ?_⟩
    · rw [hsub off (by omega)]; have := hreadret.low; omega
    · intro r hr'
      simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · simp only [span, low, hsub off (by omega), n104]; right; omega
      · simp only [span, hsub off (by omega)]
        omega
  have outRet : memLoad o.store fr.rsp 64 = fr.ret := by
    have hx := savedOutside 0 (by decide)
    rw [show fr.rsp - BitVec.ofNat 64 0 = fr.rsp by bv_omega] at hx
    exact (workFrame.memLoad_eq hx).trans hret
  have outSaved3 := (workFrame.memLoad_eq (savedOutside 16 (by decide))).trans hs3
  have outSaved14 := (workFrame.memLoad_eq (savedOutside 8 (by decide))).trans hs14
  have slotOutside : Outside work 0x201208 8 := by
    refine ⟨by decide, ?_⟩
    intro r hr'
    simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · have hh : 0x201210 ≤ fr.rsp.toNat - window ∨ fr.rsp.toNat ≤ 0x201208 := by
        cases use256 <;> simp only [window, ↓reduceIte, Bool.false_eq_true] at hslotStack ⊢ <;> omega
      simp only [span, low, BitVec.reduceToNat, n104]
      omega
    · simp only [span, BitVec.reduceToNat]
      omega
  have outSlot := (workFrame.memLoad_eq slotOutside).trans hslot
  have outDone : o.values[4] = ⟨64, fr.rsp - 56⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
      o.values[3] = ⟨64, fr.rdi⟩ ∧ o.values[5] = ⟨64, fr.rbp⟩ ∧
      o.values[12] = ⟨64, fr.r12⟩ ∧ o.values[13] = ⟨64, fr.r13⟩ ∧
      o.values[14] = ⟨64, fr.rsi⟩ ∧ o.values[15] = ⟨64, fr.r15⟩ ∧
      o.values[39] = ⟨32, fr.mxcsr⟩ ∧ o.values[50] = ⟨16, fr.ftw⟩ ∧
      o.values[51] = ⟨16, fr.fcw⟩ ∧ True := by
    change o.values[4] = ⟨64, (cargs[4]'(by change 4 < 53; decide)).get 64 + 8⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
      o.values[3] = ⟨64, (cargs[3]'(by change 3 < 53; decide)).get 64⟩ ∧
      o.values[5] = ⟨64, (cargs[5]'(by change 5 < 53; decide)).get 64⟩ ∧
      o.values[12] = ⟨64, (cargs[12]'(by change 12 < 53; decide)).get 64⟩ ∧
      o.values[13] = ⟨64, (cargs[13]'(by change 13 < 53; decide)).get 64⟩ ∧
      o.values[14] = ⟨64, (cargs[14]'(by change 14 < 53; decide)).get 64⟩ ∧
      o.values[15] = ⟨64, (cargs[15]'(by change 15 < 53; decide)).get 64⟩ ∧
      o.values[39] = ⟨32, (cargs[39]'(by change 39 < 53; decide)).get 32⟩ ∧
      o.values[50] = ⟨16, (cargs[50]'(by change 50 < 53; decide)).get 16⟩ ∧
      o.values[51] = ⟨16, (cargs[51]'(by change 51 < 53; decide)).get 16⟩ ∧ True at hdone
    rw [hcsp', show fr.rsp - 64 + 8 = fr.rsp - 56 by bv_omega,
      keep3, keep5, keep12, keep13,
      keep14, keep15, keep39,
      keep50, keep51, h3, h5, h12, h13, h14, h15, h39, h50, h51] at hdone
    exact hdone
  let next : LIR.lifted.Location :=
    ⟨(if use256 then .l10229c else .l10215c), o.values, o.store⟩
  have nextWorking : Atom.All code next.arguments next.store
      (if use256 then LIR.Fn102180.frameAt .l10229c fr else LIR.Fn102040.frameAt .l10215c fr) := by
    rcases outDone with ⟨outsp, outdf, out3, out5, out12, out13, out14, out15,
      out39, out50, out51, -⟩
    have hwk : o.values[4] = ⟨64, fr.rsp - 56⟩ ∧ o.values[22] = ⟨1, 0⟩ ∧
        o.values[3] = ⟨64, fr.rdi⟩ ∧ o.values[5] = ⟨64, fr.rbp⟩ ∧
        o.values[12] = ⟨64, fr.r12⟩ ∧ o.values[13] = ⟨64, fr.r13⟩ ∧
        o.values[14] = ⟨64, fr.rsi⟩ ∧ o.values[15] = ⟨64, fr.r15⟩ ∧
        o.values[39] = ⟨32, fr.mxcsr⟩ ∧ o.values[50] = ⟨16, fr.ftw⟩ ∧ o.values[51] = ⟨16, fr.fcw⟩ ∧
        memLoad o.store (fr.rsp - 16) 64 = fr.rbx ∧ memLoad o.store (fr.rsp - 8) 64 = fr.r14 ∧
        Readable o.store fr.rsp 8 ∧ memLoad o.store fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
        Writable code o.store (fr.rsp - BitVec.ofNat 64 window) window ∧
        fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
        Readable o.store 0x201208 8 ∧ memLoad o.store 0x201208 64 = 0x103f00 ∧
        ((if use256 then 0x2013c0 else 0x2013b0) ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True :=
      ⟨outsp, outdf, out3, out5, out12, out13, out14, out15, out39, out50, out51,
        outSaved3, outSaved14, hreadret.of_frame workFrame, outRet, hretlow,
        hstack.of_frame workFrame, hroom, halign, hslotRead.of_frame workFrame, outSlot, hslotStack, trivial⟩
    cases use256 <;> exact hwk
  have hresume : continuation.resume o = next := by
    rcases continuation with @⟨size, target, kept, arity, guard⟩
    have hs : size = 0 := by change 53 + size = 53 at arity; omega
    subst size
    have hk : kept = #v[] := Vector.eq_empty
    subst kept
    cases htarget
    rfl
  have accepted : continuation.Accepts (dialect code) o.tag = true := by
    simp only [StackFrame.Accepts, htag, hguard]
    cases use256 <;> rfl
  have callStep : LIR.program.step (dialect code)
      ⟨⟨(if use256 then .l1021ac else .l10206c), args, mem⟩, []⟩ =
      .next ⟨⟨.l102b80, cargs, original⟩, [continuation]⟩ := by
    rw [Program.step, hcall]
    rfl
  have reach := (Semantics.Reaches.single callStep).trans
    (CFGCall.exec_reaches_resume hexec continuation [] accepted)
  refine ⟨next, ?_, rfl, nextWorking, houtTypes, finalFrame, ?_⟩
  · exact (congrArg (fun l : LIR.lifted.Location ↦
        (LIR.program.sem (dialect code)).Reaches
          ⟨⟨(if use256 then .l1021ac else .l10206c), args, mem⟩, []⟩ ⟨l, []⟩) hresume).mp reach
  · change memLoad o.store (cargs[7].get 64) 64 = memLoad original (cargs[6].get 64) 64 ∧
      memLoad o.store (cargs[7].get 64 + 8) 64 = memLoad original (cargs[6].get 64 + 8) 64 ∧
      memLoad o.store (cargs[7].get 64 + 16) 64 = 0 ∧
      memLoad o.store (cargs[7].get 64 + 24) 64 = 0 at hpost
    rw [hcdst', hcsrc', loadKey.1, loadKey.2.1] at hpost
    exact hpost
end AesGcm.Proofs.Machine.GCM
