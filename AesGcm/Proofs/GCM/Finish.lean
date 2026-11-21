import AesGcm.Proofs.GCM.Memory
import AesGcm.Proofs.Machine.GHASHUpdate.Memory
import AesGcm.Proofs.GCM.Exit
import AesGcm.Proofs.Machine.GcmContext
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.Runtime.Memcpy
import AesGcm.Proofs.Machine.LIR.Fn102040.Frame
import AesGcm.Proofs.Machine.LIR.Fn102180.Frame

namespace AesGcm.Proofs.Machine.GCM
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
theorem finish_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp dst src : BitVec 64)
    (hsp : args[4].get 64 = sp) (hdst : args[3].get 64 = dst)
    (hsrc : args[14].get 64 = src) (hTypes : GPRsTyped args)
    (hstack : Writable code mem (sp - 8) 8)
    (hslotRead : Readable mem 0x201208 8)
    (hslot : memLoad mem 0x201208 64 = 0x103f00)
    (_hslotApart : RangeApart (sp - 8) 8 0x201208 8) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l10229c else .l10215c), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103f00 ∧
      continuation.target = (if use256 then .l1022b1 else .l102171) ∧
      continuation.guard = some ⟨64, if use256 then 0x1022b1 else 0x102171⟩ ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, dst + 32⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, src⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, if use256 then 240 else 176⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] →
        callee.arguments[r] = args[r]) ∧
      GPRsTyped callee.arguments ∧
      callee.store = memStore mem (sp - 8)
        (if use256 then (0x1022b1 : BitVec 64) else 0x102171) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x10229c else 0x10215c) 21 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l10215c x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l10229c x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l10215c, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l10229c, args, mem⟩ = _
      cfg_eval []
      refine_norm [hsp, hdst, hsrc]
      runtime_guards call
      rfl
    all_goals first
      | rfl
      | runtime_typed
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

set_option maxHeartbeats 1600000 in
theorem finish (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes)
    (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = (if use256 then .l10229c else .l10215c))
    (hworking : Atom.All code loc.arguments loc.store
      (if use256 then LIR.Fn102180.frameAt .l10229c fr else LIR.Fn102040.frameAt .l10215c fr))
    (hTypes : GPRsTyped loc.arguments)
    (hframe : RamWriteFrame fr.original loc.store
      [fr.region, span fr.rdi (GcmContext.size (AES16.variant use256))])
    (hschedule : AES16.ScheduleIn (AES16.variant use256) key fr.rsi loc.store)
    (hr : Readable loc.store fr.rsi (16 * ((AES16.variant use256).Nr + 1)))
    (hw : Writable code loc.store fr.rdi (GcmContext.size (AES16.variant use256)))
    (hsrcsep : (callStack fr).Disjoint (span fr.rsi (16 * ((AES16.variant use256).Nr + 1))))
    (hdstsep : (callStack fr).Disjoint (span fr.rdi (GcmContext.size (AES16.variant use256))))
    (hdatasep : (span fr.rdi (GcmContext.size (AES16.variant use256))).Disjoint
      (span fr.rsi (16 * ((AES16.variant use256).Nr + 1))))
    (hkey : memLoad loc.store fr.rdi 64 = (GcmContext.authenticationKey (AES16.variant use256) key).1 ∧
      memLoad loc.store (fr.rdi + 8) 64 = (GcmContext.authenticationKey (AES16.variant use256) key).2 ∧
      memLoad loc.store (fr.rdi + 16) 64 = 0 ∧ memLoad loc.store (fr.rdi + 24) 64 = 0) :
    ∃ output,
      LIR.program.Exec (dialect code) ⟨loc, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Fn102180.frameInfo else LIR.Fn102040.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values ∧
      RamWriteFrame fr.original output.store
        [fr.region, span fr.rdi (GcmContext.size (AES16.variant use256))] ∧
      GcmContext.ContextIn (AES16.variant use256) key fr.rdi output.store := by
  rcases loc with ⟨label, args, mem⟩
  dsimp only at *
  subst label
  change Values Value Reg.count at args
  let n := 16 * ((AES16.variant use256).Nr + 1)
  let win := if use256 then 432 else 416
  let slotHigh := if use256 then 0x2013c0 else 0x2013b0
  let sp := fr.rsp - 56
  let push := fr.rsp - 64
  let dst := fr.rdi + 32
  let ret : BitVec 64 := if use256 then 0x1022b1 else 0x102171
  let work : List MemoryRegion :=
    [⟨fr.low.toNat, sp.toNat - fr.low.toNat⟩, span dst n]
  let full := [fr.region, span fr.rdi (GcmContext.size (AES16.variant use256))]
  have hn : n = (if use256 then 240 else 176) := by cases use256 <;> rfl
  have hnpos : 0 < n := by rw [hn]; cases use256 <;> decide
  have hwin : 64 ≤ win := by cases use256 <;> decide
  have hworking' : args[4] = ⟨64, sp⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[3] = ⟨64, fr.rdi⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
      args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
      args[14] = ⟨64, fr.rsi⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 16) 64 = fr.rbx ∧
      memLoad mem (fr.rsp - 8) 64 = fr.r14 ∧
      Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧
      fr.ret.toNat < 2^32 ∧ Writable code mem (fr.rsp - BitVec.ofNat 64 win) win ∧
      fr.low.toNat + win ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      (slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hworking
  rcases hworking' with ⟨hsp, hdf, h3, h5, h12, h13, h14, h15, h39, h50, h51,
    hsave3, hsave14, hreturnRead, hreturn, hreturnLow, hstack, hroom, halign,
    hslotRead, hslot, hslotSep, -⟩
  have hspNat : sp.toNat = fr.rsp.toNat - 56 := by
    exact BitVec.toNat_sub_of_le (by
      change (56 : BitVec 64) ≤ fr.rsp
      change 56 ≤ fr.rsp.toNat
      omega)
  have hpushNat : push.toNat = fr.rsp.toNat - 64 := by
    exact BitVec.toNat_sub_of_le (by
      change (64 : BitVec 64) ≤ fr.rsp
      change 64 ≤ fr.rsp.toNat
      omega)
  have hpush : sp - 8 = push := by dsimp only [sp, push]; bv_omega
  have hdstNat : dst.toNat = fr.rdi.toNat + 32 := by
    have hl := hw.readable.low
    change fr.rdi.toNat + (32 + n) ≤ 2^32 at hl
    simp only [dst, BitVec.toNat_add, BitVec.reduceToNat]
    exact Nat.mod_eq_of_lt (by omega)
  have srcBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rsi.toNat n (by omega) hnpos hsrcsep
  have dstBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdi.toNat (32+n) (by omega) (by omega) hdstsep
  have dataBounds := disjoint_bounds fr.rdi.toNat (32+n) fr.rsi.toNat n
    (by omega) hnpos hdatasep
  have hpushWrite : Writable code mem push 8 := by
    apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  have hpushSlot : RangeApart push 8 0x201208 8 := by
    apply RangeApart.of_toNat (by have := hpushWrite.readable.low; omega) (by decide)
    rw [hpushNat]
    change fr.rsp.toNat - 64 + 8 ≤ 0x201208 ∨
      0x201208 + 8 ≤ fr.rsp.toNat - 64
    cases use256 <;> simp only [slotHigh, Bool.false_eq_true, ↓reduceIte] at hslotSep <;> omega
  obtain ⟨callee, continuation, hcall, hcallee, htarget, hguard, ca4, ca7, ca6, ca2,
      ckeep, ctypes, cmem⟩ :=
    finish_call use256 code hcode args mem sp fr.rdi fr.rsi
      (by rw [hsp]; rfl) (by rw [h3]; rfl) (by rw [h14]; rfl) hTypes
      (by rw [hpush]; exact hpushWrite) hslotRead hslot
      (by rw [hpush]; exact hpushSlot)
  rw [hpush] at cmem
  change callee.store = memStore mem push ret at cmem
  simp only [Fin.getElem_fin] at ckeep
  rw [hpush] at ca4
  have pushedFrame : RamWriteFrame mem callee.store work := by
    rw [cmem]
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨⟨fr.low.toNat, sp.toNat-fr.low.toNat⟩, by simp only [work, List.mem_cons, true_or], ?_⟩
    simp only [InRegion, hpushNat, hspNat]
    have := fr.rsp.isLt
    omega
  have pushedSourceOutside : Outside work fr.rsi n := by
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · dsimp only
      rw [hspNat]
      omega
    · simp only [span, hdstNat]
      omega
  have hschedPush := AES16.scheduleIn_of_frame hschedule pushedFrame pushedSourceOutside
  have cret : memLoad callee.store push 64 = ret := by
    rw [cmem]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have cpRead : Readable callee.store push 8 := hpushWrite.readable.of_frame pushedFrame
  have cdWrite : Writable code callee.store dst n := by
    apply (hw.of_frame pushedFrame).sub
    · rw [hdstNat]; omega
    · rw [hdstNat]; change fr.rdi.toNat + 32 + n ≤ fr.rdi.toNat + (32+n); omega
  have keepFP39 : callee.arguments[39]'(by change 39 < 53; decide) =
      ⟨32, (callee.arguments[39]'(by change 39 < 53; decide)).get 32⟩ := by
    rw [ckeep ⟨39, by decide⟩ (by decide), h39]; rfl
  have keepFP50 : callee.arguments[50]'(by change 50 < 53; decide) =
      ⟨16, (callee.arguments[50]'(by change 50 < 53; decide)).get 16⟩ := by
    rw [ckeep ⟨50, by decide⟩ (by decide), h50]; rfl
  have keepFP51 : callee.arguments[51]'(by change 51 < 53; decide) =
      ⟨16, (callee.arguments[51]'(by change 51 < 53; decide)).get 16⟩ := by
    rw [ckeep ⟨51, by decide⟩ (by decide), h51]; rfl
  have memcpyCode : ∀ x ∈ codeRange 0x103f00 LIR.bytes_l103f00, x ∈ code :=
    fun x hx => hcode x (LIR.code_l103f00 x hx)
  obtain ⟨copied, hexecCopy, htagCopy, hdoneCopy, htypesCopy, hframeCopy, hpostCopy⟩ :=
    callContract_exec_values LIR.lifted code .l103f00 LIR.Fn103f00.frameInfo
      (fun fr => [span fr.rdi fr.rdx.toNat]) _ _ (memcpy_call code memcpyCode)
      callee.store callee.arguments ret fr.low ctypes keepFP39 keepFP50 keepFP51
      ((ckeep ⟨22, by decide⟩ (by decide)).trans hdf)
      (by rw [ca4]; exact cpRead) (by rw [ca4]; exact cret)
      (by cases use256 <;> decide)
      (by intro h; change 0 < 0 at h; omega)
      (by change fr.low.toNat + 0 ≤ ((callee.arguments[4]'(by change 4 < 53; decide)).get 64).toNat
          rw [ca4]; change fr.low.toNat ≤ push.toNat; rw [hpushNat]; omega)
      (by rw [ca4]; change push.toNat % 16 = 8; rw [hpushNat]; omega)
      (by trivial)
      (by
        change Readable callee.store ((callee.arguments[6]'(by change 6 < 53; decide)).get 64)
            ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat ∧
          Writable code callee.store ((callee.arguments[7]'(by change 7 < 53; decide)).get 64)
            ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat ∧
          (((callee.arguments[6]'(by change 6 < 53; decide)).get 64).toNat +
              ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat ≤
              ((callee.arguments[7]'(by change 7 < 53; decide)).get 64).toNat ∨
            ((callee.arguments[7]'(by change 7 < 53; decide)).get 64).toNat +
              ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat ≤
              ((callee.arguments[6]'(by change 6 < 53; decide)).get 64).toNat) ∧
          RangeApart ((callee.arguments[7]'(by change 7 < 53; decide)).get 64)
            ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat
            ((callee.arguments[4]'(by change 4 < 53; decide)).get 64) 8
        have cn : ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat = n := by
          rw [ca2, hn]; cases use256 <;> rfl
        rw [cn, ca6, ca7, ca4]
        change Readable callee.store fr.rsi n ∧ Writable code callee.store dst n ∧
          (fr.rsi.toNat+n ≤ dst.toNat ∨ dst.toNat+n ≤ fr.rsi.toNat) ∧
          RangeApart dst n push 8
        refine ⟨hr.of_frame pushedFrame, cdWrite, ?_, ?_⟩
        · rw [hdstNat]; omega
        · apply RangeApart.of_toNat (by have := cdWrite.readable.low; omega)
            (by have := hpushWrite.readable.low; omega)
          rw [hdstNat, hpushNat]; omega)
  have cn : ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat = n := by
    rw [ca2, hn]; cases use256 <;> rfl
  change RamWriteFrame callee.store copied.store
    [⟨fr.low.toNat, ((callee.arguments[4]'(by change 4 < 53; decide)).get 64).toNat-fr.low.toNat⟩,
      span ((callee.arguments[7]'(by change 7 < 53; decide)).get 64)
        ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat] at hframeCopy
  rw [cn, ca4, ca7] at hframeCopy
  change (∀ i < ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat,
    copied.store[((callee.arguments[7]'(by change 7 < 53; decide)).get 64)+BitVec.ofNat 64 i]? =
      callee.store[((callee.arguments[6]'(by change 6 < 53; decide)).get 64)+
        BitVec.ofNat 64 i]?) at hpostCopy
  rw [cn, ca7, ca6] at hpostCopy
  have copyWithin : RegionsWithin
      [⟨fr.low.toNat, push.toNat-fr.low.toNat⟩, span dst n] work := by
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨⟨fr.low.toNat, sp.toNat-fr.low.toNat⟩, by simp [work], Nat.le_refl _, ?_⟩
      dsimp only
      rw [hpushNat, hspNat]
      omega
    · exact ⟨span dst n, by simp [work], Nat.le_refl _, Nat.le_refl _⟩
  have hchange : RamWriteFrame mem copied.store work := pushedFrame.trans hframeCopy copyWithin
  have workWithin : RegionsWithin work full := by
    intro r hin
    simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨fr.region, by simp [full], Nat.le_refl _, ?_⟩
      simp only [Activation.region, hspNat]
      omega
    · refine ⟨span fr.rdi (GcmContext.size (AES16.variant use256)), by simp [full], ?_, ?_⟩
      all_goals simp only [span, hdstNat, GcmContext.size]; change _ ≤ _; omega
  have hfull : RamWriteFrame fr.original copied.store full := hframe.trans hchange workWithin
  have keyOutside : Outside work fr.rdi 32 := by
    refine ⟨by have := hw.readable.low; omega, ?_⟩
    intro r hin
    simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · dsimp only
      rw [hspNat]
      omega
    · simp only [span, hdstNat]
      omega
  have keyLoad (off : Nat) (ho : off+8 ≤ 32) :
      memLoad copied.store (fr.rdi+BitVec.ofNat 64 off) 64 =
        memLoad mem (fr.rdi+BitVec.ofNat 64 off) 64 :=
    hchange.memLoad_eq (GHASHUpdate.outside_add_offset keyOutside (by decide) ho)
  have savedOutside : Outside work sp 64 := by
    refine ⟨by have := hreturnRead.low; rw [hspNat]; omega, ?_⟩
    intro r hin
    simp only [work, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · dsimp only
      omega
    · simp only [span, hdstNat]
      rw [hspNat]
      omega
  have stackRead : Readable mem sp 64 := by
    have hr56 : Readable mem sp 56 := by
      apply hstack.readable.of_offsets (addr_sub _ _) (addr_sub _ _)
      cases use256 <;> decide +kernel
    have he : sp + BitVec.ofNat 64 56 = fr.rsp := by dsimp only [sp]; bv_omega
    exact readable_append hr56 (by rw [he]; exact hreturnRead)
  have savedLoad (off : Nat) (ho : off+8 ≤ 64) :
      memLoad copied.store (sp+BitVec.ofNat 64 off) 64 =
        memLoad mem (sp+BitVec.ofNat 64 off) 64 :=
    hchange.memLoad_eq (GHASHUpdate.outside_add_offset savedOutside (by decide) ho)
  change copied.values[4] = ⟨64, ((callee.arguments[4]'(by change 4 < 53; decide)).get 64)+8⟩ ∧
    copied.values[22] = ⟨1, 0⟩ ∧
    copied.values[3] = ⟨64, (callee.arguments[3]'(by change 3 < 53; decide)).get 64⟩ ∧
    copied.values[5] = ⟨64, (callee.arguments[5]'(by change 5 < 53; decide)).get 64⟩ ∧
    copied.values[12] = ⟨64, (callee.arguments[12]'(by change 12 < 53; decide)).get 64⟩ ∧
    copied.values[13] = ⟨64, (callee.arguments[13]'(by change 13 < 53; decide)).get 64⟩ ∧
    copied.values[14] = ⟨64, (callee.arguments[14]'(by change 14 < 53; decide)).get 64⟩ ∧
    copied.values[15] = ⟨64, (callee.arguments[15]'(by change 15 < 53; decide)).get 64⟩ ∧
    copied.values[39] = ⟨32, (callee.arguments[39]'(by change 39 < 53; decide)).get 32⟩ ∧
    copied.values[50] = ⟨16, (callee.arguments[50]'(by change 50 < 53; decide)).get 16⟩ ∧
    copied.values[51] = ⟨16, (callee.arguments[51]'(by change 51 < 53; decide)).get 16⟩ ∧
      True at hdoneCopy
  rcases hdoneCopy with ⟨co4, co22, co3, co5, co12, co13, co14, co15, co39, co50, co51, -⟩
  have coSP : copied.values[4].get 64 = sp := by
    rw [co4, ca4]
    change push + 8 = sp
    dsimp only [push, sp]
    bv_omega
  have hretLoad : memLoad copied.store (sp+56) 64 = fr.ret := by
    simp only [BitVec.ofNat_eq_ofNat] at ⊢
    rw [savedLoad 56 (by decide)]
    have he : sp+56 = fr.rsp := by dsimp only [sp]; bv_omega
    change memLoad mem (sp+56) 64 = fr.ret
    rw [he, hreturn]
  obtain ⟨output, hexit, ostore, otag, o4, o3, o14, okeep, otypes⟩ :=
    exit_runBlock use256 code copied.values copied.store
      (by rw [coSP]; exact stackRead.of_frame hchange)
      (by rw [coSP, hretLoad]; exact hreturnLow)
  have hrest : LIR.program.Exec (dialect code) ⟨continuation.resume copied, []⟩ output := by
    apply Program.Exec.done
    change (LIR.program.runBlock (dialect code) (continuation.resume copied)).next
      (dialect code) [] = .done output
    have hloc : continuation.resume copied =
        ⟨(if use256 then .l1022b1 else .l102171), copied.values, copied.store⟩ := by
      rcases continuation with @⟨size, target, kept, arity, guard⟩
      have hs : size = 0 := by change Reg.count + size = Reg.count at arity; omega
      subst size
      have hk : kept = #v[] := Vector.eq_empty
      subst kept
      change target = (if use256 then .l1022b1 else .l102171) at htarget
      exact congrArg
        (fun l : LIR.Label =>
          (⟨l, copied.values, copied.store⟩ : Location Value Ram LIR.Label signature)) htarget
    rw [hloc, hexit]
    rfl
  refine ⟨output, ?_, ?_, ?_, otypes htypesCopy, ?_, ?_⟩
  · apply CFGCall.exec_call hcall
    · have he : callee = ⟨.l103f00, callee.arguments, callee.store⟩ := by
        rcases callee with ⟨l, a, m⟩
        dsimp only at hcallee ⊢
        cases hcallee
        rfl
      rw [he]
      exact hexecCopy
    · change continuation.guard = some ⟨64, ret⟩ at hguard
      simp only [StackFrame.Accepts, htagCopy, hguard, dialect, decide_eq_true_eq]
    · exact hrest
  · rw [otag, coSP, hretLoad]
  · have h5' : copied.values[5] = ⟨64, fr.rbp⟩ := by
      rw [co5, ckeep ⟨5, by decide⟩ (by decide), h5]
      rfl
    have h12' : copied.values[12] = ⟨64, fr.r12⟩ := by
      rw [co12, ckeep ⟨12, by decide⟩ (by decide), h12]
      rfl
    have h13' : copied.values[13] = ⟨64, fr.r13⟩ := by
      rw [co13, ckeep ⟨13, by decide⟩ (by decide), h13]
      rfl
    have h15' : copied.values[15] = ⟨64, fr.r15⟩ := by
      rw [co15, ckeep ⟨15, by decide⟩ (by decide), h15]
      rfl
    have h39' : copied.values[39] = ⟨32, fr.mxcsr⟩ := by
      rw [co39, ckeep ⟨39, by decide⟩ (by decide), h39]
      rfl
    have h50' : copied.values[50] = ⟨16, fr.ftw⟩ := by
      rw [co50, ckeep ⟨50, by decide⟩ (by decide), h50]
      rfl
    have h51' : copied.values[51] = ⟨16, fr.fcw⟩ := by
      rw [co51, ckeep ⟨51, by decide⟩ (by decide), h51]
      rfl
    have os3 : output.values[3] = ⟨64, fr.rbx⟩ := by
      rw [o3, coSP]
      simp only [BitVec.ofNat_eq_ofNat] at ⊢
      rw [savedLoad 40 (by decide)]
      have he : sp+40 = fr.rsp-16 := by dsimp only [sp]; bv_omega
      change (⟨64, memLoad mem (sp+40) 64⟩ : Value) = ⟨64, fr.rbx⟩
      rw [he, hsave3]
    have os14 : output.values[14] = ⟨64, fr.r14⟩ := by
      rw [o14, coSP]
      simp only [BitVec.ofNat_eq_ofNat] at ⊢
      rw [savedLoad 48 (by decide)]
      have he : sp+48 = fr.rsp-8 := by dsimp only [sp]; bv_omega
      change (⟨64, memLoad mem (sp+48) 64⟩ : Value) = ⟨64, fr.r14⟩
      rw [he, hsave14]
    have os4 : output.values[4] = ⟨64, fr.rsp+8⟩ := by
      rw [o4, coSP]
      have he : sp+64 = fr.rsp+8 := by dsimp only [sp]; bv_omega
      rw [he]
    have hd : Atom.All code output.values output.store (LIR.Fn102040.frameInfo.doneAtoms fr) := by
      change output.values[4] = _ ∧ output.values[22] = _ ∧
        output.values[3] = _ ∧ output.values[5] = _ ∧ output.values[12] = _ ∧
        output.values[13] = _ ∧ output.values[14] = _ ∧ output.values[15] = _ ∧
        output.values[39] = _ ∧ output.values[50] = _ ∧ output.values[51] = _ ∧ True
      exact ⟨os4, (okeep ⟨22, by decide⟩ (by decide)).trans co22, os3,
        (okeep ⟨5, by decide⟩ (by decide)).trans h5',
        (okeep ⟨12, by decide⟩ (by decide)).trans h12',
        (okeep ⟨13, by decide⟩ (by decide)).trans h13', os14,
        (okeep ⟨15, by decide⟩ (by decide)).trans h15',
        (okeep ⟨39, by decide⟩ (by decide)).trans h39',
        (okeep ⟨50, by decide⟩ (by decide)).trans h50',
        (okeep ⟨51, by decide⟩ (by decide)).trans h51', trivial⟩
    cases use256 <;> exact hd
  · rw [ostore]
    exact hfull
  · rw [ostore]
    refine ⟨AES16.scheduleIn_of_copy hschedPush hpostCopy, ?_, ?_, ?_, ?_⟩
    · have hk := keyLoad 0 (by decide)
      simp only [BitVec.add_zero] at hk
      rw [hk]; exact hkey.1
    · simp only [BitVec.ofNat_eq_ofNat] at ⊢
      rw [keyLoad 8 (by decide)]
      exact hkey.2.1
    · simp only [BitVec.ofNat_eq_ofNat] at ⊢
      rw [keyLoad 16 (by decide)]
      exact hkey.2.2.1
    · simp only [BitVec.ofNat_eq_ofNat] at ⊢
      rw [keyLoad 24 (by decide)]
      exact hkey.2.2.2
end AesGcm.Proofs.Machine.GCM
