import AesGcm.Proofs.Machine.Entry.InPlaceDecrypt.Blocks
import AesGcm.Proofs.Machine.LIR.Aes128gcmDecryptInPlace.Frame
import AesGcm.Proofs.Machine.LIR.Aes256gcmDecryptInPlace.Frame
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.GCM.Initialization
import AesGcm.Proofs.Machine.Runtime.Preservation

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def initializationPost (use256 : Bool) (code : CodeMap)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram) : Prop :=
  Atom.All code args mem (if use256 then LIR.Aes256gcmDecryptInPlace.frameAt .l101560 fr
    else LIR.Aes128gcmDecryptInPlace.frameAt .l101280 fr) ∧
  args[13].get 64 = fr.r9 ∧
  GcmContext.ContextIn (AES16.variant use256) key
    (fr.rsp - BitVec.ofNat 64 (frameBytes use256) + (if use256 then 0x100 else 0xc0)) mem ∧
  RamWriteFrame fr.original mem [fr.region] ∧
  GPRsTyped args

set_option maxHeartbeats 800000 in
theorem initialization_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hentry : Atom.All code args mem
      (if use256 then LIR.Aes256gcmDecryptInPlace.frameAt .l101550 fr
        else LIR.Aes128gcmDecryptInPlace.frameAt .l101270 fr))
    (hRBP : args[5] = ⟨64, fr.rsp - BitVec.ofNat 64 (frameBytes use256) + 16⟩)
    (hTypes : GPRsTyped args)
    (hSchedule : AES16.ScheduleIn (AES16.variant use256) key
      (fr.rsp - BitVec.ofNat 64 (frameBytes use256) + 16) mem)
    (hframe : RamWriteFrame fr.original mem [fr.region]) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l101550 else .l101270), args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l101560 else .l101280) ∧
      initializationPost use256 code key fr next.arguments next.store := by
  let window : Nat := if use256 then 0xdb0 else 0xb20
  let gcmWindow : Nat := if use256 then 0x1b0 else 0x1a0
  let depth : Nat := frameBytes use256 + 8
  let size : Nat := 16 * ((AES16.variant use256).Nr + 1)
  let ctxOffset : Nat := if use256 then 0x100 else 0xc0
  let ctxSize : Nat := GcmContext.size (AES16.variant use256)
  have hd : depth ≤ window := by cases use256 <;> decide
  have hcw : depth + gcmWindow ≤ window := by cases use256 <;> decide
  have hfb : frameBytes use256 ≤ window := by cases use256 <;> decide
  have hfb16 : 16 ≤ frameBytes use256 := by cases use256 <;> decide
  have hfo : ctxOffset ≤ frameBytes use256 := by cases use256 <;> decide
  have hsr : frameBytes use256 - 16 = size + (frameBytes use256 - ctxOffset) := by
    cases use256 <;> decide
  have hce : ctxSize + 48 ≤ frameBytes use256 - ctxOffset := by cases use256 <;> decide
  have hentry' : args[4] = ⟨64, fr.rsp - BitVec.ofNat 64 (frameBytes use256)⟩ ∧
      args[22] = ⟨1, 0⟩ ∧ args[3] = ⟨64, fr.rcx⟩ ∧ args[12] = ⟨64, fr.r8⟩ ∧
      args[13] = ⟨64, fr.r9⟩ ∧ args[14] = ⟨64, fr.rdx⟩ ∧ args[15] = ⟨64, fr.rsi⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧ memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧ memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧ memLoad mem (fr.rsp - 8) 64 = fr.rbp ∧
      Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code mem (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
      Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0 ∧
      Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
      (0x201238 + window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hentry
  rcases hentry' with ⟨h4, h22, h3, h12, h13, h14, h15, h39, h50, h51,
    hs3, hs12, hs13, hs14, hs15, hs5, hr, hret, hretLow, hstack, hroom, halign,
    hs0r, hs0, hs1r, hs1, hs2r, hs2, hs3r, hslot3, hslotSep, _⟩
  let lower := fr.rsp - BitVec.ofNat 64 window
  let childSP := fr.rsp - BitVec.ofNat 64 depth
  let schedule := fr.rsp - BitVec.ofNat 64 (frameBytes use256) + 16
  let context := fr.rsp - BitVec.ofNat 64 (frameBytes use256) + BitVec.ofNat 64 ctxOffset
  let writes := [span lower (window - frameBytes use256), span context ctxSize]
  have hsp : args[4].get 64 = fr.rsp - BitVec.ofNat 64 (frameBytes use256) := by rw [h4]; rfl
  have hsub (n : Nat) (hn : n ≤ window) :
      (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    have hn64 : n < 2^64 := by have := fr.rsp.isLt; omega
    have hle : BitVec.ofNat 64 n ≤ fr.rsp := by
      change n % 2^64 ≤ fr.rsp.toNat
      omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have hlower : lower.toNat = fr.rsp.toNat - window := hsub window (Nat.le_refl _)
  have hchild : childSP.toNat = fr.rsp.toNat - depth := hsub depth hd
  have hchildEq : fr.rsp - BitVec.ofNat 64 (frameBytes use256) - 8 = childSP := by
    simp only [childSP, depth, BitVec.ofNat_add]
    bv_omega
  have hschedEq : schedule = fr.rsp - BitVec.ofNat 64 (frameBytes use256 - 16) := by
    cases use256 <;> simp only [schedule, frameBytes, Bool.false_eq_true, ↓reduceIte]
    all_goals bv_omega
  have hsched : schedule.toNat = fr.rsp.toNat - (frameBytes use256 - 16) := by
    rw [hschedEq]
    exact hsub _ (by omega)
  have hctxEq : context = fr.rsp - BitVec.ofNat 64 (frameBytes use256 - ctxOffset) := by
    cases use256 <;> simp only [context, ctxOffset, frameBytes, Bool.false_eq_true, ↓reduceIte]
    all_goals bv_omega
  have hctx : context.toNat = fr.rsp.toNat - (frameBytes use256 - ctxOffset) := by
    rw [hctxEq]
    exact hsub _ (by omega)
  have hwrite8 : Writable code mem childSP 8 := hstack.sub
    (by rw [hchild, hsub window (Nat.le_refl _)]; omega)
    (by rw [hchild, hsub window (Nat.le_refl _)]
        have hh : 8 ≤ depth := by cases use256 <;> decide
        omega)
  obtain ⟨callee, continuation, hcall, hcLabel, htarget, hguard, hc4, hc7, hc6,
      hkeep, hcTypes, hmem⟩ := initialize_runBlock use256 code hcode args mem hTypes
        (by rw [hsp, hchildEq]; exact hwrite8)
  have hfSetup : RamWriteFrame mem callee.store writes := by
    rw [hmem, hsp, hchildEq]
    apply (RamWriteFrame.refl mem writes).memStore
    refine ⟨span lower (window - frameBytes use256), by simp [writes], ?_⟩
    simp only [InRegion, span, hlower, hchild]
    have hh : depth = frameBytes use256 + 8 := rfl
    have hh' := hr.low
    omega
  have writesWithin : RegionsWithin writes [span lower window] := by
    intro r hin
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · exact ⟨span lower window, by simp, Nat.le_refl _, by simp only [span]; omega⟩
    · refine ⟨span lower window, by simp, ?_, ?_⟩ <;>
        simp only [span, hctx, hlower] <;> omega
  have hfWindow : RamWriteFrame mem callee.store [span lower window] :=
    (RamWriteFrame.refl _ _).trans hfSetup writesWithin
  have scheduleOutside : Outside writes schedule size := by
    refine ⟨by rw [hsched]; have := hr.low; omega, ?_⟩
    intro r hin
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · right
      simp only [span, hlower, hsched]
      omega
    · left
      simp only [span, hctx, hsched]
      omega
  have scheduleIn := AES16.scheduleIn_of_frame hSchedule hfSetup scheduleOutside
  have c4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = childSP := by
    rw [hc4, hsp]
    exact hchildEq
  have c7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = context := by
    rw [hc7, hsp]
    cases use256 <;> rfl
  have c6 : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = schedule := by
    rw [hc6, hRBP]
    rfl
  let af := activationOfValues callee.store callee.arguments
    (if use256 then 0x101560 else 0x101280) lower
  have asp : af.rsp = childSP := c4
  have alow : af.low = lower := rfl
  have adst : af.rdi = context := c7
  have asrc : af.rsi = schedule := c6
  have childWrite : Writable code callee.store
      ((callee.arguments[4]'(by change 4 < 53; decide)).get 64 - BitVec.ofNat 64 gcmWindow)
      gcmWindow := by
    rw [c4]
    have heq : childSP - BitVec.ofNat 64 gcmWindow =
        fr.rsp - BitVec.ofNat 64 (depth + gcmWindow) := by
      simp only [childSP, BitVec.ofNat_add]
      bv_omega
    rw [heq]
    exact (hstack.of_frame hfWindow).sub
      (by rw [hsub _ hcw, hsub window (Nat.le_refl _)]; omega)
      (by rw [hsub _ hcw, hsub window (Nat.le_refl _)]; omega)
  have destWrite : Writable code callee.store context ctxSize :=
    (hstack.of_frame hfWindow).sub
      (by rw [hctx, hsub window (Nat.le_refl _)]; omega)
      (by rw [hctx, hsub window (Nat.le_refl _)]; omega)
  have sourceRead : Readable callee.store schedule size :=
    (hstack.readable.of_frame hfWindow).sub
      (by rw [hsched, hsub window (Nat.le_refl _)]; omega)
      (by rw [hsched, hsub window (Nat.le_refl _)]; omega)
  have slotOutside (addr : BitVec 64) (hlo : 0x201208 ≤ addr.toNat)
      (hhi : addr.toNat + 8 ≤ 0x201238) : Outside [span lower window] addr 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hlower]
    omega
  have hslots : Atom.All code callee.arguments callee.store
      ((if use256 then LIR.Fn102180.frameInfo else LIR.Fn102040.frameInfo).callSlotAtoms
        (if use256 then LIR.Fn102180.frameInfo else LIR.Fn102040.frameInfo).callSlots af) := by
    have s0 := (hfWindow.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans hs0
    have s1 := (hfWindow.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans hs1
    have s3 := (hfWindow.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans hslot3
    have apart : 0x201238 + gcmWindow ≤ childSP.toNat ∨ childSP.toNat ≤ 0x201208 := by
      rw [hchild]
      omega
    cases use256 <;> refine ⟨hs0r.of_frame hfWindow, s0, hs1r.of_frame hfWindow, s1,
      hs3r.of_frame hfWindow, s3, ?_, trivial⟩
    all_goals change _ ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201208
    all_goals rw [asp]; exact apart
  have hpre : AES16.ScheduleIn (AES16.variant use256) key af.rsi callee.store ∧
      Readable callee.store af.rsi size ∧ Writable code callee.store af.rdi ctxSize ∧
      (callStack af).Disjoint (span af.rsi size) ∧
      (callStack af).Disjoint (span af.rdi ctxSize) ∧
      (span af.rdi ctxSize).Disjoint (span af.rsi size) ∧
      (span af.rdi 32).Disjoint (span 0x201208 8) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [asrc]
      exact scheduleIn
    · rw [asrc]
      exact sourceRead
    · rw [adst]
      exact destWrite
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, asp, alow, asrc,
        hlower, hchild, hsched] at hx hy
      have hh : depth = frameBytes use256 + 8 := rfl
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, asp, alow, adst,
        hlower, hchild, hctx] at hx hy
      have hh : depth = frameBytes use256 + 8 := rfl
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, span, adst, asrc, hctx, hsched] at hx hy
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, span, adst, hctx] at hx hy
      change (0x201208 : Nat) ≤ x ∧ x < 0x201210 at hy
      have hh : 32 ≤ ctxSize := by cases use256 <;> decide
      omega
  have c39 : (callee.arguments[39]'(by change 39 < 53; decide)) = ⟨32, fr.mxcsr⟩ :=
    (hkeep 39 (by decide)).trans h39
  have c50 : (callee.arguments[50]'(by change 50 < 53; decide)) = ⟨16, fr.ftw⟩ :=
    (hkeep 50 (by decide)).trans h50
  have c51 : (callee.arguments[51]'(by change 51 < 53; decide)) = ⟨16, fr.fcw⟩ :=
    (hkeep 51 (by decide)).trans h51
  have hgw : (if use256 then LIR.Fn102180.frameInfo else LIR.Fn102040.frameInfo).window =
      gcmWindow := by cases use256 <;> rfl
  obtain ⟨output, hexec, htag, hdone, ht, hf, hp⟩ :=
    callContract_exec_values LIR.lifted code (if use256 then .l102180 else .l102040)
      (if use256 then LIR.Fn102180.frameInfo else LIR.Fn102040.frameInfo)
      (fun fr ↦ [span fr.rdi ctxSize]) _ _ (GCM.initialize_callContract use256 code hcode key)
      callee.store callee.arguments (if use256 then 0x101560 else 0x101280) lower
      hcTypes (by rw [c39]; rfl) (by rw [c50]; rfl) (by rw [c51]; rfl)
      ((hkeep 22 (by decide)).trans h22)
      (by rw [c4]; exact hwrite8.readable.of_frame hfWindow)
      (by rw [c4, hmem, hsp, hchildEq]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by cases use256 <;> decide)
      (by intro _; rw [hgw]; exact childWrite)
      (by rw [hgw, c4, hlower, hchild]; omega)
      (by rw [c4, hchild]
          cases use256 <;> simp only [depth, frameBytes, Bool.false_eq_true, ↓reduceIte] at hd ⊢ <;> omega)
      hslots hpre
  change Atom.All code output.values output.store
    ((if use256 then LIR.Fn102180.frameInfo else LIR.Fn102040.frameInfo).doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi ctxSize] at hf
  change GcmContext.ContextIn (AES16.variant use256) key af.rdi output.store at hp
  have hdone' : output.values[4] = ⟨64, af.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
      output.values[3] = ⟨64, af.rbx⟩ ∧ output.values[5] = ⟨64, af.rbp⟩ ∧
      output.values[12] = ⟨64, af.r12⟩ ∧ output.values[13] = ⟨64, af.r13⟩ ∧
      output.values[14] = ⟨64, af.r14⟩ ∧ output.values[15] = ⟨64, af.r15⟩ ∧
      output.values[39] = ⟨32, af.mxcsr⟩ ∧ output.values[50] = ⟨16, af.ftw⟩ ∧
      output.values[51] = ⟨16, af.fcw⟩ ∧ True := by cases use256 <;> exact hdone
  rcases hdone' with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, _⟩
  have childWithin : RegionsWithin [af.region, span af.rdi ctxSize] writes := by
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨span lower (window - frameBytes use256), by simp [writes], ?_, ?_⟩ <;>
        simp only [Activation.region, span, alow, asp, hlower, hchild]
      · omega
      · have hh : depth = frameBytes use256 + 8 := rfl
        omega
    · rw [adst]
      exact ⟨span context ctxSize, by simp [writes], Nat.le_refl _, Nat.le_refl _⟩
  have hfLocal : RamWriteFrame mem output.store writes := hfSetup.trans hf childWithin
  have hfOut : RamWriteFrame mem output.store [span lower window] :=
    (RamWriteFrame.refl _ _).trans hfLocal writesWithin
  have fullWithin : RegionsWithin [span lower window] [fr.region] := by
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
      simp only [span, Activation.region, hlower] <;> omega
  have hfFull : RamWriteFrame fr.original output.store [fr.region] :=
    hframe.trans hfOut fullWithin
  have hs48 : (fr.rsp - (48 : BitVec 64)).toNat = fr.rsp.toNat - 48 :=
    hsub 48 (by cases use256 <;> decide)
  have protectSaved : Outside writes (fr.rsp - 48) 56 := by
    refine ⟨by rw [hs48]; have := hr.low; omega, ?_⟩
    intro r hin
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · right
      simp only [span, hlower, hs48]
      have hh : 48 ≤ frameBytes use256 := by cases use256 <;> decide
      omega
    · right
      simp only [span, hctx, hs48]
      omega
  have savedLoad (offset : Nat) (hoffset : offset ≤ 48) :
      memLoad output.store (fr.rsp - BitVec.ofNat 64 offset) 64 =
        memLoad mem (fr.rsp - BitVec.ofNat 64 offset) 64 := by
    apply hfLocal.memLoad_eq
    have hout := outside_subregion (offset := 48 - offset) (count := 8)
      protectSaved (by omega) (by omega)
    have he : fr.rsp - (48 : BitVec 64) + BitVec.ofNat 64 (48 - offset) =
        fr.rsp - BitVec.ofNat 64 offset := by bv_omega
    rwa [he] at hout
  have saved3 := (savedLoad 48 (by decide)).trans hs3
  have saved12 := (savedLoad 40 (by decide)).trans hs12
  have saved13 := (savedLoad 32 (by decide)).trans hs13
  have saved14 := (savedLoad 24 (by decide)).trans hs14
  have saved15 := (savedLoad 16 (by decide)).trans hs15
  have saved5 := (savedLoad 8 (by decide)).trans hs5
  have savedReturn : memLoad output.store fr.rsp 64 = fr.ret := by
    have hh := savedLoad 0 (by decide)
    have hz : fr.rsp - BitVec.ofNat 64 0 = fr.rsp := by bv_omega
    rw [hz] at hh
    exact hh.trans hret
  have abx : af.rbx = fr.rcx := congrArg (fun v ↦ v.get 64) ((hkeep 3 (by decide)).trans h3)
  have a12 : af.r12 = fr.r8 := congrArg (fun v ↦ v.get 64) ((hkeep 12 (by decide)).trans h12)
  have a13 : af.r13 = fr.r9 := congrArg (fun v ↦ v.get 64) ((hkeep 13 (by decide)).trans h13)
  have a14 : af.r14 = fr.rdx := congrArg (fun v ↦ v.get 64) ((hkeep 14 (by decide)).trans h14)
  have a15 : af.r15 = fr.rsi := congrArg (fun v ↦ v.get 64) ((hkeep 15 (by decide)).trans h15)
  have a39 : af.mxcsr = fr.mxcsr := congrArg (fun v ↦ v.get 32) c39
  have a50 : af.ftw = fr.ftw := congrArg (fun v ↦ v.get 16) c50
  have a51 : af.fcw = fr.fcw := congrArg (fun v ↦ v.get 16) c51
  have outSP : output.values[4] = ⟨64, fr.rsp - BitVec.ofNat 64 (frameBytes use256)⟩ := by
    rw [ho4, asp]
    congr 1
    simp only [childSP, depth, BitVec.ofNat_add]
    bv_omega
  have slot0 := (hfOut.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans hs0
  have slot1 := (hfOut.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans hs1
  have slot2 := (hfOut.memLoad_eq (slotOutside 0x201228 (by decide) (by decide))).trans hs2
  have slot3 := (hfOut.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans hslot3
  let next := continuation.resume output
  have nextArgs : next.arguments = output.values := CFGCall.resume_arguments continuation output
  have nextStore : next.store = output.store := rfl
  have nextLabel : next.label = (if use256 then .l101560 else .l101280) := htarget
  have working : Atom.All code next.arguments next.store
      (if use256 then LIR.Aes256gcmDecryptInPlace.frameAt .l101560 fr
        else LIR.Aes128gcmDecryptInPlace.frameAt .l101280 fr) := by
    rw [nextArgs, nextStore]
    cases use256 <;> exact ⟨outSP, ho22, ho3.trans (congrArg (Value.mk 64) abx),
      ho12.trans (congrArg (Value.mk 64) a12), ho13.trans (congrArg (Value.mk 64) a13),
      ho14.trans (congrArg (Value.mk 64) a14), ho15.trans (congrArg (Value.mk 64) a15),
      ho39.trans (congrArg (Value.mk 32) a39),
      ho50.trans (congrArg (Value.mk 16) a50), ho51.trans (congrArg (Value.mk 16) a51),
      saved3, saved12, saved13, saved14, saved15, saved5,
      hr.of_frame hfOut, savedReturn, hretLow, hstack.of_frame hfOut, hroom, halign,
      hs0r.of_frame hfOut, slot0, hs1r.of_frame hfOut, slot1,
      hs2r.of_frame hfOut, slot2, hs3r.of_frame hfOut, slot3, hslotSep, trivial⟩
  have hexecc : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    change LIR.program.Exec (dialect code)
      ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ output
    rw [hcLabel]
    exact hexec
  have ha : continuation.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hguard, htag]
    cases use256 <;> rfl
  have hresume := CFGCall.exec_reaches_resume hexecc continuation [] ha
  have hstep : LIR.program.step (dialect code)
      ⟨⟨(if use256 then .l101550 else .l101270), args, mem⟩, []⟩ =
      .next ⟨callee, [continuation]⟩ := by rw [Program.step, hcall]; rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans hresume, nextLabel,
    working, ?_, ?_, hfFull, ?_⟩
  · rw [nextArgs, ho13, a13]
    rfl
  · rw [nextStore]
    cases use256 <;> simpa only [adst, context, ctxOffset, Bool.false_eq_true,
      ↓reduceIte, BitVec.ofNat_eq_ofNat] using hp
  · simpa only [nextArgs] using ht

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
