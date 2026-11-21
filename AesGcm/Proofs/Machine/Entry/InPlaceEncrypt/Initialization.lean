import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Blocks
import AesGcm.Proofs.Machine.LIR.Aes128gcmEncryptInPlace.Frame
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.GCM.Initialization
import AesGcm.Proofs.Machine.Runtime.Call

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def initializationPost (code : CodeMap) (key : Vector UInt8 16)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) : Prop :=
  Atom.All code args mem (LIR.Aes128gcmEncryptInPlace.frameAt .l1013c8 fr) ∧
  args[15].get 64 = fr.rcx ∧
  args[5].get 64 = memLoad fr.original (fr.rsp + 8) 64 ∧
  GcmContext.ContextIn .aes128 key (fr.rsp - 264) mem ∧
  Readable mem (fr.rsp + 8) 8 ∧
  memLoad mem (fr.rsp + 8) 64 = memLoad fr.original (fr.rsp + 8) 64 ∧
  RamWriteFrame fr.original mem [fr.region] ∧
  GPRsTyped args

set_option maxHeartbeats 400000 in
theorem initialization_reaches (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 16)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hentry : Atom.All code args mem
      (LIR.Aes128gcmEncryptInPlace.frameAt .l1013b0 fr))
    (hRBP : args[5] = ⟨64, fr.rsp - 472 + 32⟩)
    (hTypes : GPRsTyped args)
    (hSchedule : AES16.ScheduleIn .aes128 key
      (fr.rsp - 472 + 32) mem)
    (hframe : RamWriteFrame fr.original mem [fr.region])
    (hargRead : Readable fr.original (fr.rsp + 8) 8)
    :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨.l1013b0, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = .l1013c8 ∧
      initializationPost code key fr next.arguments next.store := by
  obtain ⟨h4, h22, h3, h12, h13, h14, h15, h39, h50, h51,
    hs3, hs12, hs13, hs14, hs15, hs5, hr, hret, hretLow, hstack, hroom, halign,
    hs0r, hs0, hs1r, hs1, hs2r, hs2, hs3r, hs3slot, hslotSep, _⟩ := hentry
  change args[4] = ⟨64, fr.rsp - 472⟩ at h4
  change fr.low.toNat + 0xb20 ≤ fr.rsp.toNat at hroom
  change 0x201d58 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208 at hslotSep
  change fr.rsp.toNat % 16 = 8 at halign
  have hsp : args[4].get 64 = fr.rsp - 472 := by rw [h4]; rfl
  have returnLow := hr.low
  have argLow := hargRead.low
  have hsub (n : Nat) (hn : n ≤ 0xb20) :
      (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    have hn64 : n < 2^64 := by omega
    have hle : BitVec.ofNat 64 n ≤ fr.rsp := by
      change n % 2^64 ≤ fr.rsp.toNat
      omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  let lower := fr.rsp - 0xb20
  let childSP := fr.rsp - 480
  let schedule := fr.rsp - 440
  let context := fr.rsp - 264
  let stackWrites := span lower (0xb20 - 472)
  let writes := [stackWrites, span context 208]
  have hlower : lower.toNat = fr.rsp.toNat - 0xb20 := hsub _ (by decide)
  have hchild : childSP.toNat = fr.rsp.toNat - 480 := hsub _ (by decide)
  have hsched : schedule.toNat = fr.rsp.toNat - 440 := hsub _ (by decide)
  have hctx : context.toNat = fr.rsp.toNat - 264 := hsub _ (by decide)
  have hchildEq : args[4].get 64 - 8 = childSP := by
    rw [hsp, BitVec.sub_sub]
    rfl
  have hargEq : args[4].get 64 + 480 = fr.rsp + 8 := by
    rw [hsp]
    exact sub_add_lit _ _ _ _ (by decide)
  have scheduleAddr : fr.rsp - 472 + 32 = schedule := by
    simp only [schedule, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have argAddr : (fr.rsp + (8 : BitVec 64)).toNat = fr.rsp.toNat + 8 := by
    rw [BitVec.toNat_add]
    have hb : (8 : BitVec 64).toNat = 8 := rfl
    rw [hb, Nat.mod_eq_of_lt (by omega)]
  have argOutside : Outside [fr.region] (fr.rsp + 8) 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [Activation.region, argAddr]
    omega
  have hwrite8 : Writable code mem childSP 8 :=
    hstack.sub (by rw [hchild, hlower]; omega) (by rw [hchild, hlower]; omega)
  have argRead : Readable mem (fr.rsp + 8) 8 := hargRead.of_frame hframe
  obtain ⟨callee, continuation, hcall, hcLabel, htarget, hguard, hmem, hc4, hc7, hc6,
      hc5, hkeep, hcTypes⟩ :=
    context_call false code hcode args mem
      (by rw [hchildEq]; exact hwrite8)
      (by change Readable mem (args[4].get 64 + 480) 8
          rw [hargEq]
          exact argRead)
  have hfSetup : RamWriteFrame mem callee.store writes := by
    rw [hmem, hchildEq]
    apply (RamWriteFrame.refl mem writes).memStore
    refine ⟨stackWrites, List.mem_cons_self, ?_⟩
    simp only [InRegion, stackWrites, span, hlower, hchild]
    omega
  have writesWithin : RegionsWithin writes [span lower 0xb20] := by
    intro r hin
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl <;>
      refine ⟨span lower 0xb20, List.mem_cons_self, ?_, ?_⟩ <;>
      simp only [stackWrites, span, hlower, hctx] <;> omega
  have hfWindow : RamWriteFrame mem callee.store [span lower 0xb20] :=
    (RamWriteFrame.refl _ _).trans hfSetup writesWithin
  have scheduleOutside : Outside writes schedule 176 := by
    refine ⟨by rw [hsched]; omega, ?_⟩
    intro r hin
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl <;> simp only [stackWrites, span, hlower, hsched, hctx] <;> omega
  have scheduleIn : AES16.ScheduleIn .aes128 key schedule callee.store := by
    rw [scheduleAddr] at hSchedule
    exact AES16.scheduleIn_of_frame hSchedule hfSetup scheduleOutside
  let af := activationOfValues callee.store callee.arguments 0x1013c8 lower
  have asp : af.rsp = childSP := by
    change (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = _
    rw [hc4, hchildEq]
    rfl
  have alow : af.low = lower := rfl
  have adst : af.rdi = context := by
    change (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = _
    rw [hc7, hsp]
    change fr.rsp - 472 + 208 = context
    simp only [context, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have asrc : af.rsi = schedule := by
    change (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = _
    rw [hc6, hRBP]
    change fr.rsp - 472 + 32 = schedule
    exact scheduleAddr
  have c39 : (callee.arguments[39]'(by change 39 < 53; decide)) = ⟨32, fr.mxcsr⟩ :=
    (hkeep 39 (by decide)).trans h39
  have c50 : (callee.arguments[50]'(by change 50 < 53; decide)) = ⟨16, fr.ftw⟩ :=
    (hkeep 50 (by decide)).trans h50
  have c51 : (callee.arguments[51]'(by change 51 < 53; decide)) = ⟨16, fr.fcw⟩ :=
    (hkeep 51 (by decide)).trans h51
  have hs (a : BitVec 64) (n : Nat) (hl : lower.toNat ≤ a.toNat)
      (hh : a.toNat + n ≤ lower.toNat + 0xb20) : Writable code callee.store a n :=
    (hstack.of_frame hfWindow).sub hl hh
  have childWrite : Writable code callee.store (af.rsp - 0x1a0) 0x1a0 := by
    have heq : childSP - 0x1a0 = fr.rsp - 896 := by
      dsimp only [childSP]
      rw [BitVec.sub_sub]
      rfl
    rw [asp, heq]
    have hnat : (fr.rsp - (896 : BitVec 64)).toNat = fr.rsp.toNat - 896 :=
      hsub 896 (by decide)
    apply hs <;> rw [hlower, hnat] <;> omega
  have destWrite : Writable code callee.store af.rdi 208 := by
    rw [adst]
    apply hs <;> rw [hlower, hctx] <;> omega
  have sourceRead : Readable callee.store af.rsi 176 := by
    rw [asrc]
    apply Writable.readable
    apply hs <;> rw [hlower, hsched] <;> omega
  have slotOutside (addr : BitVec 64) (hlo : 0x201208 ≤ addr.toNat)
      (hhi : addr.toNat + 8 ≤ 0x201238) : Outside [span lower 0xb20] addr 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hlower]
    omega
  have hslots : Atom.All code callee.arguments callee.store
      (LIR.Fn102040.frameInfo.callSlotAtoms LIR.Fn102040.frameInfo.callSlots af) := by
    refine ⟨hs0r.of_frame hfWindow,
      (hfWindow.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans hs0,
      hs1r.of_frame hfWindow,
      (hfWindow.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans hs1,
      hs3r.of_frame hfWindow,
      (hfWindow.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans hs3slot,
      ?_, trivial⟩
    change 0x2013d8 ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201208
    rw [asp, hchild]
    omega
  have hpre : AES16.ScheduleIn .aes128 key af.rsi callee.store ∧
      Readable callee.store af.rsi 176 ∧ Writable code callee.store af.rdi 208 ∧
      (callStack af).Disjoint (span af.rsi 176) ∧
      (callStack af).Disjoint (span af.rdi 208) ∧
      (span af.rdi 208).Disjoint (span af.rsi 176) ∧
      (span af.rdi 32).Disjoint (span 0x201208 8) := by
    refine ⟨asrc ▸ scheduleIn, sourceRead, destWrite, ?_, ?_, ?_, ?_⟩
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, asp, alow, asrc,
        hlower, hchild, hsched] at hx hy
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, asp, alow, adst,
        hlower, hchild, hctx] at hx hy
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, span, adst, asrc, hctx, hsched] at hx hy
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, span, adst, hctx] at hx
      change (0x201208 : Nat) ≤ x ∧ x < 0x201210 at hy
      omega
  obtain ⟨output, hexec, htag, hdone, ht, hf, hp⟩ :=
    callContract_exec_values LIR.lifted code .l102040 LIR.Fn102040.frameInfo
      (fun fr ↦ [span fr.rdi 208]) _ _ (GCM.initialize_callContract false code hcode key)
      callee.store callee.arguments 0x1013c8 lower
      (hcTypes hTypes) (by rw [c39]; rfl) (by rw [c50]; rfl) (by rw [c51]; rfl)
      ((hkeep 22 (by decide)).trans h22)
      (by change Readable callee.store af.rsp 8; rw [asp]; exact hwrite8.readable.of_frame hfWindow)
      (by change memLoad callee.store af.rsp 64 = 0x1013c8
          rw [asp, hmem, hchildEq]
          exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by decide)
      (fun _ ↦ childWrite)
      (by change lower.toNat + 0x1a0 ≤ af.rsp.toNat; rw [asp, hlower, hchild]; omega)
      (by change af.rsp.toNat % 16 = 8; rw [asp, hchild]; omega)
      hslots hpre
  change Atom.All code output.values output.store (LIR.Fn102040.frameInfo.doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi 208] at hf
  change GcmContext.ContextIn .aes128 key af.rdi output.store at hp
  obtain ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, _⟩ := hdone
  change output.values[4] = ⟨64, af.rsp + 8⟩ at ho4
  change output.values[5] = ⟨64, af.rbp⟩ at ho5
  change output.values[15] = ⟨64, af.r15⟩ at ho15
  have childWithin : RegionsWithin [af.region, span af.rdi 208] writes := by
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨stackWrites, List.mem_cons_self, ?_, ?_⟩ <;>
        simp only [Activation.region, stackWrites, span, alow, asp, hlower, hchild] <;> omega
    · rw [adst]
      exact ⟨span context 208, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  have hfLocal : RamWriteFrame mem output.store writes := hfSetup.trans hf childWithin
  have hfOut : RamWriteFrame mem output.store [span lower 0xb20] :=
    (RamWriteFrame.refl _ _).trans hfLocal writesWithin
  have hfFull : RamWriteFrame fr.original output.store [fr.region] := by
    refine hframe.trans hfOut ?_
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨fr.region, List.mem_cons_self, ?_, ?_⟩ <;>
      simp only [span, Activation.region, hlower] <;> omega
  have savedLoad (offset : Nat) (hoffset : offset ≤ 48) :
      memLoad output.store (fr.rsp - BitVec.ofNat 64 offset) 64 =
        memLoad mem (fr.rsp - BitVec.ofNat 64 offset) 64 := by
    apply hfLocal.memLoad_eq
    rw [show 64 / 8 = 8 by decide]
    refine ⟨by rw [hsub _ (by omega)]; omega, ?_⟩
    intro r hin
    simp only [writes, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl <;>
      simp only [stackWrites, span, hlower, hctx, hsub _ (by omega : offset ≤ 0xb20)] <;> omega
  have savedReturn : memLoad output.store fr.rsp 64 = fr.ret := by
    have hh := savedLoad 0 (by decide)
    rw [BitVec.sub_zero] at hh
    exact hh.trans hret
  have keptGPR (r : Fin 53) (hr : r.val ∈ [3,12,13,14,15,22,39,50,51])
      {x : BitVec 64} (hx : args[r] = ⟨64, x⟩) :
      (callee.arguments[r]).get 64 = x := by rw [hkeep r hr, hx]; rfl
  have outSP : output.values[4] = ⟨64, fr.rsp - 472⟩ := by
    rw [ho4, asp]
    exact congrArg (Value.mk 64) (by
      simp only [childSP, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl)
  let next := continuation.resume output
  have nextArgs : next.arguments = output.values := CFGCall.resume_arguments continuation output
  have nextStore : next.store = output.store := rfl
  have working : Atom.All code next.arguments next.store
      (LIR.Aes128gcmEncryptInPlace.frameAt .l1013c8 fr) := by
    rw [nextArgs, nextStore]
    exact ⟨outSP, ho22, ho3.trans (congrArg (Value.mk 64) (keptGPR 3 (by decide) h3)),
      ho12.trans (congrArg (Value.mk 64) (keptGPR 12 (by decide) h12)),
      ho13.trans (congrArg (Value.mk 64) (keptGPR 13 (by decide) h13)),
      ho14.trans (congrArg (Value.mk 64) (keptGPR 14 (by decide) h14)),
      ho15.trans (congrArg (Value.mk 64) (keptGPR 15 (by decide) h15)),
      ho39.trans (congrArg (fun v : Value ↦ Value.mk 32 (v.get 32)) c39),
      ho50.trans (congrArg (fun v : Value ↦ Value.mk 16 (v.get 16)) c50),
      ho51.trans (congrArg (fun v : Value ↦ Value.mk 16 (v.get 16)) c51),
      (savedLoad 48 (by decide)).trans hs3, (savedLoad 40 (by decide)).trans hs12,
      (savedLoad 32 (by decide)).trans hs13, (savedLoad 24 (by decide)).trans hs14,
      (savedLoad 16 (by decide)).trans hs15, (savedLoad 8 (by decide)).trans hs5,
      hr.of_frame hfOut, savedReturn, hretLow, hstack.of_frame hfOut, hroom, halign,
      hs0r.of_frame hfOut, (hfOut.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans hs0,
      hs1r.of_frame hfOut, (hfOut.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans hs1,
      hs2r.of_frame hfOut, (hfOut.memLoad_eq (slotOutside 0x201228 (by decide) (by decide))).trans hs2,
      hs3r.of_frame hfOut, (hfOut.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans hs3slot,
      hslotSep, trivial⟩
  have hexecc : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    change LIR.program.Exec (dialect code)
      ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ output
    rw [hcLabel]
    exact hexec
  have ha : continuation.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hguard, htag]
    rfl
  have hresume := CFGCall.exec_reaches_resume hexecc continuation [] ha
  have hstep : LIR.program.step (dialect code)
      ⟨⟨.l1013b0, args, mem⟩, []⟩ = .next ⟨callee, [continuation]⟩ := by
    have hblock : LIR.program.runBlock (dialect code) ⟨.l1013b0, args, mem⟩ =
        .call callee continuation := hcall
    rw [Program.step, hblock]
    rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans hresume, htarget,
    working, ?_, ?_, ?_, hargRead.of_frame hfFull, hfFull.memLoad_eq argOutside, hfFull, nextArgs ▸ ht⟩
  · rw [nextArgs, ho15]
    exact keptGPR 15 (by decide) h15
  · rw [nextArgs, ho5]
    change (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = _
    rw [hc5]
    change memLoad mem (args[4].get 64 + 480) 64 = _
    rw [hargEq]
    exact hframe.memLoad_eq argOutside
  · rw [nextStore]
    simpa only [adst] using hp

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
