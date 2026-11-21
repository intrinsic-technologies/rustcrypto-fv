import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Blocks
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Aes256.Call
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Preservation
import AesGcm.Proofs.Machine.Runtime.Root.Memory
import AesGcm.Proofs.AES16.KeySchedule

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Aes256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem entryMemory_frame (args : Values Value Reg.count) (mem : Ram)
    (hroom : 608 ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (entryMemory true args mem) [span (args[4].get 64 - 608) 608] := by
  simp only [entryMemory, savedMemory, saveSixRegisters, frameBytes,
    ↓reduceIte, Nat.reduceAdd]
  runtime_finish [span]

set_option maxHeartbeats 800000 in
theorem keySchedule_reaches (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 32)
    (fr : Activation) (args : Values Value Reg.count)
    (hentry : Atom.All code args fr.original
      (LIR.Aes256gcmEncryptInPlace.frameInfo.entryAtoms fr))
    (hTypes : GPRsTyped args)
    (hread : Readable fr.original fr.rdi 32)
    (hkey : (span fr.rdi 32).HasBytes
      fr.original ⟨key.toArray⟩)
    (hsep : (callStack fr).Disjoint (span fr.rdi 32)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
      ⟨⟨.l101660, args, fr.original⟩, []⟩ ⟨next, []⟩ ∧
      next.label = .l101690 ∧
      Atom.All code next.arguments next.store
        (LIR.Aes256gcmEncryptInPlace.frameAt .l101690 fr) ∧
      next.arguments[5]'(by change 5 < 53; decide) =
        ⟨64, fr.rsp - 600 + 32⟩ ∧
      GPRsTyped next.arguments ∧ RamWriteFrame fr.original next.store [fr.region] ∧
      AES16.ScheduleIn .aes256 key
        (fr.rsp - 600 + 32) next.store := by
  let window : Nat := 0xdb0
  let keyWindow : Nat := 0x260
  let depth : Nat := 608
  let size : Nat := 16 * (Standards.NIST.AES.Variant.aes256.Nr + 1)
  have hd : depth ≤ window := by decide
  have hks : depth + keyWindow ≤ window := by decide
  have he :
      args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
      args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
      args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
      args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
      args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
      fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable fr.original 0x201208 8 ∧ memLoad fr.original 0x201208 64 = 0x103f00 ∧
      Readable fr.original 0x201210 8 ∧ memLoad fr.original 0x201210 64 = 0x103880 ∧
      Readable fr.original 0x201228 8 ∧ memLoad fr.original 0x201228 64 = 0x103eb0 ∧
      Readable fr.original 0x201230 8 ∧ memLoad fr.original 0x201230 64 = 0x101230 ∧
      (0x201238 + window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := hentry
  rcases he with ⟨h4, h22, h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, h14, h15,
    h39, h50, h51, hr, hret, hretLow, hstack, hroom, halign,
    hs0r, hs0, hs1r, hs1, hs2r, hs2, hs3r, hs3, hslotSep, _⟩
  have hsp : args[4].get 64 = fr.rsp := by rw [h4]; rfl
  have hkeyPtr : args[7].get 64 = fr.rdi := by rw [h7]; rfl
  have hsub (n : Nat) (hn : n ≤ window) :
      (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    have hn64 : n < 2^64 := by have := fr.rsp.isLt; omega
    have hle : BitVec.ofNat 64 n ≤ fr.rsp := by
      change n % 2^64 ≤ fr.rsp.toNat
      omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  let lower := fr.rsp - BitVec.ofNat 64 window
  let childSP := fr.rsp - BitVec.ofNat 64 depth
  let schedule := fr.rsp - 600 + 32
  have hlower : lower.toNat = fr.rsp.toNat - window := hsub window (Nat.le_refl _)
  have hchild : childSP.toNat = fr.rsp.toNat - depth := hsub depth hd
  have hschedEq : schedule = fr.rsp - 568 := by
    dsimp only [schedule]
    bv_omega
  have hsched : schedule.toNat = fr.rsp.toNat - 568 := by
    rw [hschedEq]
    exact hsub _ (by decide)
  have hentryWrite : Writable code fr.original childSP depth :=
    hstack.sub (by rw [hchild, hsub window (Nat.le_refl _)]; omega)
      (by rw [hchild, hsub window (Nat.le_refl _)]; omega)
  obtain ⟨callee, continuation, hcall, hcLabel, htarget, hguard, hmem,
      hc4, hc7, hc6, hc3, hc5, hc12, hc13, hc14, hc15, hc22, hc39, hc50, hc51, hcTypes⟩ :=
    entry_schedule_call true code hcode args fr.original (by rw [hsp]; exact hentryWrite)
  have hfEntry : RamWriteFrame fr.original callee.store [span childSP depth] := by
    rw [hmem]
    have hf := entryMemory_frame args fr.original (by rw [hsp]; omega)
    rwa [hsp] at hf
  have entryWithin : RegionsWithin [span childSP depth] [span lower window] := by
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨span lower window, by simp, ?_, ?_⟩ <;>
      simp only [span, hlower, hchild] <;> omega
  have hfWindow : RamWriteFrame fr.original callee.store [span lower window] :=
    (RamWriteFrame.refl _ _).trans hfEntry entryWithin
  have hsrcBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rdi.toNat 32 (by omega)
    (by decide) hsep
  have sourceOutside : Outside [span lower window] fr.rdi 32 := by
    refine ⟨by have := hread.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hlower]
    omega
  have hkeyAfter := hasBytes_of_frame hfWindow hkey sourceOutside.1
    (outside_disjoint_span sourceOutside)
  have hbytes : ∀ i : Fin 32,
      callee.store[fr.rdi + BitVec.ofNat 64 i.val]? = some key[i.val] := by
    intro i
    have hi : i.val < (⟨key.toArray⟩ : ByteArray).size := by
      change i.val < key.toArray.size
      rw [key.size_toArray]
      exact i.isLt
    have hh := hkeyAfter.2 ⟨i.val, hi⟩
    simpa only [span, ofNat_toNat_add, ByteArray.getElem_eq_getElem_data,
      Vector.getElem_toArray] using hh
  have c4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = childSP := by
    rw [hc4, hsp] <;> rfl
  have c7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = schedule := by
    rw [hc7, hsp, hschedEq] <;> rfl
  have c6 : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = fr.rdi := by
    rw [hc6, hkeyPtr] <;> rfl
  let af := activationOfValues callee.store callee.arguments
    0x101690 lower
  have asp : af.rsp = childSP := c4
  have alow : af.low = lower := rfl
  have adst : af.rdi = schedule := c7
  have asrc : af.rsi = fr.rdi := c6
  have childWrite : Writable code callee.store
      ((callee.arguments[4]'(by change 4 < 53; decide)).get 64 - BitVec.ofNat 64 keyWindow)
      keyWindow := by
    rw [c4]
    have heq : childSP - BitVec.ofNat 64 keyWindow =
        fr.rsp - BitVec.ofNat 64 (depth + keyWindow) := by
      simp only [childSP, BitVec.ofNat_add]
      bv_omega
    rw [heq]
    exact (hstack.of_frame hfWindow).sub
      (by rw [hsub _ hks, hsub window (Nat.le_refl _)]; omega)
      (by rw [hsub _ hks, hsub window (Nat.le_refl _)]; omega)
  have destWrite : Writable code callee.store schedule size := by
    apply (hstack.of_frame hfWindow).sub
    · rw [hsched, hsub window (Nat.le_refl _)]
      have hh : 568 ≤ window := by decide
      omega
    · rw [hsched, hsub window (Nat.le_refl _)]
      have hh : size ≤ 568 := by decide
      omega
  have slotOutside (addr : BitVec 64) (hlo : 0x201208 ≤ addr.toNat)
      (hhi : addr.toNat + 8 ≤ 0x201238) : Outside [span lower window] addr 8 := by
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hlower]
    omega
  have hslots : Atom.All code callee.arguments callee.store
      (LIR.Fn1057c0.frameInfo.callSlotAtoms
        LIR.Fn1057c0.frameInfo.callSlots af) := by
    have s0 := (hfWindow.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans hs0
    have s1 := (hfWindow.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans hs1
    have s2 := (hfWindow.memLoad_eq (slotOutside 0x201228 (by decide) (by decide))).trans hs2
    have s3 := (hfWindow.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans hs3
    have apart : 0x201238 + keyWindow ≤ childSP.toNat ∨ childSP.toNat ≤ 0x201208 := by
      rw [hchild]
      omega
    refine ⟨hs0r.of_frame hfWindow, s0, hs1r.of_frame hfWindow, s1,
      hs2r.of_frame hfWindow, s2, hs3r.of_frame hfWindow, s3, ?_, trivial⟩
    change _ ≤ af.rsp.toNat ∨ af.rsp.toNat ≤ 0x201208
    rw [asp]
    exact apart
  have hpre : Readable callee.store af.rsi 32 ∧
      (∀ i : Fin 32,
        callee.store[af.rsi + BitVec.ofNat 64 i.val]? = some key[i.val]) ∧
      Writable code callee.store af.rdi size ∧
      (callStack af).Disjoint (span af.rsi 32) ∧
      (callStack af).Disjoint (span af.rdi size) ∧
      (span af.rdi size).Disjoint (span af.rsi 32) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [asrc]
      exact hread.of_frame hfWindow
    · rw [asrc]
      exact hbytes
    · rw [adst]
      exact destWrite
    · intro x hx hy
      apply hsep x ?_ (by simpa only [asrc] using hy)
      simp only [MemoryRegion.Contains, callStack, asp, alow, hlower, hchild] at hx ⊢
      omega
    · intro x hx hy
      simp only [MemoryRegion.Contains, callStack, span, asp, alow, adst,
        hlower, hchild, hsched] at hx hy
      omega
    · intro x hx hy
      apply hsep x ?_ (by simpa only [asrc] using hy)
      simp only [MemoryRegion.Contains, callStack, span, adst, hsched] at hx ⊢
      have hh : size ≤ 568 := by decide
      have hh' : 600 ≤ window := by decide
      omega
  have c39 : (callee.arguments[39]'(by change 39 < 53; decide)) = ⟨32, fr.mxcsr⟩ := hc39.trans h39
  have c50 : (callee.arguments[50]'(by change 50 < 53; decide)) = ⟨16, fr.ftw⟩ := hc50.trans h50
  have c51 : (callee.arguments[51]'(by change 51 < 53; decide)) = ⟨16, fr.fcw⟩ := hc51.trans h51
  have hkw : LIR.Fn1057c0.frameInfo.window = keyWindow := rfl
  obtain ⟨output, hexec, htag, hdone, ht, hf, hp⟩ :=
    callContract_exec_values LIR.lifted code .l1057c0
      LIR.Fn1057c0.frameInfo
      (fun fr ↦ [span fr.rdi size]) _ _
      (AES16.initializer_callContract true code hcode key)
      callee.store callee.arguments 0x101690 lower
      (hcTypes hTypes) (by rw [c39]; rfl) (by rw [c50]; rfl) (by rw [c51]; rfl)
      (hc22.trans h22)
      (by rw [c4]; exact (hentryWrite.readable.of_frame hfWindow).sub (Nat.le_refl _) (by
        have hh : 8 ≤ depth := by decide
        omega))
      (by
        rw [c4, hmem]
        simp only [entryMemory, hsp]
        exact memLoad_memStore_same _ _ _ (by decide) (by decide))
      (by decide)
      (by intro _; rw [hkw]; exact childWrite)
      (by rw [hkw, c4, hlower, hchild]; omega)
      (by rw [c4, hchild]; omega)
      hslots hpre

  change Atom.All code output.values output.store
    (LIR.Fn1057c0.frameInfo.doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi size] at hf
  change AES16.ScheduleIn .aes256 key af.rdi output.store at hp
  have hdone' : output.values[4] = ⟨64, af.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
      output.values[3] = ⟨64, af.rbx⟩ ∧ output.values[5] = ⟨64, af.rbp⟩ ∧
      output.values[12] = ⟨64, af.r12⟩ ∧ output.values[13] = ⟨64, af.r13⟩ ∧
      output.values[14] = ⟨64, af.r14⟩ ∧ output.values[15] = ⟨64, af.r15⟩ ∧
      output.values[39] = ⟨32, af.mxcsr⟩ ∧ output.values[50] = ⟨16, af.ftw⟩ ∧
      output.values[51] = ⟨16, af.fcw⟩ ∧ True := hdone
  rcases hdone' with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, _⟩
  have childWithin : RegionsWithin [af.region, span af.rdi size] [span lower window] := by
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨span lower window, by simp, ?_, ?_⟩ <;>
        simp only [Activation.region, span, alow, asp, hlower, hchild] <;> omega
    · refine ⟨span lower window, by simp, ?_, ?_⟩ <;>
        simp only [span, adst, hlower, hsched]
      · have hh : 600 ≤ window := by decide
        omega
      · have hh : size ≤ 568 := by decide
        omega
  have hfOut : RamWriteFrame fr.original output.store [span lower window] :=
    hfWindow.trans hf childWithin
  have fullWithin : RegionsWithin [span lower window] [fr.region] := by
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨fr.region, by simp, ?_, ?_⟩ <;>
      simp only [span, Activation.region, hlower] <;> omega
  have hfFull : RamWriteFrame fr.original output.store [fr.region] :=
    (RamWriteFrame.refl _ _).trans hfOut fullWithin
  have hs48 : (fr.rsp - (48 : BitVec 64)).toNat = fr.rsp.toNat - 48 :=
    hsub 48 (by decide)
  have protectSaved : Outside [af.region, span af.rdi size] (fr.rsp - 48) 56 := by
    refine ⟨by rw [hs48]; have := hr.low; omega, ?_⟩
    intro r hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · right
      simp only [Activation.region, alow, asp, hlower, hchild, hs48]
      have hh : 48 ≤ depth := by decide
      omega
    · right
      simp only [span, adst, hsched, hs48]
      have hh : size + 48 ≤ 568 := by decide
      omega
  have hfSaved : RamWriteFrame (entryMemory true args fr.original) output.store
      [af.region, span af.rdi size] := by rw [← hmem]; exact hf
  have callApart : RangeApart
      (args[4].get 64 - 608) 8
      (args[4].get 64 - 48) 56 := by
    apply RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _)
    decide +kernel
  obtain ⟨saved5, saved15, saved14, saved13, saved12, saved3, savedReturn, _⟩ :=
    saveSixRegisters_call_loads args fr.original
      (args[4].get 64 - 608)
      0x101690 callApart
  have hload (k : Nat) (hk : k ≤ 48) :
      memLoad output.store (fr.rsp - BitVec.ofNat 64 k) 64 =
      memLoad (entryMemory true args fr.original) (fr.rsp - BitVec.ofNat 64 k) 64 := by
    apply hfSaved.memLoad_eq
    have hout := outside_subregion (offset := 48 - k) (count := 8)
      protectSaved (by omega) (by omega)
    have he : fr.rsp - (48 : BitVec 64) + BitVec.ofNat 64 (48 - k) =
        fr.rsp - BitVec.ofNat 64 k := by
      rw [← BitVec.ofNat_sub_ofNat_of_le 48 k (by omega) (by omega)]
      bv_omega
    rwa [he] at hout
  have entryStore :
      memStore (saveSixRegisters args fr.original)
        (args[4].get 64 - 608) (0x101690 : BitVec 64) =
      entryMemory true args fr.original := by
    simp only [entryMemory, savedMemory, frameBytes, ↓reduceIte, Nat.reduceAdd] <;> rfl
  rw [entryStore, hsp, h3] at saved3
  rw [entryStore, hsp, h12] at saved12
  rw [entryStore, hsp, h13] at saved13
  rw [entryStore, hsp, h14] at saved14
  rw [entryStore, hsp, h15] at saved15
  rw [entryStore, hsp, h5] at saved5
  rw [entryStore, hsp, hret] at savedReturn
  have load3 := (hload 48 (by decide)).trans saved3
  have load12 := (hload 40 (by decide)).trans saved12
  have load13 := (hload 32 (by decide)).trans saved13
  have load14 := (hload 24 (by decide)).trans saved14
  have load15 := (hload 16 (by decide)).trans saved15
  have load5 := (hload 8 (by decide)).trans saved5
  have loadReturn := hload 0 (by decide)
  simp only [BitVec.sub_zero] at loadReturn
  have returnOut := loadReturn.trans savedReturn
  have abx : af.rbx = fr.r9 := by
    change (callee.arguments[3]'(by change 3 < 53; decide)).get 64 = fr.r9
    rw [hc3, h9]
    rfl
  have abp : af.rbp = schedule := by
    change (callee.arguments[5]'(by change 5 < 53; decide)).get 64 = schedule
    rw [hc5, hsp, hschedEq] <;> rfl
  have a12 : af.r12 = fr.rdx := by
    change (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = fr.rdx
    rw [hc12, h2]
    rfl
  have a13 : af.r13 = fr.rsi := by
    change (callee.arguments[13]'(by change 13 < 53; decide)).get 64 = fr.rsi
    rw [hc13, h6]
    rfl
  have a14 : af.r14 = fr.r8 := by
    change (callee.arguments[14]'(by change 14 < 53; decide)).get 64 = fr.r8
    rw [hc14, h8]
    rfl
  have a15 : af.r15 = fr.rcx := by
    change (callee.arguments[15]'(by change 15 < 53; decide)).get 64 = fr.rcx
    rw [hc15, h1]
    rfl
  have a39 : af.mxcsr = fr.mxcsr := congrArg (fun v ↦ v.get 32) c39
  have a50 : af.ftw = fr.ftw := congrArg (fun v ↦ v.get 16) c50
  have a51 : af.fcw = fr.fcw := congrArg (fun v ↦ v.get 16) c51
  have outSP : output.values[4] = ⟨64, fr.rsp - 600⟩ := by
    rw [ho4, asp]
    congr 1
    dsimp only [childSP, depth]
    bv_omega
  have slot0 := (hfOut.memLoad_eq (slotOutside 0x201208 (by decide) (by decide))).trans hs0
  have slot1 := (hfOut.memLoad_eq (slotOutside 0x201210 (by decide) (by decide))).trans hs1
  have slot2 := (hfOut.memLoad_eq (slotOutside 0x201228 (by decide) (by decide))).trans hs2
  have slot3 := (hfOut.memLoad_eq (slotOutside 0x201230 (by decide) (by decide))).trans hs3
  let next := continuation.resume output
  have nextArgs : next.arguments = output.values := CFGCall.resume_arguments continuation output
  have nextStore : next.store = output.store := rfl
  have nextLabel : next.label = .l101690 := htarget
  have working : Atom.All code next.arguments next.store
      (LIR.Aes256gcmEncryptInPlace.frameAt .l101690 fr) := by
    rw [nextArgs, nextStore]
    exact ⟨outSP, ho22, ho3.trans (congrArg (Value.mk 64) abx),
      ho12.trans (congrArg (Value.mk 64) a12), ho13.trans (congrArg (Value.mk 64) a13),
      ho14.trans (congrArg (Value.mk 64) a14), ho15.trans (congrArg (Value.mk 64) a15),
      ho39.trans (congrArg (Value.mk 32) a39), ho50.trans (congrArg (Value.mk 16) a50),
      ho51.trans (congrArg (Value.mk 16) a51), load3, load12, load13,
      load14, load15, load5, hr.of_frame hfFull, returnOut, hretLow,
      hstack.of_frame hfFull, hroom, halign, hs0r.of_frame hfFull, slot0,
      hs1r.of_frame hfFull, slot1, hs2r.of_frame hfFull, slot2,
      hs3r.of_frame hfFull, slot3, hslotSep, trivial⟩
  have hexecc : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    change LIR.program.Exec (dialect code)
      ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ output
    rw [hcLabel]
    exact hexec
  have ha : continuation.Accepts (dialect code) output.tag = true := by
    simp only [StackFrame.Accepts, hguard, htag] <;> rfl
  have hresume := CFGCall.exec_reaches_resume hexecc continuation [] ha
  have hstep : LIR.program.step (dialect code)
      ⟨⟨.l101660, args, fr.original⟩, []⟩ =
      .next ⟨callee, [continuation]⟩ := by
    change LIR.program.runBlock (dialect code) ⟨.l101660, args, fr.original⟩ =
      .call callee continuation at hcall
    change Transfer.next (dialect code) []
      (LIR.program.runBlock (dialect code) ⟨.l101660, args, fr.original⟩) = _
    rw [hcall] <;> rfl
  refine ⟨next, (Semantics.Reaches.single hstep).trans hresume,
    nextLabel, working, ?_, ?_, hfFull, ?_⟩
  · rw [nextArgs, ho5, abp]
  · simpa only [nextArgs] using ht
  · simpa only [nextStore, adst] using hp

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Aes256
