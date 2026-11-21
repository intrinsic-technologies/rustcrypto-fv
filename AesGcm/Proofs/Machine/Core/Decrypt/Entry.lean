import AesGcm.Proofs.Machine.Core.Decrypt.Prefix
import AesGcm.Proofs.Machine.Runtime.EntryFacts
import AesGcm.Proofs.Machine.Runtime.SavedRegisters
import AesGcm.Proofs.Machine.Runtime.Preservation
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102720.Frame

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 800000 in
theorem entry (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = (if use256 then .l102720 else .l1022c0))
    (hstore : loc.store = fr.original)
    (hentry : Atom.All code loc.arguments loc.store
      ((if use256 then LIR.Fn102720.frameInfo else LIR.Fn1022c0.frameInfo).entryAtoms fr))
    (hTypes : GPRsTyped loc.arguments)
    (length : BitVec 64) (hlen : length.toNat ≤ 2^32) (haad : fr.rcx.toNat ≤ 2^32)
    (hr : Readable fr.original fr.r8 24)
    (hload : memLoad fr.original (fr.r8 + 16) 64 = length)
    (hsep : (callStack fr).Disjoint (span fr.r8 24)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l102759 else .l1022f9) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102720.frameAt .l102759 fr
          else LIR.Fn1022c0.frameAt .l1022f9 fr) ∧
      GPRsTyped next.arguments ∧ RamWriteFrame fr.original next.store [fr.region] ∧
      (next.arguments[14]'(by change 14 < 53; decide)).get 64 = length ∧
      next.arguments[3]'(by change 3 < 53; decide) = ⟨64, 0xfffffffe0⟩ := by
  rcases loc with ⟨label, args, mem⟩
  change Values Value Reg.count at args
  dsimp only at hlabel hstore hentry hTypes ⊢
  subst label mem
  let window : Nat := if use256 then 0xb60 else 0x950
  let slotHigh : Nat := if use256 then 0x201d98 else 0x201b88
  have f := entryFacts_of_atoms hentry
  have hroom : fr.low.toNat + window ≤ fr.rsp.toNat := by
    cases use256 <;> exact f.room
  have hstack : Writable code fr.original (fr.rsp - BitVec.ofNat 64 window) window := by
    cases use256 <;> exact f.window (by decide)
  have hslotSep : slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208 := by
    cases use256 <;> exact f.callSlotsApart (by decide)
  have hretRead := f.slot
  have hret := f.ret
  have hretLow := f.retLow
  have halign := f.align
  have h4 := f.rsp
  have h8 := f.r8
  have h1 := f.rcx
  have h3 := f.rbx
  have h12 := f.r12
  have h13 := f.r13
  have h14 := f.r14
  have h15 := f.r15
  have h5 := f.rbp
  have h4get : args[4].get 64 = fr.rsp := by rw [h4]; rfl
  have h8get : args[8].get 64 = fr.r8 := by rw [h8]; rfl
  have hwindow : 48 ≤ window := by cases use256 <;> decide
  have hs48 : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := by
    rw [BitVec.toNat_sub_of_le (by change 48 ≤ fr.rsp.toNat; omega)]
    rfl
  have heframe : RamWriteFrame fr.original (entryMemory args fr.original)
      [span (fr.rsp - 48) 48] := by
    simpa only [h4get] using entryMemory_frame args fr.original (by rw [h4get]; omega)
  have hbounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.r8.toNat 24 (by omega) (by decide) hsep
  have hout : Outside [span (fr.rsp - 48) 48] fr.r8 24 := by
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hs48]
    omega
  have hload' : memLoad (entryMemory args fr.original) (args[8].get 64 + 16) 64 = length := by
    rw [h8get, heframe.memLoad_eq (outside_subregion (offset := 16) (count := 8) hout (by decide) (by decide)), hload]
  have hw48 : Writable code fr.original (args[4].get 64 - 48) 48 := by
    rw [h4get]
    apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  obtain ⟨next, hx, hl, hm, n0, n1, n3, n4, n5, n14, keep, types⟩ :=
    entry_runBlock use256 code hcode args fr.original hw48
      (by rw [h8get]; exact hr.of_offsets (rfl : fr.r8 + 16 = fr.r8 + 16) (addr_self _) (by decide))
      length hload' hlen (by rw [h1]; exact haad)
  have nt := types hTypes
  have hf : RamWriteFrame fr.original next.store [fr.region] := by
    rw [hm]
    apply (RamWriteFrame.refl _ _).trans heframe
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨fr.region, by simp only [List.mem_singleton], ?_, ?_⟩
    all_goals simp only [Activation.region, span, hs48]; omega
  have saved := saveSixRegisters_loads args fr.original
  change memLoad (entryMemory args fr.original) (args[4].get 64 - 8) 64 = args[5].get 64 ∧
    memLoad (entryMemory args fr.original) (args[4].get 64 - 16) 64 = args[15].get 64 ∧
    memLoad (entryMemory args fr.original) (args[4].get 64 - 24) 64 = args[14].get 64 ∧
    memLoad (entryMemory args fr.original) (args[4].get 64 - 32) 64 = args[13].get 64 ∧
    memLoad (entryMemory args fr.original) (args[4].get 64 - 40) 64 = args[12].get 64 ∧
    memLoad (entryMemory args fr.original) (args[4].get 64 - 48) 64 = args[3].get 64 ∧
    memLoad (entryMemory args fr.original) (args[4].get 64) 64 =
      memLoad fr.original (args[4].get 64) 64 at saved
  rw [h4get, f.rbx, f.r12, f.r13, f.r14, f.r15, f.rbp] at saved
  rw [← hm] at saved
  obtain ⟨s5, s15, s14, s13, s12, s3, _⟩ := saved
  have hret' : memLoad next.store fr.rsp 64 = fr.ret := by
    rw [hm, heframe.memLoad_eq]
    · exact hret
    · refine ⟨by have := hretRead.low; omega, ?_⟩
      intro r hin
      obtain rfl := List.mem_singleton.mp hin
      simp only [span, hs48]
      omega
  have slotEq (address : BitVec 64) (hlo : 0x201208 ≤ address.toNat)
      (hhi : address.toNat + 8 ≤ 0x201238) :
      memLoad next.store address 64 = memLoad fr.original address 64 := by
    rw [hm]
    apply heframe.memLoad_eq
    refine ⟨by omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    have : 0x201238 + 48 ≤ slotHigh := by cases use256 <;> decide
    simp only [span, hs48]
    omega
  have n4' : next.arguments[4]'(by change 4 < 53; decide) = ⟨64, fr.rsp - 216⟩ := by
    rw [n4, h4get]
  have n5' : next.arguments[5]'(by change 5 < 53; decide) = ⟨64, fr.rcx⟩ := by
    rw [n5, f.rcx]
    rfl
  refine ⟨next, .single ?_, hl, ?_, nt, hf, ?_, n3⟩
  · exact congrArg (Transfer.next (dialect code) []) hx
  · have hpost :
        next.arguments[4]'(by change 4 < 53; decide) = ⟨64, fr.rsp - 216⟩ ∧
        next.arguments[22]'(by change 22 < 53; decide) = ⟨1, 0⟩ ∧
        next.arguments[2]'(by change 2 < 53; decide) = ⟨64, fr.rdx⟩ ∧
        next.arguments[5]'(by change 5 < 53; decide) = ⟨64, fr.rcx⟩ ∧
        next.arguments[6]'(by change 6 < 53; decide) = ⟨64, fr.rsi⟩ ∧
        next.arguments[7]'(by change 7 < 53; decide) = ⟨64, fr.rdi⟩ ∧
        next.arguments[8]'(by change 8 < 53; decide) = ⟨64, fr.r8⟩ ∧
        next.arguments[9]'(by change 9 < 53; decide) = ⟨64, fr.r9⟩ ∧
        next.arguments[12]'(by change 12 < 53; decide) = ⟨64, fr.r12⟩ ∧
        next.arguments[13]'(by change 13 < 53; decide) = ⟨64, fr.r13⟩ ∧
        next.arguments[15]'(by change 15 < 53; decide) = ⟨64, fr.r15⟩ ∧
        next.arguments[39]'(by change 39 < 53; decide) = ⟨32, fr.mxcsr⟩ ∧
        next.arguments[50]'(by change 50 < 53; decide) = ⟨16, fr.ftw⟩ ∧
        next.arguments[51]'(by change 51 < 53; decide) = ⟨16, fr.fcw⟩ ∧
        memLoad next.store (fr.rsp - 48) 64 = fr.rbx ∧
        memLoad next.store (fr.rsp - 40) 64 = fr.r12 ∧
        memLoad next.store (fr.rsp - 32) 64 = fr.r13 ∧
        memLoad next.store (fr.rsp - 24) 64 = fr.r14 ∧
        memLoad next.store (fr.rsp - 16) 64 = fr.r15 ∧
        memLoad next.store (fr.rsp - 8) 64 = fr.rbp ∧
        Readable next.store fr.rsp 8 ∧ memLoad next.store fr.rsp 64 = fr.ret ∧
        fr.ret.toNat < 2^32 ∧
        Writable code next.store (fr.rsp - BitVec.ofNat 64 window) window ∧
        fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
        Readable next.store 0x201208 8 ∧ memLoad next.store 0x201208 64 = 0x103f00 ∧
        Readable next.store 0x201210 8 ∧ memLoad next.store 0x201210 64 = 0x103880 ∧
        Readable next.store 0x201228 8 ∧ memLoad next.store 0x201228 64 = 0x103eb0 ∧
        Readable next.store 0x201230 8 ∧ memLoad next.store 0x201230 64 = 0x101230 ∧
        (slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
      have slots (c : BitVec 64 × BitVec 64)
          (hc : c ∈ [(0x201208, 0x103f00), (0x201210, 0x103880),
            (0x201228, 0x103eb0), (0x201230, 0x101230)]) :
          Readable fr.original c.1 8 ∧ memLoad fr.original c.1 64 = c.2 := by
        apply f.callSlots
        cases use256 <;> exact hc
      obtain ⟨hs0r, hs0⟩ := slots (0x201208, 0x103f00) (by decide)
      obtain ⟨hs1r, hs1⟩ := slots (0x201210, 0x103880) (by decide)
      obtain ⟨hs2r, hs2⟩ := slots (0x201228, 0x103eb0) (by decide)
      obtain ⟨hs3r, hs3⟩ := slots (0x201230, 0x101230) (by decide)
      exact ⟨n4', (keep 22 (by decide)).trans f.df,
        (keep 2 (by decide)).trans f.rdx, n5', (keep 6 (by decide)).trans f.rsi,
        (keep 7 (by decide)).trans f.rdi, (keep 8 (by decide)).trans f.r8,
        (keep 9 (by decide)).trans f.r9, (keep 12 (by decide)).trans f.r12,
        (keep 13 (by decide)).trans f.r13, (keep 15 (by decide)).trans f.r15,
        (keep 39 (by decide)).trans f.mxcsr, (keep 50 (by decide)).trans f.ftw,
        (keep 51 (by decide)).trans f.fcw, s3, s12, s13, s14, s15, s5,
        hretRead.of_frame hf, hret', hretLow, hstack.of_frame hf, hroom, halign,
        hs0r.of_frame hf, (slotEq _ (by decide) (by decide)).trans hs0,
        hs1r.of_frame hf, (slotEq _ (by decide) (by decide)).trans hs1,
        hs2r.of_frame hf, (slotEq _ (by decide) (by decide)).trans hs2,
        hs3r.of_frame hf, (slotEq _ (by decide) (by decide)).trans hs3,
        hslotSep, trivial⟩
    cases use256 <;> exact hpost
  · rw [n14]
    rfl

end AesGcm.Proofs.Machine.Core.Decrypt
