import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Machine.LIR.Fn102520.Frame
import AesGcm.Proofs.Machine.LIR.Fn102980.Frame
import AesGcm.Proofs.Machine.Runtime.Preservation

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def entryMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp - 8) (args[5].get 64)
  let mem := memStore mem (sp - 16) (args[15].get 64)
  let mem := memStore mem (sp - 24) (args[14].get 64)
  let mem := memStore mem (sp - 32) (args[13].get 64)
  let mem := memStore mem (sp - 40) (args[12].get 64)
  memStore mem (sp - 48) (args[3].get 64)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem entry_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - 48) 48)
    (hr : Readable mem (args[9].get 64 + 16) 8)
    (length : BitVec 64)
    (hload : memLoad (entryMemory args mem) (args[9].get 64 + 16) 64 = length)
    (hlen : length.toNat ≤ 2^32)
    (haad : (args[8].get 64).toNat ≤ 2^32) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102980 else .l102520), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l1029c0 else .l102560) ∧
      next.store = entryMemory args mem ∧
      (next.arguments[3]'(by change 3 < 53; decide)).get 64 = args[7].get 64 ∧
      (next.arguments[4]'(by change 4 < 53; decide)).get 64 = args[4].get 64 - 200 ∧
      (next.arguments[12]'(by change 12 < 53; decide)).get 64 = length ∧
      (∀ r : Fin 53, r.val ∈ [1, 2, 5, 6, 8, 9, 13, 14, 15, 22, 39, 50, 51] →
        next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  have hshift : args[8].get 64 >>> 61 = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    change (args[8].get 64).toNat / 2^61 = 0
    omega
  have hsmall : length.toNat < 68719476704 := by omega
  simp only [entryMemory] at hload
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102980 else 0x102520) 56 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102520 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102980 x hx))).apart
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l102520, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102980, args, mem⟩ = _
      cfg_eval [hshift]
      refine_norm [hshift, hload]
      simp only [hsmall, not_true_eq_false, false_and, ite_false]
      runtime_guards transfer
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl <;> rfl)
      | runtime_finish [entryMemory, hload]

theorem entryMemory_frame (args : Values Value Reg.count) (mem : Ram)
    (hroom : 48 ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (entryMemory args mem) [span (args[4].get 64 - 48) 48] := by
  simp only [entryMemory]
  runtime_finish [span]

theorem entryMemory_saved (args : Values Value Reg.count) (mem : Ram) :
    memLoad (entryMemory args mem) (args[4].get 64 - 48) 64 = args[3].get 64 ∧
    memLoad (entryMemory args mem) (args[4].get 64 - 40) 64 = args[12].get 64 ∧
    memLoad (entryMemory args mem) (args[4].get 64 - 32) 64 = args[13].get 64 ∧
    memLoad (entryMemory args mem) (args[4].get 64 - 24) 64 = args[14].get 64 ∧
    memLoad (entryMemory args mem) (args[4].get 64 - 16) 64 = args[15].get 64 ∧
    memLoad (entryMemory args mem) (args[4].get 64 - 8) 64 = args[5].get 64 := by
  repeat' apply And.intro
  all_goals
    simp only [entryMemory]
    repeat first
      | rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
      | (rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (by
          apply RangeApart.of_diff
          simp only [sub_sub_sub_left]
          decide +kernel)])

set_option maxHeartbeats 800000 in
theorem entry (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (fr : Activation) (loc : LIR.lifted.Location)
    (hlabel : loc.label = (if use256 then .l102980 else .l102520))
    (hstore : loc.store = fr.original)
    (hentry : Atom.All code loc.arguments loc.store
      ((if use256 then LIR.Fn102980.frameInfo else LIR.Fn102520.frameInfo).entryAtoms fr))
    (hTypes : GPRsTyped loc.arguments)
    (length : BitVec 64) (hlen : length.toNat ≤ 2^32) (haad : fr.r8.toNat ≤ 2^32)
    (hr : Readable fr.original fr.r9 24)
    (hload : memLoad fr.original (fr.r9 + 16) 64 = length)
    (hsep : (callStack fr).Disjoint (span fr.r9 24)) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l1029c0 else .l102560) ∧
      Atom.All code next.arguments next.store
        (if use256 then LIR.Fn102980.frameAt .l1029c0 fr
          else LIR.Fn102520.frameAt .l102560 fr) ∧
      GPRsTyped next.arguments ∧ RamWriteFrame fr.original next.store [fr.region] ∧
      (next.arguments[12]'(by change 12 < 53; decide)).get 64 = length := by
  rcases loc with ⟨label, args, mem⟩
  change Values Value Reg.count at args
  dsimp only at hlabel hstore hentry hTypes ⊢
  subst label mem
  let window : Nat := if use256 then 0xb50 else 0x940
  let slotHigh : Nat := if use256 then 0x201d88 else 0x201b78
  have hentry' :
      args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
      args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
      args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
      args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
      args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧
      args[51] = ⟨16, fr.fcw⟩ ∧ Readable fr.original fr.rsp 8 ∧
      memLoad fr.original fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code fr.original (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable fr.original 0x201208 8 ∧ memLoad fr.original 0x201208 64 = 0x103f00 ∧
      Readable fr.original 0x201210 8 ∧ memLoad fr.original 0x201210 64 = 0x103880 ∧
      Readable fr.original 0x201228 8 ∧ memLoad fr.original 0x201228 64 = 0x103eb0 ∧
      Readable fr.original 0x201230 8 ∧ memLoad fr.original 0x201230 64 = 0x101230 ∧
      (slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hentry
  rcases hentry' with ⟨h4, h22, h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, h14, h15,
    h39, h50, h51, hretRead, hret, hretLow, hstack, hroom, halign,
    hslot0Read, hslot0, hslot1Read, hslot1, hslot2Read, hslot2, hslot3Read, hslot3,
    hslotSep, -⟩
  have h4get : args[4].get 64 = fr.rsp := by rw [h4]; rfl
  have h9get : args[9].get 64 = fr.r9 := by rw [h9]; rfl
  have hwindow : 48 ≤ window := by cases use256 <;> decide
  have hs48 : (fr.rsp - 48).toNat = fr.rsp.toNat - 48 := by
    rw [BitVec.toNat_sub_of_le (by change 48 ≤ fr.rsp.toNat; omega)]
    rfl
  have heframe : RamWriteFrame fr.original (entryMemory args fr.original)
      [span (fr.rsp - 48) 48] := by
    simpa only [h4get] using entryMemory_frame args fr.original (by rw [h4get]; omega)
  have hbounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.r9.toNat 24 (by omega) (by decide) hsep
  have hout : Outside [span (fr.rsp - 48) 48] fr.r9 24 := by
    refine ⟨by have := hr.low; omega, ?_⟩
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    simp only [span, hs48]
    omega
  have hload' : memLoad (entryMemory args fr.original) (args[9].get 64 + 16) 64 = length := by
    rw [h9get, heframe.memLoad_eq (outside_subregion (offset := 16) (count := 8) hout (by decide) (by decide)), hload]
  have hw48 : Writable code fr.original (args[4].get 64 - 48) 48 := by
    rw [h4get]
    apply hstack.of_offsets (addr_sub _ _) (addr_sub _ _)
    cases use256 <;> decide +kernel
  obtain ⟨next, hx, hl, hm, n3, n4, n12, keep, types⟩ :=
    entry_runBlock use256 code hcode args fr.original hw48
      (by rw [h9get]; exact hr.of_offsets (rfl : fr.r9 + 16 = fr.r9 + 16) (addr_self _) (by decide))
      length hload' hlen (by rw [h8]; exact haad)
  have nt := types hTypes
  have hf : RamWriteFrame fr.original next.store [fr.region] := by
    rw [hm]
    apply (RamWriteFrame.refl _ _).trans heframe
    intro r hin
    obtain rfl := List.mem_singleton.mp hin
    refine ⟨fr.region, by simp only [List.mem_singleton], ?_, ?_⟩
    all_goals simp only [Activation.region, span, hs48]; omega
  have saved := entryMemory_saved args fr.original
  rw [h4get, h3, h12, h13, h14, h15, h5] at saved
  change memLoad (entryMemory args fr.original) (fr.rsp - 48) 64 = fr.rbx ∧
    memLoad (entryMemory args fr.original) (fr.rsp - 40) 64 = fr.r12 ∧
    memLoad (entryMemory args fr.original) (fr.rsp - 32) 64 = fr.r13 ∧
    memLoad (entryMemory args fr.original) (fr.rsp - 24) 64 = fr.r14 ∧
    memLoad (entryMemory args fr.original) (fr.rsp - 16) 64 = fr.r15 ∧
    memLoad (entryMemory args fr.original) (fr.rsp - 8) 64 = fr.rbp at saved
  have saved' := saved
  rw [← hm] at saved'
  rcases saved' with ⟨s3, s12, s13, s14, s15, s5⟩
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
  have n4' : next.arguments[4]'(by change 4 < 53; decide) = ⟨64, fr.rsp - 200⟩ := by
    have hv := nt.value ⟨4, by decide⟩
    change next.arguments[4]'(by change 4 < 53; decide) =
      ⟨64, (next.arguments[4]'(by change 4 < 53; decide)).get 64⟩ at hv
    rw [hv, n4, h4get]
  have n3' : next.arguments[3]'(by change 3 < 53; decide) = ⟨64, fr.rdi⟩ := by
    have hv := nt.value ⟨3, by decide⟩
    change next.arguments[3]'(by change 3 < 53; decide) =
      ⟨64, (next.arguments[3]'(by change 3 < 53; decide)).get 64⟩ at hv
    rw [hv, n3, h7]
    rfl
  refine ⟨next, .single ?_, hl, ?_, nt, hf, n12⟩
  · exact congrArg (Transfer.next (dialect code) []) hx
  · have hpost :
        next.arguments[4]'(by change 4 < 53; decide) = ⟨64, fr.rsp - 200⟩ ∧
        next.arguments[22]'(by change 22 < 53; decide) = ⟨1, 0⟩ ∧
        next.arguments[1]'(by change 1 < 53; decide) = ⟨64, fr.rcx⟩ ∧
        next.arguments[2]'(by change 2 < 53; decide) = ⟨64, fr.rdx⟩ ∧
        next.arguments[3]'(by change 3 < 53; decide) = ⟨64, fr.rdi⟩ ∧
        next.arguments[5]'(by change 5 < 53; decide) = ⟨64, fr.rbp⟩ ∧
        next.arguments[6]'(by change 6 < 53; decide) = ⟨64, fr.rsi⟩ ∧
        next.arguments[8]'(by change 8 < 53; decide) = ⟨64, fr.r8⟩ ∧
        next.arguments[9]'(by change 9 < 53; decide) = ⟨64, fr.r9⟩ ∧
        next.arguments[13]'(by change 13 < 53; decide) = ⟨64, fr.r13⟩ ∧
        next.arguments[14]'(by change 14 < 53; decide) = ⟨64, fr.r14⟩ ∧
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
      exact ⟨n4', (keep 22 (by decide)).trans h22, (keep 1 (by decide)).trans h1,
        (keep 2 (by decide)).trans h2, n3', (keep 5 (by decide)).trans h5,
        (keep 6 (by decide)).trans h6, (keep 8 (by decide)).trans h8,
        (keep 9 (by decide)).trans h9, (keep 13 (by decide)).trans h13,
        (keep 14 (by decide)).trans h14, (keep 15 (by decide)).trans h15,
        (keep 39 (by decide)).trans h39, (keep 50 (by decide)).trans h50,
        (keep 51 (by decide)).trans h51, s3, s12, s13, s14, s15, s5,
        hretRead.of_frame hf, hret', hretLow, hstack.of_frame hf, hroom, halign,
        hslot0Read.of_frame hf, (slotEq _ (by decide) (by decide)).trans hslot0,
        hslot1Read.of_frame hf, (slotEq _ (by decide) (by decide)).trans hslot1,
        hslot2Read.of_frame hf, (slotEq _ (by decide) (by decide)).trans hslot2,
        hslot3Read.of_frame hf, (slotEq _ (by decide) (by decide)).trans hslot3,
        hslotSep, trivial⟩
    cases use256 <;> exact hpost

end AesGcm.Proofs.Machine.Core.Encrypt
