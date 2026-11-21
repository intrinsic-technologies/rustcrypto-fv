import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Fn104370.Frame
import AesGcm.Proofs.Machine.LIR.Fn1057c0.Frame

namespace AesGcm.Proofs.Machine.AES16.KeySchedule

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def savedMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let mem := memStore mem (sp - 8) (args[5].get 64)
  let mem := memStore mem (sp - 16) (args[15].get 64)
  let mem := memStore mem (sp - 24) (args[14].get 64)
  let mem := memStore mem (sp - 32) (args[13].get 64)
  let mem := memStore mem (sp - 40) (args[12].get 64)
  let mem := memStore mem (sp - 48) (args[3].get 64)
  let mem := memStore mem (sp - (if use256 then 0x38 else 0x48)) (args[7].get 64)
  mem

def entryMemory (use256 : Bool) (args : Values Value Reg.count) (mem : Ram) : Ram :=
  memStore (savedMemory use256 args mem)
    (args[4].get 64 - (if use256 then 0x170 else 0x110))
    (if use256 then (0x1057f1 : BitVec 64) else 0x1043a4)

set_option maxHeartbeats 1600000 in
theorem entry_memset_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hstack : Writable code mem (args[4].get 64 - (if use256 then 0x260 else 0x200))
      (if use256 then 0x260 else 0x200))
    (hroom : (if use256 then 0x260 else 0x200) ≤ (args[4].get 64).toNat)
    (hslotRead : Readable mem 0x201228 8)
    (hslot : memLoad mem 0x201228 64 = 0x103eb0)
    (hsep : (if use256 then 0x201498 else 0x201438) ≤ (args[4].get 64).toNat ∨
      (args[4].get 64).toNat ≤ 0x201208) :
    ∃ callee continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1057c0 else .l104370), args, mem⟩ = .call callee continuation ∧
      callee.label = .l103eb0 ∧
      continuation.target = (if use256 then .l1057f1 else .l1043a4) ∧
      continuation.guard = some ⟨64, if use256 then 0x1057f1 else 0x1043a4⟩ ∧
      callee.store = entryMemory use256 args mem ∧
      (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = args[4].get 64 - (if use256 then 0x170 else 0x110) ∧
      (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = args[4].get 64 - (if use256 then 0x15c else 0x100) ∧
      (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = 0 ∧
      (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = (if use256 then 0xf0 else 0xb0) ∧
      (callee.arguments[12]'(by change 12 < 53; decide)).get 64 = args[6].get 64 ∧
      (callee.arguments[14]'(by change 14 < 53; decide)).get 64 =
        args[4].get 64 - (if use256 then 0x15c else 0x100) ∧
      (callee.arguments[15]'(by change 15 < 53; decide)).get 64 =
        (if use256 then args[15].get 64 else 0) ∧
      callee.arguments[3]'(by change 3 < 53; decide) = args[3] ∧
      callee.arguments[5]'(by change 5 < 53; decide) = args[5] ∧
      callee.arguments[13]'(by change 13 < 53; decide) = args[13] ∧
      callee.arguments[22]'(by change 22 < 53; decide) = args[22] ∧
      callee.arguments[39]'(by change 39 < 53; decide) = args[39] ∧
      callee.arguments[50]'(by change 50 < 53; decide) = args[50] ∧
      callee.arguments[51]'(by change 51 < 53; decide) = args[51] ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  have hstackRead := hstack.readable
  have hstackLow := hstackRead.low
  have hpres {m : Ram} {v : BitVec 64} (n : Nat) (hn : 8 ≤ n)
      (hnw : n ≤ if use256 then 0x260 else 0x200) :
      memLoad (memStore m (args[4].get 64 - BitVec.ofNat 64 n) v) 0x201228 64 =
        memLoad m 0x201228 64 := by
    have hn64 : n < 2^64 := by
      cases use256 <;> simp_all only [Bool.false_eq_true, ↓reduceIte] <;> omega
    have hns : n ≤ (args[4].get 64).toNat := by omega
    have ht : (args[4].get 64 - BitVec.ofNat 64 n).toNat = (args[4].get 64).toNat - n := by
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
      have hrew : 2^64 - n + (args[4].get 64).toNat =
          2^64 + ((args[4].get 64).toNat - n) := by omega
      rw [hrew, Nat.add_mod]
      have hs : (args[4].get 64).toNat - n < 2^64 := by
        have := (args[4].get 64).isLt
        omega
      simp only [Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hs]
    apply memLoad_memStore_of_rangeApart
    apply RangeApart.of_toNat
    · rw [ht]
      have := (args[4].get 64).isLt
      omega
    · decide
    · rw [ht]
      cases use256 <;>
        simp_all only [Bool.false_eq_true, ↓reduceIte, BitVec.reduceToNat, Nat.reduceDiv] <;> omega
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hstack hstackRead hstackLow hroom hsep ⊢
  all_goals have hp8 {m : Ram} {v : BitVec 64} := @hpres m v 8 (by decide) (by decide)
  all_goals have hp16 {m : Ram} {v : BitVec 64} := @hpres m v 16 (by decide) (by decide)
  all_goals have hp24 {m : Ram} {v : BitVec 64} := @hpres m v 24 (by decide) (by decide)
  all_goals have hp32 {m : Ram} {v : BitVec 64} := @hpres m v 32 (by decide) (by decide)
  all_goals have hp40 {m : Ram} {v : BitVec 64} := @hpres m v 40 (by decide) (by decide)
  all_goals have hp48 {m : Ram} {v : BitVec 64} := @hpres m v 48 (by decide) (by decide)
  all_goals have hp56 {m : Ram} {v : BitVec 64} := @hpres m v 56 (by decide) (by decide)
  all_goals have hp72 {m : Ram} {v : BitVec 64} := @hpres m v 72 (by decide) (by decide)
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x104370 52 := by
      have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l104370 x hx))
      have hl : LIR.bytes_l104370.length = 52 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    have hslotSaved : memLoad (savedMemory false args mem) 0x201228 64 = 0x103eb0 := by
      simp only [savedMemory, Bool.false_eq_true, ↓reduceIte]
      refine hp72.trans ?_
      exact hp48.trans
        (hp40.trans (hp32.trans (hp24.trans (hp16.trans (hp8.trans hslot)))))
    simp only [savedMemory, Bool.false_eq_true, ↓reduceIte] at hslotSaved
    runtime_context [hslot, hslotSaved]
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l104370, args, mem⟩ = _
      cfg_eval [hslotSaved, hslot]
      refine_norm [hslotSaved, hslot]
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish [entryMemory, savedMemory]
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x1057c0 49 := by
      have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1057c0 x hx))
      have hl : LIR.bytes_l1057c0.length = 49 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    have hslotSaved : memLoad (savedMemory true args mem) 0x201228 64 = 0x103eb0 := by
      simp only [savedMemory, ↓reduceIte]
      refine hp56.trans ?_
      exact hp48.trans
        (hp40.trans (hp32.trans (hp24.trans (hp16.trans (hp8.trans hslot)))))
    simp only [savedMemory, ↓reduceIte] at hslotSaved
    runtime_context [hslot, hslotSaved]
    refine ⟨?_, ?_, ?exec256, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec256 =>
      change LIR.program.runBlock (dialect code) ⟨.l1057c0, args, mem⟩ = _
      cfg_eval [hslotSaved, hslot]
      refine_norm [hslotSaved, hslot]
      runtime_guards call
      rfl
    all_goals first | rfl | (intro hTypes; runtime_typed) | runtime_finish [entryMemory, savedMemory]

theorem entryMemory_frame (use256 : Bool) (args : Values Value Reg.count) (mem : Ram)
    (hroom : (if use256 then 0x260 else 0x200) ≤ (args[4].get 64).toNat) :
    RamWriteFrame mem (entryMemory use256 args mem)
      [span (args[4].get 64 - (if use256 then 0x260 else 0x200))
        (if use256 then 0x260 else 0x200)] := by
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hroom ⊢
  all_goals simp only [entryMemory, savedMemory, Bool.false_eq_true, ↓reduceIte]
  all_goals runtime_finish [span]


theorem initializer_entry_atoms (use256 : Bool) (code : CodeMap)
    (fr : Activation) (args : Values Value Reg.count)
    (hats : Atom.All code args fr.original
      ((if use256 then LIR.Fn1057c0.frameInfo else LIR.Fn104370.frameInfo).entryAtoms fr)) :
args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[1] = ⟨64, fr.rcx⟩ ∧ args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧
      args[5] = ⟨64, fr.rbp⟩ ∧ args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧
      args[8] = ⟨64, fr.r8⟩ ∧ args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧
      args[13] = ⟨64, fr.r13⟩ ∧ args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
      fr.ret.toNat < 2 ^ 32 ∧
      Writable code fr.original (fr.rsp - (if use256 then 608 else 512))
        (if use256 then 608 else 512) ∧
      fr.low.toNat + (if use256 then 608 else 512) ≤ fr.rsp.toNat ∧
      fr.rsp.toNat % 16 = 8 ∧
      Readable fr.original 0x201208 8 ∧ memLoad fr.original 0x201208 64 = 0x103f00 ∧
      Readable fr.original 0x201210 8 ∧ memLoad fr.original 0x201210 64 = 0x103880 ∧
      Readable fr.original 0x201228 8 ∧ memLoad fr.original 0x201228 64 = 0x103eb0 ∧
      Readable fr.original 0x201230 8 ∧ memLoad fr.original 0x201230 64 = 0x101230 ∧
      ((if use256 then 0x201498 else 0x201438) ≤ fr.rsp.toNat ∨
        fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hats

end AesGcm.Proofs.Machine.AES16.KeySchedule
