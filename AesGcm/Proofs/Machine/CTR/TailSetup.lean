import AesGcm.Proofs.Machine.CTR.Outer.Invariant
import AesGcm.Proofs.Machine.GHASHUpdate.Counts
import AesGcm.Proofs.Machine.Runtime.StackGeometry
import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem tail_clear (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp source remainder : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hStack : Writable code mem (sp + 8) 240)
    (hsource : memLoad mem (sp + 240) 64 = source)
    (hrem : memLoad mem (sp + 232) 64 = remainder) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l109509 else .l10805f), args, mem⟩ = .jump next ∧
      next.label = (if remainder = 0 then (if use256 then .l109961 else .l1084c1)
        else (if use256 then .l10956a else .l1080c0)) ∧
      next.arguments[5]'(by change 5 < 53; decide) = ⟨64, source⟩ ∧
      next.arguments[12]'(by change 12 < 53; decide) = ⟨64, remainder⟩ ∧
      (∀ r : Fin 53, r.val ∈ [2,4,9,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store [span (sp + 8) 64] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hRange {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x109509 else 0x10805f) 97 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10805f x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l109509 x hx))).apart
  by_cases hz : remainder = 0
  all_goals cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
    runtime_context [hsp, hsource, hrem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l10805f, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l109509, args, mem⟩ = _
      cfg_eval [LIR.program, hsp]
      runtime_guards branch
      runtime_finish [hz]
      try rfl
    · simp only [hz, ↓reduceIte]
      try rfl
    · runtime_finish []
    · runtime_finish []
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 4096 in
theorem tail_setup (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp source destination remainder count schedule : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hsource : args[5].get 64 = source) (hdestination : args[2].get 64 = destination)
    (hremainder : args[12].get 64 = remainder)
    (hStack : Writable code mem (sp + 216) 128)
    (hcount : memLoad mem (sp + 320) 64 = count)
    (hschedule : memLoad mem (sp + 336) 64 = schedule) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l10956a else .l1080c0), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l1095b0 else .l108110) ∧
      next.arguments[5]'(by change 5 < 53; decide) = ⟨64, source + ((count &&& 0xffffffffffffffc) <<< 4)⟩ ∧
      next.arguments[3]'(by change 3 < 53; decide) = ⟨64, schedule⟩ ∧
      next.arguments[12]'(by change 12 < 53; decide) = ⟨64, (remainder.setWidth 32 <<< 4).setWidth 64⟩ ∧
      next.arguments[13]'(by change 13 < 53; decide) = ⟨64, 0⟩ ∧
      next.arguments[14]'(by change 14 < 53; decide) = ⟨64, sp + 152⟩ ∧
      next.arguments[15]'(by change 15 < 53; decide) = ⟨64, sp + 256⟩ ∧
      next.store = memStore mem (sp + 216) (destination + ((count &&& 0xffffffffffffffc) <<< 4)) ∧
      (∀ r : Fin 53, r.val ∈ [4,9,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store [span (sp + 216) 8] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hRange {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x10956a else 0x1080c0) (if use256 then 70 else 80) := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1080c0 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10956a x hx))).apart
  cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
    runtime_context [hsp, hsource, hdestination, hremainder, hcount, hschedule]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l1080c0, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l10956a, args, mem⟩ = _
      cfg_eval [LIR.program, hsp, hsource, hdestination, hremainder]
      runtime_guards transfer
      rfl
    · rfl
    · runtime_finish []
    · runtime_finish []
    · rfl
    · rfl
    · rfl
    · rfl
    · simp only [hcount]
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

set_option maxHeartbeats 800000 in
theorem tail_keystream_setup (use256 : Bool) (code : CodeMap) (fr : Activation)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (input : ByteArray)
    (count : Nat) (hsize : input.size = 16 * count) (hn : count % 4 ≠ 0)
    (schedule counter src dst : BitVec 64) (exit : LIR.lifted.Location)
    (h : OuterExit use256 code fr key input count schedule counter src dst exit) :
    let sp := outerStackPointer fr use256
    let offset := BitVec.ofNat 64 (input.size - input.size % 64)
    ∃ loc : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨exit, []⟩ ⟨loc, []⟩ ∧
      loc.label = (if use256 then .l1095b0 else .l108110) ∧ GPRsTyped loc.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4,9,22,39,50,51] → loc.arguments[r] = exit.arguments[r]) ∧
      loc.arguments[5]'(by change 5 < 53; decide) = ⟨64, src + offset⟩ ∧
      loc.arguments[3]'(by change 3 < 53; decide) = ⟨64, schedule⟩ ∧
      loc.arguments[12]'(by change 12 < 53; decide) = ⟨64, BitVec.ofNat 64 (16 * (count % 4))⟩ ∧
      loc.arguments[13]'(by change 13 < 53; decide) = ⟨64, 0⟩ ∧
      loc.arguments[14]'(by change 14 < 53; decide) = ⟨64, sp+152⟩ ∧
      loc.arguments[15]'(by change 15 < 53; decide) = ⟨64, sp+256⟩ ∧
      memLoad loc.store (sp+216) 64 = dst + offset ∧
      RamWriteFrame exit.store loc.store [span (sp+8) 64, span (sp+216) 8] := by
  let sp := outerStackPointer fr use256
  let win : Nat := if use256 then 2688 else 2160
  let lower := fr.rsp - (if use256 then 2688 else 2160)
  let offset := BitVec.ofNat 64 (input.size - input.size % 64)
  have f : Atom.All code exit.arguments exit.store
      (if use256 then LIR.Fn1084e0.frameAt .l109509 fr else LIR.Fn107050.frameAt .l10805f fr) := by
    have shape := h.frame
    cases use256 <;> simpa only [cryptFrameAt, h.label, Bool.false_eq_true, ↓reduceIte] using shape
  have fs : Writable code exit.store lower win ∧ fr.low.toNat + win ≤ fr.rsp.toNat ∧ Readable exit.store fr.rsp 8 := by
    cases use256 <;> obtain ⟨_,_,_,_,_,_,_,_,_,_,_,r,_,_,w,room,_⟩ := f <;> exact ⟨w,room,r⟩
  obtain ⟨stack,room,rsp⟩ := fs
  have low := rsp.low
  have len := h.toOuterState.source_read.low
  have sn : sp.toNat = fr.rsp.toNat - (if use256 then 2312 else 1800) := by
    cases use256 <;> apply stack_sub_toNat fr room <;> decide
  have ln : lower.toNat = fr.rsp.toNat - win := by
    cases use256 <;> exact stack_sub_toNat fr room (Nat.le_refl _)
  have bounds : (if use256 then 2312 else 1800) ≤ win ∧ 344 ≤ (if use256 then 2312 else 1800) := by
    cases use256 <;> decide
  have addN (k : Nat) (hk : k ≤ 344) : (sp + BitVec.ofNat 64 k).toNat = sp.toNat+k := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2^64 by omega),
      Nat.mod_eq_of_lt (show sp.toNat+k < 2^64 by omega)]
  have sub (k n : Nat) (hk : k+n ≤ 344) : Writable code exit.store (sp+BitVec.ofNat 64 k) n := by
    apply stack.sub <;> rw [addN k (by omega), ln] <;> omega
  have rem : memLoad exit.store (sp+232) 64 = BitVec.ofNat 64 (count % 4) :=
    atomsAll_mem (atom := .mem (sp+232) 64 _) h.outer
      (by simp only [sp, outerAtoms, List.mem_cons, true_or, or_true])
  have cnt : memLoad exit.store (sp+320) 64 = BitVec.ofNat 64 count :=
    atomsAll_mem (atom := .mem (sp+320) 64 _) h.outer
      (by simp only [sp, outerAtoms, List.mem_cons, true_or, or_true])
  have nr : BitVec.ofNat 64 (count % 4) ≠ 0 := by
    intro hz
    have he := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show count % 4 < 2^64 by omega)] at he
    exact hn he
  obtain ⟨mid,clear,ml,m5,m12,keep0,typed0,frame0⟩ := tail_clear use256 code hcode
    _ _ sp src _ h.typed (congrArg (Value.get 64) h.toOuterState.stackPointer)
    (sub 8 240 (by decide)) h.toOuterState.source_word rem
  rw [ite_eq_right nr] at ml
  have saved (k : Nat) (hk : 72 ≤ k) (kn : k ≤ 336) :
      memLoad mid.store (sp+BitVec.ofNat 64 k) 64 = memLoad exit.store (sp+BitVec.ofNat 64 k) 64 := by
    apply frame0.memLoad_eq
    refine ⟨?_, ?_⟩
    · rw [addN k (by omega)]; omega
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      change _ ≤ (sp+8).toNat ∨ (sp+8).toNat+64 ≤ _
      rw [addN k (by omega), show (sp+8).toNat = sp.toNat+8 from addN 8 (by decide)]
      right; omega
  obtain ⟨loc,setup,hl,r5,r3,r12,r13,r14,r15,store,keep1,typed1,frame1⟩ :=
    tail_setup use256 code hcode _ _ sp src dst _ _ schedule typed0
      (congrArg (Value.get 64) ((keep0 4 (by decide)).trans h.toOuterState.stackPointer))
      (congrArg (Value.get 64) m5)
      (congrArg (Value.get 64) ((keep0 2 (by decide)).trans h.toOuterState.destination))
      (congrArg (Value.get 64) m12) ((sub 216 128 (by decide)).of_frame frame0)
      ((saved 320 (by decide) (by decide)).trans cnt)
      ((saved 336 (by decide) (by decide)).trans h.toOuterState.schedule_word)
  have jump {a b : LIR.lifted.Location} {l : LIR.Label} (lab : a.label = l)
      (run : LIR.program.runBlock (dialect code) ⟨l, a.arguments, a.store⟩ = .jump b) :
      (LIR.program.sem (dialect code)).Reaches ⟨a,[]⟩ ⟨b,[]⟩ := by
    cases a with | mk label args mem =>
      dsimp only at lab
      subst l
      apply Semantics.Reaches.single
      exact congrArg (fun t => t.next (dialect code) []) run
  have mask : ((BitVec.ofNat 64 count &&& 0xffffffffffffffc) <<< 4) = offset := by
    apply BitVec.eq_of_toNat_eq
    have cb : count < 2^64 := by omega
    have d : 16 * (BitVec.ofNat 64 count &&& 0xffffffffffffffc).toNat ≤ 2^32 := by
      rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cb]
      change 16 * (count &&& 0xffffffffffffffc) ≤ 2^32
      have := Nat.and_le_left (n := count) (m := 0xffffffffffffffc)
      omega
    rw [GHASHUpdate.shift_count_toNat _ d, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt cb]
    change 16 * (count &&& ((2^58-1)*2^2)) = (input.size-input.size%64)%2^64
    rw [GHASHUpdate.nat_and_shifted_mask]
    simp only [Nat.reducePow, Nat.mod_eq_of_lt (show count/4 < 2^58 by omega),
      Nat.mod_eq_of_lt (show input.size-input.size%64 < 2^64 by omega)]
    omega
  have remLen : (((BitVec.ofNat 64 (count % 4)).setWidth 32 <<< 4).setWidth 64) =
      BitVec.ofNat 64 (16 * (count % 4)) := by
    rcases (show count % 4 = 1 ∨ count % 4 = 2 ∨ count % 4 = 3 by omega) with hr | hr | hr <;> rw [hr] <;> decide
  change loc.arguments[12]'(by change 12 < 53; decide) =
    ⟨64, (((BitVec.ofNat 64 (count%4)).setWidth 32 <<< 4).setWidth 64)⟩ at r12
  refine ⟨loc, (jump h.label clear).trans (jump ml setup), hl, typed1, ?_,
    by simpa only [mask] using r5, r3, by simpa only [remLen] using r12, r13,r14,r15, ?_, ?_⟩
  · intro r hr
    exact (keep1 r hr).trans (keep0 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      omega))
  · rw [store,mask,memLoad_memStore_same _ _ _ (by decide) (by decide)]
  · apply ((RamWriteFrame.refl _ _).trans frame0 ?_).trans frame1
    all_goals intro r hr
    all_goals obtain rfl := List.mem_singleton.mp hr
    all_goals exact ⟨_, by simp [sp], Nat.le_refl _, Nat.le_refl _⟩

end AesGcm.Proofs.Machine.CTR
