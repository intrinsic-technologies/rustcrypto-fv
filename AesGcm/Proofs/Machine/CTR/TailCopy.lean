import X86Proofs.Program.ReadWrite.RepString
import AesGcm.Proofs.Machine.LIR
import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.Runtime.TagCopy

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem tail_copy (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp index length : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hindex : args[13].get 64 = index) (hlength : args[12].get 64 = length)
    (hRead : Readable mem (sp + 152) 104)
    (hWrite : Writable code mem (sp + index + 8) 16) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1095ed else .l10814d), args, mem⟩ = .jump next ∧
      next.label = (if length = index + 16 then
        (if use256 then .l109618 else .l108178) else
        (if use256 then .l1095b0 else .l108110)) ∧
      next.arguments[13]'(by change 13 < 53; decide) = ⟨64, index + 16⟩ ∧
      next.arguments[9]'(by change 9 < 53; decide) = ⟨64, memLoad mem (sp + 248) 64⟩ ∧
      next.store = copyTagWords mem (sp + index + 8) (sp + 152) ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store [span (sp + index + 8) 16] := by
  have hReadLow := hRead.low
  have hWriteRead := hWrite.readable
  have hWriteLow := hWriteRead.low
  have hRange {m : Ram} {a : BitVec 64} {n : Nat} (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x1095ed else 0x10814d) 43 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l10814d x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1095ed x hx))).apart
  by_cases he : length = index + 16
  all_goals cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
    runtime_context [hsp, hindex, hlength]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l10814d, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l1095ed, args, mem⟩ = _
      cfg_eval [LIR.program, hsp, hindex, hlength]
      runtime_guards branch
      runtime_finish [he]
      try rfl
    · simp only [he, ↓reduceIte]
      try rfl
    · rfl
    · rfl
    · simp only [copyTagWords, BitVec.add_assoc, BitVec.reduceAdd]
      rfl
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]

private def tailXorEntry (use256 : Bool) (j : Nat) : LIR.Label :=
  if use256 then
    if j = 0 then .l109618 else if j = 1 then .l109739 else .l109867
  else
    if j = 0 then .l108178 else if j = 1 then .l108299 else .l1083c7

private def tailXorExit (use256 : Bool) : LIR.Label :=
  if use256 then .l109961 else .l1084c1

private def tailSourceReg (j : Nat) : Fin 53 := if j = 0 then 5 else 2

private theorem tailLoad32 (mem : Ram) (a : BitVec 64) :
    memLoad mem a 32 = (memLoad mem a 64).setWidth 32 := by
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  have h := extractLsb'_memLoad mem a (n := 64) 0 32 (by decide) (by decide) (by decide)
  change _ = memLoad mem (a + 0) 32 at h
  exact (congrArg (fun b => memLoad mem b 32) (BitVec.add_zero a).symm).trans h.symm

set_option maxHeartbeats 3800000 in
set_option maxRecDepth 4096 in
private theorem tailXorStep (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp src dst : BitVec 64)
    (j n : Nat) (hj : j < 3) (hn : j < n ∧ n < 4)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hsrc : (args[tailSourceReg j]'(tailSourceReg j).isLt).get 64 = src)
    (hdst : memLoad mem (sp + 216) 64 = dst)
    (hrem : memLoad mem (sp + 232) 64 = BitVec.ofNat 64 n)
    (hDstReg : j = 2 → args[1].get 64 = dst)
    (hstack : Writable code mem sp 240)
    (hread : Readable mem src (16 * (j + 1)))
    (hwrite : Writable code mem dst (16 * (j + 1)))
    (hs : sp.toNat + 240 ≤ src.toNat ∨ src.toNat + 16 * (j + 1) ≤ sp.toNat)
    (hd : sp.toNat + 240 ≤ dst.toNat ∨ dst.toNat + 16 * (j + 1) ≤ sp.toNat) :
    ∃ next,
      LIR.program.runBlock (dialect code) ⟨tailXorEntry use256 j, args, mem⟩ = .jump next ∧
      next.label = (if n = j + 1 then tailXorExit use256 else tailXorEntry use256 (j + 1)) ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (j < 2 → (next.arguments[2]'(by change 2 < 53; decide)).get 64 = src) ∧
      (j = 1 → (next.arguments[1]'(by change 1 < 53; decide)).get 64 = dst) ∧
      RamWriteFrame mem next.store [span (sp + 120) 32, span (dst + BitVec.ofNat 64 (16 * j)) 16] ∧
      ∀ i < 16, memLoad next.store (dst + BitVec.ofNat 64 (16 * j + i)) 8 =
        memLoad mem (src + BitVec.ofNat 64 (16 * j + i)) 8 ^^^
          memLoad mem (sp + 8 + BitVec.ofNat 64 (16 * j + i)) 8 := by
  have hStackRead := hstack.readable
  have hWriteRead := hwrite.readable
  have hStackLow := hStackRead.low
  have hWriteLow := hWriteRead.low
  have hReadLow := hread.low
  have hCmp : (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n := by
    have hn' := hn.2
    have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
    rcases hcases with rfl | rfl | rfl <;> rfl
  have hRange {m : Ram} {a : BitVec 64} {k : Nat} (h : Writable code m a k) :
      RangeApart a k
        (if use256 then if j = 0 then 0x109618 else if j = 1 then 0x109739 else 0x109867
          else if j = 0 then 0x108178 else if j = 1 then 0x108299 else 0x1083c7)
        (if j = 0 then 289 else if j = 1 then 302 else 250) := by
    have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hj' with rfl | rfl | rfl <;> cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l108178 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l109618 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l108299 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l109739 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l1083c7 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l109867 x hx))).apart
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 := by omega
  have hbranch1 : (BitVec.ofNat 32 n = 1) ↔ n = 1 := by
    rcases hcases with rfl | rfl | rfl <;> decide
  have hbranch2 : (BitVec.ofNat 32 n = 2) ↔ n = 2 := by
    rcases hcases with rfl | rfl | rfl <;> decide
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  by_cases hstop : n = j + 1
  all_goals rcases hj' with rfl | rfl | rfl <;> cases use256
  all_goals try (exfalso; omega)
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.one_ne_zero, Nat.reduceEqDiff,
      tailXorEntry, tailXorExit, tailSourceReg] at hhelperApart hsrc ⊢
    first
    | change args[5].get 64 = src at hsrc
    | change args[2].get 64 = src at hsrc
    have hsrcRead : Readable mem _ _ := hread
    rw [← hsrc] at hsrcRead
    try
      have hDst := hDstReg rfl
      have hdstWrite : Writable code mem _ _ := hwrite
      rw [← hDst] at hdstWrite
      have := hdstWrite.readable
      runtime_context [hDst]
    simp only [Nat.reduceAdd] at hstop
    runtime_context [hsp, hsrc, hdst, hrem]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l108178, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l109618, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l108299, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l109739, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l1083c7, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l109867, args, mem⟩ = _
      cfg_eval [LIR.program, hsp, hsrc]
      runtime_guards branch
      runtime_local_memory_norm [tailLoad32, hCmp, hbranch1, hbranch2, hstop,
        setWidth_mergeGPR8, Nat.reduceAdd]
      try rfl
    · first | rfl | (simp only [hstop, ↓reduceIte, Nat.reduceAdd] <;> rfl)
    · runtime_typed
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl <;> rfl
    · intro hj'
      first | omega | (change _ = src; first | rfl | exact hsrc)
    · intro hj'
      first | (exfalso; omega) | runtime_finish [hdst]
    · runtime_finish [span, Nat.reduceAdd]
    · intro i hi
      have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
          i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
      rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals runtime_finish [setWidth_mergeGPR8, BitVec.xor_comm, Nat.reduceAdd, Nat.reduceMul]
      all_goals try rfl

private theorem tailOutside (sp dst addr : BitVec 64) (len width : Nat)
    (hb : addr.toNat + width ≤ 2 ^ 64)
    (hs : addr.toNat + width ≤ (sp + 120).toNat ∨ (sp + 120).toNat + 32 ≤ addr.toNat)
    (hd : addr.toNat + width ≤ dst.toNat ∨ dst.toNat + len ≤ addr.toNat) :
    Outside [span (sp + 120) 32, span dst len] addr width := by
  refine ⟨hb, ?_⟩
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hs
  · exact hd

private theorem tailWithin (sp dst : BitVec 64) (start len total : Nat)
    (hlow : dst.toNat + total ≤ 2 ^ 32) (hbound : start + len ≤ total) :
    RegionsWithin [span (sp + 120) 32, span (dst + BitVec.ofNat 64 start) len]
      [span (sp + 120) 32, span dst total] := by
  intro region hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
  · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_, ?_⟩ <;>
      simp only [span, toNat_add_ofNat dst start (by omega)] <;> omega

theorem tail_xor (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (loc : LIR.lifted.Location) (sp src dst : BitVec 64) (n : Nat) (hn : 0 < n ∧ n < 4)
    (hlab : loc.label = (if use256 then .l109618 else .l108178))
    (ht : GPRsTyped loc.arguments) (hsp : (loc.arguments[4]'(by change 4 < 53; decide)).get 64 = sp)
    (hsrc : (loc.arguments[5]'(by change 5 < 53; decide)).get 64 = src) (hdst : memLoad loc.store (sp+216) 64 = dst)
    (hrem : memLoad loc.store (sp+232) 64 = BitVec.ofNat 64 n)
    (hstack : Writable code loc.store sp 240) (hr : Readable loc.store src (16*n))
    (hw : Writable code loc.store dst (16*n))
    (hs : (span sp 240).Disjoint (span src (16*n)))
    (hd : (span sp 240).Disjoint (span dst (16*n)))
    (hsd : src = dst ∨ (span src (16*n)).Disjoint (span dst (16*n))) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      next.label = (if use256 then .l109961 else .l1084c1) ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → next.arguments[r] = loc.arguments[r]) ∧
      RamWriteFrame loc.store next.store [span (sp+120) 32, span dst (16*n)] ∧
      ∀ i < 16*n, next.store[dst+BitVec.ofNat 64 i]? = some
        (memByte loc.store (src+BitVec.ofNat 64 i) ^^^ memByte loc.store (sp+8+BitVec.ofNat 64 i)) := by
  have hStackLow := hstack.readable.low
  have hSrcLow := hr.low
  have hDstLow := hw.readable.low
  have hStackSrc := disjoint_bounds sp.toNat 240 src.toNat (16*n) (by omega) (by omega) hs
  have hStackDst := disjoint_bounds sp.toNat 240 dst.toNat (16*n) (by omega) (by omega) hd
  have hSp120 : (sp + 120).toNat = sp.toNat + 120 := toNat_add_ofNat sp 120 (by omega)
  have hprefix (j : Nat) (hj : j ≤ n) :
      ∃ mid : LIR.lifted.Location,
        (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨mid, []⟩ ∧
        mid.label = (if j = n then tailXorExit use256 else tailXorEntry use256 j) ∧
        GPRsTyped mid.arguments ∧
        (∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → mid.arguments[r] = loc.arguments[r]) ∧
        (j < n → (mid.arguments[tailSourceReg j]'(tailSourceReg j).isLt).get 64 = src) ∧
        (j = 2 → (mid.arguments[1]'(by change 1 < 53; decide)).get 64 = dst) ∧
        RamWriteFrame loc.store mid.store [span (sp + 120) 32, span dst (16*j)] ∧
        ∀ i < 16*j, memLoad mid.store (dst + BitVec.ofNat 64 i) 8 =
          memLoad loc.store (src + BitVec.ofNat 64 i) 8 ^^^
            memLoad loc.store (sp + 8 + BitVec.ofNat 64 i) 8 := by
    induction j with
    | zero =>
      refine ⟨loc, .refl _, ?_, ht, fun _ _ ↦ rfl, fun _ ↦ hsrc,
        fun h ↦ by omega, RamWriteFrame.refl _ _, fun i hi ↦ by omega⟩
      cases use256 <;> simpa only [Nat.ne_of_lt hn.1, ↓reduceIte,
        tailXorEntry, Bool.false_eq_true] using hlab
    | succ j ih =>
      have hjn : j < n := by omega
      obtain ⟨mid, hreach, hlabel, htypes, hkeep, hsource, hdstReg, hframe, hbytes⟩ :=
        ih (by omega)
      have hentry : mid.label = tailXorEntry use256 j := by
        simpa only [Nat.ne_of_lt hjn, ↓reduceIte] using hlabel
      have hmidSp : (mid.arguments[4]'(by change 4 < 53; decide)).get 64 = sp := by
        exact (congrArg (Value.get 64) (hkeep 4 (by decide))).trans hsp
      have hspSlot (k : Nat) (hk : 152 ≤ k ∧ k + 8 ≤ 240) :
          memLoad mid.store (sp + BitVec.ofNat 64 k) 64 =
            memLoad loc.store (sp + BitVec.ofNat 64 k) 64 := by
        apply hframe.memLoad_eq
        apply tailOutside
        all_goals rw [toNat_add_ofNat sp k (by omega)]
        · omega
        · exact Or.inr (by rw [hSp120]; omega)
        · rcases hStackDst with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
      obtain ⟨next, hstep, hnext, hnextTypes, hnextKeep, hnextSrc, hnextDst, hnextFrame, hnextBytes⟩ :=
        tailXorStep use256 code hcode mid.arguments mid.store sp src dst j n (by omega) ⟨hjn, hn.2⟩
          htypes hmidSp (hsource hjn)
          ((hspSlot 216 (by decide)).trans hdst) ((hspSlot 232 (by decide)).trans hrem) hdstReg
          (hstack.of_frame hframe)
          ((hr.of_frame hframe).sub (Nat.le_refl _) (by omega))
          ((hw.of_frame hframe).sub (Nat.le_refl _) (by omega))
          (hStackSrc.imp_right (by omega)) (hStackDst.imp_right (by omega))
      have hstep' : (LIR.program.sem (dialect code)).Step ⟨mid, []⟩ ⟨next, []⟩ := by
        change LIR.program.step (dialect code) ⟨mid, []⟩ = .next ⟨next, []⟩
        cases mid with
        | mk label args mem =>
          change label = tailXorEntry use256 j at hentry
          subst label
          exact congrArg (fun t => t.next (dialect code) []) hstep
      have hframe' : RamWriteFrame loc.store next.store
          [span (sp + 120) 32, span dst (16 * (j + 1))] := by
        have hprior : RamWriteFrame loc.store mid.store
            [span (sp + 120) 32, span dst (16 * (j + 1))] :=
          (RamWriteFrame.refl _ _).trans hframe (by
            have hf := tailWithin sp dst 0 (16 * j) (16 * (j + 1)) (by omega) (by omega)
            change RegionsWithin [span (sp + 120) 32, span (dst + 0) (16 * j)] _ at hf
            exact (congrArg (fun d => RegionsWithin
              [span (sp + 120) 32, span d (16 * j)] _) (BitVec.add_zero dst)).mp hf)
        exact hprior.trans hnextFrame
          (tailWithin sp dst (16 * j) 16 (16 * (j + 1)) (by omega) (by omega))
      refine ⟨next, hreach.tail hstep', ?_, hnextTypes,
        fun r h ↦ (hnextKeep r h).trans (hkeep r h), ?_, ?_, hframe', ?_⟩
      · exact hnext.trans (ite_cond_congr (propext eq_comm))
      · intro hjn'
        simp only [tailSourceReg, show j + 1 ≠ 0 by omega, ↓reduceIte]
        exact hnextSrc (by omega)
      · intro htwo
        exact hnextDst (by omega)
      · intro i hi
        by_cases hprev : i < 16 * j
        · rw [hnextFrame.memLoad_eq (k := 8) (show Outside _ _ 1 from ?_), hbytes i hprev]
          have hAddDst := toNat_add_ofNat dst i (by omega)
          have hAddNext := toNat_add_ofNat dst (16 * j) (by omega)
          apply tailOutside
          all_goals rw [hAddDst]
          · omega
          · rw [hSp120]
            rcases hStackDst with h | h
            · exact Or.inr (by omega)
            · exact Or.inl (by omega)
          · rw [hAddNext]
            exact Or.inl (by omega)
        · have hi' : 16*j + (i - 16*j) = i := by omega
          have hvalue := hnextBytes (i - 16*j) (by omega)
          rw [hi'] at hvalue
          rw [hvalue]
          congr 1
          · apply hframe.memLoad_eq
            apply tailOutside
            all_goals rw [toNat_add_ofNat src i (by omega)]
            · omega
            · rw [hSp120]
              rcases hStackSrc with h | h
              · exact Or.inr (by omega)
              · exact Or.inl (by omega)
            · rcases hsd with he | hApart
              · rw [he]
                exact Or.inr (by omega)
              · rcases disjoint_bounds src.toNat (16*n) dst.toNat (16*n) (by omega) (by omega) hApart with h | h
                · exact Or.inl (by omega)
                · exact Or.inr (by omega)
          · apply hframe.memLoad_eq
            rw [BitVec.add_assoc]
            change Outside _ (sp + (BitVec.ofNat 64 8 + BitVec.ofNat 64 i)) _
            rw [← BitVec.ofNat_add]
            apply tailOutside
            all_goals rw [toNat_add_ofNat sp (8 + i) (by omega)]
            · omega
            · rw [hSp120]
              exact Or.inl (by omega)
            · rcases hStackDst with h | h
              · exact Or.inl (by omega)
              · exact Or.inr (by omega)
  obtain ⟨next, hreach, hlabel, htypes, hkeep, _, _, hframe, hbytes⟩ := hprefix n (Nat.le_refl n)
  refine ⟨next, hreach, ?_, htypes, hkeep, hframe, ?_⟩
  · exact hlabel.trans (ite_eq_left rfl)
  · intro i hi
    have hpresent := (hw.readable.of_frame hframe).present i hi
    have hbyte := hbytes i hi
    cases hread : next.store[dst + BitVec.ofNat 64 i]? with
    | none => rw [hread] at hpresent; cases hpresent
    | some b =>
      simp only [memLoad_8, ← UInt8.toBitVec_xor] at hbyte
      change (next.store[dst + BitVec.ofNat 64 i]?.getD 0).toBitVec = _ at hbyte
      rw [hread, Option.getD_some] at hbyte
      exact congrArg some (UInt8.toBitVec_inj.mp hbyte)

end AesGcm.Proofs.Machine.CTR
