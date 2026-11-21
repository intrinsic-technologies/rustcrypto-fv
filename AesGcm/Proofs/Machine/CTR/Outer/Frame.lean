import AesGcm.Proofs.Machine.CTR.Outer.Invariant
import AesGcm.Proofs.Machine.Runtime.StackGeometry
import AesGcm.Proofs.Machine.Runtime.Root.Memory

namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

variable {use256 : Bool} {code : CodeMap} {fr : Activation}
  {key : Vector UInt8 (AES16.variant use256).keyBytes} {input : ByteArray}
  {batches c blockCount : Nat} {schedule counter source destination : BitVec 64}
  {loc next : LIR.lifted.Location}

abbrev batchWriteRegions (sp counter destination : BitVec 64) (c : Nat) :=
  [span (sp - 296) 512, span (sp + 224) 8, span (sp + 256) 64,
   span (counter + 16) 4, span (destination + BitVec.ofNat 64 (64 * c)) 64]

theorem OuterInvariant.batch_stack_bounds
    (h : OuterInvariant use256 code fr key input batches c schedule counter source destination loc) :
    let sp := outerStackPointer fr use256
    fr.low.toNat + 296 ≤ sp.toNat ∧ sp.toNat + 1800 ≤ fr.rsp.toNat ∧
      fr.rsp.toNat + 8 ≤ 2^32 ∧
      (sp.toNat + 320 ≤ 0x201208 ∨ 0x201238 + 296 ≤ sp.toNat) := by
  have hf := h.frame
  rw [h.label] at hf
  have hr : fr.low.toNat + (if use256 then 2688 else 2160) ≤ fr.rsp.toNat :=
    atomsAll_mem (atom := .fact _) hf (by
      cases use256 <;> simp [cryptFrameAt, LIR.Fn107050.frameAt, LIR.Fn107050.frameAtG6,
        LIR.Fn1084e0.frameAt, LIR.Fn1084e0.frameAtG6])
  have hs : Readable loc.store fr.rsp 8 :=
    atomsAll_mem (atom := .readable fr.rsp 8) hf (by
      cases use256 <;> simp [cryptFrameAt, LIR.Fn107050.frameAt, LIR.Fn107050.frameAtG6,
        LIR.Fn1084e0.frameAt, LIR.Fn1084e0.frameAtG6])
  have ha : (if use256 then 0x201cb8 else 0x201aa8) ≤ fr.rsp.toNat ∨
      fr.rsp.toNat ≤ 0x201208 :=
    atomsAll_mem (atom := .fact _) h.outer (by simp [outerAtoms])
  have hb := hs.low
  cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte, outerStackPointer] at hr ha ⊢
  · have e : (fr.rsp - 1800).toNat = fr.rsp.toNat - 1800 :=
      stack_sub_toNat fr hr (by decide : 1800 ≤ 2160)
    omega
  · have e : (fr.rsp - 2312).toNat = fr.rsp.toNat - 2312 :=
      stack_sub_toNat fr hr (by decide : 2312 ≤ 2688)
    omega

theorem OuterInvariant.batch_stack_apart
    (h : OuterInvariant use256 code fr key input batches c schedule counter source destination loc)
    (a : BitVec 64) (n : Nat) (hn : 0 < n)
    (ha : span a n ∈ [span fr.rdi 8, span fr.rsi 32,
      span schedule (16 * ((AES16.variant use256).Nr + 1)), span counter 20,
      span source input.size, span destination input.size]) :
    a.toNat + n ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ a.toNat := by
  let ns := 16 * ((AES16.variant use256).Nr + 1)
  have hstack : ∀ region ∈ [span fr.rdi 8, span fr.rsi 32, span schedule ns, span counter 20,
      span source input.size, span destination input.size], (callStack fr).Disjoint region :=
    atomsAll_mem (atom := .fact _) h.outer (by simp [outerAtoms, ns])
  obtain ⟨hl, hu, _⟩ := h.batch_stack_bounds
  have sep := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat) a.toNat n
    (by omega) hn (hstack _ ha)
  omega

private theorem batch_outside_of_bounds {sp counter destination a : BitVec 64} {c size n : Nat}
    (hsp : 296 ≤ sp.toNat) (hsp' : sp.toNat + 320 ≤ 2^32)
    (hc : counter.toNat + 20 ≤ 2^32) (hd : destination.toNat + size ≤ 2^32)
    (hbatch : 64 * c + 64 ≤ size) (hbound : a.toNat + n ≤ 2^64)
    (hscratch : a.toNat + n ≤ sp.toNat - 296 ∨ sp.toNat + 216 ≤ a.toNat)
    (hcount : a.toNat + n ≤ sp.toNat + 224 ∨ sp.toNat + 232 ≤ a.toNat)
    (hcopy : a.toNat + n ≤ sp.toNat + 256 ∨ sp.toNat + 320 ≤ a.toNat)
    (hcounter : a.toNat + n ≤ counter.toNat ∨ counter.toNat + 20 ≤ a.toNat)
    (hdest : a.toNat + n ≤ destination.toNat ∨ destination.toNat + size ≤ a.toNat) :
    Outside (batchWriteRegions sp counter destination c) a n := by
  have hsub : (sp - 296).toNat = sp.toNat - 296 := BitVec.toNat_sub_of_le (by exact hsp)
  have hadd (v : BitVec 64) (k : Nat) (hk : v.toNat + k ≤ 2^32) :
      (v + BitVec.ofNat 64 k).toNat = v.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have h224 : (sp + 224).toNat = sp.toNat + 224 := hadd sp 224 (by omega)
  have h256 : (sp + 256).toNat = sp.toNat + 256 := hadd sp 256 (by omega)
  have h16 : (counter + 16).toNat = counter.toNat + 16 := hadd counter 16 (by omega)
  have hout := hadd destination (64 * c) (by omega)
  refine ⟨hbound, ?_⟩
  intro region hr
  simp only [batchWriteRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp only [span, hsub, h224, h256, h16, hout] <;> omega


theorem OuterInvariant.batch_outside
    (h : OuterInvariant use256 code fr key input batches c schedule counter source destination loc)
    (hsize : input.size = 16 * blockCount) (hbatches : batches = blockCount / 4) :
    let sp := outerStackPointer fr use256
    let regions := batchWriteRegions sp counter destination c
    (∀ (a : BitVec 64) (n : Nat),
      sp.toNat + 216 ≤ a.toNat → a.toNat + n ≤ fr.rsp.toNat + 8 →
      (a.toNat + n ≤ sp.toNat + 224 ∨ sp.toNat + 232 ≤ a.toNat) →
      (a.toNat + n ≤ sp.toNat + 256 ∨ sp.toNat + 320 ≤ a.toNat) →
      Outside regions a n) ∧
    (∀ slot ∈ ([0x201208, 0x201210, 0x201230] : List (BitVec 64)), Outside regions slot 8) ∧
    Outside regions schedule (16 * ((AES16.variant use256).Nr + 1)) := by
  let sp := outerStackPointer fr use256
  let ns := 16 * ((AES16.variant use256).Nr + 1)
  rcases h.batch_stack_bounds with ⟨hl, hu, hr, hg⟩
  change fr.low.toNat + 296 ≤ sp.toNat at hl
  change sp.toNat + 1800 ≤ fr.rsp.toNat at hu
  change sp.toNat + 320 ≤ 0x201208 ∨ 0x201238 + 296 ≤ sp.toNat at hg
  have hc := h.count_lt
  have hbatch : 64 * c + 64 ≤ input.size := by omega
  have hcounter := h.toOuterState.counter_write.readable.low
  have hdestination := h.toOuterState.destination_write.readable.low
  have hns : 0 < ns := by dsimp only [ns]; omega
  have hd : ∀ region ∈ [span fr.rdi 8, span fr.rsi 32, span schedule ns, span counter 20],
      (span destination input.size).Disjoint region :=
    atomsAll_mem (atom := .fact _) h.outer (by simp [outerAtoms, ns])
  have hct : ∀ region ∈ [span fr.rdi 8, span fr.rsi 32, span schedule ns,
      span source input.size, span destination input.size], (span counter 20).Disjoint region :=
    atomsAll_mem (atom := .fact _) h.outer (by simp [outerAtoms, ns])
  have hslots : ∀ slot ∈ ([0x201208, 0x201210, 0x201230] : List (BitVec 64)),
      (span destination input.size).Disjoint (span slot 8) ∧
      (span counter 20).Disjoint (span slot 8) :=
    atomsAll_mem (atom := .fact _) h.outer (by simp [outerAtoms])
  have dstApart (a : BitVec 64) (n : Nat) (hn : 0 < n)
      (ha : (span destination input.size).Disjoint (span a n)) :
      a.toNat + n ≤ destination.toNat ∨ destination.toNat + input.size ≤ a.toNat :=
    (disjoint_bounds _ _ _ _ (by omega) hn ha).symm
  have ctrApart (a : BitVec 64) (n : Nat) (hn : 0 < n)
      (ha : (span counter 20).Disjoint (span a n)) :
      a.toNat + n ≤ counter.toNat ∨ counter.toNat + 20 ≤ a.toNat :=
    (disjoint_bounds _ _ _ _ (by decide) hn ha).symm
  have outside (a : BitVec 64) (n : Nat) :=
    @batch_outside_of_bounds sp counter destination a c input.size n
      (by omega) (by omega) hcounter hdestination hbatch
  refine ⟨?_, ?_, ?_⟩
  · intro a n ha hn hcnt hcopy
    change sp.toNat + 216 ≤ a.toNat at ha
    have hsc := h.batch_stack_apart counter 20 (by decide) (by simp)
    have hsd := h.batch_stack_apart destination input.size (by omega) (by simp)
    exact outside a n
      (by omega) (Or.inr ha) hcnt hcopy (by omega) (by omega)
  · intro slot hslot
    have hp : 0x201208 ≤ slot.toNat ∧ slot.toNat + 8 ≤ 0x201238 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hslot
      rcases hslot with rfl | rfl | rfl <;> decide
    obtain ⟨hdslot, hcslot⟩ := hslots slot hslot
    exact outside slot 8
      (by omega) (by omega) (by omega) (by omega) (ctrApart _ _ (by decide) hcslot)
      (dstApart _ _ (by decide) hdslot)
  · have hss := h.batch_stack_apart schedule ns hns (by simp [ns])
    have hs := h.schedule_read.low
    change schedule.toNat + ns ≤ 2^32 at hs
    exact outside schedule ns
      (by omega) (by omega) (by omega) (by omega) (ctrApart _ _ hns (hct _ (by simp)))
      (dstApart _ _ hns (hd _ (by simp)))


theorem OuterInvariant.batch_frame
    (h : OuterInvariant use256 code fr key input batches c schedule counter source destination loc)
    (hsize : input.size = 16 * blockCount) (hbatches : batches = blockCount / 4)
    (hlabel : next.label = (if use256 then .l108e98 else .l107a08) ∨
      next.label = (if use256 then .l109509 else .l10805f))
    (hf : RamWriteFrame loc.store next.store
      (batchWriteRegions (outerStackPointer fr use256) counter destination c))
    (hd : next.arguments[2]'(by change 2 < 53; decide) = ⟨64, destination⟩)
    (hsp : next.arguments[4]'(by change 4 < 53; decide) = ⟨64, outerStackPointer fr use256⟩)
    (hc : next.arguments[9]'(by change 9 < 53; decide) = ⟨64, counter⟩)
    (hregs : ∀ r : Fin Reg.count, r.val ∈ [22, 39, 50, 51] →
      next.arguments[r] = loc.arguments[r]) :
    Atom.All code next.arguments next.store (cryptFrameAt use256 next.label fr) ∧
    Atom.All code next.arguments next.store
      (outerAtoms use256 fr key input blockCount schedule counter source destination) ∧
    AES16.ScheduleIn (AES16.variant use256) key schedule next.store ∧
    memLoad next.store (outerStackPointer fr use256 + 216) 64 = destination := by
  let sp := outerStackPointer fr use256
  let regions := batchWriteRegions sp counter destination c
  obtain ⟨hlocal, hslot, hschedule⟩ := h.batch_outside hsize hbatches
  obtain ⟨hl, hu, hr, _⟩ := h.batch_stack_bounds
  change fr.low.toNat + 296 ≤ sp.toNat at hl
  change sp.toNat + 1800 ≤ fr.rsp.toNat at hu
  have saved (k : Nat) (hk : k ≤ 48) : Outside regions (fr.rsp - BitVec.ofNat 64 k) 8 := by
    have ha := stack_sub_toNat fr (window := 48) (by omega) hk
    apply hlocal <;> rw [ha] <;> dsimp only [sp] at hu <;> omega
  have ret : Outside regions fr.rsp 8 := by simpa using saved 0 (by decide)
  have localBytes (k n : Nat) (hk : 216 ≤ k ∧ k + n ≤ 1800 ∧
      (k + n ≤ 224 ∨ 232 ≤ k) ∧ (k + n ≤ 256 ∨ 320 ≤ k)) :
      Outside regions (sp + BitVec.ofNat 64 k) n := by
    have ha : (sp + BitVec.ofNat 64 k).toNat = sp.toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    apply hlocal <;> rw [ha] <;> dsimp only [sp] at ha hu ⊢ <;> omega
  have hw : ∀ i < 8 * ((AES16.variant use256).Nr + 1),
      Outside regions (wordAddr (sp + 344) 64 i) 8 := by
    intro i hi
    have himax : 8 * ((AES16.variant use256).Nr + 1) ≤ 120 := by cases use256 <;> decide
    have haddr : wordAddr (sp + 344) 64 i = sp + BitVec.ofNat 64 (344 + 8 * i) := by
      simp only [wordAddr, Nat.reduceDiv, BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
    rw [haddr]
    exact localBytes _ _ (by omega)
  have h4 := hsp.trans h.toOuterState.stackPointer.symm
  have h2 := hd.trans h.toOuterState.destination.symm
  have h9 := hc.trans h.toOuterState.counter.symm
  have hfr := h.frame
  rw [h.label] at hfr
  have heq : cryptFrameAt use256 next.label fr =
      cryptFrameAt use256 (if use256 then .l108e98 else .l107a08) fr := by
    rcases hlabel with e | e <;> rw [e] <;> cases use256 <;> rfl
  refine ⟨?_, ?_, AES16.scheduleIn_of_frame h.schedule_in hf hschedule, ?_⟩
  · rw [heq]
    apply atomsAll_of_frame hf _ hfr
    cases use256 <;>
      simp only [cryptFrameAt, Bool.false_eq_true, ↓reduceIte, LIR.Fn107050.frameAt,
        LIR.Fn107050.frameAtG6, LIR.Fn1084e0.frameAt, LIR.Fn1084e0.frameAtG6,
        List.forall_mem_cons, List.not_mem_nil, false_implies, true_and, Atom.gpr, AtomPreserved, Nat.reduceDiv]
    all_goals exact ⟨h4, hregs 22 (by decide), hregs 39 (by decide), hregs 50 (by decide),
      hregs 51 (by decide), saved 48 (by decide), saved 40 (by decide), saved 32 (by decide),
      saved 24 (by decide), saved 16 (by decide), saved 8 (by decide), ret,
      hslot 0x201210 (by decide), hslot 0x201230 (by decide), fun _ => trivial⟩
  · have ho := h.outer
    rw [show input.size / 16 = blockCount by omega] at ho
    apply atomsAll_of_frame hf _ ho
    simp only [outerAtoms, List.forall_mem_cons, List.not_mem_nil, false_implies, true_and, Atom.gpr,
      AtomPreserved, Nat.reduceDiv]
    exact ⟨h2, h4, h9,
      localBytes 232 8 (by decide),
      localBytes 240 8 (by decide),
      localBytes 248 8 (by decide),
      localBytes 320 8 (by decide),
      localBytes 328 8 (by decide),
      localBytes 336 8 (by decide),
      hslot 0x201208 (by decide), hslot 0x201210 (by decide), hslot 0x201230 (by decide), hw, fun _ => trivial⟩
  · exact (hf.memLoad_eq (localBytes 216 8 (by decide))).trans h.destination_slot

open Standards.NIST.GCM in
theorem OuterInvariant.batch_memory
    (inv : OuterInvariant use256 code fr key input batches c schedule counter source destination loc)
    (hsize : input.size = 16 * blockCount) (hbatches : batches = blockCount / 4)
    {mid cipher after : Ram}
    (inputFrame : let sp := outerStackPointer fr use256
      RamWriteFrame loc.store mid [span (sp - 80) 80, span (sp + 8) 64,
        span (sp + 256) 64, span (counter + 16) 4])
    (cipherFrame : let sp := outerStackPointer fr use256
      RamWriteFrame mid cipher [span (sp - 296) 512, span (sp + 224) 8])
    (xorFrame : let sp := outerStackPointer fr use256
      RamWriteFrame cipher after [span (sp + 72) 80, span (sp + 224) 8,
        span (destination + BitVec.ofNat 64 (64 * c)) 64]) :
    RamWriteFrame loc.store after
      (batchWriteRegions (outerStackPointer fr use256) counter destination c) ∧
    (span (source + BitVec.ofNat 64 (64 * c)) (input.size - 64 * c)).HasBytes
      cipher (input.extract (64 * c) input.size) ∧
    memLoad after (counter + 16) 32 = memLoad mid (counter + 16) 32 ∧
    bitsOfBytes (initialCounterBlock loc.store counter) =
      Nat.repeat (inc 32) (4 * c) (bitsOfBytes (initialCounterBlock fr.original counter)) := by
  let sp := outerStackPointer fr use256
  let pos := 64 * c
  let preRegions := [span (sp - 296) 512, span (sp + 224) 8,
    span (sp + 256) 64, span (counter + 16) 4]
  obtain ⟨hlo, hhi, hrsp, _⟩ := inv.batch_stack_bounds
  change fr.low.toNat + 296 ≤ sp.toNat at hlo
  change sp.toNat + 1800 ≤ fr.rsp.toNat at hhi
  have hcount := inv.count_lt
  have hbatch : pos + 64 ≤ input.size := by dsimp only [pos]; omega
  have hsource := inv.toOuterState.source_read.low
  have hdest := inv.toOuterState.destination_write.readable.low
  have hcounter := inv.toOuterState.counter_write.readable.low
  have addr (base : BitVec 64) (k : Nat) (hk : base.toNat + k ≤ 2^32) :
      (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have s296 : (sp - 296).toNat = sp.toNat - 296 := BitVec.toNat_sub_of_le (by change 296 ≤ sp.toNat; omega)
  have s80 : (sp - 80).toNat = sp.toNat - 80 := BitVec.toNat_sub_of_le (by change 80 ≤ sp.toNat; omega)
  have s8 : (sp + 8).toNat = sp.toNat + 8 := addr sp 8 (by omega)
  have s72 : (sp + 72).toNat = sp.toNat + 72 := addr sp 72 (by omega)
  have s224 : (sp + 224).toNat = sp.toNat + 224 := addr sp 224 (by omega)
  have s256 : (sp + 256).toNat = sp.toNat + 256 := addr sp 256 (by omega)
  have c16 : (counter + 16).toNat = counter.toNat + 16 := addr counter 16 (by omega)
  have dpos := addr destination pos (by omega)
  have stackSource := inv.batch_stack_apart source input.size (by omega) (by simp)
  have stackCounter := inv.batch_stack_apart counter 20 (by decide) (by simp)
  have counterApart : ∀ r ∈ [span fr.rdi 8, span fr.rsi 32,
      span schedule (16 * ((AES16.variant use256).Nr + 1)),
      span source input.size, span destination input.size], (span counter 20).Disjoint r :=
    atomsAll_mem (atom := .fact _) inv.outer (by simp [outerAtoms])
  have sep (base : BitVec 64) (apart : (span counter 20).Disjoint (span base input.size)) :
      counter.toNat + 20 ≤ base.toNat ∨ base.toNat + input.size ≤ counter.toNat :=
    disjoint_bounds _ _ _ _ (by decide) (by omega) apart
  have ctrSource := sep source (counterApart _ (by simp))
  have ctrDest := sep destination (counterApart _ (by simp))
  have inputWithin : RegionsWithin [span (sp - 80) 80, span (sp + 8) 64,
      span (sp + 256) 64, span (counter + 16) 4] preRegions := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine ⟨span (sp - 296) 512, by simp [preRegions], ?_, ?_⟩ <;>
        simp only [span, s296, s80] <;> omega
    · refine ⟨span (sp - 296) 512, by simp [preRegions], ?_, ?_⟩ <;>
        simp only [span, s296, s8] <;> omega
    all_goals exact ⟨_, by simp [preRegions], Nat.le_refl _, Nat.le_refl _⟩
  have preFrame : RamWriteFrame loc.store cipher preRegions := by
    apply ((RamWriteFrame.refl _ preRegions).trans inputFrame inputWithin).trans cipherFrame
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact ⟨_, by simp [preRegions, sp], Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have preWithin : RegionsWithin preRegions (batchWriteRegions sp counter destination c) := by
      intro r hr
      refine ⟨r, ?_, Nat.le_refl _, Nat.le_refl _⟩
      simp only [preRegions, batchWriteRegions, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h | h | h <;> simp [h]
    apply ((RamWriteFrame.refl _ _).trans preFrame preWithin).trans xorFrame
    intro r hr
    change r ∈ [span (sp + 72) 80, span (sp + 224) 8,
      span (destination + BitVec.ofNat 64 pos) 64] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨span (sp - 296) 512, by simp [batchWriteRegions], ?_, ?_⟩ <;>
        simp only [span, s296, s72] <;> omega
    all_goals exact ⟨_, by simp [batchWriteRegions, pos], Nat.le_refl _, Nat.le_refl _⟩
  · have srcOutside : Outside preRegions source input.size := by
      refine ⟨by omega, ?_⟩
      intro r hr
      simp only [preRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;>
        simp only [span, s296, s224, s256, c16] <;> omega
    have suffix := outside_subregion (offset := pos) (count := input.size - pos)
      srcOutside (by omega) (by omega)
    exact hasBytes_of_frame preFrame inv.source_bytes suffix.1 (outside_disjoint_span suffix)
  · have cipherOutside : Outside [span (sp - 296) 512, span (sp + 224) 8] (counter + 16) 4 := by
      refine ⟨by rw [c16]; omega, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [span, s296, s224, c16] <;> omega
    have xorOutside : Outside [span (sp + 72) 80, span (sp + 224) 8,
        span (destination + BitVec.ofNat 64 pos) 64] (counter + 16) 4 := by
      refine ⟨by rw [c16]; omega, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [span, s72, s224, c16, dpos] <;> omega
    exact (xorFrame.memLoad_eq xorOutside).trans (cipherFrame.memLoad_eq cipherOutside)
  · have prefixOutside : Outside [fr.region, span (counter + 16) 4, span destination input.size]
        counter 16 := by
      refine ⟨by omega, ?_⟩
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [Activation.region, span, c16] <;> omega
    apply initialCounterBlock_advance fr.original loc.store counter (4 * c) _ _ inv.counter_value
    · intro k
      exact inv.written.memLoad_eq (outside_subregion prefixOutside (by have := k.isLt; omega) (by have := k.isLt; omega))
    · exact inv.written.memLoad_eq (outside_subregion (offset := 12) prefixOutside (by decide) (by decide))

end AesGcm.Proofs.Machine.CTR
