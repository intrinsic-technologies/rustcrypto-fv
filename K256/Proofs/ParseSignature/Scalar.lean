import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Fill
import K256.Proofs.ParseSignature.BlackBox
import K256.Proofs.ParseSignature.Scalar.Setup
import K256.Proofs.ParseSignature.Scalar.Middle
import K256.Proofs.ParseSignature.Scalar.Return

namespace K256.Proofs.ParseSignature

open Standards.SECG.DomainParameters K256.Spec K256.Proofs.Common Prelude X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR Scalar

theorem decode_call {code : CodeMap} (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (hn : fr.rdx = 32)
    (hr : Readable fr.original fr.rsi 32) (hw : Writable code fr.original fr.rdi 40)
    (hin : Outside [callStack fr] fr.rsi 32) (hout : Outside [callStack fr] fr.rdi 40) :
    Call code .l107730 LIR.Fn107730.frameInfo fr [buffer fr.rdi 40] fun out =>
      let x := scalarValue fr.original fr.rsi
      if x < Secp256k1.domain.n then
        memLoad out.store fr.rdi 64 = 0 ∧
          scalarLimbsAt out.store (fr.rdi + 8) fr.original fr.rsi
      else memLoad out.store fr.rdi 64 = 1 := by
  intro args hentry
  have hstack := hentry
  change Atom.All code args fr.original (Fn107730.frameAt .l107730 fr) at hstack
  simp only [Fn107730.frameAt, Fn107730.frameAtG0, Atom.All, Atom.Holds] at hstack
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hread, hret, hretLow,
    hwrite, hroom, halign, _⟩ := hstack
  obtain ⟨setup, fillArgs, fillMem, jumpSetup, callFill, preFill⟩ := setup_fill hcode fr args hentry hn hr hin
  let child := fillActivation fr fillMem
  obtain ⟨filled, execFill, tagFill, regsFill, frameFill, widthsFill, flagFill, wordsFill⟩ :=
    fill_call hcode child rfl rfl rfl preFill.source preFill.dest preFill.sourceOutside
      preFill.destOutside preFill.separate preFill.slot fillArgs preFill.atoms
  obtain ⟨borrowArgs, jumpBorrow, keepFill, widthsBorrow⟩ := branch_after_fill (code := code) (mem := filled.store) flagFill widthsFill
  rw [← Fn127d70.doneAt_canonical] at regsFill
  simp only [Fn127d70.doneAt, Atom.All, Atom.Holds] at regsFill
  obtain ⟨fillSp, fillDF, fillBX, _, _, _, fill14, _, fillMXCSR, fillFTW, fillFCW, _⟩ := regsFill
  let sp := fr.rsp - 152
  have borrowSp : borrowArgs[4] = ⟨64, sp⟩ := by
    calc
      _ = filled.values[4] := keepFill 4 (by decide)
      _ = ⟨64, child.rsp + 8⟩ := fillSp
      _ = ⟨64, sp⟩ := by
        congr 1
        change fr.rsp - 160 + 8 = fr.rsp - 152
        bv_omega
  have hAddr (d : Nat) (hd : d ≤ 368) :
      (fr.rsp - BitVec.ofNat 64 d).toNat = fr.rsp.toNat - d := by
    have hmod : (BitVec.ofNat 64 d).toNat = d := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_sub_of_le (by
      change (BitVec.ofNat 64 d).toNat ≤ fr.rsp.toNat
      rw [hmod]
      omega), hmod]
  have windowPart {mem : Ram} (h : Writable code mem (fr.rsp - (368#64)) 368)
      (d n : Nat) (hd : d ≤ 368) (hn : n ≤ d) :
      Writable code mem (fr.rsp - BitVec.ofNat 64 d) n := by
    apply h.sub
    · rw [hAddr 368 (by decide), hAddr d hd]
      omega
    · rw [hAddr 368 (by decide), hAddr d hd]
      omega
  let work : MemoryRegion := ⟨fr.low.toNat, fr.rsp.toNat - 80 - fr.low.toNat⟩
  have workEnd : work.start + work.size = fr.rsp.toNat - 80 := by
    change fr.low.toNat + (fr.rsp.toNat - 80 - fr.low.toNat) = fr.rsp.toNat - 80
    omega
  have inWork (d n : Nat) (hd : d ≤ 368) (hn : 80 + n ≤ d) :
      InRegions [work] (fr.rsp - BitVec.ofNat 64 d) n := by
    refine ⟨work, List.mem_singleton_self _, ?_⟩
    unfold InRegion
    rw [hAddr d hd, workEnd]
    change fr.low.toNat ≤ fr.rsp.toNat - d ∧ _
    have := fr.rsp.isLt
    omega
  have singletonWithin {small : MemoryRegion} {big : List MemoryRegion} (h : small ∈ big) :
      RegionsWithin [small] big := by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨small, h, Nat.le_refl _, Nat.le_refl _⟩
  have fillWithin : RegionsWithin (child.region :: [buffer child.rdx 32]) [work] := by
    intro r hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    refine ⟨work, List.mem_singleton_self _, ?_⟩
    rcases hm with rfl | rfl
    · change fr.low.toNat ≤ fr.low.toNat ∧
        fr.low.toNat + ((fr.rsp - (160#64)).toNat - fr.low.toNat) ≤ work.start + work.size
      rw [hAddr 160 (by decide), workEnd]
      omega
    · change fr.low.toNat ≤ (fr.rsp - (112#64)).toNat ∧ (fr.rsp - (112#64)).toNat + 32 ≤ work.start + work.size
      rw [hAddr 112 (by decide), workEnd]
      omega
  have workFill : RamWriteFrame fillMem filled.store [work] :=
    (RamWriteFrame.refl _ _).trans frameFill fillWithin
  have fillWindow := (hwrite.of_frame preFill.frame).of_frame workFill
  have wordAddrSp (i : Nat) :
      wordAddr (fr.rsp - 112) 64 i = sp + BitVec.ofNat 64 (40 + 8 * i) := by
    have base : sp + (40#64) = fr.rsp - 112 := by dsimp only [sp]; bv_omega
    simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, ← BitVec.add_assoc, base]
  let word := scalarWord fr.original fr.rsi
  have loaded (i : Nat) (hi : i < 4) :
      memLoad filled.store (sp + BitVec.ofNat 64 (40 + 8 * i)) 64 = word i := by
    rw [← wordAddrSp i]
    exact (wordsFill i hi).trans (preFill.words i hi)
  have tmpAddr : sp + 8 = fr.rsp - 144 := by dsimp only [sp]; bv_omega
  have callAddr : sp - 8 = fr.rsp - (160#64) := by dsimp only [sp]; bv_omega
  have callByte : sp - 8 - 1 = fr.rsp - 161 := by dsimp only [sp]; bv_omega
  have tmpIn : InRegions [work] (sp + 8) 8 := by rw [tmpAddr]; exact inWork 144 8 (by decide) (by decide)
  have callIn : InRegions [work] (sp - 8) 8 := by rw [callAddr]; exact inWork 160 8 (by decide) (by decide)
  have writeTmp : Writable code filled.store (sp + 8) 8 := by
    rw [tmpAddr]
    exact windowPart fillWindow 144 8 (by decide) (by decide)
  have writeCall : Writable code filled.store (sp - 8) 8 := by
    rw [callAddr]
    exact windowPart fillWindow 160 8 (by decide) (by decide)
  have limbLoad (i : Nat) (hi : i < 4) :
      LoadOk filled.store (sp + BitVec.ofNat 64 (40 + 8 * i)) 8 := by
    have ha : sp + BitVec.ofNat 64 (40 + 8 * i) = fr.rsp - BitVec.ofNat 64 (112 - 8 * i) := by
      dsimp only [sp]
      bv_omega
    rw [ha]
    let h := (windowPart fillWindow (112 - 8 * i) 8 (by omega) (by omega)).readable
    exact ⟨h.low, h.present⟩
  obtain ⟨boxArgs, boxMem, callBox, borrowVal, boxSp, w0, w1, w2, w3, keepBorrow,
    widthsBox, frameBorrow, retBox⟩ :=
    borrow_block hcode tmpIn callIn borrowSp writeTmp writeCall
      (limbLoad 0 (by decide)) (limbLoad 1 (by decide)) (limbLoad 2 (by decide)) (limbLoad 3 (by decide))
      widthsBorrow (word 0) (word 1) (word 2) (word 3)
      (loaded 0 (by decide)) (loaded 1 (by decide)) (loaded 2 (by decide)) (loaded 3 (by decide))
  let boxBase : Activation :=
    { fr with
      original := boxMem
      rsp := sp - 8
      ret := 0x107880
      rbx := fr.rdi
      r14 := 1
      r15 := word 0
      r12 := word 1
      r13 := word 2
      rbp := word 3 }
  let box := withArguments boxBase boxArgs
  have boxWindow := fillWindow.of_frame frameBorrow
  have boxRead : Readable boxMem box.rsp 8 := writeCall.readable.of_frame frameBorrow
  have boxWrite : Writable code boxMem (box.rsp - 1) 1 := by
    change Writable code boxMem (sp - 8 - 1) 1
    rw [callByte]
    exact windowPart boxWindow 161 1 (by decide) (by decide)
  have boxRoom : box.low.toNat + 1 ≤ box.rsp.toNat := by
    change fr.low.toNat + 1 ≤ (sp - 8).toNat
    rw [callAddr, hAddr 160 (by decide)]
    omega
  have boxAlign : box.rsp.toNat % 16 = 8 := by
    change (sp - 8).toNat % 16 = 8
    rw [callAddr, hAddr 160 (by decide)]
    omega
  have boxEntry : Atom.All code boxArgs boxMem (Fn127d50.frameInfo.entryAtoms box) := by
    change Atom.All code boxArgs boxMem (Fn127d50.frameAt .l127d50 box)
    simp only [Fn127d50.frameAt, Fn127d50.frameAtG0, Atom.All, Atom.Holds]
    refine ⟨boxSp, ?_, entryArgument widthsBox boxBase 1 (by decide),
      entryArgument widthsBox boxBase 2 (by decide), ?_, w3,
      entryArgument widthsBox boxBase 6 (by decide), entryArgument widthsBox boxBase 7 (by decide),
      entryArgument widthsBox boxBase 8 (by decide), entryArgument widthsBox boxBase 9 (by decide),
      w1, w2, ?_, w0, ?_, ?_, ?_, boxRead, retBox, (by change (0x107880#64).toNat < 2 ^ 32; decide), boxWrite, boxRoom, boxAlign, trivial⟩
    · exact (keepBorrow 22 (by decide)).trans ((keepFill 22 (by decide)).trans fillDF)
    · exact (keepBorrow 3 (by decide)).trans ((keepFill 3 (by decide)).trans fillBX)
    · exact (keepBorrow 14 (by decide)).trans ((keepFill 14 (by decide)).trans fill14)
    · exact (keepBorrow 39 (by decide)).trans ((keepFill 39 (by decide)).trans fillMXCSR)
    · exact (keepBorrow 50 (by decide)).trans ((keepFill 50 (by decide)).trans fillFTW)
    · exact (keepBorrow 51 (by decide)).trans ((keepFill 51 (by decide)).trans fillFCW)
  obtain ⟨boxed, execBox, tagBox, regsBox, frameBox, widthsReturn, postBox⟩ :=
    blackBox_call hcode box boxArgs boxEntry
  rw [← Fn127d50.doneAt_canonical] at regsBox
  simp only [Fn127d50.doneAt, Atom.All, Atom.Holds] at regsBox
  obtain ⟨boxRetSP, boxDF, boxBX, boxBP, box12, box13, box14, box15, boxMXCSR, boxFTW, boxFCW, _⟩ :=
    regsBox
  have boxWithin : RegionsWithin [box.region] [work] := by
    intro r hm
    rw [List.mem_singleton] at hm
    subst r
    refine ⟨work, List.mem_singleton_self _, Nat.le_refl _, ?_⟩
    change fr.low.toNat + ((sp - 8).toNat - fr.low.toNat) ≤ work.start + work.size
    rw [callAddr, hAddr 160 (by decide), workEnd]
    omega
  have workFrame : RamWriteFrame fillMem boxed.store [work] :=
    (workFill.trans frameBorrow (singletonWithin (List.mem_singleton_self _))).trans frameBox boxWithin
  have workWithin : RegionsWithin [work] [fr.region] := by
    intro r hm
    rw [List.mem_singleton] at hm
    subst r
    refine ⟨fr.region, List.mem_singleton_self _, Nat.le_refl _, ?_⟩
    rw [workEnd]
    change fr.rsp.toNat - 80 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
    omega
  have stackFrame := preFill.frame.trans workFrame workWithin
  have loadSaved (k r : Nat) (hm : (k, r) ∈ [(48, 3), (40, 12), (32, 13), (24, 14), (16, 15), (8, 5)]) :
      memLoad boxed.store (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r := by
    have hk : k ≤ 48 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
      omega
    rw [workFrame.memLoad_eq, preFill.saved k r hm]
    refine ⟨?_, ?_⟩
    · rw [hAddr k (by omega)]
      have := hread.low
      omega
    · intro region hregion
      rw [List.mem_singleton] at hregion
      subst region
      right
      rw [workEnd, hAddr k (by omega)]
      omega
  have returnRead := hread.of_frame stackFrame
  have returnWord : memLoad boxed.store fr.rsp 64 = fr.ret := by
    rw [stackFrame.memLoad_eq, hret]
    refine ⟨by have := hread.low; omega, ?_⟩
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    right
    change fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ≤ fr.rsp.toNat
    omega
  have returnAtoms : Atom.All code boxed.values boxed.store (Fn107730.frameAt .l107880 fr) := by
    simp only [Fn107730.frameAt, Fn107730.frameAtG0, Atom.All, Atom.Holds]
    refine ⟨?_, boxDF, boxBX, boxMXCSR, boxFTW, boxFCW,
      loadSaved 48 3 (by decide), loadSaved 40 12 (by decide), loadSaved 32 13 (by decide),
      loadSaved 24 14 (by decide), loadSaved 16 15 (by decide), loadSaved 8 5 (by decide),
      returnRead, returnWord, hretLow, hwrite.of_frame stackFrame, hroom, halign, trivial⟩
    rw [boxRetSP]
    change Value.mk 64 (sp - 8 + 8) = Value.mk 64 sp
    rw [BitVec.sub_add_cancel]
  let valid := decide (scalarValue fr.original fr.rsi < Secp256k1.domain.n)
  have validity : box.rdi = if valid then 1 else 0 := by
    change boxArgs[7].get 64 = _
    rw [borrowVal]
    change borrowChain (word 0) (word 1) (word 2) (word 3) = _
    rw [borrowChain_eq]
    change (if scalarValue fr.original fr.rsi < Secp256k1.domain.n then 1 else 0) = _
    by_cases h : scalarValue fr.original fr.rsi < Secp256k1.domain.n <;> simp [valid, h]
  have returnFlag : boxed.values[0] = ⟨64, if valid then 1 else 0⟩ := by
    rw [postBox, validity]
    cases valid <;> rfl
  obtain ⟨out, execReturn, returnTag, doneAtoms, returnFrame, doneWidths, decodePost⟩ :=
    finish_decode hcode fr boxed.values boxed.store valid returnAtoms returnFlag box14
      (hw.of_frame stackFrame) hout box15 box12 box13 boxBP widthsReturn
  refine ⟨out, ?_, returnTag, doneAtoms, ?_, doneWidths, ?_⟩
  · apply Program.Exec.next (next := ⟨setup, []⟩)
    · simp only [Program.step, jumpSetup, Transfer.next]
    apply exec_call callFill execFill
    · rw [tagFill]
      rfl
    have resumed : fillResume.resume filled = (⟨.l1077bf, filled.values, filled.store⟩ :
        Location Value Ram Label signature) := by
      change Location.mk Label.l1077bf (fillResume.resume filled).arguments filled.store = _
      rw [resume_arguments]
    rw [resumed]
    apply Program.Exec.next (next := ⟨⟨.l1077c7, borrowArgs, filled.store⟩, []⟩)
    · simp only [Program.step, jumpBorrow, Transfer.next]
    apply exec_call callBox execBox
    · rw [tagBox]
      rfl
    have resumed : borrowResume.resume boxed = (⟨.l107880, boxed.values, boxed.store⟩ :
        Location Value Ram Label signature) := by
      change Location.mk Label.l107880 (borrowResume.resume boxed).arguments boxed.store = _
      rw [resume_arguments]
    rw [resumed]
    exact execReturn
  · let regions := [fr.region, buffer fr.rdi 40]
    have before := (RamWriteFrame.refl fr.original regions).trans stackFrame
      (singletonWithin (List.mem_cons_self ..))
    exact before.trans returnFrame (singletonWithin (by exact List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  · by_cases h : scalarValue fr.original fr.rsi < Secp256k1.domain.n <;>
      simpa [valid, h] using decodePost

end K256.Proofs.ParseSignature
