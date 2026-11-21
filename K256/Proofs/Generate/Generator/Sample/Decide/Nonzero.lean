import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Frame
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Compare
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Prepare
import K256.Proofs.Generate.Generator.Sample.Memory
import K256.Proofs.Generate.Generator.Activation

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

structure AfterNonzero (s : RamState) (random : ByteArray) (fr : Activation) (i : Nat)
    (a : Registers) (m : Ram) : Prop extends Frame .l106001 fr a m where
  rdxWidth : a[2].width = 64
  rbxWidth : a[3].width = 64
  r8Width : a[8].width = 64
  r9Width : a[9].width = 64
  cursorReg : a[5] = ⟨64, cursor s i⟩
  remainingReg : a[13] = ⟨64, remaining random i⟩
  scratch : a[12] = ⟨64, fr.rsp - 288⟩
  decoded : a[15] = ⟨64, fr.rsp - 168⟩
  limbs : WordsAt m (fr.rsp - 352) 64 (Vector.ofFn fun j : Fin 4 => word s i j.val)
  flag : a[0].get 8 = 1 ↔ ¬ ∀ j < 4, word s i j = 0

theorem checkNonzero {s : RamState} {random : ByteArray} {fr : Activation} {a : Registers}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (entry : Entry s fr a) {i : Nat}
    {b : Registers} {mem : Ram} (decoded : AfterDecode s random fr i b mem)
    (stack : List (StackFrame Value Label signature Reg.count)) :
    ∃ c m, Run.Reaches ⟨⟨.l105f70, b, mem⟩, stack⟩ ⟨⟨.l106001, c, m⟩, stack⟩ ∧
      AfterNonzero s random fr i c m := by
  obtain ⟨c, m, push, csp, di, si, widths, kept, prep, retCompare, limbs, left, zeros⟩ :=
    prepareCompare decoded
  have caller := decoded.atoms
  simp only [Fn105f30.frameAt, Fn105f30.frameAtG0, Atom.All, Atom.Holds] at caller
  obtain ⟨_, df, r14, mx, ft, fc, savedOut, savedBx, saved12, saved13, saved14, saved15, savedBp,
    readRet, callerRet, retLow, window, room, align, _, _, _, _, apart, _⟩ := caller
  let base := {fr with
    rsp := fr.rsp - 400, low := fr.rsp - 416,
    rbx := remaining random (i+1), rbp := cursor s i, r12 := fr.rsp - 288,
    r13 := remaining random i, r14 := fr.rsi, r15 := fr.rsp - 168}
  have keep (j : Fin Reg.count) (hj : j.val ∈ nonzeroPreserved) : c[j] = preservedValue base j.val := by
    rw [kept j hj]
    obtain ⟨j, bound⟩ := j
    simp only [nonzeroPreserved, List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact decoded.nextLength | exact decoded.cursorReg | exact decoded.scratch
                    | exact decoded.remainingReg | exact r14 | exact decoded.decoded
                    | exact df | exact mx | exact ft | exact fc
  have top := readRet.low
  have off (k : Nat) (hk : k ≤ 10168) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have reduced : (BitVec.ofNat 64 k).toNat = k := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, reduced]; omega), reduced]
  have bottom : (fr.rsp - 10168).toNat = fr.rsp.toNat - 10168 := off 10168 (by decide)
  have low : base.low.toNat = fr.rsp.toNat - 416 := off 416 (by decide)
  have sp : base.rsp.toNat = fr.rsp.toNat - 400 := off 400 (by decide)
  have windowAt {n : Ram} (win : Writable Extracted.programImage n (fr.rsp - 10168) 10168)
      (k len : Nat) (hk : k ≤ 10168) (hn : len ≤ k) :
      Writable Extracted.programImage n (fr.rsp - BitVec.ofNat 64 k) len := by
    apply win.sub <;> rw [bottom, off k hk] <;> omega
  have preWin := window.of_frame prep
  let cmp := compareChild base c m 0x105ff5
  have argL : cmp.rdi = fr.rsp - 320 := congrArg (Value.get 64) di
  have argR : cmp.rsi = fr.rsp - 168 := congrArg (Value.get 64) si
  have cmpEntry := sampleChildEntry (base := base) Fn10a280.frameInfo rfl (by decide)
    csp keep widths (windowAt preWin 400 8 (by decide) (by decide)).readable retCompare
    (by decide +kernel) (by
      change Writable _ _ (fr.rsp - 400 - 16) 16
      rw [show fr.rsp - 400 - 16 = fr.rsp - 416 by bv_omega]
      exact windowAt preWin 416 16 (by decide) (by decide))
    (by change base.low.toNat + 16 ≤ base.rsp.toNat; rw [low, sp]; omega)
    (by rw [sp]; omega)
  have outsideChild (k : Nat) (hk : k ≤ 352) (hn : 32 ≤ k) :
      Outside [base.region] (fr.rsp - BitVec.ofNat 64 k) 32 := by
    simp only [Outside, List.mem_singleton, forall_eq, Activation.region, off k (by omega), low, sp]
    omega
  obtain ⟨o, cmpRun, cmpTag, cmpDone, cmpWrites, cmpWidths, eqFlag, bit⟩ :=
    compareFour cmp (argL ▸ (windowAt preWin 320 32 (by decide) (by decide)).readable)
      (argR ▸ (windowAt preWin 168 32 (by decide) (by decide)).readable)
      (argL ▸ outsideChild 320 (by decide) (by decide)) (argR ▸ outsideChild 168 (by decide) (by decide))
      c cmpEntry
  obtain ⟨osp, oKeep⟩ := sampleChildReturn (base := base) (a := c) (tag := 0x105ff5) (m := m) cmpDone
  have test : o.values[0].get 8 = 1 ↔ ∀ j < 4, word s i j = 0 := by
    rw [eqFlag, argL, argR]
    have values (j : Nat) (hj : j < 4) := left j hj
    have zero (j : Nat) (hj : j < 4) := zeros j hj
    simp only [Vector.getElem_ofFn] at values
    simp only [Vector.getElem_replicate] at zero
    constructor <;> intro h j hj
    · exact (values j hj).symm.trans ((h j hj).trans (zero j hj))
    · exact (values j hj).trans ((h j hj).trans (zero j hj).symm)
  have addr : base.rsp + 8 - 8 = base.rsp := by bv_omega
  have winO := preWin.of_frame cmpWrites
  have slotW := windowAt winO 400 8 (by decide) (by decide)
  obtain ⟨d, boxPush, dsp, darg, dwidth, dkeep⟩ := complementCall (sp := base.rsp + 8) (m := o.store)
    (congrArg (Value.get 64) osp) (by rw [addr]; exact slotW) cmpWidths
  rw [addr] at boxPush dsp
  let pushed := memStore o.store base.rsp (0x106001 : BitVec 64)
  let box := compareChild base d pushed 0x106001
  have boxEntry := sampleChildEntry (base := base) (m := pushed) (tag := 0x106001)
    Fn127d50.frameInfo rfl (by decide) dsp (fun j hj => (dkeep j hj).trans (oKeep j hj)) dwidth
    (slotW.readable.memStore _ _) (memLoad_memStore_same _ _ _ (by decide) (by decide)) (by decide +kernel)
    (by
      change Writable _ _ (fr.rsp - 400 - 1) 1
      rw [show fr.rsp - 400 - 1 = fr.rsp - 401 by bv_omega]
      exact (windowAt winO 401 1 (by decide) (by decide)).memStore _ _)
    (by change base.low.toNat + 1 ≤ base.rsp.toNat; rw [low, sp]; omega) (by rw [sp]; omega)
  obtain ⟨out, boxRun, boxTag, boxDone, boxWrites, outputWidths, byte⟩ :=
    blackBox_call Common.fnCode_subset_programImage box d boxEntry
  obtain ⟨outSp, outKeep⟩ := sampleChildReturn (base := base) (a := d) (m := pushed) (tag := 0x106001) boxDone
  let scratchArea : MemoryRegion := ⟨base.low.toNat, 24⟩
  have childWithin : RegionsWithin [base.region] [scratchArea] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_singleton_self _, Nat.le_refl _, ?_⟩
    change base.low.toNat + (base.rsp.toNat - base.low.toNat) ≤ base.low.toNat + 24
    rw [low, sp]; omega
  have first : RamWriteFrame m o.store [scratchArea] :=
    (RamWriteFrame.refl _ _).trans cmpWrites childWithin
  have middle : RamWriteFrame m pushed [scratchArea] := by
    apply first.memStore
    refine ⟨scratchArea, List.mem_singleton_self _, ?_⟩
    change base.low.toNat ≤ base.rsp.toNat ∧ base.rsp.toNat + 8 ≤ base.low.toNat + 24 ∧
      base.rsp.toNat + 8 ≤ 2^64
    rw [low, sp]; omega
  have after := middle.trans boxWrites childWithin
  have inFrame (k len : Nat) (hk : k ≤ 10168) (hn : len ≤ k) :
      fr.region.start ≤ (fr.rsp - BitVec.ofNat 64 k).toNat ∧
      (fr.rsp - BitVec.ofNat 64 k).toNat + len ≤ fr.region.start + fr.region.size := by
    simp only [Activation.region, off k hk]; omega
  have prepWithin : RegionsWithin (compareRegions fr) (regions fr) := by
    intro r hr
    simp only [compareRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, .head _, inFrame 400 8 (by decide) (by decide)⟩
    · exact ⟨_, .head _, inFrame 352 64 (by decide) (by decide)⟩
    · exact ⟨_, .head _, inFrame 168 32 (by decide) (by decide)⟩
  have writes := (decoded.writes.trans prep prepWithin).trans after (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, .head _, inFrame 416 24 (by decide) (by decide)⟩)
  have saved (k : Nat) (hk : k ≤ 48 ∨ k = 360) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 k) 64 =
        memLoad mem (fr.rsp - BitVec.ofNat 64 k) 64 := by
    rw [after.memLoad_eq, prep.memLoad_eq]
    all_goals
      simp only [compareRegions, Outside, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, scratchArea, low, off k (by omega), Nat.reduceDiv]
      have o400 : (fr.rsp - 400).toNat = fr.rsp.toNat - 400 := sp
      have o352 : (fr.rsp - 352).toNat = fr.rsp.toNat - 352 := off 352 (by decide)
      have o168 : (fr.rsp - 168).toNat = fr.rsp.toNat - 168 := off 168 (by decide)
      omega
  have slot := Fn105f30.callSlots_loaded
    (show rodataSection ∈ Extracted.programSections by simp [rodataSection, Extracted.programSections])
    (loaded_of_stackFrame call (stackFrame call entry writes))
  obtain ⟨read1, val1⟩ := slot (0x203de0, 0x129770) (by decide)
  obtain ⟨read2, val2⟩ := slot (0x203e20, 0x100a20) (by decide)
  refine ⟨out.values, out.store, (reachesAfterSampleCall push cmpRun cmpTag stack).trans
    (reachesAfterSampleCall boxPush boxRun boxTag stack), ⟨⟨?_, writes⟩, outputWidths 2 (by decide),
    congrArg Value.width (outKeep 3 (by decide)), outputWidths 8 (by decide), outputWidths 9 (by decide),
    outKeep 5 (by decide), outKeep 13 (by decide), outKeep 12 (by decide), outKeep 15 (by decide), ?_, ?_⟩⟩
  · simp only [Fn105f30.frameAt, Fn105f30.frameAtG0, Atom.All, Atom.Holds]
    have savedRet := saved 0 (by decide)
    change memLoad out.store (fr.rsp - 0) 64 = memLoad mem (fr.rsp - 0) 64 at savedRet
    rw [show fr.rsp - 0 = fr.rsp by bv_omega] at savedRet
    refine ⟨?_, outKeep 22 (by decide), outKeep 14 (by decide), outKeep 39 (by decide),
      outKeep 50 (by decide), outKeep 51 (by decide), (saved 360 (by decide)).trans savedOut,
      (saved 48 (by decide)).trans savedBx, (saved 40 (by decide)).trans saved12,
      (saved 32 (by decide)).trans saved13, (saved 24 (by decide)).trans saved14,
      (saved 16 (by decide)).trans saved15, (saved 8 (by decide)).trans savedBp,
      (readRet.of_frame prep).of_frame after, savedRet.trans callerRet, retLow,
      preWin.of_frame after, room, align, read1, val1, read2, val2, apart, trivial⟩
    apply outSp.trans
    congr 1
    change fr.rsp - 400 + 8 = fr.rsp - 392
    bv_omega
  · intro j hj
    rw [after.memLoad_eq]
    · exact limbs j hj
    have hj' : 8*j < 352 := by omega
    have adr : wordAddr (fr.rsp - 352) 64 j = fr.rsp - BitVec.ofNat 64 (352 - 8*j) := by
      unfold wordAddr
      rw [← BitVec.ofNat_sub_ofNat_of_le 352 (8*j) (by omega) (by omega)]
      bv_omega
    simp only [Outside, adr, off (352 - 8*j) (by omega), scratchArea, low, List.mem_singleton, forall_eq, Nat.reduceDiv]
    omega
  · have arg : box.rdi = ((~~~(o.values[0].get 8)) &&& 1).setWidth 64 := congrArg (Value.get 64) darg
    rw [← test, byte, arg]
    rcases bit with h | h <;> rw [h] <;> decide

end K256.Proofs.Generate.Generator.Sample
