import K256.Proofs.Sec1.SqrtLaterProducts.Early.Product
import K256.Proofs.Sec1.SqrtChainExecution.ProductResume
import K256.Proofs.Sec1.SqrtLaterProducts.Middle.Blocks
import K256.Proofs.Sec1.SqrtLaterProducts.Words

namespace K256.Proofs.Sec1.SqrtLaterProducts.Middle

open X86 X86.Machine X86.UserProcess X86Proofs CFG Lift Refine Prelude Common.Field
open SqrtChainExecution
attribute [local irreducible] chainWord

private theorem loopWindow {code fr args mem}
    (win : Early.Window code fr args mem (fr.rsp - 440)) :
    Writable code mem (fr.rsp - 440) 432 :=
  win.writable.of_offsets (addr_self _) (addr_sub _ 8) (by decide)

private theorem stackWidth {code fr args mem}
    (frame : Early.StandardFrame code fr args mem) :
    args[4].width = 64 := congrArg Value.width frame.1

private theorem loopWrites {before after : Ram} {sp : Word} (room : 8 ≤ sp.toNat)
    (writes : RamWriteFrame before after [⟨sp.toNat, 384⟩]) :
    RamWriteFrame before after [Early.scratchRegion sp] := by
  apply (RamWriteFrame.refl _ _).trans writes
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
  · change (sp - 8).toNat ≤ sp.toNat
    rw [BitVec.toNat_sub_of_le (by change 8 ≤ _; exact room)]
    change sp.toNat - 8 ≤ sp.toNat
    omega
  · change sp.toNat + 384 ≤ (sp - 8).toNat + 392
    rw [BitVec.toNat_sub_of_le (by change 8 ≤ _; exact room)]
    change sp.toNat + 384 ≤ sp.toNat - 8 + 392
    omega

private theorem loopStage {code fr a i args mem regs out}
    (geo : Geometry code fr) (st : ProductState code fr a i.castSucc args mem)
    (frameIn : Early.StandardFrame code fr args mem)
    (frameOut : LIR.Fn115950.frameAt squarePC[i] fr = LIR.Fn115950.frameAt .l116316 fr)
    (block : LIR.program.runBlock (dialect code) ⟨productPC[i.castSucc], args, mem⟩ =
      .jump ⟨squarePC[i], regs, out⟩)
    (keptSp : regs[4] = args[4])
    (regFacts : ProductRegisters args regs)
    (written : RamWriteFrame mem out [Early.scratchRegion (fr.rsp - 440)])
    (saved : Atom.All code regs out (savedAtoms i.succ (fr.rsp - 440) a))
    (countedLoop : counted i = true)
    (wordsAtBase : WordsAt out (fr.rsp - 440) 64 (words a (2 * (i.val + 1))))
    (src : regs[srcReg i].get 64 = fr.rsp - 440)
    (dst : regs[dstReg i].get 64 = fr.rsp - 440 + 40)
    (counter : regs[countReg i] = ⟨64, BitVec.ofNat 64 squareCount[i]⟩) :
    ∃ b m, Parser.Reaches code productPC[i.castSucc] args mem squarePC[i] b m ∧
      SquareState code fr a i b m := by
  have win := Early.window frameIn
  refine ⟨regs, out, Parser.reaches_jump block, ?_, saved, ?_, fun _ => src, fun _ => dst,
    fun _ => counter, Early.preservedSource win geo st.source st.sourceRead written,
    st.sourceRead.of_frame written, st.destWrite.of_frame written, ?_, ?_,
    Early.extendWrites win st.writes written⟩
  · rw [frameOut]
    exact Early.standardFrameOfWrites frameIn (keptSp.trans frameIn.1) regFacts.control written
  · dsimp only
    rw [countedLoop]
    exact wordsAtBase
  · intro r hr
    apply regFacts.widths
    simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    omega
  · intro _ r hr
    apply regFacts.widths
    simp only [Activation.entryNumbers, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    omega

private abbrev commonOffsets : List Word :=
  [352, 328, 304, 336, 320, 240, 288, 312, 256, 248, 160, 176, 208, 168, 144]

private theorem prefixAtoms {code args mem} {as : List Atom} (n : Nat)
    (h : Atom.All code args mem as) : Atom.All code args mem (as.take n) :=
  ((Atom.all_append (as.take n) (as.drop n)).1 ((List.take_append_drop n as).symm ▸ h)).1

private theorem suffixAtoms {code args mem} {as : List Atom} (n : Nat)
    (h : Atom.All code args mem as) : Atom.All code args mem (as.drop n) :=
  ((Atom.all_append (as.take n) (as.drop n)).1 ((List.take_append_drop n as).symm ▸ h)).2

private theorem retainPrefix {mem out sp} {extra : List Word}
    (retained : PreservesWords mem out sp (commonOffsets ++ extra)) :
    PreservesWords mem out sp commonOffsets :=
  fun off hm => retained off (List.mem_append_left extra hm)

private theorem carryPrefix {code args regs mem out sp a}
    (before : Atom.All code args mem ((savedAtoms 5 sp a).take 15))
    (retain : PreservesWords mem out sp commonOffsets) :
    Atom.All code regs out ((savedAtoms 5 sp a).take 15) := by
  obtain ⟨w352, w328, w304, w336, w320, w240, w288, w312, w256, w248,
    w160, w176, w208, w168, w144, _⟩ := before
  exact ⟨(retain 352 (by decide)).trans w352,
    (retain 328 (by decide)).trans w328,
    (retain 304 (by decide)).trans w304,
    (retain 336 (by decide)).trans w336,
    (retain 320 (by decide)).trans w320,
    (retain 240 (by decide)).trans w240,
    (retain 288 (by decide)).trans w288,
    (retain 312 (by decide)).trans w312,
    (retain 256 (by decide)).trans w256,
    (retain 248 (by decide)).trans w248,
    (retain 160 (by decide)).trans w160,
    (retain 176 (by decide)).trans w176,
    (retain 208 (by decide)).trans w208,
    (retain 168 (by decide)).trans w168,
    (retain 144 (by decide)).trans w144, trivial⟩

private theorem firstWord {m : Ram} {sp : Word} {v : Limbs}
    (words : WordsAt m sp 64 v) : memLoad m sp 64 = v[0] := by
  have h := words 0 (by decide)
  change memLoad m (sp + (0 : Word)) 64 = _ at h
  rwa [show sp + (0 : Word) = sp from BitVec.add_zero sp] at h

private theorem savedRead {v : Value} {w : Word} (eq : v = ⟨64, w⟩) : v.get 64 = w :=
  congrArg (Value.get 64) eq

private theorem savesSix {code args regs mem out sp a}
    (before : Atom.All code args mem (savedAtoms 5 sp a))
    (retained : PreservesWords mem out sp commonOffsets)
    (result : WordsAt out sp 64 (words a 12))
    (p0 : memLoad out (sp + 136) 64 = memLoad out sp 64)
    (reg1 : regs[13] = ⟨64, memLoad out (sp + 8) 64⟩)
    (reg2 : regs[5] = ⟨64, memLoad out (sp + 16) 64⟩)
    (reg3 : regs[15] = ⟨64, memLoad out (sp + 24) 64⟩)
    (reg4 : regs[12] = ⟨64, memLoad out (sp + 32) 64⟩) :
    Atom.All code regs out (savedAtoms 6 sp a) := by
  have common : Atom.All code regs out ((savedAtoms 5 sp a).take 15) :=
    carryPrefix (a := a) (sp := sp) (prefixAtoms 15 before) retained
  change Atom.All code regs out ((savedAtoms 5 sp a).take 15 ++ (savedAtoms 6 sp a).drop 15)
  refine (Atom.all_append _ _).2 ⟨common, ?_⟩
  exact ⟨p0.trans (firstWord result), reg1.trans (congrArg (Value.mk 64) (result 1 (by decide))),
    reg2.trans (congrArg (Value.mk 64) (result 2 (by decide))),
    reg3.trans (congrArg (Value.mk 64) (result 3 (by decide))),
    reg4.trans (congrArg (Value.mk 64) (result 4 (by decide))), trivial⟩

private theorem savesSeven {code args regs mem out sp a}
    (before : Atom.All code args mem (savedAtoms 6 sp a))
    (retained : PreservesWords mem out sp (commonOffsets ++ [136]))
    (result : WordsAt out sp 64 (words a 14))
    (p0 : memLoad out (sp + 120) 64 = memLoad out sp 64)
    (p1 : memLoad out (sp + 96) 64 = memLoad out (sp + 8) 64)
    (p2 : memLoad out (sp + 128) 64 = memLoad out (sp + 16) 64)
    (p3 : memLoad out (sp + 80) 64 = memLoad out (sp + 24) 64)
    (p4 : memLoad out (sp + 88) 64 = memLoad out (sp + 32) 64)
    (spill3 : memLoad out (sp + 104) 64 = args[15].get 64)
    (spill4 : memLoad out (sp + 112) 64 = args[12].get 64)
    (spill1 : memLoad out (sp + 192) 64 = args[13].get 64)
    (spill2 : memLoad out (sp + 264) 64 = args[5].get 64)
    (reg0 : regs[5] = ⟨64, memLoad out sp 64⟩)
    (reg3 : regs[12] = ⟨64, memLoad out (sp + 24) 64⟩) :
    Atom.All code regs out (savedAtoms 7 sp a) := by
  have prior := prefixAtoms 15 before
  change Atom.All code args mem ((savedAtoms 5 sp a).take 15) at prior
  have common := carryPrefix (regs := regs) prior (retainPrefix (extra := [136]) retained)
  change Atom.All code regs out ((savedAtoms 5 sp a).take 15 ++ (savedAtoms 7 sp a).drop 15)
  refine (Atom.all_append _ _).2 ⟨common, ?_⟩
  obtain ⟨old136, oldR13, oldRbp, oldR15, oldR12, _⟩ :=
    suffixAtoms 15 before
  exact ⟨(retained 136 (by decide)).trans old136, spill1.trans (savedRead oldR13),
    spill2.trans (savedRead oldRbp), spill3.trans (savedRead oldR15), spill4.trans (savedRead oldR12),
    p0.trans (firstWord result), p1.trans (result 1 (by decide)), p2.trans (result 2 (by decide)),
    p3.trans (result 3 (by decide)), p4.trans (result 4 (by decide)),
    reg0.trans (congrArg (Value.mk 64) (firstWord result)),
    reg3.trans (congrArg (Value.mk 64) (result 3 (by decide))), trivial⟩

private theorem savesEight {code args regs mem out sp a}
    (before : Atom.All code args mem (savedAtoms 7 sp a))
    (retained : PreservesWords mem out sp (commonOffsets ++ [136, 192, 264, 104, 112, 120, 96, 128, 80, 88]))
    (result : WordsAt out sp 64 (words a 16))
    (p0 : memLoad out (sp + 152) 64 = memLoad out sp 64)
    (p1 : memLoad out (sp + 184) 64 = memLoad out (sp + 8) 64)
    (p3 : memLoad out (sp + 200) 64 = memLoad out (sp + 24) 64)
    (p4 : memLoad out (sp + 232) 64 = memLoad out (sp + 32) 64)
    (reg1 : regs[13] = ⟨64, memLoad out (sp + 8) 64⟩)
    (reg2 : regs[5] = ⟨64, memLoad out (sp + 16) 64⟩)
    (reg3 : regs[12] = ⟨64, memLoad out (sp + 24) 64⟩) :
    Atom.All code regs out (savedAtoms 8 sp a) := by
  have prior := prefixAtoms 15 before
  change Atom.All code args mem ((savedAtoms 5 sp a).take 15) at prior
  have common := carryPrefix (regs := regs) prior (retainPrefix (extra := [136, 192, 264, 104, 112, 120, 96, 128, 80, 88]) retained)
  change Atom.All code regs out ((savedAtoms 5 sp a).take 15 ++ (savedAtoms 8 sp a).drop 15)
  refine (Atom.all_append _ _).2 ⟨common, ?_⟩
  have prev := suffixAtoms 15 before
  obtain ⟨old136, old192, old264, old104, old112, old120, old96, old128, old80, old88, _⟩ := prev
  exact ⟨(retained 136 (by decide)).trans old136,
    (retained 192 (by decide)).trans old192,
    (retained 264 (by decide)).trans old264,
    (retained 104 (by decide)).trans old104,
    (retained 112 (by decide)).trans old112,
    (retained 120 (by decide)).trans old120,
    (retained 96 (by decide)).trans old96,
    (retained 128 (by decide)).trans old128,
    (retained 80 (by decide)).trans old80,
    (retained 88 (by decide)).trans old88,
    p0.trans (firstWord result), p1.trans (result 1 (by decide)),
    reg1.trans (congrArg (Value.mk 64) (result 1 (by decide))),
    reg2.trans (congrArg (Value.mk 64) (result 2 (by decide))),
    p3.trans (result 3 (by decide)), reg3.trans (congrArg (Value.mk 64) (result 3 (by decide))),
    p4.trans (result 4 (by decide)), trivial⟩

private theorem savesNine {code args regs mem out sp a}
    (before : Atom.All code args mem (savedAtoms 8 sp a))
    (retained : PreservesWords mem out sp (commonOffsets ++ [136, 192, 264, 104, 112, 120, 96, 128, 80, 88])) :
    Atom.All code regs out (savedAtoms 9 sp a) := by
  have prior := prefixAtoms 15 before
  change Atom.All code args mem ((savedAtoms 5 sp a).take 15) at prior
  have common := carryPrefix (regs := regs) prior (retainPrefix (extra := [136, 192, 264, 104, 112, 120, 96, 128, 80, 88]) retained)
  change Atom.All code regs out ((savedAtoms 5 sp a).take 15 ++ (savedAtoms 9 sp a).drop 15)
  refine (Atom.all_append _ _).2 ⟨common, ?_⟩
  have prev := suffixAtoms 15 before
  obtain ⟨old136, old192, old264, old104, old112, old120, old96, old128, old80, old88, _⟩ := prev
  exact ⟨(retained 136 (by decide)).trans old136,
    (retained 192 (by decide)).trans old192,
    (retained 264 (by decide)).trans old264,
    (retained 104 (by decide)).trans old104,
    (retained 112 (by decide)).trans old112,
    (retained 120 (by decide)).trans old120,
    (retained 96 (by decide)).trans old96,
    (retained 128 (by decide)).trans old128,
    (retained 80 (by decide)).trans old80,
    (retained 88 (by decide)).trans old88,
    trivial⟩

private abbrev ProductCertificate (code : CodeMap) (fr : Activation) (a : Limbs) (i : Fin 13) :=
  ∀ {args mem}, ProductState code fr a i.castSucc args mem →
    OutputWords (fr.rsp - 440) (words a (2 * (i.val + 1)))
      (LIR.program.runBlock (dialect code) ⟨productPC[i.castSucc], args, mem⟩)

private theorem callSix {code fr a} (geo : Geometry code fr)
    (certify : ProductCertificate code fr a 5) {args mem}
    (st : ProductState code fr a 5 args mem) :
    ∃ child : LIR.lifted.Location,
      LIR.program.runBlock (dialect code) ⟨.l117297, args, mem⟩ =
        .call child (Wrapper.callFrame .l1176f2 0x1176f2) ∧
      ProductCall code fr a 5 child 0x1176f2 := by
  let sp := fr.rsp - 440
  have frameIn : Early.StandardFrame code fr args mem := st.frame
  have win := Early.window frameIn
  obtain ⟨room, low, apart⟩ := win.blockBounds geo (start := 0x117297) (finish := 0x1176f2)
    (by decide) (by decide)
  obtain ⟨regs, out, block, rsp, dst, src, rdi, rsi, slot, writes, flags,
    p0, reg1, reg2, reg3, reg4, retained⟩ :=
    stageSix win.rsp win.writable room low apart
  have actual := certify st
  change OutputWords sp (words a 12)
    (LIR.program.runBlock (dialect code) ⟨.l117297, args, mem⟩) at actual
  rw [block] at actual
  have result : WordsAt out sp 64 (words a 12) := actual
  have after : Atom.All code regs out (savedAtoms 6 sp a) :=
    savesSix (a := a) (sp := sp) st.saved retained result p0 reg1 reg2 reg3 reg4
  exact ⟨⟨.l1145f0, regs, out⟩, block,
    Early.productCallOfFrame (i := 5) geo st frameIn rfl rfl rsp rsi rdi flags.control flags.widths
      writes slot (by decide) (fun _ => src) (fun _ => dst) after result⟩

private theorem multiplySeven {code fr a} (geo : Geometry code fr)
    (certify : ProductCertificate code fr a 6) : MultiplyStage code fr a 6 := by
  intro args mem st
  let sp := fr.rsp - 440
  have frameIn : Early.StandardFrame code fr args mem := st.frame
  have win := Early.window frameIn
  obtain ⟨room, low, apart⟩ := win.blockBounds geo (start := 0x117bde) (finish := 0x118040)
    (by decide) (by decide)
  obtain ⟨regs, out, block, rsp, count, src, dst, writes, flags, p0, p1, p2, p3, p4, spill3, spill4, spill1, spill2, reg0, reg3, retained⟩ :=
    stageSeven win.rsp (stackWidth frameIn) (loopWindow win) low
      (apart.imp id (fun h => Nat.le_trans (by decide) h))
  have actual := certify st
  change OutputWords sp (words a 14)
    (LIR.program.runBlock (dialect code) ⟨.l117bde, args, mem⟩) at actual
  rw [block] at actual
  have result : WordsAt out sp 64 (words a 14) := actual
  have after : Atom.All code regs out (savedAtoms 7 sp a) :=
    savesSeven (a := a) (sp := sp) st.saved retained result p0 p1 p2 p3 p4 spill3 spill4 spill1 spill2 reg0 reg3
  exact loopStage geo st frameIn rfl block rsp flags (loopWrites room writes)
    after rfl result src dst count

private theorem multiplyEight {code fr a} (geo : Geometry code fr)
    (certify : ProductCertificate code fr a 7) : MultiplyStage code fr a 7 := by
  intro args mem st
  let sp := fr.rsp - 440
  have frameIn : Early.StandardFrame code fr args mem := st.frame
  have win := Early.window frameIn
  obtain ⟨room, low, apart⟩ := win.blockBounds geo (start := 0x118081) (finish := 0x1184d0)
    (by decide) (by decide)
  obtain ⟨regs, out, block, rsp, count, src, dst, writes, flags, p0, p1, p3, p4, reg1, reg2, reg3, retained⟩ :=
    stageEight win.rsp (stackWidth frameIn) (loopWindow win) low
      (apart.imp id (fun h => Nat.le_trans (by decide) h))
  have actual := certify st
  change OutputWords sp (words a 16)
    (LIR.program.runBlock (dialect code) ⟨.l118081, args, mem⟩) at actual
  rw [block] at actual
  have result : WordsAt out sp 64 (words a 16) := actual
  have after : Atom.All code regs out (savedAtoms 8 sp a) :=
    savesEight (a := a) (sp := sp) st.saved retained result p0 p1 p3 p4 reg1 reg2 reg3
  exact loopStage geo st frameIn rfl block rsp flags (loopWrites room writes)
    after rfl result src dst count

private theorem multiplyNine {code fr a} (geo : Geometry code fr)
    (certify : ProductCertificate code fr a 8) : MultiplyStage code fr a 8 := by
  intro args mem st
  let sp := fr.rsp - 440
  have frameIn : Early.StandardFrame code fr args mem := st.frame
  have win := Early.window frameIn
  obtain ⟨room, low, apart⟩ := win.blockBounds geo (start := 0x118511) (finish := 0x118950)
    (by decide) (by decide)
  obtain ⟨regs, out, block, rsp, count, src, dst, writes, flags, retained⟩ :=
    stageNine win.rsp (stackWidth frameIn) (loopWindow win) low
      (apart.imp id (fun h => Nat.le_trans (by decide) h))
  have actual := certify st
  change OutputWords sp (words a 18)
    (LIR.program.runBlock (dialect code) ⟨.l118511, args, mem⟩) at actual
  rw [block] at actual
  have result : WordsAt out sp 64 (words a 18) := actual
  have after : Atom.All code regs out (savedAtoms 9 sp a) :=
    savesNine (a := a) (sp := sp) st.saved retained
  exact loopStage geo st frameIn rfl block rsp flags (loopWrites room writes)
    after rfl result src dst count

private theorem multiplySix {code fr a} (geo : Geometry code fr)
    (certify : ProductCertificate code fr a 5) : MultiplyStage code fr a 5 := by
  intro args mem st
  obtain ⟨child, block, entry⟩ := callSix geo certify st
  exact productResume (i := 5) geo (by decide) block entry

private theorem middleIndex (i : Fin 13) (lo : 5 ≤ i.val) (hi : i.val ≤ 8) :
    i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
  have h : i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨ i.val = 8 := by omega
  exact h.imp (fun h => Fin.ext h) (fun h =>
    h.imp (fun h => Fin.ext h) (fun h => h.imp (fun h => Fin.ext h) (fun h => Fin.ext h)))

private theorem middleStagesOf {code fr a} (i : Fin 13) (lo : 5 ≤ i.val) (hi : i.val ≤ 8)
    (geo : Geometry code fr) (certify : ProductCertificate code fr a i) :
    MultiplyStage code fr a i := by
  rcases middleIndex i lo hi with rfl | rfl | rfl | rfl
  · exact multiplySix geo certify
  · exact multiplySeven geo certify
  · exact multiplyEight geo certify
  · exact multiplyNine geo certify

private theorem middleStandardFrame {code fr a i args mem} (lo : 5 ≤ (i : Fin 13).val)
    (hi : i.val ≤ 8) (st : ProductState code fr a i.castSucc args mem) :
    Early.StandardFrame code fr args mem := by
  rcases middleIndex i lo hi with rfl | rfl | rfl | rfl <;> exact st.frame

theorem middleStages {code fr a x} (i : Fin 13) (lo : 5 ≤ i.val) (hi : i.val ≤ 8)
    (geo : Geometry code fr) (ha : FieldRepr a x 8) : MultiplyStage code fr a i := by
  apply middleStagesOf i lo hi geo
  intro args mem st
  have win := Early.window (middleStandardFrame lo hi st)
  have haddr := win.value
  have room := win.room
  have low := win.stackLow
  exact productWords i (by omega) ha st win.rsp win.writable (by omega) (by omega)

end K256.Proofs.Sec1.SqrtLaterProducts.Middle
