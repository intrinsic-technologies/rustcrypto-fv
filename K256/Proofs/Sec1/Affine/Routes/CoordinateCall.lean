import K256.Proofs.Sec1.Affine.Calls
import K256.Proofs.Sec1.Affine.Dispatch
import K256.Proofs.Sec1.Parser.Control
import K256.Proofs.Sec1.Serialize.Choice
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall

namespace K256.Proofs.Sec1.Affine

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR

set_option maxHeartbeats 400000 in
theorem reachCoordinateCall {code : CodeMap} (cover : ∀ x ∈ fnCode, x ∈ code)
    {args : Values Value Reg.count} {mem : Ram} {sp src : BitVec 64} {tag : BitVec 8}
    (tagValid : tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5)
    (ax : args[0] = ⟨64, tag.setWidth 64⟩) (dx : args[2] = ⟨64, src⟩)
    (rsp : args[4] = ⟨64, sp⟩) (win : Writable code mem (sp - 9) 9) :
    let compressed := tag != 4
    let ret : BitVec 64 := if compressed then 0x1214ce else 0x121502
    let resume := if compressed then Label.l1214ce else .l121502
    let parity : BitVec 64 := if tag = 3 then 1 else 0
    ∃ (child : Values Value Reg.count) (written : Ram),
      (program.sem (dialect code)).Reaches ⟨⟨.l1214a0, args, mem⟩, []⟩
        ⟨⟨if compressed then .l1205b0 else .l11f780, child, written⟩, [Wrapper.callFrame resume ret]⟩ ∧
      child[4] = ⟨64, sp - 8⟩ ∧ child[7] = ⟨64, sp⟩ ∧ child[6] = ⟨64, src + 1⟩ ∧
      child[14] = ⟨64, src + 1⟩ ∧ child[2] = ⟨64, if compressed then parity else src + 33⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 15, 22, 39, 50, 51] → child[i] = args[i]) ∧
      memLoad written (sp - 8) 64 = ret ∧ RamWriteFrame mem written [⟨(sp - 9).toNat, 9⟩] := by
  dsimp only
  let compressed := tag != 4
  let parity : BitVec 64 := if tag = 3 then 1 else 0
  let region : List MemoryRegion := [⟨(sp - 9).toNat, 9⟩]
  let routeArgs :=
    ((args.set 1 ⟨64, mergeGPR 8 (tag &&& 6) ((tag.setWidth 32).setWidth 64)⟩).set 14
      ⟨64, src + 1⟩).set 19 (.ofBool ((tag &&& 6) == 2))
  have dispatch := dispatchCoordinates (code := code) args mem
  simp only [ax, dx, Value.get_mk,
    BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq] at dispatch
  change program.runBlock (dialect code) ⟨.l1214a0, args, mem⟩ =
    (if (tag &&& 6) == 2 then .jump ⟨.l1214ae, routeArgs, mem⟩
      else .jump ⟨.l1214b5, routeArgs, mem⟩) at dispatch
  have compact := dispatchCompact (code := code) routeArgs mem
  have routeAx : routeArgs[0] = ⟨64, tag.setWidth 64⟩ := by
    simpa only [routeArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using ax
  have routeTag : (routeArgs[0].get 64).setWidth 8 = tag := by
    rw [routeAx, Value.get_mk, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq]
  change program.runBlock (dialect code) ⟨.l1214b5, routeArgs, mem⟩ =
    .jump ⟨if (routeArgs[0].get 64).setWidth 8 == 5 then .l1214b9 else .l1214f3,
      routeArgs.set 19 (.ofBool ((routeArgs[0].get 64).setWidth 8 == 5)), mem⟩ at compact
  rw [routeTag] at compact
  have routePtr : routeArgs[14] = ⟨64, src + 1⟩ := by
    simp only [routeArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
  have routeSp : routeArgs[4] = ⟨64, sp⟩ := by
    simpa only [routeArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using rsp
  have routeDx : routeArgs[2] = ⟨64, src⟩ := by
    simpa only [routeArgs, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using dx
  let saved : List Nat := [3, 5, 12, 13, 15, 22, 39, 50, 51]
  have savedNe {i r : Nat} (hi : i ∈ saved) (hr : r ∉ saved) : r ≠ i :=
    fun h => hr (h.symm ▸ hi)
  have routeKeep (i : Fin Reg.count) (hi : i.val ∈ saved) : routeArgs[i] = args[i] := by
    change routeArgs[i.val] = args[i.val]
    simp only [routeArgs, Vector.getElem_set, savedNe hi (r := 1) (by decide),
      savedNe hi (r := 14) (by decide), savedNe hi (r := 19) (by decide), ↓reduceIte]
  have slot (m : Ram) (h : Writable code m (sp - 9) 9) : Writable code m (sp - 8) 8 :=
    h.of_offsets (addr_sub sp 8) (addr_sub sp 9) (by decide)
  have slotWithin : InRegions region (sp - 8) 8 := by
    have low := win.readable.low
    have addr : (sp - 8).toNat = (sp - 9).toNat + 1 := by
      have ha := toNat_of_offsets (addr_sub sp 8) (addr_sub sp 9) low (n := 8) (by decide)
      have hc : ((0 - 8) - (0 - 9) : BitVec 64).toNat = 1 := by decide +kernel
      simpa only [hc] using ha
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change (sp - 9).toNat ≤ (sp - 8).toNat ∧ (sp - 8).toNat + 8 ≤ (sp - 9).toNat + 9 ∧ _
    omega
  obtain ⟨ready, m, reach, readySp, readyPtr, readyArg, readyKeep, frame⟩ :
      ∃ (ready : Values Value Reg.count) (m : Ram),
        Parser.Reaches code .l1214a0 args mem (if compressed then .l1214c0 else .l1214f3) ready m ∧
        ready[4] = ⟨64, sp⟩ ∧ ready[14] = ⟨64, src + 1⟩ ∧
        (if compressed then ((ready[0].get 64).setWidth 8).setWidth 64 else ready[2].get 64 + 33) =
          (if compressed then parity else src + 33) ∧
        (∀ i : Fin Reg.count, i.val ∈ saved → ready[i] = args[i]) ∧
        RamWriteFrame mem m region := by
    by_cases ht : tag = 4
    · have hmask : ((tag &&& 6) == 2) = false := by rw [ht]; decide
      have hcompact : (tag == 5) = false := by rw [ht]; decide
      have hcompress : compressed = false := by simp only [compressed, ht]; decide
      simp only [hmask, Bool.false_eq_true, ↓reduceIte] at dispatch
      rw [hcompact] at compact
      simp only [hcompress, Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, mem, (Parser.reaches_jump dispatch).trans (Parser.reaches_jump compact),
        ?_, ?_, ?_, ?_, RamWriteFrame.refl _ _⟩
      · simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using routeSp
      · simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using routePtr
      · simp only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte, routeDx, Value.get_mk]
      · intro i hi
        change (routeArgs.set 19 (.ofBool false))[i.val] = args[i.val]
        simp only [Vector.getElem_set, savedNe hi (r := 19) (by decide), ↓reduceIte]
        exact routeKeep i hi
    · have hcompress : compressed = true := by
        simp only [compressed, bne, beq_eq_false_iff_ne.mpr ht, Bool.not_false]
      obtain ⟨parityArgs, beforeParity, parityIn, paritySp, parityPtr, parityKeep⟩ :
          ∃ a : Values Value Reg.count, Parser.Reaches code .l1214a0 args mem .l1214bb a mem ∧
            a[7] = ⟨64, parity⟩ ∧ a[4] = ⟨64, sp⟩ ∧ a[14] = ⟨64, src + 1⟩ ∧
            (∀ i : Fin Reg.count, i.val ∈ saved → a[i] = args[i]) := by
        by_cases h5 : tag = 5
        · have hmask : ((tag &&& 6) == 2) = false := by rw [h5]; decide
          have hcompact : (tag == 5) = true := by rw [h5]; decide
          simp only [hmask, Bool.false_eq_true, ↓reduceIte] at dispatch
          rw [hcompact] at compact
          refine ⟨_, (Parser.reaches_jump dispatch).trans ((Parser.reaches_jump compact).trans
            (Parser.reaches_jump (compactParity _ _))), ?_, ?_, ?_, ?_⟩
          · simp only [Vector.getElem_set, ↓reduceIte, parity, h5]
            rfl
          · simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using routeSp
          · simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using routePtr
          · intro i hi
            change ((routeArgs.set 19 (.ofBool true)).set 7 ⟨64, 0⟩)[i.val] = args[i.val]
            simp only [Vector.getElem_set, savedNe hi (r := 7) (by decide),
              savedNe hi (r := 19) (by decide), ↓reduceIte]
            exact routeKeep i hi
        · have h23 : tag = 2 ∨ tag = 3 := by
            rcases tagValid with h | h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact (ht h).elim
            · exact (h5 h).elim
          have hmask : ((tag &&& 6) == 2) = true := by rcases h23 with h | h <;> rw [h] <;> decide
          have hpar : (tag &&& 1).setWidth 64 = parity := by rcases h23 with h | h <;> simp only [parity, h] <;> rfl
          simp only [hmask, ↓reduceIte] at dispatch
          have step := compressedParity (code := code) routeArgs mem
          simp only [routeAx, Value.get_mk,
            BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), BitVec.setWidth_eq, hpar] at step
          refine ⟨_, (Parser.reaches_jump dispatch).trans (Parser.reaches_jump step),
            ?_, ?_, ?_, ?_⟩
          · simp only [Vector.getElem_set, ↓reduceIte]
          · simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using routeSp
          · simpa only [Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using routePtr
          · intro i hi
            change ((routeArgs.set 0 _).set 7 ⟨64, parity⟩)[i.val] = args[i.val]
            simp only [Vector.getElem_set, savedNe hi (r := 0) (by decide),
              savedNe hi (r := 7) (by decide), ↓reduceIte]
            exact routeKeep i hi
      let pushed := memStore mem (sp - 8) (0x1214c0 : BitVec 64)
      let callee := parityArgs.set 4 ⟨64, sp - 8⟩
      have call := parityCall cover parityArgs mem sp (by rw [paritySp, Value.get_mk]) (slot mem win)
      have savedRet : memLoad pushed (sp - 8) 64 = 0x1214c0 :=
        memLoad_memStore_same _ _ _ (by decide) (by decide)
      have scratchAddr : sp - 8 - 1 = sp - 9 := by bv_omega
      have scratch : Writable code pushed (sp - 8 - 1) 1 := by
        rw [scratchAddr]
        exact (win.memStore _ (0x1214c0 : BitVec 64)).sub (Nat.le_refl _) (by omega)
      obtain ⟨out, returned, returnTag, outSp, outAx, writes, keeps⟩ := Serialize.choiceBlock
        (fun e he => cover e (code_l127d50 e he)) (args := callee)
        (by simp only [callee, Vector.getElem_set, ↓reduceIte, Value.get_mk])
        scratch ((slot mem win).readable.memStore _ (0x1214c0 : BitVec 64))
        (by rw [savedRet]; decide)
      have run : program.Exec (dialect code) ⟨⟨.l127d50, callee, pushed⟩, []⟩ out :=
        .done (by simp only [Program.step, returned, Transfer.next])
      have returnPath := Serialize.Coordinates.reaches_call call run
        (by simpa only [savedRet] using returnTag)
      have pushedFrame : RamWriteFrame mem pushed region :=
        (RamWriteFrame.refl _ _).memStore _ slotWithin
      simp only [hcompress, ↓reduceIte]
      refine ⟨out.values, out.store, beforeParity.trans returnPath, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [BitVec.sub_add_cancel] using outSp
      · have ptr : callee[14] = ⟨64, src + 1⟩ := by
          simpa only [callee, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using parityPtr
        exact (keeps 14 (by decide)).trans ptr
      · have arg7 : callee[7] = ⟨64, parity⟩ := by
          simpa only [callee, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using parityIn
        rw [outAx, arg7, Value.get_mk, Value.get_mk]
        by_cases h3 : tag = 3 <;> simp only [parity, h3, ↓reduceIte] <;> rfl
      · intro i hi
        have hkeeps : i.val ∈ [1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22, 39, 50, 51] := by
          simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with h | h|h | h|h | h|h | h|h <;> rw [h] <;> decide
        refine (keeps i hkeeps).trans ?_
        change callee[i.val] = args[i.val]
        simp only [callee, Vector.getElem_set, savedNe hi (r := 4) (by decide), ↓reduceIte]
        exact parityKeep i hi
      · apply pushedFrame.trans writes
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        refine ⟨_, List.mem_singleton_self _, ?_⟩
        simp only [scratchAddr]
        change (sp - 9).toNat ≤ (sp - 9).toNat ∧ (sp - 9).toNat + 1 ≤ (sp - 9).toNat + 9
        omega
  let ret : BitVec 64 := if compressed then 0x1214ce else 0x121502
  let next := if compressed then Label.l1214ce else .l121502
  let result := if compressed then Label.l1205b0 else .l11f780
  let arg := if compressed then parity else src + 33
  let child := (((ready.set 2 ⟨64, arg⟩).set 4 ⟨64, sp - 8⟩).set 6 ⟨64, src + 1⟩).set 7 ⟨64, sp⟩
  have call := coordinateCall cover compressed ready m sp (by rw [readySp, Value.get_mk])
    (slot m (win.of_frame frame))
  rw [readyArg, readyPtr, Value.get_mk] at call
  change program.runBlock (dialect code) _ =
    .call ⟨result, child, memStore m (sp - 8) ret⟩ (Wrapper.callFrame next ret) at call
  refine ⟨child, memStore m (sp - 8) ret, reach.trans (.single ?_), ?_, ?_, ?_, ?_, ?_, ?_,
    memLoad_memStore_same _ _ _ (by decide) (by decide), frame.memStore ret slotWithin⟩
  · simp only [Program.sem, Program.step, call, Transfer.next, result, next, ret, compressed]
  · simp only [child, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
  · simp only [child, Vector.getElem_set, ↓reduceIte]
  · simp only [child, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
  · simpa only [child, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte] using readyPtr
  · simp only [child, arg, compressed, parity, Vector.getElem_set, Nat.reduceEqDiff, ↓reduceIte]
  · intro i hi
    change child[i.val] = args[i.val]
    simp only [child, Vector.getElem_set, savedNe hi (r := 2) (by decide),
      savedNe hi (r := 4) (by decide), savedNe hi (r := 6) (by decide),
      savedNe hi (r := 7) (by decide), ↓reduceIte]
    exact readyKeep i hi

end K256.Proofs.Sec1.Affine
