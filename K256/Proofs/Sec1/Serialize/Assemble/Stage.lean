import K256.Proofs.Sec1.Serialize.Assemble.Memory
import K256.Proofs.Sec1.LIR.Fn1215e0

namespace K256.Proofs.Sec1.Serialize.Assemble

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem stageCoordinates {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {sp : BitVec 64} {x y : Vector (BitVec 64) 4}
    (hcode : ∀ entry ∈ fnCode, entry ∈ code)
    (rsp : args[4].get 64 = sp) (stack : Writable code mem (sp - 8) 288)
    (hx : WordsAt mem (sp + 151) 64 x) (hy : WordsAt mem (sp + 183) 64 y) :
    ∃ (next : Values Value Reg.count) (staged : Ram),
      program.runBlock (dialect code) ⟨.l121702, args, mem⟩ = .jump ⟨.l12176c, next, staged⟩ ∧
      next[0].get 8 = 4 ∧ next[4] = args[4] ∧
      (∀ i : Fin Reg.count, i.val ∈ [2,3,5,6,8,9,10,11,12,13,14,15,22,39,50,51] →
        next[i] = args[i]) ∧
      WordsAt staged (sp + 80) 64 x ∧ WordsAt staged (sp + 8) 64 y ∧
      RamWriteFrame mem staged [⟨(sp + 80).toNat, 32⟩, ⟨(sp + 8).toNat, 32⟩] := by
  have hload {a c : BitVec 64} (ha : a = sp + c) (h : (c - (0 - 8)).toNat + 8 ≤ 288) :
      LoadOk mem a 8 :=
    let slot := (stackSlot stack ha h).readable
    ⟨slot.low, slot.present⟩
  have hstore {a c pc : BitVec 64} (ha : a = sp + c) (h : (c - (0 - 8)).toNat + 8 ≤ 288)
      (hp : (pc - 0x121702).toNat + 5 ≤ bytes_l121702.length) :
      StoreOk code mem a 8 pc 5 :=
    storeOk_inBlock (stackSlot stack ha h) (fun entry he => hcode entry (code_l121702 entry he)) hp
  have x0 : memLoad mem (sp + 151) 64 = x[0] := wordsAtOffset hx 0 (by decide)
  have x1 : memLoad mem (sp + 159) 64 = x[1] := wordsAtOffset hx 1 (by decide)
  have x2 : memLoad mem (sp + 167) 64 = x[2] := wordsAtOffset hx 2 (by decide)
  have x3 : memLoad mem (sp + 175) 64 = x[3] := wordsAtOffset hx 3 (by decide)
  have y0 : memLoad mem (sp + 183) 64 = y[0] := wordsAtOffset hy 0 (by decide)
  have y1 : memLoad mem (sp + 191) 64 = y[1] := wordsAtOffset hy 1 (by decide)
  have y2 : memLoad mem (sp + 199) 64 = y[2] := wordsAtOffset hy 2 (by decide)
  have y3 : memLoad mem (sp + 207) 64 = y[3] := wordsAtOffset hy 3 (by decide)
  refine ⟨?next, ?staged, ?step, ?tag, ?stackReg, ?regs, ?x, ?y, ?frame⟩
  case step =>
    cfg_eval [rsp]
    iterate 16
      refine (ite_eq_left ?_).trans ?_
      · repeat first | apply loadOk_memStore | apply storeOk_memStore
        first
        | apply hload rfl <;> decide
        | apply hstore rfl <;> decide
    simp (disch := (apply RangeApart.of_offsets rfl rfl; decide)) only
      [memLoad_memStore_of_rangeApart, x0, x1, x2, x3, y0, y1, y2, y3]
    rfl
  case tag =>
    change (mergeGPR 8 4 y[3]).setWidth 8 = 4
    exact setWidth_mergeGPR8 _ _
  case stackReg => rfl
  case regs =>
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case x =>
    apply fourWordsAt <;>
      simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide)) only [memLoad_memStore_same,
          memLoad_memStore_of_rangeApart, Lift.reduceAddOffset]
  case y =>
    apply fourWordsAt <;>
      simp (disch := first | decide | (apply RangeApart.of_offsets rfl rfl; decide)) only [memLoad_memStore_same,
          memLoad_memStore_of_rangeApart, Lift.reduceAddOffset]
  case frame =>
    iterate 4
      apply RamWriteFrame.memStore
      case hin => exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        inStackRegionOffsets stack rfl rfl (by decide) (by decide)⟩
    iterate 4
      apply RamWriteFrame.memStore
      case hin => exact ⟨_, List.mem_cons_self, inStackRegionOffsets stack rfl rfl (by decide) (by decide)⟩
    exact RamWriteFrame.refl _ _

end K256.Proofs.Sec1.Serialize.Assemble
