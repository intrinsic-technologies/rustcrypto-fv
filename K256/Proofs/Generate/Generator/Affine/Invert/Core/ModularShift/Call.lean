import K256.Proofs.Generate.Generator.Affine.Invert.Core.ModularShift.State
import K256.Proofs.Generate.Generator.Affine.Invert.Core.LinearCombination
import K256.Proofs.ParseSignature.Call
import K256.Proofs.Generate.Generator.Entry

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.ModularShift

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Common.Invert.ModularShift

private def stackRegion (sp : Word) : MemoryRegion := ⟨(sp - 304).toNat, 304⟩

private def preludeRegions (sp : Word) : List MemoryRegion :=
  [⟨(sp - 48).toNat, 48⟩, ⟨(sp - 176).toNat, 8⟩]

private def savedSlots (a : Registers) (sp : Word) : List Atom :=
  [.mem (sp - 8) 64 (a[5].get 64), .mem (sp - 16) 64 (a[15].get 64),
   .mem (sp - 24) 64 (a[14].get 64), .mem (sp - 32) 64 (a[13].get 64),
   .mem (sp - 40) 64 (a[12].get 64), .mem (sp - 48) 64 (a[3].get 64)]

set_option maxHeartbeats 750000 in
set_option maxRecDepth 4096 in
private theorem linearCallBlock {a : Registers} {m : Ram} {sp dst : Word} {shift : BitVec 32}
    (rsp : a[4].get 64 = sp) (rdi : a[7].get 64 = dst) (hs : a[9].get 32 = shift)
    (win : Writable Extracted.programImage m (sp - 304) 304) (room : 304 ≤ sp.toNat) :
    ∃ b m', program.runBlock (dialect Extracted.programImage) ⟨.l108980, a, m⟩ =
      .call ⟨.l1084e0, b, m'⟩ (callFrame .l10899e 0x10899e) ∧
      b[4] = ⟨64, sp - 176⟩ ∧ b[7] = ⟨64, sp - 152⟩ ∧
      b[3] = ⟨64, dst⟩ ∧ b[5] = ⟨64, shift.setWidth 64⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [1, 2, 6, 8, 22, 39, 50, 51] → b[i] = a[i]) ∧
      RamWriteFrame m m' (preludeRegions sp) ∧
      memLoad m' (sp - 176) 64 = 0x10899e ∧
      Atom.All Extracted.programImage b m' (savedSlots a sp) := by
  refine ⟨?_, ?_, ?run, ?post⟩
  case run =>
    have shiftWord : (a[9].get 64).setWidth 32 = shift :=
      (BitVec.setWidth_setWidth_of_le _ (by decide)).trans hs
    arithmetic_segment using code_l108980 [rsp, rdi, shiftWord, callFrame]
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · unfold preludeRegions
      slot_state region
    · lifted_word_reads []
      lifted_word_eq []
    · simp only [savedSlots, Atom.All, Atom.Holds]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
      all_goals lifted_word_reads [] <;> lifted_word_eq []

set_option linter.unusedVariables false in
theorem linearCall {a : Registers} {m : Ram} {sp dst ret : Word} {x y : Int} {u v : Word} {shift : Nat}
    (fr : CalleeFrame a m sp dst ret 304 33)
    (args : LinearArgs a m sp dst 304 33 x y u v)
    (hs : a[9].get 32 = BitVec.ofNat 32 shift) (pos : 0 < shift) (hshift : shift ≤ 62)
    (stackArgs : Readable m (sp + 8) 16)
    (argHigh : sp.toNat + 24 ≤ 2^32)
    (argApart : dst.toNat + 33 ≤ sp.toNat ∨ sp.toNat + 24 ≤ dst.toNat)
    (modPtr : memLoad m (sp + 8) 64 = 0x2021e0)
    (inv : memLoad m (sp + 16) 64 = 0x27c7f6e22ddacacf)
    : ∃ p : Inputs, ∃ b m', p.shift.toNat = shift ∧ Represents p (x * u.toInt + y * v.toInt) ∧
      Reaches .l108980 a m .l10899e b m' ∧ TailFrame a m sp dst ret b m' ∧
      Atom.All Extracted.programImage b m' (afterLinear sp dst p) := by
  have room := fr.depthBound
  have align := fr.aligned
  have win : Writable Extracted.programImage m (sp - 304) 304 := fr.stack
  have rspBits : a[4].get 64 = sp := congrArg (Value.get 64) fr.rsp
  have dstBits : a[7].get 64 = dst := congrArg (Value.get 64) fr.rdi
  obtain ⟨c, before, block, rsp, rdi, rbx, rbp, keep, prep, callRet, saved⟩ :=
    linearCallBlock rspBits dstBits hs win room
  have subNat (k : Word) (hk : k.toNat ≤ 304) : (sp - k).toNat = sp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (by exact Nat.le_trans hk room)
  have at304 : (sp - 304).toNat = sp.toNat - 304 := subNat _ (by decide)
  have at288 : (sp - 288).toNat = sp.toNat - 288 := subNat _ (by decide)
  have at176 : (sp - 176).toNat = sp.toNat - 176 := subNat _ (by decide)
  have at152 : (sp - 152).toNat = sp.toNat - 152 := subNat _ (by decide)
  have at48 : (sp - 48).toNat = sp.toNat - 48 := subNat _ (by decide)
  have prepFrame : RamWriteFrame m before [stackRegion sp] := by
    refine (RamWriteFrame.refl _ _).trans prep ?_
    intro r hr
    simp only [preludeRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    rcases hr with rfl | rfl
    · simp only [stackRegion, at304, at48]; omega
    · simp only [stackRegion, at304, at176]; omega
  have beforeWin := win.of_frame prepFrame
  have childStack : Writable Extracted.programImage before (sp - 176 - BitVec.ofNat 64 112) 112 := by
    rw [show sp - 176 - BitVec.ofNat 64 112 = sp - 288 by bv_omega]
    exact beforeWin.sub (by omega) (by omega)
  have childOutput : Writable Extracted.programImage before (sp - 152) 41 :=
    beforeWin.sub (by omega) (by omega)
  have childReturn : Readable before (sp - 176) 8 :=
    beforeWin.readable.sub (by omega) (by omega)
  have frame : CalleeFrame c before (sp - 176) (sp - 152) 0x10899e 112 41 := by
    refine ⟨rsp, rdi, (keep 22 (by decide)).trans fr.df,
      Core.stackImage win prepFrame fr.image, ?_, ?_, childReturn, callRet, by decide,
      childStack, childOutput, ?_⟩
    · omega
    · omega
    · right; omega
  have transfer {addr : Word} {n : Int} (src : SignedSource m sp dst addr 304 33 n) :
      SignedSource before (sp - 176) (sp - 152) addr 112 41 n := by
    have safe := src.stackApart
    have low := src.read.low
    have outside : Outside [stackRegion sp] addr 32 := by
      simp only [Outside, List.mem_singleton, forall_eq, stackRegion, at304]
      exact ⟨by omega, by omega⟩
    refine ⟨src.read.of_frame prepFrame, ?_, ?_, ?_⟩
    · omega
    · omega
    · obtain ⟨w, neg, words, sign, eq⟩ := src.signed
      have signAddr : (addr + 32).toNat = addr.toNat + 32 := by
        rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.reduceToNat]; omega)]
        rfl
      have signOutside : Outside [stackRegion sp] (addr + 32) 1 := by
        simp only [Outside, List.mem_singleton, forall_eq, stackRegion, at304, signAddr]
        omega
      exact ⟨w, neg, words.of_frame prepFrame (by decide) outside,
        (prepFrame.memLoad_eq signOutside).trans sign, eq⟩
  have childArgs : LinearArgs c before (sp - 176) (sp - 152) 112 41 x y u v := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (congrArg (Value.get 64) (keep 6 (by decide))).symm ▸ transfer args.left
    · exact (congrArg (Value.get 64) (keep 2 (by decide))).symm ▸ transfer args.right
    · exact (congrArg (Value.get 64) (keep 1 (by decide))).trans args.coeffLeft
    · exact (congrArg (Value.get 64) (keep 8 (by decide))).trans args.coeffRight
  obtain ⟨out, run, result, w, neg, words, sign, value⟩ := linearCombination frame childArgs
  have childFrame : RamWriteFrame before out.store
      [⟨(sp - 288).toNat, 112⟩, ⟨(sp - 152).toNat, 41⟩] := by
    have hf := result.frame
    rwa [show sp - 176 - BitVec.ofNat 64 112 = sp - 288 by bv_omega] at hf
  have fullFrame : RamWriteFrame m out.store [stackRegion sp] := by
    refine prepFrame.trans childFrame ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    refine ⟨_, List.mem_cons_self, ?_⟩
    rcases hr with rfl | rfl <;> simp only [stackRegion, at304, at288, at152] <;> omega
  have loadSaved (k : Word) (hk : 8 ≤ k.toNat ∧ k.toNat ≤ 48) :
      memLoad out.store (sp - k) 64 = memLoad before (sp - k) 64 := by
    apply childFrame.memLoad_eq
    refine ⟨by rw [subNat k (by omega)]; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [at288, subNat k (by omega), Nat.reduceDiv]; omega
    · simp only [at152, subNat k (by omega), Nat.reduceDiv]; omega
  have loadCaller (k : Word) (hk : k.toNat ≤ 16) :
      memLoad out.store (sp + k) 64 = memLoad m (sp + k) 64 := by
    have addr : (sp + k).toNat = sp.toNat + k.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    apply fullFrame.memLoad_eq
    simp only [Outside, List.mem_singleton, forall_eq, Nat.reduceDiv, addr, stackRegion, at304]
    omega
  let p : Inputs := ⟨w, if neg then 1 else 0, BitVec.ofNat 32 shift⟩
  refine ⟨p, out.values, out.store, Nat.mod_eq_of_lt (by omega), ?_, ?_, ?_, ?_⟩
  · refine ⟨neg, rfl, ?_⟩
    have mag : K256.Proofs.Common.Invert.LinearCombination.wideValue w =
        (((w[4].toNat * 2^64 + w[3].toNat) * 2^64 + w[2].toNat) * 2^64 +
          w[1].toNat) * 2^64 + w[0].toNat := by
      simp only [K256.Proofs.Common.Invert.LinearCombination.wideValue,
        K256.Proofs.Common.Invert.LinearCombination.packFive, Vector.getElem_map, Nat.add_mul]
      omega
    change _ = if neg then -(K256.Proofs.Common.Invert.LinearCombination.wideValue w : Int)
      else (K256.Proofs.Common.Invert.LinearCombination.wideValue w : Int)
    rwa [mag]
  · refine .step (b := ⟨⟨.l1084e0, c, before⟩, [callFrame .l10899e 0x10899e]⟩) ?_ ?_
    · simp only [Program.sem, Program.step, block, Transfer.next]
    · exact ParseSignature.exec_reaches_resume run _ [] (by rw [result.returned]; rfl)
  · have outSp := result.rsp
    rw [show sp - 176 + 8 = sp - 168 by bv_omega] at outSp
    refine ⟨outSp, fun i hi => (result.controls i hi).trans (keep i ?_),
      ?_, fullFrame, ?_, (loadCaller 8 (by decide)).trans modPtr,
      (loadCaller 16 (by decide)).trans inv, Core.stackImage win fullFrame fr.image⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega
    · change Atom.All _ _ _ (savedSlots a sp)
      simp only [savedSlots, Atom.All, Atom.Holds] at saved ⊢
      obtain ⟨s8, s16, s24, s32, s40, s48, _⟩ := saved
      exact ⟨(loadSaved 8 (by decide)).trans s8, (loadSaved 16 (by decide)).trans s16,
        (loadSaved 24 (by decide)).trans s24, (loadSaved 32 (by decide)).trans s32,
        (loadSaved 40 (by decide)).trans s40, (loadSaved 48 (by decide)).trans s48, trivial⟩
    · have same := loadCaller 0 (by decide)
      rw [show sp + (0 : Word) = sp by bv_omega] at same
      exact same.trans fr.retAddr
  · simp only [afterLinear, Atom.All, Atom.Holds, Atom.gpr]
    refine ⟨(result.kept 5 (by decide) (congrArg Value.width rbp)).trans rbp,
      (result.kept 3 (by decide) (congrArg Value.width rbx)).trans rbx, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [show sp - 0x98 = wordAddr (sp - 152) 64 0 by unfold wordAddr; bv_omega]
      exact words 0 (by decide)
    · rw [show sp - 0x90 = wordAddr (sp - 152) 64 1 by unfold wordAddr; bv_omega]
      exact words 1 (by decide)
    · rw [show sp - 0x88 = wordAddr (sp - 152) 64 2 by unfold wordAddr; bv_omega]
      exact words 2 (by decide)
    · rw [show sp - 0x80 = wordAddr (sp - 152) 64 3 by unfold wordAddr; bv_omega]
      exact words 3 (by decide)
    · rw [show sp - 0x78 = wordAddr (sp - 152) 64 4 by unfold wordAddr; bv_omega]
      exact words 4 (by decide)
    · rw [show sp - 0x70 = sp - 152 + 40 by bv_omega]
      exact sign

end K256.Proofs.Generate.Generator.Affine.Invert.Core.ModularShift
