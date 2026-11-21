import K256.Proofs.Verify.Core.Affine.Memory
import K256.Proofs.Verify.Core.Affine.Products.Input
import K256.Proofs.Generate.Generator.Affine.Products.Barrier.Call
import K256.Proofs.Generate.Generator.Affine.Products.Frame
import K256.Proofs.Generate.Serialize.Transfer.Blocks
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Affine

open Ecdh.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator.Affine
open Standards.SECG.ECC

theorem loadEcdhInverse {fr : Activation} {a : Registers} {m : Ram} {x y z : Fin modulus}
    (s : CallState .l10ed84 fr a m) (h : Coordinates m fr.rsi x y z) (hi : InverseAt fr m z) :
    ∃ b m', Reaches .l10ed84 a m .l10eda1 b m' ∧ CallState .l10eda1 fr b m' ∧
      Coordinates m' fr.rsi x y z ∧ LoadedInverse b z := by
  obtain ⟨rsp, df, bx, _, _, _, r14, _, mx, ft, fc, rest⟩ := s.atoms
  have before : Atom.All Extracted.programImage a m (Fn10fe50.frameAt .l10eda1 fr) :=
    ⟨rsp, df, bx, r14, mx, ft, fc, rest⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, win, room, _⟩ := rest
  change Writable Extracted.programImage m (fr.rsp - 976) 976 at win
  change fr.low.toNat + 976 ≤ fr.rsp.toNat at room
  let sp := fr.rsp - 232
  let slot := sp - 8
  let mem := memStore m slot (0x10eda1 : Word)
  have slotAddr : slot = fr.rsp + (0 - 240) := by dsimp [slot, sp]; bv_omega
  have byteAddr : slot - 1 = fr.rsp + (0 - 241) := by rw [slotAddr]; bv_omega
  have window : Writable Extracted.programImage m slot 136 :=
    win.of_offsets slotAddr (addr_sub fr.rsp 976) (by decide)
  have writable : Writable Extracted.programImage mem (slot - 1) 1 :=
    (win.of_offsets byteAddr (addr_sub fr.rsp 976) (by decide)).memStore _ _
  have readSlot : Readable mem slot 8 :=
    (window.readable.sub (a := slot) (Nat.le_refl _) (by omega)).memStore _ _
  have ret : memLoad mem slot 64 = 0x10eda1 := by
    refine_norm [mem]
  obtain ⟨b, call, bs, arg, b15, b12, b13, b5, bk⟩ := inverseCall rsp window
  obtain ⟨out, blk, tag, afterSP, flag, childFrame, kept⟩ := Sec1.Serialize.choiceBlock
    (fun v hv => Common.fnCode_subset_programImage v (Sec1.LIR.code_l127d50 v hv))
    (show b[4].get 64 = slot by rw [bs]; rfl) writable readSlot (by rw [ret]; decide)
  have sec : Sec1.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50, b, mem⟩, []⟩ out :=
    .done (by simp only [Program.step, blk, Transfer.next])
  have run : program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50, b, mem⟩, []⟩ out :=
    Generate.Serialize.Relabel.exec Generate.Serialize.matches_blocks sec rfl
  have reach : Reaches .l10ed84 a m .l10eda1 out.values out.store := by
    refine .step (b := ⟨⟨.l127d50, b, mem⟩, [inverseReturn]⟩) ?_ ?_
    · simp only [Program.sem, Program.step, call, Transfer.next, mem, slot, sp]
    · exact ParseSignature.exec_reaches_resume run inverseReturn [] (by rw [tag, ret]; rfl)
  let areas : List MemoryRegion := [⟨slot.toNat, 8⟩, ⟨(slot - 1).toNat, 1⟩]
  have f : RamWriteFrame m mem areas := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, ?_⟩
    have := window.readable.low
    change slot.toNat + 8 ≤ 2^64
    store_disch
  have writes := f.trans childFrame (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)
  have bounds : ProductScratch fr areas := by
    have hs : slot.toNat = fr.rsp.toNat - 240 := by
      rw [show slot = fr.rsp - 240 by rw [slotAddr]; bv_omega,
        BitVec.toNat_sub_of_le (by change 240 ≤ fr.rsp.toNat; omega)]
      rfl
    have hb : (slot - 1).toNat = slot.toNat - 1 := by
      rw [BitVec.toNat_sub_of_le (by change 1 ≤ slot.toNat; omega)]
      rfl
    intro r hr
    simp only [areas, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only <;> omega
  have resume : CallState .l10eda1 fr out.values out.store := by
    apply s.afterProductScratch before rfl writes bounds
    intro i hi
    rw [List.mem_cons] at hi
    rcases hi with h | others
    · have e : i = 4 := Fin.ext h
      subst i
      exact afterSP.trans ((congrArg (fun v : Word => (⟨64, v⟩ : Value))
        (show slot + 8 = sp by dsimp only [slot]; bv_omega)).trans rsp.symm)
    · have hk : i.val ∈ [3,14,22,39,50,51] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at others ⊢
        grind
      have hk' : i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        grind
      exact (kept i hk').trans (bk i hk)
  obtain ⟨bit, inv⟩ := hi
  let words : Vector Word 4 := Vector.ofFn fun i =>
    memLoad m (fr.rsp - 144 + BitVec.ofNat 64 (8*i.val)) 64
  have ww (i : Nat) (hi : i < 4) :
      memLoad m (fr.rsp - 144 + BitVec.ofNat 64 (8*i)) 64 = words[i] := by
    simp [words]
  have val (hz : z.val ≠ 0) := inv hz
  refine ⟨_, _, reach, resume, coordinatesAfterScratch h writes bounds s.srcAddr s.high, ⟨?_, ?_⟩⟩
  · have read (i : Nat) (hi : i < 4) :
        memLoad m (sp + BitVec.ofNat 64 (88 + 8*i)) 64 = words[i] := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc,
        show sp + BitVec.ofNat 64 88 = fr.rsp - 144 by dsimp only [sp]; bv_omega]
      exact ww i hi
    refine ⟨words, ?_, ?_, ?_, ?_, ?_⟩
    · exact (kept 15 (by decide)).trans (b15.trans (congrArg (Value.mk 64) (read 0 (by decide))))
    · exact (kept 12 (by decide)).trans (b12.trans (congrArg (Value.mk 64) (read 1 (by decide))))
    · exact (kept 13 (by decide)).trans (b13.trans (congrArg (Value.mk 64) (read 2 (by decide))))
    · exact (kept 5 (by decide)).trans (b5.trans (congrArg (Value.mk 64) (read 3 (by decide))))
    · intro nz
      obtain ⟨t, stored, eq, _⟩ := val nz
      have same : words = t := Vector.ext fun i h =>
        (ww i h).symm.trans (stored i h)
      rwa [same]
  · rw [flag, arg]
    have low : (memLoad m (sp + 120) 32).setWidth 8 = (choiceBit z).setWidth 8 := by
      rw [show sp + 120 = fr.rsp - 112 by dsimp only [sp]; bv_omega,
        BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 32)]
      simpa only [Nat.reduceDiv, BitVec.add_zero, bit] using
        extractLsb'_memLoad m (fr.rsp - 112) (n := 32) 0 8 (by decide) (by decide) (by decide)
    change (⟨64, (((memLoad m (sp + 120) 32).setWidth 64).setWidth 8).setWidth 64⟩ : Value) = _
    rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64), low]
    by_cases hz : z.val = 0 <;> simp [choiceBit, hz]

end K256.Proofs.Verify.Core.Affine
