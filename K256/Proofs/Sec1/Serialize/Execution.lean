import K256.Proofs.Sec1.Serialize.Contract
import K256.Proofs.Sec1.Serialize.Coordinates.Schedule
import K256.Proofs.Sec1.Serialize.Assemble.Execution
import K256.Proofs.Sec1.Serialize.SelectionReturn

namespace K256.Proofs.Sec1.Serialize

open K256.Spec.Program X86 X86.UserProcess K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR
open Prelude X86.Machine X86Proofs K256.Proofs.Common
open Standards.SECG.ECC Standards.SECG.DomainParameters

private theorem uncompressedTag {mem : Ram} {dst : BitVec 64} {x y : Nat}
    (h : (⟨dst.toNat, 65⟩ : MemoryRegion).HasBytes mem
      (Points.encodePoint Secp256k1.domain false (.affine x y))) :
    memLoad mem dst 8 = 4 := by
  let head : ByteArray := ⟨#[4]⟩
  let xs := Encoding.natToOctets 32 x
  let ys := Encoding.natToOctets 32 y
  change (⟨dst.toNat, 65⟩ : MemoryRegion).HasBytes mem (head ++ xs ++ ys) at h
  have len : (head ++ xs ++ ys).size = 65 := h.1
  have h0 := h.2 ⟨0, by omega⟩
  have hh : 0 < head.size := by decide
  have hx : 0 < (head ++ xs).size := by rw [ByteArray.size_append]; omega
  have first : mem[dst]? = some 4 := by
    simp only [Nat.add_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ByteArray.getElem_append_left hx, ByteArray.getElem_append_left hh] at h0
    exact h0
  apply Bytes.memLoad _ (by decide) (by decide)
  intro i hi
  obtain rfl : i = 0 := by change i < 1 at hi; omega
  rw [show dst + BitVec.ofNat 64 0 = dst from BitVec.add_zero _]
  exact first

theorem serializerExecution : SerializerExecution := by
  intro args mem sp src dst ret point rsp rsi rdi compress df width pointAt source dest
    window retSlot retLow align room destAbove pointAbove gotRead gotTarget
  obtain ⟨x, y, rfl, xl, yl, xWords, yWords, finite, xRepr, yRepr⟩ := pointAt
  let base := sp - 312
  have sub (i : Nat) (hi : i ≤ 448) :
      (sp - BitVec.ofNat 64 i).toNat = sp.toNat - i := by
    have hn : (BitVec.ofNat 64 i).toNat = i := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hn]; omega), hn]
  have baseNat : base.toNat = sp.toNat - 312 := sub 312 (by decide)
  have startNat : (sp - 448).toNat = sp.toNat - 448 := sub 448 (by decide)
  have fAddr : base - 121 = sp - 433 := by change sp - 312 - 121 = _; rw [BitVec.sub_sub]; rfl
  have fNat : (base - 121).toNat = sp.toNat - 433 := by rw [fAddr]; exact sub 433 (by decide)
  have sAddr : base - 9 = sp - 321 := by change sp - 312 - 9 = _; rw [BitVec.sub_sub]; rfl
  have sNat : (base - 9).toNat = sp.toNat - 321 := by rw [sAddr]; exact sub 321 (by decide)
  have entry : base + 312 = sp := BitVec.sub_add_cancel _ _
  have after : base + 320 = sp + 8 := by
    rw [show (320 : BitVec 64) = 312 + 8 by rfl, ← BitVec.add_assoc, entry]
  have fwin : Writable Extracted.programImage mem (base - 121) 433 := window.sub (by omega) (by omega)
  have swin : Writable Extracted.programImage mem (base - 9) 329 := window.sub (by omega) (by omega)
  have textApart : base.toNat + 312 ≤ 0x100000 ∨ 0x12a9bf ≤ (base - 121).toNat := by
    have := writable_text_apart fwin (by decide)
    omega
  have cover := Common.fnCode_subset_programImage
  obtain ⟨c, m, coords, cut⟩ := Coordinates.schedule (base := base) (point := src) (dest := dst) cover
    (by rw [entry, rsp] <;> rfl) (by rw [rsi] <;> rfl) (by rw [rdi] <;> rfl) compress df
    (width 12 (by decide)) (width 13 (by decide)) fwin source (by omega) textApart
    (by omega) xWords yWords
  obtain ⟨b, t, assembly, encoding, zero, bSp, bDst, bKept, assembled⟩ :=
    Assemble.uncompressedExecution cover cut.rsp cut.rbx cut.r14 (by rw [cut.rbp]; rfl)
      cut.packedX cut.packedY xRepr yRepr (cut.finite.trans finite)
      (source.of_frame cut.frame) ((swin.sub (Nat.le_refl _) (by omega)).of_frame cut.frame)
      (by omega) (by omega)
  let internal : List MemoryRegion := [⟨(sp - 448).toNat, 448⟩]
  have internalFrame : RamWriteFrame mem t internal := by
    refine ((RamWriteFrame.refl mem _).trans cut.frame ?_).trans assembled ?_ <;>
      intro r hr <;> obtain rfl := List.mem_singleton.mp hr <;> refine ⟨_, List.mem_cons_self .., ?_⟩
    · change (sp - 448).toNat ≤ (base - 121).toNat ∧ (base - 121).toNat + 433 ≤ (sp - 448).toNat + 448
      omega
    · change (sp - 448).toNat ≤ (base - 9).toNat ∧ (base - 9).toNat + 289 ≤ (sp - 448).toNat + 448
      omega
  have gotT : memLoad t 0x203dd0 64 = 0x12a820 := by
    rw [← gotTarget]
    apply internalFrame.memLoad_eq
    refine ⟨by decide, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    have := writable_copy_slot_apart window (by decide)
    change 0x203dd0 + 8 ≤ (sp - 448).toNat ∨ (sp - 448).toNat + 448 ≤ 0x203dd0
    omega
  have lowMem := window.readable.low
  have saved (i : Nat) (lo : 280 ≤ i) (hi : i ≤ 312) :
      memLoad t (base + BitVec.ofNat 64 i) 64 = memLoad m (base + BitVec.ofNat 64 i) 64 := by
    have addr : (base + BitVec.ofNat 64 i).toNat = base.toNat + i := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    apply assembled.memLoad_eq
    refine ⟨by change _ + 8 ≤ 2^64; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact Or.inr (by change (base - 9).toNat + 289 ≤ _; omega)
  have restored : memLoad t (base + 312) 64 = ret :=
    (saved 312 (by decide) (by decide)).trans (cut.slot.trans (by rwa [entry]))
  have keeps (i : Fin Reg.count) (hi : i.val ∈ [12,13,22,39,50,51]) : b[i] = args[i] :=
    (bKept i hi).trans (cut.kept i hi)
  obtain ⟨out, finish, tag, outSp, bx, r14, r15, bp, rest, wf, output⟩ :=
    selectAndReturn (sp := base) (dst := dst) bSp bDst zero (congrArg (Value.get 1) ((keeps 22 (by decide)).trans df))
      (swin.of_frame internalFrame) (by omega) (by omega) (dest.of_frame internalFrame)
      ⟨gotRead.1, fun i hi => internalFrame.present _ (gotRead.2 i hi)⟩ gotT
      (by rw [restored]; exact retLow) encoding
  have cm (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15]) :
      (⟨64, args[i].get 64⟩ : Value) = args[i] := (Coordinates.canonicalValue (width i hi)).symm
  have reg (i : Nat) (r : Fin Reg.count) (lo : 280 ≤ i) (hi : i ≤ 312)
      (hr : r.val ∈ [3,5,12,13,14,15])
      (pop : out.values[r] = ⟨64, memLoad t (base + BitVec.ofNat 64 i) 64⟩)
      (push : memLoad m (base + BitVec.ofNat 64 i) 64 = args[r].get 64) :
      out.values[r] = args[r] :=
    pop.trans ((congrArg (fun v => (⟨64,v⟩ : Value)) ((saved i lo hi).trans push)).trans (cm r hr))
  refine ⟨out, Program.Exec.of_sem ((coords.trans assembly).exec finish.sem),
    tag.trans (congrArg (fun v => some (⟨64,v⟩ : Value)) restored),
    outSp.trans (congrArg (fun v => (⟨64,v⟩ : Value)) after), ?_, ?_, uncompressedTag output, output⟩
  · intro r hr
    rcases r with ⟨r, bound⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact reg 280 3 (by decide) (by decide) (by decide) bx cut.saved.rbx
    · exact reg 304 5 (by decide) (by decide) (by decide) bp cut.saved.rbp
    · exact (rest 12 (by decide)).trans (keeps 12 (by decide))
    · exact (rest 13 (by decide)).trans (keeps 13 (by decide))
    · exact reg 288 14 (by decide) (by decide) (by decide) r14 cut.saved.r14
    · exact reg 296 15 (by decide) (by decide) (by decide) r15 cut.saved.r15
    · exact (rest 22 (by decide)).trans (keeps 22 (by decide))
    · exact (rest 39 (by decide)).trans (keeps 39 (by decide))
    · exact (rest 50 (by decide)).trans (keeps 50 (by decide))
    · exact (rest 51 (by decide)).trans (keeps 51 (by decide))
  · refine ((RamWriteFrame.refl mem _).trans internalFrame ?_).trans wf ?_
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | ht
      · refine ⟨_, List.mem_cons_self .., ?_⟩
        change (sp - 448).toNat ≤ (base - 9).toNat ∧ (base - 9).toNat + 289 ≤ (sp - 448).toNat + 448
        omega
      · obtain rfl := List.mem_singleton.mp ht
        exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), Nat.le_refl _, Nat.le_refl _⟩

end K256.Proofs.Sec1.Serialize
