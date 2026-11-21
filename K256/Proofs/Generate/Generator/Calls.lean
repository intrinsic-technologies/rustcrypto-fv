import K256.Proofs.Generate.Generator.Entry
import K256.Proofs.Common.Lift.Generated.Values.Load

namespace K256.Proofs.Generate.Generator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

abbrev ScalarWords := Vector (BitVec 64) 4

def multiplyMemory (m : Ram) (sp : BitVec 64) (w : ScalarWords) : Ram :=
  let m := memStore m (sp + 24) w[3]
  let m := memStore m (sp + 16) w[2]
  let m := memStore m (sp + 8) w[1]
  let m := memStore m sp w[0]
  memStore m (sp - 8) (0x1060b7 : BitVec 64)

theorem multiplyCall {a : Vector Value 53} {m : Ram} {sp : BitVec 64} {w : ScalarWords}
    (rsp : a[4].get 64 = sp) (win : Writable Extracted.programImage m (sp - 8) 80)
    (words : WordsAt m (sp + 40) 64 w) :
    ∃ b : Vector Value 53,
      program.runBlock (dialect Extracted.programImage) ⟨.l10607d, a, m⟩ = .call
        ⟨.l10ee80, b, multiplyMemory m sp w⟩ (callFrame .l1060b7 0x1060b7) ∧
      b[0] = ⟨64, w[0]⟩ ∧ b[1] = ⟨64, w[1]⟩ ∧ b[4] = ⟨64, sp - 8⟩ ∧
      b[6] = ⟨64, sp⟩ ∧ b[7] = ⟨64, sp + 224⟩ ∧ b[14] = ⟨64, sp + 224⟩ ∧
      ∀ i : Fin 53, i.val ∈ [2, 3, 5, 8, 9, 12, 13, 15, 22, 39, 50, 51] → b[i] = a[i] := by
  let m1 := memStore m (sp + 24) w[3]
  let m2 := memStore m1 (sp + 16) w[2]
  let m3 := memStore m2 (sp + 8) w[1]
  let m4 := memStore m3 sp w[0]
  have win1 := win.memStore (sp + 24) w[3]
  have win2 := win1.memStore (sp + 16) w[2]
  have win3 := win2.memStore (sp + 8) w[1]
  have win4 := win3.memStore sp w[0]
  have incl := fun x hx => Common.fnCode_subset_programImage x (code_l10607d x hx)
  have v0 : memLoad m (sp + 40) 64 = w[0] := by
    rw [← show wordAddr (sp + 40) 64 0 = sp + 40 by unfold wordAddr; bv_omega]
    exact words 0 (by decide)
  have v1 : memLoad m (sp + 48) 64 = w[1] := by
    rw [← show wordAddr (sp + 40) 64 1 = sp + 48 by unfold wordAddr; bv_omega]
    exact words 1 (by decide)
  have v2 : memLoad m (sp + 56) 64 = w[2] := by
    rw [← show wordAddr (sp + 40) 64 2 = sp + 56 by unfold wordAddr; bv_omega]
    exact words 2 (by decide)
  have v3 : memLoad m (sp + 64) 64 = w[3] := by
    rw [← show wordAddr (sp + 40) 64 3 = sp + 64 by unfold wordAddr; bv_omega]
    exact words 3 (by decide)
  have r3 : LoadOk m (sp + 64) 8 := LoadOk.of_offsets win.readable rfl (addr_sub sp 8) (by decide)
  have r2 : LoadOk m1 (sp + 56) 8 := LoadOk.of_offsets win1.readable rfl (addr_sub sp 8) (by decide)
  have q2 : memLoad m1 (sp + 56) 64 = w[2] := by
    dsimp only [m1]
    repeat' rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by decide))]
    exact v2
  have r0 : LoadOk m2 (sp + 40) 8 := LoadOk.of_offsets win2.readable rfl (addr_sub sp 8) (by decide)
  have q0 : memLoad m2 (sp + 40) 64 = w[0] := by
    dsimp only [m2, m1]
    repeat' rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by decide))]
    exact v0
  have r1 : LoadOk m2 (sp + 48) 8 := LoadOk.of_offsets win2.readable rfl (addr_sub sp 8) (by decide)
  have q1 : memLoad m2 (sp + 48) 64 = w[1] := by
    dsimp only [m2, m1]
    repeat' rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl (by decide))]
    exact v1
  have g0 : StoreOk Extracted.programImage m (sp + 24) 8 0x106082 5 :=
    ParseSignature.storeOk_of_codeRange (off := 5) (win.of_offsets rfl (addr_sub sp 8) (by decide)) incl (by decide)
  have g1 : StoreOk Extracted.programImage m1 (sp + 16) 8 0x10608c 5 :=
    ParseSignature.storeOk_of_codeRange (off := 15) (win1.of_offsets rfl (addr_sub sp 8) (by decide)) incl (by decide)
  have g2 : StoreOk Extracted.programImage m2 (sp + 8) 8 0x10609b 5 :=
    ParseSignature.storeOk_of_codeRange (off := 30) (win2.of_offsets rfl (addr_sub sp 8) (by decide)) incl (by decide)
  have g3 : StoreOk Extracted.programImage m3 sp 8 0x1060a0 4 :=
    ParseSignature.storeOk_of_codeRange (off := 35) (win3.of_offsets (addr_self sp) (addr_sub sp 8) (by decide)) incl (by decide)
  have g4 : StoreOk Extracted.programImage m4 (sp - 8) 8 0x1060b2 5 :=
    ParseSignature.storeOk_of_codeRange (off := 53) (win4.of_offsets (addr_sub sp 8) (addr_sub sp 8) (by decide)) incl (by decide)
  dsimp only [m1, m2, m3, m4] at r2 r0 r1 g1 g2 g3 g4 q2 q0 q1
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp]
    simp only [r3, v3, g0, r2, q2, g1, r0, q0, r1, q1, g2, g3, g4, ↓reduceIte]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem affineCall {a : Vector Value 53} {m : Ram} {sp : BitVec 64} (rsp : a[4].get 64 = sp)
    (src : a[14].get 64 = sp + 224) (w : Writable Extracted.programImage m (sp - 8) 8) :
    ∃ b : Vector Value 53, program.runBlock (dialect Extracted.programImage) ⟨.l1060b7, a, m⟩ =
      .call ⟨.l10fe50, b, memStore m (sp - 8) (0x1060c7 : BitVec 64)⟩ (callFrame .l1060c7 0x1060c7) ∧
      b[4] = ⟨64, sp - 8⟩ ∧ b[6] = ⟨64, sp + 224⟩ ∧ b[7] = ⟨64, sp + 136⟩ ∧
      ∀ i : Fin 53, i.val ∈ [1,2,3,5,8,9,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  have guard : StoreOk Extracted.programImage m (sp - 8) 8 0x1060c2 5 :=
    ParseSignature.storeOk_of_codeRange (off := 11) w
      (fun x hx => Common.fnCode_subset_programImage x (code_l1060b7 x hx)) (by decide)
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, src, guard]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_⟩
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Generate.Generator
