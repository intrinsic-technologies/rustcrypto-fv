import K256.Proofs.Generate.Generator.Multiply.Lookup.Choice
import K256.Proofs.Generate.Generator.Multiply.Split.Contract
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.Split.Rounding

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

theorem choice {fr : Activation} {a : Registers} {m : Ram} {flag : BitVec 64}
    (entry : Atom.All Extracted.programImage a m (Fn11b8f0.frameAt .l11badf fr))
    (widths : ParseSignature.ArgumentWidths a)
    (flagReg : a[15] = ⟨64, flag⟩) (flagBit : flag = 0 ∨ flag = 1) :
    ∃ c n, Reaches .l11badf a m .l11bae7 c n ∧
      Atom.All Extracted.programImage c n (Fn11b8f0.frameAt .l11bae7 fr) ∧
      ParseSignature.ArgumentWidths c ∧ c[0].get 8 = flag.setWidth 8 ∧
      c[3] = a[3] ∧ c[12] = a[12] ∧
      RamWriteFrame m n [⟨(fr.rsp - 0xa8).toNat, 16⟩] := by
  simp only [Fn11b8f0.frameAt, Fn11b8f0.frameAtG1, Atom.All, Atom.Holds] at entry ⊢
  obtain ⟨rsp, df, r14, mx, ft, fc, s120, s48, s40, s32, s24, s16, s8,
    readable, ret, retLow, stack, room, align, _⟩ := entry
  let sp := fr.rsp - 0x98
  have hslot : sp - 8 = fr.rsp - 160 := by dsimp only [sp]; bv_omega
  have htmp : sp - 8 - 1 = fr.rsp - 161 := by dsimp only [sp]; bv_omega
  have r4 : a[4].get 64 - 8 = fr.rsp - 160 := by
    exact (congrArg (fun v : Value => v.get 64 - 8) rsp).trans hslot
  have push : StoreOk Extracted.programImage m (fr.rsp - 160) 8 0x11bae2 5 := by
    slot_guard using code_l11badf
  have block : ∃ b : Registers,
      program.runBlock (dialect Extracted.programImage) ⟨.l11badf, a, m⟩ =
        .call ⟨.l127d50, b, memStore m (sp - 8) (0x11bae7 : BitVec 64)⟩
          (callFrame .l11bae7 0x11bae7) ∧
      b[4].get 64 = sp - 8 ∧ b[7] = ⟨64,flag⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [1,2,3,6,8,9,12,14,22,39,50,51] → b[i] = a[i] := by
    refine ⟨?_, ?run, ?post⟩
    case run =>
      arithmetic_segment using code_l11badf [flagReg, r4, hslot, push]
    case post =>
      refine ⟨?_, ?_, ?_⟩
      · rw [hslot]
        rfl
      · rcases flagBit with rfl | rfl <;> rfl
      · rintro ⟨i, hi⟩ hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨b, call, brsp, bflag, bkeep⟩ := block
  have tmp : Writable Extracted.programImage m (fr.rsp - 161) 1 := by slot_state region
  have slot : Readable m (fr.rsp - 160) 8 := by slot_state region
  obtain ⟨c, n, reach, crsp, cflag, post, ckeep⟩ := Lookup.resumeChoice call brsp
    (htmp.symm ▸ tmp) (hslot.symm ▸ slot) (by decide)
  rw [htmp, hslot] at post
  have offset (off : BitVec 64) (h : off.toNat ≤ 224) :
      (fr.rsp - off).toNat = fr.rsp.toNat - off.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have s168Nat : (fr.rsp - 168).toNat = fr.rsp.toNat - 168 := offset 168 (by decide)
  have s161Nat : (fr.rsp - 161).toNat = fr.rsp.toNat - 161 := offset 161 (by decide)
  have s160Nat : (fr.rsp - 160).toNat = fr.rsp.toNat - 160 := offset 160 (by decide)
  have high := readable.low
  let area : MemoryRegion := ⟨(fr.rsp - 168).toNat, 16⟩
  have pushed : RamWriteFrame m (memStore m (fr.rsp - 160) (0x11bae7 : BitVec 64)) [area] := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨area, List.mem_singleton_self _, ?_⟩
    simp only [area, InRegion, s168Nat, s160Nat, Nat.reduceDiv]
    omega
  have frame : RamWriteFrame m n [area] := by
    apply pushed.trans post
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨area, List.mem_singleton_self _, ?_, ?_⟩ <;>
      simp only [area, s168Nat, s161Nat] <;> omega
  have same (off : BitVec 64) (h : off.toNat ≤ 120) :
      memLoad n (fr.rsp - off) 64 = memLoad m (fr.rsp - off) 64 := by
    apply frame.memLoad_eq
    simp only [Outside, area, s168Nat, offset off (by omega), Nat.reduceDiv, List.mem_singleton]
    refine ⟨by omega, fun r hr => Or.inr ?_⟩
    subst r
    change fr.rsp.toNat - 168 + 16 ≤ fr.rsp.toNat - off.toNat
    omega
  have retSame : memLoad n fr.rsp 64 = memLoad m fr.rsp 64 := by
    simpa only [show fr.rsp - (0 : BitVec 64) = fr.rsp by bv_omega] using same 0 (by decide)
  have keep (i : Fin Reg.count) (hi : i.val ∈ [1,2,3,6,8,9,12,14,22,39,50,51]) :
      c[i] = a[i] :=
    (ckeep i (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      omega)).trans (bkeep i hi)
  have outWidths : ParseSignature.ArgumentWidths c := by
    rintro ⟨i, hi⟩ hm
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact congrArg Value.width ((ckeep ⟨7, hi⟩ (by decide +revert)).trans bflag)
      | rw [keep ⟨_, hi⟩ (by decide +revert)]; exact widths ⟨_, hi⟩ (by decide +revert)
  have outFlag : c[0].get 8 = flag.setWidth 8 := by
    rw [cflag, bflag]
    rcases flagBit with rfl | rfl <;> rfl
  refine ⟨c,n,reach,?_,outWidths,outFlag,keep 3 (by decide),keep 12 (by decide),frame⟩
  exact ⟨crsp, (keep 22 (by decide)).trans df, (keep 14 (by decide)).trans r14,
    (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft, (keep 51 (by decide)).trans fc,
    (same 120 (by decide)).trans s120, (same 48 (by decide)).trans s48,
    (same 40 (by decide)).trans s40, (same 32 (by decide)).trans s32,
    (same 24 (by decide)).trans s24, (same 16 (by decide)).trans s16, (same 8 (by decide)).trans s8,
    readable.of_frame frame, retSame.trans ret, retLow, stack.of_frame frame, room, align, trivial⟩

end K256.Proofs.Generate.Generator.Multiply.Split.Rounding
