import K256.Proofs.Sec1.Serialize.Coordinates.PackCall
import K256.Proofs.Sec1.Serialize.Normalize.Execution

namespace K256.Proofs.Sec1.Serialize.Coordinates

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Common.Field

def normalizeWrites (base : Word) : List MemoryRegion :=
  [⟨(base - 121).toNat, 113⟩, ⟨(base + 80).toNat, 40⟩]

theorem stackOffsets {base : Word} (lo : (base - 121).toNat + 433 ≤ 2^32) :
    (base - 121).toNat + 121 = base.toNat ∧ (base - 8).toNat + 8 = base.toNat ∧
    ∀ i : Nat, i ≤ 312 → (base + BitVec.ofNat 64 i).toNat = base.toNat + i := by
  have hb := toNat_of_offsets (n := 1) (addr_self base) (addr_sub base 121) lo (by decide)
  rw [show ((0 : Word) - (0 - 121)).toNat = 121 by decide] at hb
  have hs := toNat_of_offsets (n := 8) (addr_sub base 8) (addr_sub base 121) lo (by decide)
  rw [show ((0 - 8 : Word) - (0 - 121)).toNat = 113 by decide] at hs
  refine ⟨hb.symm, by omega, ?_⟩
  intro i hi
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem normalize {code : CodeMap} {args : Values Value Reg.count} {m : Ram}
    {base ret : Word} {a : Limbs} (rsp : args[4] = ⟨64, base - 8⟩)
    (src : args[6] = ⟨64, base + 8⟩) (dst : args[7] = ⟨64, base + 80⟩)
    (df : args[22] = ⟨1, 0⟩)
    (saved : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] →
      args[i] = ⟨64, args[i].get 64⟩)
    (win : Writable code m (base - 121) 433) (aligned : base.toNat % 16 = 0)
    (textApart : base.toNat + 312 ≤ 0x100000 ∨ 0x12a9bf ≤ (base - 121).toNat)
    (retLow : ret.toNat < 2^32) (slot : memLoad m (base - 8) 64 = ret)
    (words : WordsAt m (base + 8) 64 a) :
    ∃ out, program.Exec (dialect code) ⟨⟨.l114930, args, m⟩, []⟩ out ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, base⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = args[i]) ∧
      RamWriteFrame m out.store (normalizeWrites base) ∧
      WordsAt out.store (base + 80) 64 (Normalize.normalize a) := by
  let c : Normalize.Ctx := ⟨base + 8, base + 80, args[39], args[50], args[51]⟩
  let fr : Activation := {
    original := m, rsp := base - 8, low := base - 121, ret := ret
    rbx := args[3].get 64, rbp := args[5].get 64, r12 := args[12].get 64
    r13 := args[13].get 64, r14 := args[14].get 64, r15 := args[15].get 64
    rsi := base + 8, rdi := base + 80, rdx := 0, rcx := 0, r8 := 0, r9 := 0
    mxcsr := 0, ftw := 0, fcw := 0, fs := default }
  let initialDst : Limbs := Vector.ofFn fun i => memLoad m (wordAddr c.dst 64 i.val) 64
  have hdw : WordsAt m c.dst 64 initialDst := by
    intro i hi
    simp only [initialDst, Vector.getElem_ofFn]
  obtain ⟨hbase, hslot, offset⟩ := stackOffsets win.readable.low
  have hsp : (base - 8).toNat = (base - 121).toNat + 113 := by omega
  have hsrc : (base + 8).toNat = base.toNat + 8 := offset 8 (by decide)
  have hdst : (base + 80).toNat = base.toNat + 80 := offset 80 (by decide)
  have hw : Writable code m ((base - 8) - 113) 113 := by
    rw [BitVec.sub_sub, show (8 : Word) + 113 = 121 by decide]
    exact win.sub (Nat.le_refl _) (by omega)
  have entry : Atom.All code args m
      (Normalize.frameAt .l114930 fr ++ Normalize.core.atoms .entry c fr ⟨c.dst, a, initialDst⟩) := by
    rw [Normalize.frameAt_114930, Atom.all_append]
    constructor
    · exact ⟨rsp, df, saved 3 (by decide), saved 5 (by decide), src, dst,
        saved 12 (by decide), saved 13 (by decide), saved 14 (by decide), saved 15 (by decide),
        win.readable.of_offsets (addr_sub base 8) (addr_sub base 121) (by decide), slot, retLow, hw,
        Nat.le_of_eq hsp.symm, by change (base - 8).toNat % 16 = 8; omega, trivial⟩
    · refine ⟨src, dst, rfl, rfl, rfl, rfl, words,
        win.readable.of_offsets rfl (addr_sub _ _) (by decide), hdw,
        win.of_offsets rfl (addr_sub _ _) (by decide), ?_, Or.inr ?_, Or.inr ?_, Or.inr ?_, ?_, ?_, trivial⟩
      all_goals dsimp only [Atom.Holds, c, fr]
      all_goals omega
  obtain ⟨out, run, tag, atoms, frame⟩ := Normalize.normalizeExecution c fr a initialDst args m
    entry (RamWriteFrame.refl _ _)
  rw [Normalize.doneAt_eq] at atoms
  obtain ⟨r4,r22,r3,r5,r12,r13,r14,r15,r39,r50,r51,_,_,result,_⟩ := atoms
  have same (i : Fin Reg.count) (hi : i.val ∈ [3,5,12,13,14,15,22,39,50,51]) :
      out.values[i] = args[i] := by
    rcases i with ⟨i, hi'⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact Eq.trans r3 (saved 3 (by decide)).symm
    · exact Eq.trans r5 (saved 5 (by decide)).symm
    · exact Eq.trans r12 (saved 12 (by decide)).symm
    · exact Eq.trans r13 (saved 13 (by decide)).symm
    · exact Eq.trans r14 (saved 14 (by decide)).symm
    · exact Eq.trans r15 (saved 15 (by decide)).symm
    · exact Eq.trans r22 df.symm
    · exact r39
    · exact r50
    · exact r51
  refine ⟨out, run, tag, ?_, same, ?_, result⟩
  · change out.values[4] = ⟨64, (base - 8) + 8⟩ at r4
    simpa only [BitVec.sub_add_cancel] using r4
  · change RamWriteFrame m out.store
      [⟨(base - 121).toNat, (base - 8).toNat - (base - 121).toNat⟩, ⟨(base + 80).toNat, 40⟩] at frame
    rwa [hsp, Nat.add_sub_cancel_left] at frame

end K256.Proofs.Sec1.Serialize.Coordinates
