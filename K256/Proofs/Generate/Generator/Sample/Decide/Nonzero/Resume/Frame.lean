import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Flag
import K256.Proofs.Generate.Generator.Sample.Calls
import K256.Proofs.Generate.LIR.Fn10a280.Frame

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

def preservedValue (fr : Activation) (j : Nat) : Value :=
  if j = 22 then ⟨1, 0⟩ else fr.entryValue j

def compareChild (base : Activation) (a : Registers) (m : Ram) (tag : BitVec 64) : Activation :=
  ParseSignature.withArguments {base with original := m, ret := tag} a

theorem sampleChildEntry {base : Activation} {a : Registers} {m : Ram} {tag : BitVec 64}
    (info : FrameInfo) (empty : info.callSlots = []) (pos : 0 < info.window)
    (sp : a[4] = ⟨64, base.rsp⟩)
    (keep : ∀ j : Fin Reg.count, j.val ∈ nonzeroPreserved → a[j] = preservedValue base j.val)
    (widths : ParseSignature.ArgumentWidths a)
    (rd : Readable m base.rsp 8) (ret : memLoad m base.rsp 64 = tag) (small : tag.toNat < 2^32)
    (wr : Writable Extracted.programImage m (base.rsp - BitVec.ofNat 64 info.window) info.window)
    (room : base.low.toNat + info.window ≤ base.rsp.toNat) (align : base.rsp.toNat % 16 = 8) :
    Atom.All Extracted.programImage a m (info.entryAtoms (compareChild base a m tag)) := by
  simp only [FrameInfo.entryAtoms, FrameInfo.frameAtoms, FrameInfo.entryFrame, FrameInfo.entryRegs,
    FrameInfo.stackAtoms, FrameInfo.callSlotAtoms, empty, Activation.below, ↓reduceIte,
    Nat.ne_of_gt pos, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Atom.All, Atom.Holds]
  refine ⟨sp, keep 22 (by decide), ?_, ?_, keep 3 (by decide), keep 5 (by decide),
    ?_, ?_, ?_, ?_, keep 12 (by decide), keep 13 (by decide), keep 14 (by decide),
    keep 15 (by decide), keep 39 (by decide), keep 50 (by decide), keep 51 (by decide),
    rd, ret, small, wr, room, align, trivial⟩
  all_goals exact ParseSignature.entryArgument widths _ _ (by decide)

theorem sampleChildReturn {base : Activation} {a : Registers} {m : Ram} {tag : BitVec 64}
    {out : Output Value Ram Reg.count}
    (done : Atom.All Extracted.programImage out.values out.store
      (Fn127d50.doneAt (compareChild base a m tag))) :
    out.values[4] = ⟨64, base.rsp + 8⟩ ∧
    ∀ j : Fin Reg.count, j.val ∈ nonzeroPreserved → out.values[j] = preservedValue base j.val := by
  simp only [Fn127d50.doneAt, Atom.All, Atom.Holds] at done
  obtain ⟨sp, df, bx, bp, r12, r13, r14, r15, mx, ft, fc, _⟩ := done
  refine ⟨sp, ?_⟩
  intro ⟨j, hj⟩ h
  simp only [nonzeroPreserved, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact bx | exact bp | exact r12 | exact r13 | exact r14 | exact r15 | exact df | exact mx | exact ft | exact fc

end K256.Proofs.Generate.Generator.Sample
