import K256.Proofs.Ecdh.Transfer.Split
import K256.Proofs.Ecdh.Transfer.Sec1
import K256.Spec.Program.Extracted.Image

namespace K256.Proofs.Ecdh.Transfer

open X86.Machine X86.UserProcess K256.Spec.Program K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Generate.Serialize

private def entryAt (p : BitVec 64) : Option LIR.Label :=
  match p.toNat with
  | 0x109e60 => some .l109e60
  | 0x10a280 => some .l10a280
  | 0x10fe50 => some .l10fe50
  | 0x1148d0 => some .l1148d0
  | 0x114930 => some .l114930
  | 0x11c880 => some .l11c880
  | 0x1205b0 => some .l1205b0
  | 0x121480 => some .l121480
  | 0x127d50 => some .l127d50
  | 0x12a820 => some .l12a820
  | _ => none

private theorem entryAt_dst (dst : LIR.Label) :
    entryAt (LIR.address dst) = none ∨ entryAt (LIR.address dst) = some dst := by
  cases dst <;> rename_i l <;> cases l <;> first | exact .inl rfl | exact .inr rfl

set_option maxHeartbeats 600000 in
private theorem entryAt_generate (src : Generate.LIR.Label)
    (entry : Generate.LIR.address src ∈
      [0x109e60, 0x10a280, 0x127d50, 0x11c880, 0x10fe50, 0x114930, 0x1148d0, 0x12a820]) :
    generateTarget src = entryAt (Generate.LIR.address src) ∧ (generateTarget src).isSome = true := by
  cases src <;> rename_i l <;> cases l <;>
    first | exact absurd entry (of_decide_eq_false rfl) | exact ⟨rfl, rfl⟩

set_option maxHeartbeats 600000 in
private theorem entryAt_sec1 (src : Sec1.LIR.Label)
    (entry : Sec1.LIR.address src ∈ [0x121480, 0x1205b0, 0x114930, 0x1148d0, 0x12a820, 0x127d50]) :
    sec1Target src = entryAt (Sec1.LIR.address src) ∧ (sec1Target src).isSome = true := by
  cases src <;> rename_i l <;> cases l <;>
    first | exact absurd entry (of_decide_eq_false rfl) | exact ⟨rfl, rfl⟩

private theorem target_eq {label : Option LIR.Label} {dst : LIR.Label}
    (pos : label.isSome = true) (eq : label = entryAt (LIR.address dst)) :
    label = some dst := by
  rcases entryAt_dst dst with h | h
  · rw [eq, h] at pos
    contradiction
  · exact eq.trans h

theorem generateExec {src : Generate.LIR.Label} {dst : LIR.Label}
    (entry : Generate.LIR.address src ∈
      [0x109e60, 0x10a280, 0x127d50, 0x11c880, 0x10fe50, 0x114930, 0x1148d0, 0x12a820])
    (addr : Generate.LIR.address src = LIR.address dst)
    {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : Generate.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨src,a,m⟩,[]⟩ out) :
    LIR.program.Exec (dialect Extracted.programImage) ⟨⟨dst,a,m⟩,[]⟩ out := by
  obtain ⟨same, pos⟩ := entryAt_generate src entry
  have label := target_eq pos (same.trans (congrArg entryAt addr))
  apply mergedExec
  apply Relabel.exec generateBlocks run
  simp only [Relabel.state, Relabel.location, label, List.map_nil]

theorem sec1Exec {src : Sec1.LIR.Label} {dst : LIR.Label}
    (entry : Sec1.LIR.address src ∈ [0x121480, 0x1205b0, 0x114930, 0x1148d0, 0x12a820, 0x127d50])
    (addr : Sec1.LIR.address src = LIR.address dst)
    {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : Sec1.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨src,a,m⟩,[]⟩ out) :
    LIR.program.Exec (dialect Extracted.programImage) ⟨⟨dst,a,m⟩,[]⟩ out := by
  obtain ⟨same, pos⟩ := entryAt_sec1 src entry
  have label := target_eq pos (same.trans (congrArg entryAt addr))
  apply Relabel.exec sec1Blocks run
  simp only [Relabel.state, Relabel.location, label, List.map_nil]

end K256.Proofs.Ecdh.Transfer
