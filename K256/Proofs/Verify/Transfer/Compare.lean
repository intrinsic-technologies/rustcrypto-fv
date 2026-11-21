import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Verify.LIR.Program

namespace K256.Proofs.Verify.Transfer

open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Generate.Serialize

def compareTarget : Generate.LIR.Label → Option LIR.Label
  | .l10a280 => some .l10a280
  | .l10a293 => some .l10a293
  | .l127d50 => some .l127d50
  | .l127f50 => some .l127f50
  | .l127f55 => some .l127f55
  | .l127f5a => some .l127f5a
  | .l127f70 => some .l127f70
  | .l127f8a => some .l127f8a
  | .l127f9a => some .l127f9a
  | .l127fa9 => some .l127fa9
  | _ => none

private theorem compareBlocks (a : Generate.LIR.Label) (b : LIR.Label)
    (h : compareTarget a = some b) :
    Relabel.block compareTarget (Generate.LIR.program.blocks a) =
      Relabel.block some (LIR.program.blocks b) := by
  unfold compareTarget at h
  split at h <;> cases h <;> rfl

theorem compareExec {src : Generate.LIR.Label} {dst : LIR.Label}
    (label : compareTarget src = some dst)
    {V S : Type} {d : Dialect Op V S} {a : Values V Reg.count}
    {m : S} {out : Output V S Reg.count}
    (run : Generate.LIR.program.Exec d ⟨⟨src, a, m⟩, []⟩ out) :
    LIR.program.Exec d ⟨⟨dst, a, m⟩, []⟩ out := by
  apply Relabel.exec compareBlocks run
  simp only [Relabel.state, Relabel.location, label, List.map_nil]

end K256.Proofs.Verify.Transfer
