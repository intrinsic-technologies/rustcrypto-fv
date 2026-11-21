import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Generate.Serialize.Transfer.Labels
import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Sec1.LIR.Program

namespace K256.Proofs.Generate.Serialize

theorem matches_blocks (a : Sec1.LIR.Label) (b : LIR.Label) (h : sharedTarget a = some b) :
    Relabel.block sharedTarget (Sec1.LIR.program.blocks a) = Relabel.block some (LIR.program.blocks b) := by
  cases a <;> rename_i l <;> cases l <;> cases h <;> rfl

end K256.Proofs.Generate.Serialize
