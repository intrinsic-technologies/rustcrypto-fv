import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.CFG.Simulation

namespace K256.Proofs.Sec1.Parser

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Sec1.LIR

abbrev Reaches (code : CodeMap) (l : Label) (a : Values Value Reg.count) (m : Ram)
    (l' : Label) (b : Values Value Reg.count) (m' : Ram) :=
  (program.sem (dialect code)).Reaches ⟨⟨l, a, m⟩, []⟩ ⟨⟨l', b, m'⟩, []⟩

theorem reaches_jump {code : CodeMap} {l l' : Label} {a b : Values Value Reg.count} {m m' : Ram}
    (h : program.runBlock (dialect code) ⟨l, a, m⟩ = .jump ⟨l', b, m'⟩) :
    Reaches code l a m l' b m' := by
  apply Semantics.Reaches.single
  change (program.runBlock (dialect code) _).next _ [] = _
  rw [h]
  rfl

end K256.Proofs.Sec1.Parser
