import K256.Proofs.Generate.Generator.Sample.Loop
import K256.Proofs.Generate.Generator.CopyFrame

namespace K256.Proofs.Generate

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Standards.SECG.ECC
  Standards.SECG.DomainParameters

theorem generate {initial : RamState} {random : ByteArray}
    (call : ValidCall signingKeyGenerateFromRng initial [random]) :
    ∃ args mem d point, Run.Reaches ⟨LIR.lifted.locationOf .l102510 initial, []⟩
      ⟨⟨.l102539, args, mem⟩, []⟩ ∧ KeyReady initial random args mem d point := by
  let stack := [Generator.callFrame .l102539 0x102539]
  have start : Run.Reaches ⟨LIR.lifted.locationOf .l102510 initial, []⟩
      ⟨⟨.l105f30, Generator.entryArgs initial, Generator.entryMemory initial⟩, stack⟩ := by
    apply Semantics.Reaches.single
    change LIR.program.step _ _ = _
    simp only [Program.step, Generator.entry call, Transfer.next, stack]
  obtain ⟨a, m, d, sampled, draw, accepted⟩ :=
    Generator.Sample.sample call (Generator.sampleEntry call) stack
  obtain ⟨b, n, calls, copyReady⟩ := Generator.copyReady_of_calls
    Generator.Multiply.execution Generator.Affine.execution call draw accepted
  obtain ⟨c, o, copied, result⟩ := copySigningKey call copyReady
  exact ⟨c, o, d, _, start.trans (sampled.trans (calls.trans copied)), result⟩

end K256.Proofs.Generate
