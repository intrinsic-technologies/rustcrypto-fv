import K256.Proofs.Generate.Generator.Multiply.Caller.Execution
import K256.Proofs.Generate.Generator.Multiply.Return
import K256.Spec.Program
import K256.Proofs.Generate.Curve
import K256.Proofs.Generate.Generator.Affine.Repr
import K256.Proofs.Generate.LIR.Fn10ee80.Frame

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters

theorem execution {fr : Activation} {a : Values Value Reg.count} {d : Nat}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (high : fr.rsp.toNat + 352 ≤ 2^32)
    (src : fr.rsi = fr.rsp + 8) (dst : fr.rdi = fr.rsp + 232)
    (source : Readable fr.original fr.rsi 32)
    (destination : Writable Extracted.programImage fr.original fr.rdi 120)
    (words : WordsAt fr.original fr.rsi 64
      (Vector.ofFn fun i : Fin 4 => BitVec.ofNat 64 (d / 2^(64*i.val))))
    (pos : 0 < d) (bound : d < Secp256k1.domain.n) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10ee80, a, fr.original⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage out.values out.store (Fn10ee80.doneAt fr) ∧
      (∀ i : Fin Reg.count, i.val ∈ [1,2,8,9] → out.values[i].width = 64) ∧
      RamWriteFrame fr.original out.store [fr.region, ⟨fr.rdi.toNat, 120⟩] ∧
      Affine.ProjectiveAt out.store fr.rdi (Curve.generatorWindow d) := by
  obtain ⟨b, m, path, ready, widths, frame, point⟩ :=
    caller (@coreExecution) atoms image room low high src dst source destination words pos bound
  obtain ⟨out, run, tag, store, done_, _, kept⟩ := returnBlock fr b m ready
  have last : program.Exec (dialect Extracted.programImage) ⟨⟨.l10f12f, b, m⟩, []⟩ out :=
    .done (by simp only [Program.step, run, Transfer.next])
  refine ⟨out, Program.Exec.of_sem (path.exec last.sem), tag, store ▸ done_, ?_, store ▸ frame, store ▸ point⟩
  intro i hi
  have arg : i.val ∈ Activation.argumentNumbers := by
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega
  rw [kept i arg]
  exact widths i hi

end K256.Proofs.Generate.Generator.Multiply
