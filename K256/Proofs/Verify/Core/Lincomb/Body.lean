import K256.Proofs.Verify.Core.Lincomb.GeneratorPath
import K256.Proofs.Verify.Core.Lincomb.PeerPath
import K256.Proofs.Verify.Core.Lincomb.AccumulationPath
import K256.Proofs.Verify.Core.Lincomb.Return

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Affine (ProjectiveAt)

theorem execute {fr : Activation} {a b c : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram} (e : Entry fr a p digest r s) (h : Products fr b m u v r)
    (args : Arguments fr b c) (hu : u < domain.n) (hv : v < domain.n) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10fb20, c, push m fr⟩, []⟩ out ∧
      out.tag = some ⟨64, 0x10526c⟩ ∧ out.values[4] = ⟨64, localSp fr⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = c[i]) ∧
      RamWriteFrame m out.store (writes fr) ∧
      ProjectiveAt out.store (localSp fr + 8)
        (wnafAccumulator (combinationBases p u v) 129 (fun i => Naf.digits (combinationScalars u v i))) := by
  obtain ⟨d, n, first, frame₁, gen⟩ := generatorPath e h args hu
  obtain ⟨f, t, second, frame₂, peer⟩ := peerPath e h args hv frame₁ gen
  obtain ⟨g, z, third, frame₃, point⟩ := accumulationPath e h args hu hv frame₂ peer
  obtain ⟨out, block, mem, tag, sp, keep⟩ :=
    finish e frame₃ (h.frame.trans frame₃.frame (frameBounds e).1)
  have tail : program.Exec (dialect Extracted.programImage) ⟨⟨.l10fca6,g,z⟩,[]⟩ out := by
    apply Program.Exec.of_sem
    exact .ret (by simp only [Program.sem, Program.step, block, Transfer.next])
  exact ⟨out, Program.Exec.of_sem (((first.trans second).trans third).exec tail.sem),
    tag, sp, keep, mem ▸ frame₃.frame, mem ▸ point⟩

end K256.Proofs.Verify.Core.Lincomb
