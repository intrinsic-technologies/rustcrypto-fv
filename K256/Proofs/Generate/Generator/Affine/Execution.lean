import K256.Proofs.Generate.Generator.Affine.Normalize
import K256.Proofs.Generate.Generator.Affine.Invert
import K256.Proofs.Generate.Generator.Affine.Products
import K256.Proofs.Generate.Generator.Affine.Select

namespace K256.Proofs.Generate.Generator.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open Standards.SECG.ECC

theorem execution {fr : Activation} {a : Registers} {m : Ram} {point : Curve.Point}
    (s : State .l10fe50 fr a m) (hp : ProjectiveAt m fr.rsi point) (hne : point ≠ .infinity) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10fe50, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store
        (Fn10fe50.doneAt fr) ∧ RamWriteFrame fr.original out.store (writes fr) ∧
      Sec1.Parser.PublicKeyAt out.store fr.rdi point := by
  obtain ⟨x, y, z, xl, yl, zl, wx, wy, wz, rx, ry, rz, rfl⟩ := hp
  have nz : z.val ≠ 0 := fun hz => hne (ite_eq_left hz)
  obtain ⟨_, _, n, sn, cn, hn⟩ := normalizeZ s (x := x) (y := y) (z := z)
    ⟨xl, yl, zl, wx, wy, wz, rx, ry, rz⟩
  obtain ⟨_, _, i, si, ci, hi⟩ := invertZ sn cn hn nz
  obtain ⟨_, _, p, sp, prod⟩ := multiplyCoordinates si ci hi nz
  obtain ⟨out, ret, post⟩ := selectPoint sp prod
  exact ⟨out, Program.Exec.of_sem (((n.trans i).trans p).exec ret.sem), post⟩

end K256.Proofs.Generate.Generator.Affine
