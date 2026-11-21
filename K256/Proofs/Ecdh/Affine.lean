import K256.Proofs.Ecdh.Affine.Normalize
import K256.Proofs.Ecdh.Affine.Inverse
import K256.Proofs.Ecdh.Affine.Products
import K256.Proofs.Ecdh.Affine.Select

namespace K256.Proofs.Ecdh.Affine

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open K256.Proofs.Generate.Generator.Affine
open Standards.SECG.ECC

theorem execution {fr : Activation} {a : Registers} {m : Ram} {point : Curve.Point}
    (s : CallState .l10fe50 fr a m) (h : ProjectiveAt m fr.rsi point) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10fe50, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store
        (Fn10fe50.doneAt fr) ∧ RamWriteFrame fr.original out.store (writes fr) ∧
      XAt out.store fr.rdi point := by
  obtain ⟨x, y, z, xl, yl, zl, wx, wy, wz, rx, ry, rz, rfl⟩ := h
  obtain ⟨_, _, n, sn, cn, hn⟩ := normalizeExecution s (x := x) (y := y) (z := z)
    ⟨xl, yl, zl, wx, wy, wz, rx, ry, rz⟩
  obtain ⟨_, _, i, si, ci, hi⟩ := inverseExecution sn cn hn
  obtain ⟨_, _, p, sp, hp⟩ := productsExecution si ci hi
  obtain ⟨out, ret, post⟩ := selectionExecution sp hp
  exact ⟨out, Program.Exec.of_sem (((n.trans i).trans p).exec ret.sem), post⟩

end K256.Proofs.Ecdh.Affine
