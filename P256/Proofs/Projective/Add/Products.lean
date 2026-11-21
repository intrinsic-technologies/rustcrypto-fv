import P256.Proofs.Projective.Add.Products.X
import P256.Proofs.Projective.Add.Products.Y
import P256.Proofs.Projective.Add.Products.Z

set_option autoImplicit false

namespace P256.Proofs.Projective.Add

open P256.Spec.Program.Routines P256.Proofs.Program P256.Proofs.Program.ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem products_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {left right : Projective} (pre : CalleePre s boundary 0x1051f0 96 96 920)
    (leftAt : ProjectiveAt s (s.regValue .rdi) left)
    (rightAt : ProjectiveAt s (s.regValue .rsi) right) :
    ∃ fuel t, Advances boundary fuel s t ∧ FrameState s t 96 920 632 ∧
      t.RIP = 0x10531f ∧ ProductsAt s t left right := by
  obtain ⟨nx, x, runX, stateX, ripX, leftX, rightX, bxX, r14X, xx⟩ :=
    x_product pre leftAt rightAt
  obtain ⟨ny, y, runY, stateY, ripY, leftY, rightY, bxY, r14Y, xxY, yy⟩ :=
    y_product pre stateX ripX leftX rightX bxX r14X xx
  obtain ⟨nz, z, runZ, stateZ, ripZ, products⟩ :=
    z_product pre stateY ripY leftY rightY bxY r14Y xxY yy
  exact ⟨nx + ny + nz, z, (runX.trans runY).trans runZ, stateZ, ripZ, products⟩

end P256.Proofs.Projective.Add
