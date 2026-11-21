import P256.Proofs.Ecdh.Initial.Prefix
import P256.Proofs.Ecdh.Initial.Select
import P256.Proofs.Ecdh.Initial.Copy

set_option autoImplicit false

namespace P256.Proofs.Ecdh

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Standards.SECG.ECC

theorem initial_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {point : Curve.Point}
    (pre : Pre s boundary) (peer : Sec1.AffineAt s (s.regValue .rdx) point) :
    ∃ fuel t, Advances boundary fuel s t ∧ Initial s t point := by
  obtain ⟨a,t,runT,copied⟩ := Initial.prefix_correct pre peer
  obtain ⟨b,u,runU,selected⟩ := Initial.select_correct pre copied
  obtain ⟨c,v,runV,initial⟩ := Initial.copy_correct pre selected
  exact ⟨a+b+c,v,(runT.trans runU).trans runV,initial⟩

end P256.Proofs.Ecdh
