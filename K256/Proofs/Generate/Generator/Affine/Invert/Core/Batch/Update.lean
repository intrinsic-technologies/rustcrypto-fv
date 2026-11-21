import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.Linear
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.Modular
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Update.Copy

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open SafeGcd.Batch (Words)

variable {a b : Registers} {m p : Ram} {sp : Word} {z : Fin modulus} {w : Vector Word 4}

theorem update (h : Entry a m sp z w) {j : Nat} (hj : j < 10) {d e : Int}
    (state : LoopState a m sp z (roundsBefore j) b p d e) {c : Registers} {q : Ram}
    {s : Words} (rows : Rows c q sp s) (kept : Controls b c)
    (frame : RamWriteFrame p q (setupWrites sp))
    (shift : memLoad q (base sp + 116) 32 = BitVec.ofNat 32 (count j))
    (rem : memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j))
    (delta : s.delta.toInt = (Core.model z (roundsBefore (j+1))).delta)
    (rep : (SafeGcd.Batch.matrix s).Represents ((2:Int)^count j)
      (Core.model z (roundsBefore j)).f (Core.model z (roundsBefore j)).g (Core.model z (roundsBefore (j+1))))
    (bound : (SafeGcd.Batch.matrix s).Bounded (2^count j)) :
    ∃ c' q' d' e', Reaches .l108f97 c q (batchLabel (j+1)) c' q' ∧
      LoopState a m sp z (roundsBefore (j+1)) c' q' d' e' := by
  obtain ⟨cl, ml, el, linear⟩ := linearRows h hj state rows kept frame shift rem rep
  obtain ⟨cm, mm, d', e', em, modular, db, eb, dc, ec⟩ := modularRows h hj state linear bound
  obtain ⟨last, mem, tail, post⟩ := copyRows h hj state modular delta db eb
    (rowInvariant state.dInvariant state.eInvariant rep.1 dc)
    (rowInvariant state.dInvariant state.eInvariant rep.2 ec)
  exact ⟨last, mem, d', e', (el.trans em).trans tail, post⟩

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
