import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Update.Linear
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Update.Modular
import K256.Proofs.Verify.Core.Scalars.Inverse.Batch.Update.Copy

namespace K256.Proofs.Verify.Core.Scalars.Inverse.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords)
open Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult signedAt)

open Generate.Generator.Affine.Invert
open SafeGcd.Batch (Words)

theorem update (shift : ModularShift) {a b c : Registers} {m p q : Ram} {sp : Word}
    {s n : Nat} {d e : Int} {w : Words} (h : Entry a m sp s)
    (state : LoopState a m sp s n b p d e) (more : n < 591)
    (rows : Rows c w) (rsp : c[4] = b[4]) (k : c[9].get 32 = BitVec.ofNat 32 (count n))
    (controls : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i])
    (frame : RamWriteFrame p q (setupWrites sp))
    (remaining : memLoad q (base sp + 336) 64 = BitVec.ofNat 64 (591-n))
    (delta : w.delta.toInt = (Inverse.model s (n+count n)).delta)
    (rep : (SafeGcd.Batch.matrix w).Represents ((2:Int)^(count n)) (Inverse.model s n).f
      (Inverse.model s n).g (Inverse.model s (n+count n)))
    (bound : (SafeGcd.Batch.matrix w).Bounded (2^(count n))) :
    ∃ c' q' d' e',
      Reaches .l1095c1 c q (if n+count n = 591 then .l109948 else .l1097fe) c' q' ∧
        LoopState a m sp s (n+count n) c' q' d' e' := by
  obtain ⟨cl, ml, el, linear⟩ := linearRows h state more rows rsp k controls frame remaining rep
  obtain ⟨cm, mm, d', e', em, modular, db, eb, dc, ec⟩ := modularRows shift h state more linear bound
  obtain ⟨last, mem, tail, post⟩ := copyRows h state more modular delta db eb
    (coefficient_update _ state.dInvariant state.eInvariant rep.1 dc)
    (coefficient_update _ state.dInvariant state.eInvariant rep.2 ec)
  exact ⟨last, mem, d', e', (el.trans em).trans tail, post⟩

end K256.Proofs.Verify.Core.Scalars.Inverse.Batch
