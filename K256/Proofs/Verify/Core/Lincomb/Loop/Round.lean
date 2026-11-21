import K256.Proofs.Verify.Core.Lincomb.Loop.StartColumn
import K256.Proofs.Verify.Core.Lincomb.Loop.Step
import K256.Proofs.Verify.Core.Lincomb.Loop.Advance
import K256.Proofs.Verify.Core.Lincomb.Loop.BackEdge

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

theorem round {a b : Registers} {m n : Ram} {sp dst dataPtr : BitVec 64}
    {p : Curve.Point} {u v k : Nat} (entry : RoutineEntry a m sp 0x478)
    (hu : u < domain.n) (hv : v < domain.n) (hp : Curve.onCurve domain p)
    (nonzero : dataPtr ≠ 0) (tableRead : Readable m dataPtr 0x1340)
    (dataApart : Outside [scratch sp 0x478, ⟨dst.toNat, 120⟩] dataPtr 0x1340)
    (generator : Prepared m dataPtr (dataPtr + 0x780) domain.G u)
    (peer : Prepared m (dataPtr + 0x9a0) (dataPtr + 0x1120) p v)
    (bound : k < 129) (state : RoundState a m sp dst dataPtr (combinationBases p u v)
      (fun i => Naf.digits (combinationScalars u v i)) (k+1) b n) :
    ∃ c store, Reaches .l110278 b n (if k = 0 then .l11075a else .l110278) c store ∧
      RoundState a m sp dst dataPtr (combinationBases p u v)
        (fun i => Naf.digits (combinationScalars u v i)) k c store := by
  let bases := combinationBases p u v
  let ds (j) := Naf.digits (combinationScalars u v j)
  let plus (q : Curve.Point) (j : Fin 4) := Curve.add domain q (selectDigit (bases j) ((ds j)[k]?.getD 0))
  have step (j : Fin 4) {q c store} (s : Column a m sp dst dataPtr k q c store)
      (cur : Cursor sp dataPtr j (j.val%2) c store) :
      ∃ b' n', Reaches .l11034e c store (if j.val = 3 then .l110260 else .l11034e) b' n' ∧
        Column a m sp dst dataPtr k (plus q j) b' n' ∧
        ∀ h : j.val + 1 < 4, Cursor sp dataPtr ⟨j.val+1,h⟩ ((j.val+1)%2) b' n' := by
    obtain ⟨c',store',run,s',cur'⟩ := applyDigit j entry hu hv hp tableRead dataApart generator peer bound s cur
    obtain ⟨b',n',next,s'',cur''⟩ := advance j entry nonzero tableRead s' cur'
    exact ⟨b',n',run.trans next,s'',cur''⟩
  obtain ⟨_,_,beginRun,s,cur⟩ := startColumn entry bound nonzero tableRead state
  obtain ⟨_,_,run0,s0,c0⟩ := step 0 s cur
  obtain ⟨_,_,run1,s1,c1⟩ := step 1 s0 (c0 (by decide))
  obtain ⟨_,_,run2,s2,c2⟩ := step 2 s1 (c1 (by decide))
  obtain ⟨_,_,run3,s3,_⟩ := step 3 s2 (c2 (by decide))
  have done := suffix_succ (bases := bases) (ds := ds) bound
  change suffix bases ds k = plus (plus (plus (plus _ 0) 1) 2) 3 at done
  rw [← done] at s3
  obtain ⟨c,back,s'⟩ := backEdge entry s3.toSavedFrame (congrArg (Value.get 64) s3.counter)
    (by omega) s3.last s3.back s3.savedFront s3.savedNext s3.savedBack s3.point s3.inactive
  exact ⟨c,_,beginRun.trans (run0.trans (run1.trans (run2.trans (run3.trans back)))),s'⟩

end K256.Proofs.Verify.Core.Lincomb.Loop
