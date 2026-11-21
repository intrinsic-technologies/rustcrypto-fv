import K256.Proofs.Verify.Core.Lincomb.Loop.Initialize
import K256.Proofs.Verify.Core.Lincomb.Loop.Round
import K256.Proofs.Verify.Core.Lincomb.Loop.Return

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

theorem accumulate {a : Registers} {m : Ram} {sp dst iterator dataPtr : BitVec 64}
    {p : Curve.Point} {u v : Nat} (entry : RoutineEntry a m sp 0x478)
    (di : a[7].get 64 = dst) (si : a[6].get 64 = iterator)
    (hu : u < domain.n) (hv : v < domain.n) (hp : Curve.onCurve domain p)
    (first : memLoad m iterator 64 = dataPtr)
    (last : memLoad m (iterator + 8) 64 = dataPtr + 0x1340)
    (unset : memLoad m (iterator + 16) 64 = 0 ∧ memLoad m (iterator + 64) 64 = 0)
    (nonzero : dataPtr ≠ 0)
    (iterRead : Readable m iterator 112) (tableRead : Readable m dataPtr 0x1340)
    (write : Writable Extracted.programImage m dst 120)
    (iterApart : Outside [scratch sp 0x478, ⟨dst.toNat, 120⟩] iterator 112)
    (dataApart : Outside [scratch sp 0x478, ⟨dst.toNat, 120⟩] dataPtr 0x1340)
    (dest : Outside [scratch sp 0x478, ⟨sp.toNat, 8⟩] dst 120)
    (generator : Prepared m dataPtr (dataPtr + 0x780) domain.G u)
    (peer : Prepared m (dataPtr + 0x9a0) (dataPtr + 0x1120) p v) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1100a0, a, m⟩, []⟩ out ∧
      RoutineReturn a m sp 0x478 [⟨dst.toNat, 120⟩] out ∧
      Generate.Generator.Affine.ProjectiveAt out.store dst
        (wnafAccumulator (combinationBases p u v) 129 (fun i => Naf.digits (combinationScalars u v i))) := by
  let bases := combinationBases p u v
  let ds := fun i => Naf.digits (combinationScalars u v i)
  obtain ⟨k, b, n, small, start, state⟩ := Loop.startRounds entry di si hu hv hp first last unset
    nonzero iterRead tableRead iterApart dataApart generator peer
  suffices finish : ∀ j (h : j < 129) (c : Registers) (store : Ram),
      Loop.RoundState a m sp dst dataPtr bases ds (j+1) c store →
      ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l110278,c,store⟩,[]⟩ out ∧
        RoutineReturn a m sp 0x478 [⟨dst.toNat,120⟩] out ∧
        Generate.Generator.Affine.ProjectiveAt out.store dst (wnafAccumulator bases 129 ds) by
    obtain ⟨out, exec, post⟩ := finish k small b n state
    exact ⟨out, Program.Exec.of_sem (start.exec exec.sem), post⟩
  intro j
  induction j with
  | zero =>
    intro h c store st
    obtain ⟨d, n', step, st'⟩ := Loop.round entry hu hv hp nonzero tableRead dataApart
      generator peer h st
    obtain ⟨q, atQ, _, value⟩ := st'.point
    obtain ⟨out, doneRun, ret, stored⟩ := Loop.finish entry st'.toSavedFrame write dest atQ
    refine ⟨out, Program.Exec.of_sem (step.exec doneRun.sem), ret, ?_⟩
    change q.value = wnafAccumulator bases 129 ds at value
    rw [← value]
    exact stored.projectiveAt
  | succ j ih =>
    intro h c store st
    obtain ⟨d, n', step, st'⟩ := Loop.round entry hu hv hp nonzero tableRead dataApart
      generator peer h st
    obtain ⟨out, doneRun, post⟩ := ih (by omega) d n' st'
    exact ⟨out, Program.Exec.of_sem (step.exec doneRun.sem), post⟩

end K256.Proofs.Verify.Core.Lincomb
