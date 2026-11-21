import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare
import P256.Proofs.Field.Inverse.SafeGcd.Core.Update
import P256.Proofs.Field.Inverse.SafeGcd.Core.Prefix.Routine

namespace P256.Proofs.Field.Inverse.SafeGcd.Core

open Shared (batchCount nextState)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

namespace Loop

theorem run_stopped (fuel : Nat) (p : Inputs) (s : LoopState) (h : s.remaining = 0) :
    runBatches fuel p s = s := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [runBatches, h, ite_true]

theorem step [Bindings] (last : Bool) {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111f1a)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hpos : 1 ≤ s.remaining) (hbound : s.remaining ≤ 591)
    (hlast : if last then s.remaining = batchCount s else batchCount s < s.remaining)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1179fa initial).arguments
      initial.external (loopAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = Machine.lifted.address (Update.Finish.exit last) ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf (Update.Finish.exit last) final).arguments final.external
        (Update.Finish.finishAtoms last fr controls p (nextState p s)) := by
  obtain ⟨n1, s1, e1, ready1, rip1, frame1, atoms1⟩ :=
    Prepare.run_batch hcode hready hrip hframe hout hpos hbound hcore
  obtain ⟨n2, s2, e2, ready2, rip2, frame2, atoms2⟩ :=
    Update.advances hcode ready1 rip1 frame1 hout hpos hbound atoms1
  obtain ⟨n3, s3, e3, ready3, rip3, frame3, atoms3⟩ :=
    Update.Finish.advances last hcode ready2 rip2 frame2 hout hlast atoms2
  exact ⟨n1+n2+n3, s3, (e1.trans e2).trans e3, ready3, rip3, frame3, atoms3⟩

set_option maxRecDepth 2048 in
set_option maxHeartbeats 600000 in
theorem iterate [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code) (batches : Nat)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111f1a)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code) (hpos : 1 ≤ s.remaining) (hbound : s.remaining ≤ 591)
    (hbudget : s.remaining ≤ 62 * batches)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1179fa initial).arguments
      initial.external (loopAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x112108 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l117be8 final).arguments final.external
        (Update.Finish.haltAtoms fr controls p (runBatches batches p s)) := by
  induction batches generalizing initial s with
  | zero => omega
  | succ batches ih =>
    have hactive : s.remaining ≠ 0 := by omega
    have hcount : batchCount s = min s.remaining 62 := rfl
    by_cases hlast : s.remaining = batchCount s
    · obtain ⟨n1, s1, e1, ready1, rip1, frame1, atoms1⟩ :=
        step true hcode hready hrip hframe hout hpos hbound hlast hcore
      refine ⟨n1, s1, e1, ready1, rip1, frame1, ?_⟩
      have hdone : (nextState p s).remaining = 0 := by
        change s.remaining - batchCount s = 0
        omega
      simp only [runBatches, hactive, ite_false, run_stopped batches p (nextState p s) hdone]
      exact atoms1
    · have hlt : batchCount s < s.remaining := by omega
      obtain ⟨n1, s1, e1, ready1, rip1, frame1, atoms1⟩ :=
        step false hcode hready hrip hframe hout hpos hbound hlt hcore
      have hp' : 1 ≤ (nextState p s).remaining := by
        change 1 ≤ s.remaining - batchCount s
        omega
      have hb' : (nextState p s).remaining ≤ 591 := by
        change s.remaining - batchCount s ≤ 591
        omega
      have hn' : (nextState p s).remaining ≤ 62 * batches := by
        change s.remaining - batchCount s ≤ 62 * batches
        rw [Nat.mul_succ] at hbudget
        omega
      obtain ⟨n2, s2, e2, ready2, rip2, frame2, atoms2⟩ :=
        ih ready1 rip1 frame1 hp' hb' hn' atoms1
      refine ⟨n1+n2, s2, e1.trans e2, ready2, rip2, frame2, ?_⟩
      simp only [runBatches, hactive, ite_false]
      exact atoms2

theorem initialized [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111b70)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l117650 initial).arguments
      initial.external (Prefix.atoms .entry fr controls p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x112108 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l117be8 final).arguments final.external
        (Update.Finish.haltAtoms fr controls p (finalState p)) := by
  obtain ⟨n1, s1, e1, ready1, rip1, frame1, atoms1⟩ :=
    Prefix.advances hcode hready hrip hframe hout hcore
  obtain ⟨n2, s2, e2, ready2, rip2, frame2, atoms2⟩ :=
    iterate hcode 10 ready1 rip1 frame1 hout (by change 1 ≤ 591; decide) (by change 591 ≤ 591; decide)
      (by change 591 ≤ 62 * 10; decide) atoms1
  exact ⟨n1+n2, s2, e1.trans e2, ready2, rip2, frame2, atoms2⟩

end Loop

end P256.Proofs.Field.Inverse.SafeGcd.Core
