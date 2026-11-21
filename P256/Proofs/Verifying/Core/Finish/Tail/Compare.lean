import P256.Proofs.Verifying.Core.Finish.Tail.ArgumentsRun
import P256.Proofs.Verifying.Core.Finish.Tail.EqualCall
import P256.Proofs.Verifying.Core.Digest.Finish.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

theorem compare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x r : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10e116)
    (input : Nat256At t (frameBase s) x)
    (scalar : Nat256At t (frameBase s+704) r) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10e16c ∧
      memLoad u.external (frameBase s+384) 64 = memLoad t.external (frameBase s+384) 64 ∧
      (u.regValue .rax).setWidth 8 = if x % Operations.domain.n == r then 1 else 0 := by
  obtain ⟨n,a,runA,stateA,eA,xA,_⟩ := Digest.Finish.copy pre state 0xe116
    (by decide) (by decide +kernel) rip input
  have rA := Digest.Finish.copy_slot (offset := 704) state.rsp eA (by decide) (by decide) scalar
  have bxA : memLoad a.external (frameBase s+384) 64 = memLoad t.external (frameBase s+384) 64 := by
    apply memLoad_congr (n := 64)
    intro i hi
    change (a.external[_]?).getD 0 = (t.external[_]?).getD 0
    congr 1
    apply eA.agrees.byte
    intro c hc ha
    simp only [Digest.Finish.CopyBlock.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨j,hj,eq⟩ := ha
    all_goals change _ = stackPtr t+_+_ at eq
    all_goals rw [state.rsp] at eq
    all_goals change _ = frameBase s+_+_ at eq
    all_goals bv_omega
  obtain ⟨m,b,runB,stateB,eB⟩ := reduce_arguments pre stateA eA.rip
  have memB : b.external = a.external := eB.agrees.external
    (by simp [reduceArgumentEffect,Effect.components,Component.Covers])
  have xB : Nat256At b (frameBase s+128) x :=
    ⟨xA.1,fun i hi => by rw [memB]; exact xA.2 i hi⟩
  have rB : Nat256At b (frameBase s+704) r :=
    ⟨rA.1,fun i hi => by rw [memB]; exact rA.2 i hi⟩
  have siB : b.regValue .rsi = frameBase s+128 :=
    eB.writes.2.1.trans (congrArg (·+128) stateA.rsp)
  have diB : b.regValue .rdi = frameBase s := eB.writes.2.2.trans stateA.rsp
  have rbxB : b.regValue .rbx = frameBase s := eB.writes.1.trans stateA.rsp
  obtain ⟨k,c,runC,stateC,ripC,regsC,xC,bytesC,_⟩ := reduce_call pre stateB eB.rip siB diB xB
  have rC : Nat256At c (frameBase s+704) r := by
    refine ⟨rB.1,fun i hi => ?_⟩
    have addr : frameBase s+704 = stackPtr s-472#64 := by
      simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr,bytesC 472 32 (by decide) (by decide) (Or.inl (by decide)) i hi,← addr]
    exact rB.2 i hi
  obtain ⟨l,d,runD,stateD,eD⟩ := equal_arguments pre stateC ripC
  have memD : d.external = c.external := eD.agrees.external
    (by simp [equalArgumentEffect,Effect.components,Component.Covers])
  have xD : Nat256At d (frameBase s) (x % Operations.domain.n) :=
    ⟨xC.1,fun i hi => by rw [memD]; exact xC.2 i hi⟩
  have rD : Nat256At d (frameBase s+704) r :=
    ⟨rC.1,fun i hi => by rw [memD]; exact rC.2 i hi⟩
  have siD : d.regValue .rsi = frameBase s :=
    eD.writes.2.trans ((regsC .rbx (by simp)).trans rbxB)
  have diD : d.regValue .rdi = frameBase s+704 :=
    eD.writes.1.trans (congrArg (·+704) stateC.rsp)
  obtain ⟨j,u,runU,stateU,ripU,bxU,result⟩ := equal_call pre stateD eD.rip siD diD xD rD
  refine ⟨n+m+k+l+j,u,(((runA.trans runB).trans runC).trans runD).trans runU,
    stateU,ripU,?_,result⟩
  apply bxU.trans
  rw [memD]
  apply Eq.trans _ bxA
  rw [← memB]
  have addr : frameBase s+384 = stackPtr s-792#64 := by
    simp only [frameBase,BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  rw [addr]
  apply memLoad_congr (n := 64)
  intro i hi
  change (c.external[_]?).getD 0 = (b.external[_]?).getD 0
  rw [bytesC 792 8 (by decide) (by decide) (Or.inl (by decide)) i hi]

end P256.Proofs.Verifying.Core.Finish.Tail
