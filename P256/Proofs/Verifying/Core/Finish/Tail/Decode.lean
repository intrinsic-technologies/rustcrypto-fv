import P256.Proofs.Verifying.Core.Finish.Tail.SetupRun
import P256.Proofs.Verifying.Core.Finish.Tail.Read

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

set_option maxRecDepth 2048 in
theorem decode [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x r : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10e098)
    (input : x < 2^256 ∧ (⟨(frameBase s+392).toNat,32⟩ : MemoryRegion).HasBytes t.external
      (Standards.SECG.ECC.Encoding.natToOctets 32 x))
    (saved : Nat256At t (frameBase s+704) r) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10e116 ∧
      memLoad u.external (frameBase s+384) 64 = memLoad t.external (frameBase s+384) 64 ∧ Nat256At u (frameBase s) x ∧
      Nat256At u (frameBase s+704) r := by
  obtain ⟨m,b,runB,stateB,eB,bytesB⟩ := setup pre state rip
  have bxB : memLoad b.external (frameBase s+384) 64 = memLoad t.external (frameBase s+384) 64 := by
    apply memLoad_congr (n := 64)
    intro i hi
    change (b.external[_]?).getD 0 = (t.external[_]?).getD 0
    congr 1
    have h := bytesB (384+i) (by omega) (Or.inl (by omega)) (by omega)
    simpa only [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using h
  have source : b.regValue .rdi = frameBase s+392 :=
    eB.writes.2.2.2.2.2.2.2.1.trans (congrArg (·+392) state.rsp)
  have dest : b.regValue .rdx = frameBase s := by
    have h : b.regValue .rdx = stackPtr t+0 := eB.writes.2.2.2.2.2.2.2.2.1
    change b.regValue .rdx = stackPtr t+0#64 at h
    rw [BitVec.add_zero] at h
    exact h.trans state.rsp
  have octets : (⟨(frameBase s+392).toNat,32⟩ : MemoryRegion).HasBytes b.external
      (Standards.SECG.ECC.Encoding.natToOctets 32 x) := by
    refine ⟨input.2.1,fun i => ?_⟩
    have hi : i.val < 32 := by
      simpa only [SecretKeyFromBytes.Encoding.natToOctets_size] using i.isLt
    have h := input.2.2 i
    change b.external[BitVec.ofNat 64 ((frameBase s+392).toNat+i.val)]? = _
    change t.external[BitVec.ofNat 64 ((frameBase s+392).toNat+i.val)]? = _ at h
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] at h ⊢
    have hb := bytesB (392+i.val) (by omega) (Or.inl (by omega)) (by omega)
    simp only [BitVec.ofNat_add,← BitVec.add_assoc] at hb
    exact hb.trans h
  have scalar : Nat256At b (frameBase s+704) r := by
    refine ⟨saved.1,fun i hi => ?_⟩
    have hb := bytesB (704+i) (by omega) (Or.inr (by omega)) (by omega)
    simp only [BitVec.ofNat_add,← BitVec.add_assoc] at hb
    exact hb.trans (saved.2 i hi)
  obtain ⟨k,u,runU,stateU,ripU,bxU,xU,rU⟩ := read pre stateB eB.rip source dest
    eB.writes.2.2.2.2.2.2.2.2.2.1 eB.writes.2.2.2.2.2.2.2.2.2.2.1
    eB.writes.2.2.2.2.2.2.2.2.2.2.2 input.1 octets scalar
  exact ⟨m+k,u,runB.trans runU,stateU,ripU,bxU.trans bxB,xU,rU⟩

end P256.Proofs.Verifying.Core.Finish.Tail
