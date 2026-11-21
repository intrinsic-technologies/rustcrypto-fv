import P256.Proofs.Signing.Wrapper.Entry.Construct.Tail
import P256.Proofs.Signing.Wrapper.Entry.Construct.PointCall

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar

theorem correct : ConstructContract := by
  intro bindings initial s secret message ctx decoded
  obtain ⟨na,a,runA,sa,ea⟩ := arguments ctx decoded.toState decoded.rip
  have memory := ea.agrees.external (by simp [Arguments.effect,Effect.components,Component.Covers])
  have inputA : Nat256At a (stackPtr initial-344) (Ecdsa.secretValue secret) :=
    ⟨decoded.input.1,fun i hi => by rw [memory]; exact decoded.input.2 i hi⟩
  have scalarA : Nat256At a (stackPtr initial-520) (Ecdsa.secretValue secret) :=
    ⟨decoded.scalar.1,fun i hi => by rw [memory]; exact decoded.scalar.2 i hi⟩
  have di : a.regValue .rdi=stackPtr initial-424 :=
    (show a.regValue .rdi=stackPtr s+96 from ea.writes.1).trans
      (address decoded.toState (off := 96) (by decide))
  have si : a.regValue .rsi=stackPtr initial-344 :=
    (show a.regValue .rsi=stackPtr s+176 from ea.writes.2).trans
      (address decoded.toState (off := 176) (by decide))
  obtain ⟨nb,b,runB,sb,ipb,scalarB,regsB,slotsB⟩ :=
    point_call ctx sa ea.rip di si inputA scalarA
  have scalarB' : Nat256At b (stackPtr b+0) (Ecdsa.secretValue secret) := by
    simpa [sb.rsp] using scalarB
  obtain ⟨nc,c,runC,sc,ipc,scalarC,gc,slotsC⟩ := copy ctx sb ipb scalarB'
  have countA : a.regValue .r13=2 :=
    (ea.agrees.read (n := 64) (r := 13) (by simp [Arguments.effect,Effect.components])).trans decoded.count
  have countC : c.regValue .r13=2 :=
    (gc.read (n := 64) (r := 13) (by simp [ScalarFrame.Copy32.components])).trans
      ((regsB .r13 (by simp)).trans countA)
  obtain ⟨nt,t,runT,st,ipt,scalarT,regsT,slotsT⟩ := tail ctx sc ipc scalarC countC
  have slots (off : Nat) (member : off ∈ [192,200,208]) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) 64 =
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) 64 := by
    have bounds : 192 ≤ off ∧ off ≤ 208 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl <;> omega
    have ac : stackPtr c+BitVec.ofNat 64 (520-off)=stackPtr initial-BitVec.ofNat 64 off :=
      by simpa only [show 520-(520-off)=off by omega] using address sc (off := 520-off) (by omega)
    have ab : stackPtr b+BitVec.ofNat 64 (520-off)=stackPtr initial-BitVec.ofNat 64 off :=
      by simpa only [show 520-(520-off)=off by omega] using address sb (off := 520-off) (by omega)
    have ht := slotsT (520-off) (by omega) (by omega)
    have hc := slotsC (520-off) (by omega) (by omega)
    rw [ac] at ht
    rw [ab] at hc
    exact ht.trans (hc.trans ((slotsB off member).trans (by rw [memory])))
  refine ⟨na+nb+nc+nt,t,((runA.trans runB).trans runC).trans runT,
    ⟨st,ipt,?_,?_,scalarT,?_,?_⟩⟩
  · exact (regsT .r12 (by simp)).trans
      ((gc.read (n := 64) (r := 12) (by simp [ScalarFrame.Copy32.components])).trans
      ((regsB .r12 (by simp)).trans
      ((ea.agrees.read (n := 64) (r := 12) (by simp [Arguments.effect,Effect.components])).trans decoded.pointers)))
  · exact (slots 192 (by simp)).trans decoded.lengths
  · exact (slots 208 (by simp)).trans decoded.output
  · exact (slots 200 (by simp)).trans decoded.capacity

end P256.Proofs.Signing.Wrapper.Entry.Construct
