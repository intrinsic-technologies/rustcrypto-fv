import P256.Proofs.Signing.Core.Iteration.Call
import P256.Proofs.Verifying.Core.Reduce.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem reduce [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d26d)
    (source : t.regValue .rsi = frameBase s+528)
    (destination : t.regValue .rdi = frameBase s+176)
    (input : Nat256At t (frameBase s+528) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10d272 ∧
      Nat256At u (frameBase s+176) (x % Operations.domain.n) ∧
      (∀ offset < 2280, offset < 176 ∨ 208 ≤ offset →
        u.external[frameBase s+BitVec.ofNat 64 offset]? =
          t.external[frameBase s+BitVec.ofNat 64 offset]?) ∧
      (∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],
        u.regValue reg = t.regValue reg) := by
  obtain ⟨a,callRun,readyA,call⟩ := ScalarFrame.scalar_call hp.toCalleePre
    (by decide) (by decide) (NextNonce.scalarFrame frame) 0xd26d 0x5eae
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x13120 (by decide)) rip
  have cp := local_call_pre hp frame readyA call
    (inputBytes := 32) (outputBytes := 32) (reserve := 104)
    (inProgram_of_textOffset 0xd272 (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (.inr (by decide)) source destination
  have src : a.regValue .rsi = frameBase s+528 :=
    (call.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have dst : a.regValue .rdi = frameBase s+176 :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have valueA : Nat256At a (a.regValue .rsi) x := by
    rw [src]
    exact ⟨input.1, fun i hi =>
      (local_call_copy frame call (by decide) i hi).trans (input.2 i hi)⟩
  obtain ⟨u,result,value⟩ := Verifying.Core.Reduce.reduce_correct cp valueA
  obtain ⟨n,run⟩ := result.execution
  refine ⟨1+n,u,callRun.trans run,
    after_call hp frame readyA call result (by decide) (by decide) destination,
    result.rip.trans (callEffect_stack call).1,dst ▸ value,?_,?_⟩
  · intro offset bound apart
    have h := local_result_copy (output := 176) hp frame call result destination
      (offset := offset) (len := 1) (by omega) (by decide) (by omega) 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  · intro reg hr
    refine (result.calleeSaved reg hr).trans ?_
    rcases (show reg = .rbx ∨ reg = .rbp ∨ reg = .r12 ∨ reg = .r13 ∨ reg = .r14 ∨ reg = .r15
      from by simpa using hr) with rfl|rfl|rfl|rfl|rfl|rfl
    · exact call.agrees.read (n := 64) (r := 3) (by simp)
    · exact call.agrees.read (n := 64) (r := 5) (by simp)
    · exact call.agrees.read (n := 64) (r := 12) (by simp)
    · exact call.agrees.read (n := 64) (r := 13) (by simp)
    · exact call.agrees.read (n := 64) (r := 14) (by simp)
    · exact call.agrees.read (n := 64) (r := 15) (by simp)

end P256.Proofs.Signing.Core.Iteration.Components
