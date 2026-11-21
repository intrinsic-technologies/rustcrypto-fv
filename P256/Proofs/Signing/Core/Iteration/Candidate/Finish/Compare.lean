import P256.Proofs.Signing.Core.Iteration.Call
import P256.Proofs.Generate.Zero.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Candidate.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem compare [Bindings] {s t : RamState} {boundary : ReturnBoundary} {nonce : Nat}
    (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cb95)
    (di : t.regValue .rdi = frameBase s + 432)
    (si : t.regValue .rsi = frameBase s + 1328)
    (input : Nat256At t (frameBase s + 432) nonce)
    (zero : Nat256At t (frameBase s + 1328) 0) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10cb9a ∧
      (u.regValue .rax).setWidth 8 = (if nonce = 0 then 1 else 0) ∧
      (∀ offset < 2280, u.external[frameBase s + BitVec.ofNat 64 offset]? =
        t.external[frameBase s + BitVec.ofNat 64 offset]?) ∧
      (∀ reg ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        u.regValue reg = t.regValue reg) := by
  obtain ⟨v, runV, readyV, effectV⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) (NextNonce.scalarFrame frame) 0xcb95 0x6726
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x132c0 (by decide)) rip
  have effect : (callEffect (fun _ => 0x1132c0) 0x10cb9a t).Holds t v := effectV
  have cp := local_call_pre pre frame readyV effect
    (inputBytes := 32) (outputBytes := 32) (reserve := 32)
    (inProgram_of_textOffset 0xcb9a (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (.inr (by decide)) si di
  have siV : v.regValue .rsi = frameBase s + 1328 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans si
  have diV : v.regValue .rdi = frameBase s + 432 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans di
  have left : Nat256At v (v.regValue .rdi) nonce := by
    rw [diV]
    exact ⟨input.1, fun i hi =>
      (local_call_copy frame effect (offset := 432) (len := 32) (by decide) i hi).trans
        (input.2 i hi)⟩
  have right : Nat256At v (v.regValue .rsi) 0 := by
    rw [siV]
    exact ⟨zero.1, fun i hi =>
      (local_call_copy frame effect (offset := 1328) (len := 32) (by decide) i hi).trans
        (zero.2 i hi)⟩
  obtain ⟨u, result, flag, _, memory⟩ := Generate.Zero.zero_correct cp left right
  have narrow : CalleeResult v u boundary 0 32 := { result with
    frame := fun a ha => memory a (fun region hr => ha region (by simpa using Or.inr hr)) }
  obtain ⟨n, runU⟩ := result.execution
  refine ⟨1+n, u, runV.trans runU,
    after_call pre frame readyV effect narrow (by decide) (by decide) di,
    result.rip.trans (callEffect_stack effect).1, flag, ?_, ?_⟩
  · intro offset bound
    have h := local_result_copy pre frame effect narrow di (offset := offset) (len := 1)
      (by omega) (by decide) (by omega) 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  · intro reg hr
    refine (result.calleeSaved reg hr).trans ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)

end P256.Proofs.Signing.Core.Iteration.Candidate.Finish
