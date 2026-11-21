import P256.Proofs.Signing.Core.Iteration.Point.Call
import P256.Proofs.Signing.Core.Iteration.Point.State
import P256.Proofs.Projective.Multiply.Machine.Radix.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Multiply

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open Projective.Multiply.Machine
open Projective.Multiply
open SecretKeyFromBytes.Scalar (Nat256At)

def radixSite : Loop.CallSite 0x10b720 :=
  ⟨0xcf3b,0xffffe7e0,by decide,by decide +kernel,by decide +kernel⟩

theorem radix_call [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary} {nonce : Nat}
    (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cf3b)
    (source : t.regValue .rsi = frameBase s+304)
    (destination : t.regValue .rdi = frameBase s+432)
    (scalar : Nat256At t (frameBase s+304) nonce) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10cf40 ∧
      Bytes u.external (frameBase s+432) 65
        (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte nonce i)) ∧
      (∀ r ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15], u.regValue r = t.regValue r) ∧
      (∀ offset len, offset+len ≤ 2280 → (offset+len ≤ 432 ∨ 497 ≤ offset) →
        ∀ i < len, u.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
          t.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]?) := by
  obtain ⟨v,run,ready,effect⟩ := call_site pre frame radixSite
    (inProgram_of_textOffset 0xb720 (by decide)) rip
  have cp : CalleePre v boundary 0x10b720 32 65 136 :=
    local_call_pre pre frame ready effect (inProgram_of_textOffset 0xcf40 (by decide))
      (by decide) (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
      source destination
  have srcV : v.regValue .rsi = frameBase s+304 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have dstV : v.regValue .rdi = frameBase s+432 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have value : Nat256At v (v.regValue .rsi) nonce := by
    rw [srcV]
    exact ⟨scalar.1,fun i hi => (local_call_copy frame effect (by decide) i hi).trans (scalar.2 i hi)⟩
  obtain ⟨u,result,_,digits⟩ := Radix.radix_correct bindings v boundary nonce cp value
  obtain ⟨fuel,executed⟩ := result.execution
  exact ⟨1+fuel,u,run.trans executed,after_call pre frame ready effect result (by decide)
      (by decide) destination,result.rip.trans (callEffect_stack effect).1,
    dstV ▸ digits,call_registers effect result,
    fun offset len bound apart => local_result_copy pre frame effect result destination bound (by decide) apart⟩

end P256.Proofs.Signing.Core.Iteration.Point.Multiply
