import P256.Proofs.Projective.Multiply.Machine.Radix.Correct
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.FieldCall.Memory

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame FieldCall
open SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Projective.Multiply P256.Proofs.Projective.Multiply.Machine

theorem radix_call [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary} {d : Nat}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x1002ff)
    (source : t.regValue .rsi = s.regValue .rsi)
    (destination : t.regValue .rdi = stackPtr s - 1976)
    (scalar : Nat256At t (s.regValue .rsi) d) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      u.RIP = 0x100304 ∧
      Bytes u.external (stackPtr s - 1976) 65
        (fun i => UInt8.ofBitVec (ProjectiveRadix.digitByte d i)) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15], u.regValue r = t.regValue r) ∧
      (∀ i < 768, u.external[stackPtr s-1040+BitVec.ofNat 64 i]? =
        t.external[stackPtr s-1040+BitVec.ofNat 64 i]?) := by
  obtain ⟨v,run,ready,effect⟩ := scalar_call pre (by decide) (by decide) state
    0x2ff 0xb41c (by decide) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0xb720 (by decide)) rip
  have frame : FrameState s v 32 3464 2064 :=
    state.after_call pre (by decide) (by decide) ready effect
  have vin : v.regValue .rsi = s.regValue .rsi :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have vout : v.regValue .rdi = stackPtr s - 1976 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have ret : (returnBoundary v).rip = 0x100304 := (callEffect_stack effect).1
  have cp : CalleePre v boundary 0x10b720 32 65 136 :=
    CalleePre.of_input_and_stack pre
      (⟨2064,1976,by decide,by decide,by decide,by decide⟩ : StackBufferLayout 3464 65 136)
      frame.bindingsSupported frame.machine frame.directionFlag frame.loaded frame.allocated
      effect.rip frame.rsp vin vout (ret ▸ inProgram_of_textOffset 0x304 (by decide))
  have sv : Nat256At v (v.regValue .rsi) d := by
    rw [vin]
    refine ⟨scalar.1,fun i hi => ?_⟩
    refine (effect.agrees.byte ?_).trans (scalar.2 i hi)
    intro c hc covered
    simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact covered.elim
    · rw [scalar_call_address state] at covered
      exact pre.separation 0 2 (by decide) _
        (memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
        (stack_contains pre (offset := 2064) (by decide) (by decide) covered)
    · exact covered.elim
  obtain ⟨u,result,_,digits⟩ := Radix.radix_correct bindings v boundary d cp sv
  obtain ⟨fuel,executed⟩ := result.execution
  refine ⟨1+fuel,u,run.trans executed,
    after_result pre (frameOffset := 2056) frame result (by decide)
      (stack_result_work_frame pre (frameOffset := 2056) frame result vout
        (by decide) (by decide) (by decide) (by decide)),
    result.rip.trans ret,vout ▸ digits,?_,?_⟩
  · intro r hr
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  · intro i hi
    exact (stack_result_byte pre (frameOffset := 2056) frame result vout
      (by decide) (by decide) (offset := 1040) (len := 768)
      (by decide) (by decide) (by decide) hi).trans
      (scalar_call_byte (frameOffset := 2056) (by decide) state effect
        (offset := 1040) (len := 768) (by decide) (by decide) hi)

end P256.Proofs.Ecdh.Prepare
