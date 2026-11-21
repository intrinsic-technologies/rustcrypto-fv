import P256.Proofs.Scalar.Inverse.Wrapper.Input
import P256.Proofs.Common.Memory.LoadByte
import P256.Proofs.Field.Inverse.SafeGcd.Core.Input.Memory
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Output

set_option autoImplicit false

namespace P256.Proofs.Scalar.Inverse.Wrapper

open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar

variable [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem result_of_post (pre : CalleePre s boundary 0x112e30 32 40 768)
    (run : ∃ fuel, Advances boundary fuel s t) (ready : EntryReady Machine.fnCode t)
    (post : Machine.Inverse.Post (activation s) [outputRegion (activation s)] t)
    (mxcsr : t.MXCSR = s.MXCSR) (fcw : t.FP87_Control = s.FP87_Control) :
    CalleeResult s t boundary 40 768 := by
  have frame : MemoryWriteFrame s t #v[registerRegion s .rdi 40, Stack.region s 768] := by
    apply post.frame.memoryWriteFrame
    intro a ha r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro hc
      apply ha (Stack.region s 768) (by simp)
      have hlow := stack_sub_toNat pre.stack (offset  := 768) (by decide)
      change (stackPtr s - 768).toNat = (stackPtr s).toNat-768 at hlow
      change (stackPtr s - 768).toNat ≤ a ∧
        a < (stackPtr s - 768).toNat + ((stackPtr s).toNat - (stackPtr s - 768).toNat) at hc
      change (stackPtr s).toNat-768 ≤ a ∧
        a < (stackPtr s).toNat-768+((stackPtr s).toNat+8-((stackPtr s).toNat-768))
      rw [hlow] at hc
      omega
    · intro hc
      apply ha (registerRegion s .rdi 40) (by simp)
      change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 40
      change (s.regValue .rdi).toNat ≤ a ∧ a < (s.regValue .rdi).toNat + 33 at hc
      omega
  refine ⟨run, post.rip, Value.eq_bits post.rsp,
    ⟨ready.ready.smrr, ready.ready.memoryType, pre.bindingsSupported.stringStride,
      ready.ready.features.lzcnt⟩,
    ready.ready.supported ready.sse, ?_, post.df, mxcsr, fcw, frame, ?_, post.frame.present⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Value.eq_bits (post.preserved 3 (by decide))
    · exact Value.eq_bits (post.preserved 5 (by decide))
    · exact Value.eq_bits (post.preserved 12 (by decide))
    · exact Value.eq_bits (post.preserved 13 (by decide))
    · exact Value.eq_bits (post.preserved 14 (by decide))
    · exact Value.eq_bits (post.preserved 15 (by decide))
  · intro a byte hb
    rw [frame a]
    · exact pre.loaded a byte hb
    · intro region hr hc
      exact pre.avoids region (by simpa using hr) a hc (.inl ⟨byte, hb⟩)

end P256.Proofs.Scalar.Inverse.Wrapper
