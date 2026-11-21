import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Input

set_option autoImplicit false

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude P256.Proofs.Program P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.SecretKeyFromBytes.Scalar

theorem output_nat256 {s : RamState} {address : BitVec 64} {words : Vector (BitVec 64) 4}
    (hw : WordsAt s.external address 64 words) (hr : Refine.Readable s.external address 32) :
    Nat256At s address (limbs words).toNat := by
  have h0 := hw 0 (by decide)
  have h1 := hw 1 (by decide)
  have h2 := hw 2 (by decide)
  have h3 := hw 3 (by decide)
  simp only [wordAddr, Nat.mul_zero, BitVec.add_zero] at h0
  change memLoad s.external (address+8) 64 = words[1] at h1
  change memLoad s.external (address+16) 64 = words[2] at h2
  change memLoad s.external (address+24) 64 = words[3] at h3
  have he : readLimbs s address = limbs words := by
    simp only [readLimbs, limbs, h0, h1, h2, h3]
  rw [← he]
  exact nat256At_readLimbs hr.present

variable [bindings : Bindings] {s t : RamState} {boundary : ReturnBoundary}

theorem result_of_post (pre : Pre s boundary)
    (run : ∃ fuel, Advances boundary fuel s t) (ready : EntryReady Machine.fnCode t)
    (post : Machine.Correction.Post (activation s) [outputRegion (activation s)] t)
    (mxcsr : t.MXCSR = s.MXCSR) (fcw : t.FP87_Control = s.FP87_Control) :
    CalleeResult s t boundary 32 56 := by
  have frame : MemoryWriteFrame s t #v[registerRegion s .rdi 32, Stack.region s 56] := by
    apply post.frame.memoryWriteFrame
    intro a ha r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · intro hc
      apply ha (Stack.region s 56) (by simp)
      have hlow := stack_sub_toNat pre.stack (offset := 56) (by decide)
      change (stackPtr s - 56).toNat = (stackPtr s).toNat-56 at hlow
      change (stackPtr s - 56).toNat ≤ a ∧
        a < (stackPtr s - 56).toNat + ((stackPtr s).toNat - (stackPtr s - 56).toNat) at hc
      change (stackPtr s).toNat-56 ≤ a ∧
        a < (stackPtr s).toNat-56+((stackPtr s).toNat+8-((stackPtr s).toNat-56))
      rw [hlow] at hc
      omega
    · exact ha _ (by simp [outputRegion, activation, registerRegion])
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

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution
