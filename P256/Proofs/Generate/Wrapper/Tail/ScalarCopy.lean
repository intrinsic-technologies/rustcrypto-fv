import P256.Proofs.Generate.Wrapper.Tail.OutputSafety
import P256.Proofs.Generate.Wrapper.Tail.ScalarCopyBlock
import P256.Proofs.Generate.Wrapper.Geometry
import P256.Proofs.Program.ScalarFrame.Copy32Bytes

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open P256.Proofs.Common.Instructions

theorem output_apart_stack [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {d off len outOff outLen : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (bound : off ≤ 4024) (size : len ≤ off+8) (output : outOff+outLen ≤ 105) :
    RangeApart (initial.regValue .rcx+BitVec.ofNat 64 outOff) outLen
      (stackPtr initial-BitVec.ofNat 64 off) len := by
  intro i hi j hj eq
  apply output_stack_disjoint call _ (output_contains call draw output ⟨i,hi,rfl⟩)
  rw [eq]
  exact stack_buffer_contains call.stackAvailable.1 bound size
    (memoryRegion_contains_add (stack_buffer_bounded call.stackAvailable.1 bound size)
      (Nat.le_refl _) (Nat.le_refl _) hj)

theorem scalar_copy [Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input} {d : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (state : State initial s 264) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x106dc4)
    (bytes : Bytes s.external (stackPtr initial-256) 32
      (fun i => UInt8.ofNat (d / 256^(31-i) % 256))) :
    ∃ t, OutputState initial t input ∧ t.RIP = 0x106de8 ∧
      Bytes t.external (initial.regValue .rcx+8) 32
        (fun i => UInt8.ofNat (d / 256^(31-i) % 256)) ∧
      AgreesExcept (Copy32.components (initial.regValue .rcx+8)) s t := by
  have src : (Operand.reg 4 : Operand 64).read s+8 = stackPtr initial-256 := by
    change stackPtr s+8 = _
    rw [state.rsp]
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc,BitVec.reduceNeg,BitVec.reduceAdd]
  have dst : (Operand.reg 14 : Operand 64).read s+8 = initial.regValue .rcx+8 := by
    change s.regValue .r14+8 = _
    rw [state.output]
  have readable : MemReadable s (stackPtr initial-256) 32 :=
    readable_of_grow (stack_sub_readable call.stackAvailable.1 (by decide) (by decide)) state.allocated
  have writable := (output_writable call draw state.allocated).add 8 (len := 32) (by decide)
  have pre : Copy32.Pre (Extracted.textAddress+BitVec.ofNat 64 0x6dc4)
      (fun q => (Operand.reg 4 : Operand 64).read q+8)
      (fun q => (Operand.reg 14 : Operand 64).read q+8) s := by
    refine ⟨rip,?_,?_,?_,?_⟩
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals rw [src]
      · exact ((stack_buffer_writable call state.allocated (offset := 256) (len := 32) (by decide) (by decide) (by decide)).add 0 (by decide)).toMemReadable
      · exact ((stack_buffer_writable call state.allocated (offset := 256) (len := 32) (by decide) (by decide) (by decide)).add 8 (by decide)).toMemReadable
      · exact ((stack_buffer_writable call state.allocated (offset := 256) (len := 32) (by decide) (by decide) (by decide)).add 16 (by decide)).toMemReadable
      · exact ((stack_buffer_writable call state.allocated (offset := 256) (len := 32) (by decide) (by decide) (by decide)).add 24 (by decide)).toMemReadable
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals rw [dst]
      · exact writable.add 0 (by decide)
      · exact writable.add 8 (by decide)
      · exact writable.add 16 (by decide)
      · exact writable.add 24 (by decide)
    · rw [src,dst]
      exact output_apart_stack call draw (by decide) (by decide) (by decide)
    · intro i hi k l bound
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals rw [dst]
      · exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (output_code call draw (off := 8) (len := 32) (by decide) bound) 0 (by decide)
      · exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (output_code call draw (off := 8) (len := 32) (by decide) bound) 8 (by decide)
      · exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (output_code call draw (off := 8) (len := 32) (by decide) bound) 16 (by decide)
      · exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (output_code call draw (off := 8) (len := 32) (by decide) bound) 24 (by decide)
  obtain ⟨fuel,t,run,ready,_,effect⟩ := Tail.ScalarCopyBlock.run
    (returnBoundary initial) outside 0x6dc4 (by decide) s
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x6dc4 _
      (by decide) (by decide +kernel)) pre
  have agrees : AgreesExcept (Copy32.components (initial.regValue .rcx+8)) s t := by
    simpa only [dst] using Copy32.frame effect
  have next := after_output_effect call (state.with_output input) run ready agrees (by
    intro c hc a ha
    simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> try exact ha.elim
    exact ⟨_,by simp,output_contains call draw (by decide) ha⟩)
    ((agrees.read (n := 64) (r := 4) (by simp [Copy32.components])).trans state.rsp)
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [Copy32.components])
    (by simp [Copy32.components])
  have copied := Copy32.copy_bytes effect (by rwa [src]) (by
    rw [dst]
    exact ((output_writable call draw next.allocated).add 8 (len := 32) (by decide)).toMemReadable)
  refine ⟨t,next,effect.rip,?_,agrees⟩
  intro i hi
  have h := copied i hi
  rw [src,dst] at h
  exact h.trans (bytes i hi)

end P256.Proofs.Generate.Wrapper
