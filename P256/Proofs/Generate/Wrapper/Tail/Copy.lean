import P256.Proofs.Generate.Wrapper.Tail.CopyPre
import P256.Proofs.Program.CopyBytes

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

theorem copy_point [Bindings] {initial s : RamState} {input point : ByteArray}
    {slices : Array Input} {d : Nat}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (draw : Ecdh.drawNonzeroScalar input = some d)
    (state : OutputState initial s input) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x106e76) (source : s.regValue .rsi = stackPtr initial-256)
    (destination : s.regValue .rdi = initial.regValue .rcx+40)
    (count : s.regValue .rdx = 65) (length : s.regValue .r15 = 65)
    (bytes : (MemoryRegion.mk (stackPtr initial-256).toNat 65).HasBytes s.external point)
    (scalar : Bytes s.external (initial.regValue .rcx+8) 32
      (fun i => UInt8.ofNat (d / 256^(31-i) % 256))) :
    ∃ t, OutputState initial t input ∧ t.RIP = 0x106e7c ∧ t.regValue .r15 = 65 ∧
      (MemoryRegion.mk (initial.regValue .rcx+40).toNat 65).HasBytes t.external point ∧
      Bytes t.external (initial.regValue .rcx+8) 32
        (fun i => UInt8.ofNat (d / 256^(31-i) % 256)) := by
  have stack_contains {off len : Nat} {a : BitVec 64} (bound : off ≤ 4024)
      (endBound : len ≤ off+8)
      (covered : (Component.mem (stackPtr initial-BitVec.ofNat 64 off) len).Covers a) :
      (Stack.region initial 4024).Contains a.toNat := by
    obtain ⟨i,hi,rfl⟩ := covered
    exact stack_buffer_contains call.stackAvailable.1 bound endBound
      (memoryRegion_contains_add (stack_buffer_bounded call.stackAvailable.1 bound endBound)
        (Nat.le_refl _) (Nat.le_refl _) hi)
  have push : pushAddr s = stackPtr initial-272 := by
    rw [pushAddr,state.rsp,BitVec.sub_sub]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [push]
    exact writable_of_grow (stack_sub_writable8 call.stackAvailable.1
      (fun a ha hp => call_stack_avoids call a ha (.inr hp)) (by decide) (by decide)) state.allocated
  have apart : RangeApart (pushAddr s) 8 0x106e76 6 := by
    rw [push]
    intro i hi j hj eq
    apply call_stack_avoids call _ (stack_contains (off := 272) (by decide) (by decide) ⟨i,hi,rfl⟩)
    apply Or.inl
    change InProgram (stackPtr initial - 272 + BitVec.ofNat 64 i)
    rw [eq]
    have h := inProgram_of_textOffset (0x6e76+j) (by omega)
    simpa only [BitVec.ofNat_add,← BitVec.add_assoc,Extracted.textAddress,BitVec.reduceAdd,BitVec.ofNat_eq_ofNat] using h
  have pointer := memcpy_pointer state.loaded
  have target : callMemPtr 0x106e76 (.rip 0xfd67c) s = 0x11c930 := pointer.2
  obtain ⟨a,step,ready,effect⟩ := call_m64_effect_step 0x106e76 (.rip 0xfd67c)
    trivial rfl rfl s (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x6e76 _
      (by decide) (by decide +kernel))
    ⟨⟨⟨rip,writable,apart⟩,by rw [target]; decide⟩,pointer.1⟩
  have effect' : (callEffect (fun _ => 0x11c930) 0x106e7c s).Holds s a := by
    change (callEffect (callMemPtr 0x106e76 (.rip 0xfd67c)) 0x106e7c s).Holds s a at effect
    simpa only [callEffect,pushEffect,target] using effect
  have run : Advances (returnBoundary initial) 1 s a := Advances.of_step step (.inl (by
    rw [effect'.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x1c930 (by decide))))
  have agA : AgreesExcept [.reg 4,.mem (stackPtr initial-272) 8,.rip] s a := by
    simpa only [pushEffect_components,push] using effect'.agrees
  have stateA : OutputState initial a input 272 := state.after_effect call run ready agA
    (by
      intro c hc x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact hx.elim
      · exact ⟨workRegion initial,by simp,work_contains call.stackAvailable.1 (by decide) (by decide) hx⟩
      · exact hx.elim)
    (effect'.writes.1.trans push) (by simp) (by simp)
  have srcA : a.regValue .rsi = stackPtr initial-256 :=
    (agA.read (n := 64) (r := 6) (by simp)).trans source
  have dstA : a.regValue .rdi = initial.regValue .rcx+40 :=
    (agA.read (n := 64) (r := 7) (by simp)).trans destination
  have child := copy_pre call draw stateA outside effect'.rip srcA dstA (by
    change InProgram (stackTop a)
    rw [(callEffect_stack effect').1]
    exact inProgram_of_textOffset 0x6e7c (by decide))
  have countA := (agA.read (n := 64) (r := 2) (by simp)).trans count
  obtain ⟨u,result,copied,agCopy⟩ := memcpy_correct child countA (by decide)
  let changes : List Component := [.reg 0,.reg 1,.reg 2,.reg 4,.reg 6,.reg 7,.reg 8,
    .flags,.rip,.mem (initial.regValue .rcx+40) 65,.mem (stackPtr initial-272) 8]
  have ag : AgreesExcept changes s u := (agA.trans agCopy).mono (by
    simp [changes,Copy.copyComponents,Copy.registerComponents,dstA])
  obtain ⟨fuel,childRun⟩ := result.execution
  have next := after_output_effect call state (run.trans childRun)
    (readyToStep result.machine result.bindingsSupported) ag (by
      intro c hc x hx
      simp only [changes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hx.elim
      · exact ⟨_,by simp,output_contains call draw (by decide) hx⟩
      · exact ⟨workRegion initial,by simp,work_contains call.stackAvailable.1 (by decide) (by decide) hx⟩)
    ((result.rsp.trans (callEffect_stack effect').2).trans state.rsp)
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [changes]) (by simp [changes])
  refine ⟨u,next,result.rip.trans (callEffect_stack effect').1,
    (ag.read (n := 64) (r := 15) (by simp [changes])).trans length,?_,?_⟩
  · apply hasBytes_copy bytes
    intro i hi
    rw [← dstA,copied i hi,srcA]
    apply agA.byte
    intro c hc hv
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hv.elim
    obtain ⟨j,hj,eq⟩ := hv
    exact stack_sub_apart call.stackAvailable.1 (a := 272) (b := 256)
      (na := 8) (nb := 65) (by decide) (by decide) (by decide) (by decide)
      (.inl (by decide)) j hj i hi eq.symm
  · intro i hi
    refine (ag.byte ?_).trans (scalar i hi)
    intro c hc hv
    simp only [changes,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    · obtain ⟨j,hj,eq⟩ := hv
      have distinct : OffsetsApart 40 65 8 32 := by unfold OffsetsApart; decide +kernel
      exact distinct.ne (initial.regValue .rcx) hj hi (by decide) eq.symm
    · obtain ⟨j,hj,eq⟩ := hv
      exact output_apart_stack call draw (off := 272) (len := 8)
        (outOff := 8) (outLen := 32) (by decide) (by decide) (by decide) i hi j hj eq

end P256.Proofs.Generate.Wrapper
