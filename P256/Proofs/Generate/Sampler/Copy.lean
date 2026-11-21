import P256.Proofs.Generate.Sampler.Input
import P256.Proofs.Generate.Sampler.Entry
import P256.Proofs.Generate.Sampler.ChunkCopy
import P256.Proofs.Generate.Sampler.Preserve
import P256.Proofs.Program.CopyBytes

set_option autoImplicit false
set_option maxRecDepth 1024

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Projective.Double.Output

theorem copy_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset : Nat} (pre : Pre s boundary input)
    (state : LoopReady s t input offset 0x100cab 32)
    (available : offset+32 ≤ input.size)
    (remaining : t.regValue .rbx = BitVec.ofNat 64 (input.size-(offset+32))) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      LoopReady s u input offset 0x100ccf 32 ∧
      u.regValue .rbx = BitVec.ofNat 64 (input.size-(offset+32)) ∧
      (MemoryRegion.mk (stackPtr s-224#64).toNat 32).HasBytes
        u.external (input.extract offset (offset+32)) := by
  have src : (Operand.reg 5 : Operand 64).read t+18446744073709551584#64 =
      source s+BitVec.ofNat 64 offset := by
    change t.regValue .rbp+_ = _
    simp only [state.source,BitVec.ofNat_add,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero]
  have hp : CopyPre 0x100cab 5 18446744073709551584 40 t := by
    refine ⟨state.rip,?_,?_,?_,?_⟩
    · intro off member
      change MemReadable t (((Operand.reg 5 : Operand 64).read t+18446744073709551584#64)+off) 8
      rw [src]
      have readable := state.toState.chunk_readable pre available
      have bound : off.toNat+8 ≤ 32 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide
      refine ⟨?_,?_⟩
      · have low := readable.low
        rw [BitVec.toNat_add]
        omega
      · intro i hi
        simpa only [BitVec.add_assoc,BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
          using readable.mem (off.toNat+i) (by omega)
    · intro off member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals simpa only [BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using
        (state.toState.stack_writable pre (by decide)).crossPage (by decide)
    · change RangeApart (stackPtr t+40#64) 32
        ((Operand.reg 5 : Operand 64).read t+18446744073709551584#64) 32
      rw [src]
      exact state.toState.chunk_stack_apart pre available (by decide)
    · intro off member codeOffset codeLen codeBound
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals simpa only [BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] using
        state.toState.stack_code pre (by decide) codeBound
  obtain ⟨fuel,u,run,ready,_,effect⟩ := ChunkCopy.correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xcab _ (by decide) (by decide +kernel)) hp
  have agrees := Copy32.frame effect
  have frame := state.toState.after pre ready agrees (by
    intro c hc a covered
    simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨workRegion s 3624,by simp [bodyWrites],state.toState.work_writes pre (by decide) covered⟩)
    (agrees.read (n := 64) (r := 4) (by simp [Copy32.components]))
  have output : memLoad u.external (stackPtr s-192#64) 64 = s.regValue .rdi := by
    have addr : stackPtr t+72#64 = stackPtr s-192#64 :=
      scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by decide)
    rw [←addr]
    refine (stack_load_preserved agrees ?_).trans ?_
    · intro c hc a covered
      simp only [Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      obtain ⟨i,hi,eq⟩ := covered
      exact ⟨40,i,eq,32,hi,by unfold OffsetsApart; decide +kernel,by decide⟩
    · rw [addr]
      exact state.output
  have copied := Copy32.copy_bytes effect (by rw [src]; exact state.toState.chunk_readable pre available)
    (by
      have sp : stackPtr u = stackPtr t := frame.rsp.trans state.rsp.symm
      rw [←sp]
      exact frame.stack_readable pre (by decide))
  have bytes := hasBytes_copy (state.toState.chunk_bytes pre available)
    (by simpa only [src] using copied)
  refine ⟨u,⟨fuel,run⟩,
    { toState := frame, rip := effect.rip, descriptor := ?_,
      source := ?_,remaining := ?_,decoded := ?_,buffer := ?_,output := output },?_,?_⟩
  · exact (agrees.read (n := 64) (r := 14) (by simp [Copy32.components])).trans state.descriptor
  · exact (agrees.read (n := 64) (r := 5) (by simp [Copy32.components])).trans state.source
  · exact (agrees.read (n := 64) (r := 13) (by simp [Copy32.components])).trans state.remaining
  · exact (agrees.read (n := 64) (r := 15) (by simp [Copy32.components])).trans state.decoded
  · exact (agrees.read (n := 64) (r := 12) (by simp [Copy32.components])).trans state.buffer
  · exact (agrees.read (n := 64) (r := 3) (by simp [Copy32.components])).trans remaining
  · have addr : stackPtr t+40#64 = stackPtr s-224#64 :=
      scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by decide)
    simpa only [addr] using bytes

end P256.Proofs.Generate.Sampler
