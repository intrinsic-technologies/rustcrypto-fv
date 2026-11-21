import P256.Proofs.Generate.Sampler.FirstRead
import P256.Proofs.Generate.Sampler.Input
import P256.Proofs.Generate.Sampler.ReadSetup

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem read_setup_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} {offset : Nat} (pre : Pre s boundary input)
    (state : ReadReady s t input offset) (available : offset+32 ≤ input.size) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧
      LoopReady s u input offset 0x100cab 32 ∧
      u.regValue .rbx = BitVec.ofNat 64 (input.size-(offset+32)) := by
  have hp : ReadSetupPre t := by
    refine ⟨state.rip,?_,?_⟩
    · intro off member
      change P256.Proofs.Common.Der.Memory.MemWritable t (t.regValue .r14+off) 8
      rw [state.descriptor]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      all_goals exact state.toState.descriptor_writable pre (by decide)
    · change RangeApart (t.regValue .r14) 16 0x100ca0#64 11
      rw [state.descriptor]
      exact descriptor_code pre (codeOffset := 0xca0) (by decide)
  obtain ⟨fuel,u,run,ready,_,effect⟩ := read_setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported) (read_setup_loaded state.loaded) hp
  have memory : ∀ c ∈ (readSetupEffect t).components, ∀ a, c.Covers a →
      ∃ r ∈ bodyWrites s, r.Contains a.toNat := by
    intro c hc a covered
    simp only [readSetupEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
      Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.append_nil] at hc
    rcases hc with (rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals
      refine ⟨registerRegion s .rsi 16,by simp [bodyWrites],?_⟩
      obtain ⟨i,hi,rfl⟩ := covered
      have hd : (Operand.reg 14#5 : Operand 64).read t = s.regValue .rsi := state.descriptor
      rw [hd]
    · exact memoryRegion_contains_add (region := registerRegion s .rsi 16) pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) (by change i < 16; omega)
    · change (registerRegion s .rsi 16).Contains (s.regValue .rsi+8#64+BitVec.ofNat 64 i).toNat
      have h := memoryRegion_contains_add (region := registerRegion s .rsi 16) pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) (by change 8+i < 16; omega)
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using h
  have frame := state.toState.after pre ready effect.agrees memory
    (effect.agrees.read (n := 64) (r := 4) (by simp [readSetupEffect,Effect.components]))
  have output : memLoad u.external (stackPtr s-192#64) 64 = s.regValue .rdi := by
    apply (preserved_load effect.agrees ?_).trans state.output
    intro i hi c hc covered
    have apart := state.toState.stack_descriptor pre (offset := 72) (len := 8) (by decide)
    have addr : stackPtr t+72#64=stackPtr s-192#64 :=
      ScalarFrame.scalar_stack_address (frameOffset := 264) state.rsp (by decide) (by decide)
    simp only [readSetupEffect,Effect.components,List.map_cons,List.map_nil,Write.component,
      Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.append_nil] at hc
    rcases hc with (rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals
      obtain ⟨j,hj,eq⟩ := covered
      have hd : (Operand.reg 14#5 : Operand 64).read t = s.regValue .rsi := state.descriptor
      rw [hd] at eq
      have addr2 : stackPtr t+72#64 = stackPtr s-192 := addr
      rw [←addr2] at eq
    · exact apart i hi j (by omega) eq
    · apply apart i hi (8+j) (by omega)
      change stackPtr t+72#64+BitVec.ofNat 64 i = s.regValue .rsi+8#64+BitVec.ofNat 64 j at eq
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq
  refine ⟨u,⟨fuel,run⟩,
    { toState := frame, rip := effect.rip,
      descriptor := ?_,source := ?_,remaining := ?_,decoded := ?_,buffer := ?_,output := output },?_⟩
  · exact (effect.agrees.read (n := 64) (r := 14) (by simp [readSetupEffect,Effect.components])).trans state.descriptor
  · exact (effect.agrees.read (n := 64) (r := 5) (by simp [readSetupEffect,Effect.components])).trans state.source
  · exact (effect.agrees.read (n := 64) (r := 13) (by simp [readSetupEffect,Effect.components])).trans state.remaining
  · exact (effect.agrees.read (n := 64) (r := 15) (by simp [readSetupEffect,Effect.components])).trans state.decoded
  · exact (effect.agrees.read (n := 64) (r := 12) (by simp [readSetupEffect,Effect.components])).trans state.buffer
  · have h : u.regValue .rbx = t.regValue .r13-32#64 := effect.writes.1
    rw [h,state.remaining]
    have count : input.size-offset = (input.size-(offset+32))+32 := by omega
    rw [count,BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _

end P256.Proofs.Generate.Sampler
