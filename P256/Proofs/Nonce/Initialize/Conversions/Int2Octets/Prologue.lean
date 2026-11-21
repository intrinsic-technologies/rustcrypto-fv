import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.State
import X86Proofs.Instructions.Sub.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program (save_registers saveFrame saveMemory saveMemory_saved)

theorem prologue_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Pre s boundary) :
    ∃ t, Stage s t boundary ∧ EntryRegisters s t ∧ t.RIP = 0x106f4e := by
  obtain ⟨u, run, ready, loaded, rip, rsp, memory, agrees⟩ :=
    save_registers (codeOffset := 0x6f40) pre.stack (pre.avoids _ (by simp))
      pre.outerBoundary (readyToStep pre.machine pre.bindingsSupported) pre.loaded (by decide) pre.rip
      (by constructor <;> decide +kernel)
  obtain ⟨t, step, ready', effect⟩ :=
    (sub_r64_imm8_effect_step 0x106f4a 0x48 0xec 24
      (by constructor <;> decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x6f4a _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x6f4e (by decide)))
  have frame : AgreesExcept (saveFrame s ++ [.flags]) s t := by
    apply (agrees.trans effect.agrees).mono
    simp only [subR64Imm8Effect_components, saveFrame, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl | rfl) <;> simp [gprNumber, rexB, modrmRm]
  have memory' : t.external = saveMemory s :=
    (effect.agrees.external (by simp [subR64Imm8Effect_components, Component.Covers])).trans memory
  have writes : WritesWithin (saveFrame s ++ [.flags])
      #v[registerRegion s .rdx 32, Stack.region s 128] := by
    intro c hc a ha
    refine ⟨Stack.region s 128, by simp, ?_⟩
    simp only [saveFrame, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact False.elim ha
    all_goals exact stackRegion_contains_sub pre.stack.2.2.1 (by decide) (by decide) ha
  have writeFrame := frame.memoryWriteFrame writes
  refine ⟨t, {
    execution := ⟨7, run.trans step⟩
    bindingsSupported := bindingsSupported_of_ready_agrees pre.bindingsSupported ready' frame
    machine := supportedMachine_of_ready_agrees pre.machine ready' frame
    loaded := ?_
    allocated := frame.grow
    frame := writeFrame
    rsp := ?_
    saved := ?_
    returnAddress := ?_
    directionFlag := frame.directionFlagClear (by component_not_mem) pre.directionFlag
    mxcsr := frame.mxcsr (by component_not_mem)
    fp87 := frame.fcw (by component_not_mem)
  }, {
    input := frame.read (n := 64) (r := 7) (by simp [saveFrame])
    order := frame.read (n := 64) (r := 6) (by simp [saveFrame])
    output := frame.read (n := 64) (r := 2) (by simp [saveFrame])
    length := (frame.read (n := 64) (r := 1) (by simp [saveFrame])).trans pre.length
  }, effect.rip⟩
  · intro a b fetch
    rw [writeFrame a]
    · exact pre.loaded a b fetch
    · intro region member inside
      exact pre.avoids region (by simpa using member) a inside (.inl ⟨b, fetch⟩)
  · have subtract : stackPtr t = stackPtr u - 24 := effect.writes
    rw [subtract, rsp, BitVec.sub_sub]
    rfl
  · intro entry member
    rw [memory']
    exact saveMemory_saved s entry member
  · rw [memory']
    simp only [saveMemory, BitVec.sub_eq_add_neg]
    repeat rw [memLoad_memStore_apart_right _ (stackPtr s) _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets
