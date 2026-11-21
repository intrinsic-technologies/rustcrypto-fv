import Md5.Spec
import Md5.Proofs.Machine
import Md5.Proofs.Block.Control
import Md5.Proofs.RFC1321.Processing
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Call.Triple

namespace Md5.Proofs.Block

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem compression_empty_run [Bindings] (boundary : ReturnBoundary) {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hEntry : s.RIP = 0x101ba0)
    (hZero : s.regValue .rdx = 0)
    (hRead : MemReadable s (stackPtr s) 8)
    (hLow : (returnBoundary s).rip.toNat < userAddressLimit)
    (hOutside : OutsideCompression boundary.rip) :
    ∃ t, (boundary = returnBoundary s → Returns boundary 3 s t) ∧
      (boundary.rip ≠ (returnBoundary s).rip → Advances boundary 3 s t) ∧
      ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      AgreesExcept [.flags, .rip, .reg 4] s t ∧
      t.RIP = (returnBoundary s).rip ∧ stackPtr t = stackPtr s + 8 := by
  have hz₁ : (Operand.reg 2 : Operand 64).read s = 0 := hZero
  have hb₁ : CodeIn (codeRange 0x101ba0 [0x48, 0x85, 0xd2]) s :=
    program_text_slice hCode 0x1ba0 3 (by decide +kernel)
  obtain ⟨s₂, h₂, hr₂, he₂⟩ :=
    (test_r64_r64_effect_step 0x101ba0 0x48 0xd2 (by unfold RexWPrefix; decide +kernel)
      (by decide +kernel)).advances hReady hb₁ hEntry
      (outsideCompression_ne (pc := 0x101ba3) hOutside (by decide +kernel)
        (by decide +kernel))
  change (testR64R64Effect 0x101ba0 2 2 s).Holds s s₂ at he₂
  have hzf : condHolds 4 (StatusFlags.ofRFLAGS s₂.RFLAGS) = true := by
    have hf := he₂.flags
    simp only [Effect.FlagsHold, testR64R64Effect, hz₁, BitVec.and_self] at hf
    exact hf.2.2.2.1
  have hc₂ := he₂.codeIn (testR64R64Effect_avoids _ _ _ _ _) hCode
  have hb₂ : CodeIn (codeRange 0x101ba3 [0x0f, 0x84, 0xaf, 0x08, 0x00, 0x00]) s₂ :=
    program_text_slice hc₂ 0x1ba3 6 (by decide +kernel)
  obtain ⟨s₃, h₃, hr₃, he₃⟩ :=
    (jcc_rel32_effect_step 0x101ba3 4 0x8af).advances hr₂ hb₂
      ⟨he₂.rip, fun _ ↦ by decide +kernel⟩ (by
        simp only [jccEffect, hzf, branchEffect, ↓reduceIte]
        change 0x102458#64 ≠ boundary.rip
        exact outsideCompression_ne hOutside (by decide +kernel) (by decide +kernel))
  have hj₃ := jccEffect_taken hzf he₃
  have hc₃ := hj₃.codeIn (jmpEffect_avoids _ _ _ _) hc₂
  have ha₃ : AgreesExcept [.flags, .rip, .rip] s s₃ :=
    he₂.agrees.trans hj₃.agrees
  have hm₃ := ha₃.external (by simp [Component.Covers])
  have hs₃ : stackPtr s₃ = stackPtr s :=
    ha₃.read (n := 64) (r := 4) (by simp)
  have ht₃ : stackTop s₃ = (returnBoundary s).rip := by
    simp only [stackTop, hs₃, returnBoundary, Operand.read, hm₃]
  have hb₃ : CodeIn (codeRange 0x102458 [0xc3]) s₃ :=
    program_text_slice hc₃ 0x2458 1 (by decide +kernel)
  have hp₃ : RetPre 0x102458 s₃ := by
    refine ⟨⟨hj₃.rip, ?_⟩, ?_⟩
    · rw [hs₃]
      exact hRead.of_external_eq hm₃
    · rw [ht₃]
      exact hLow
  obtain ⟨t, hstep, hr, he⟩ := ret_effect_step 0x102458 s₃ hr₃ hb₃ hp₃
  have hsp : stackPtr t = stackPtr s + 8 := by
    have hw := he.writes
    change stackPtr t = stackPtr s₃ + 8 at hw
    exact hw.trans (congrArg (· + 8) hs₃)
  have hrip : t.RIP = (returnBoundary s).rip := he.rip.trans ht₃
  refine ⟨t, ?_, ?_, hr, he.codeIn (Effect.avoids_of_components_reg_rip (retEffect_components s₃) _) hc₃, ?_, hrip, hsp⟩
  · intro hb
    exact h₂.returns (h₃.returns (Returns.of_step hstep (by rw [hb]; exact hrip)
      (by rw [hb]; exact hsp)))
  · intro hd
    have hn : t.RIP ≠ boundary.rip := by rw [hrip]; exact Ne.symm hd
    exact h₂.trans (h₃.trans (Advances.of_step hstep (.inl hn)))
  · exact (ha₃.trans he.agrees).mono (by simp)

theorem compression_empty [Bindings] {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hEntry : s.RIP = 0x101ba0)
    (hZero : s.regValue .rdx = 0)
    (hRead : MemReadable s (stackPtr s) 8)
    (hLow : (returnBoundary s).rip.toNat < userAddressLimit)
    (hOutside : OutsideCompression (returnBoundary s).rip) :
    ∃ t, Returns (returnBoundary s) 3 s t ∧ ReadyToStep t ∧
      AgreesExcept [.flags, .rip, .reg 4] s t ∧ stackPtr t = stackPtr s + 8  := by
  obtain ⟨t, hReturn, _, hReady', _, hFrame, _, hStack⟩ :=
    compression_empty_run (returnBoundary s) hReady hCode hEntry hZero hRead hLow hOutside
  exact ⟨t, hReturn rfl, hReady', hFrame, hStack⟩

theorem compress_empty
    {initial : Machine.RamState} {buffer : Standards.RFC.MD5.Buffer} {input : ByteArray}
    (bindings : Machine.Bindings)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : Compress.ValidCall bindings initial buffer input)
    (hZero : (initial.regValue .rdx).toNat = 0) :
    ∃ (fuel : Nat) (final : Machine.RamState),
      UniqueExecution (bindings := bindings) initial fuel final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      MemoryWriteFrame initial final
        #v[Compress.outputRegion initial, Stack.region initial Compress.minStackBytes] ∧
      Compress.readOutput initial final =
        .ok (Standards.RFC.MD5.processBlocks buffer (Standards.RFC.MD5.wordsOfBytes input)).toBytes ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final := by
  letI := bindings
  have hEntry := entryReady bindings hBindings hMachine hCall.programLoaded
  have hRead := stack_return_readable hCall.stackAvailable
  have hBoundary := nearReturn64Boundary_eq initial hEntry.ready.dataReady hMachine.integer.ss hRead
  obtain ⟨boundary, hb, hLow, hOutside⟩ := hCall.returnAddress
  have heq : boundary = returnBoundary initial := Except.ok.inj (hb.symm.trans hBoundary)
  subst boundary
  obtain ⟨s, hJump, hReady, hEffect⟩ := compress_jump hEntry.ready hEntry.code hCall.atEntryPoint
    (text_address_ne_return hOutside 0x1ba0 (by decide +kernel))
  have hCode := hEffect.codeIn (jmpEffect_avoids _ _ _ _) hEntry.code
  have hMemory := hEffect.agrees.external (by simp [Component.Covers])
  have hStack : stackPtr s = stackPtr initial :=
    hEffect.agrees.read (r := 4) (n := 64) (by simp)
  have hReturn : returnBoundary s = returnBoundary initial := by
    simp only [returnBoundary, hStack, Operand.read, hMemory]
  have hCount : s.regValue .rdx = 0 := by
    have hz : initial.regValue .rdx = 0 := BitVec.eq_of_toNat_eq hZero
    exact (hEffect.agrees.read (r := 2) (n := 64) (by simp)).trans hz
  obtain ⟨final, hRun, hFinal, hAgrees, _⟩ := compression_empty hReady hCode hEffect.rip hCount
    (by rw [hStack]; exact hRead.of_external_eq hMemory)
    (by rw [hReturn]; exact hLow)
    (by rw [hReturn]; exact outsideCompression_of_not_inProgram hOutside)
  rw [hReturn] at hRun
  have hAll : AgreesExcept [.flags, .rip, .reg 4] initial final :=
    (hEffect.agrees.trans hAgrees).mono (by simp)
  have hMemoryFinal := hAll.external (by simp [Component.Covers])
  obtain ⟨fuel, hUnique⟩ := (hJump.returns hRun).unique_of_boundary hBoundary
  refine ⟨fuel, final, hUnique,
    supportedIntegerMachineState_of_ready hFinal hAll hMachine.sse,
    machineRamUnitStrideDecodable_of_ready hFinal hBindings.stringStride,
    ?_, ?_, ?_, hAll.directionFlagClear (by simp) hCall.directionFlagUnset⟩
  · intro address _
    exact congrArg (·[address]?) hMemoryFinal
  · have hSize : input.size = 0 := by
      have hLength := hCall.blockCountArgumentMatchesBlocks
      change 64 * (initial.regValue .rdx).toNat = input.size at hLength
      omega
    have hWords : Standards.RFC.MD5.wordsOfBytes input = #[] := by
      apply Array.eq_empty_of_size_eq_zero
      simp [Standards.RFC.MD5.wordsOfBytes, hSize]
    rw [hWords, Md5.Proofs.RFC1321.processBlocks_empty]
    exact compress_readOutput_of_external_eq hCall.outputInMemory.2 hMemoryFinal
  · intro register hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hAll.read (r := 3) (n := 64) (by decide +kernel)
    · exact hAll.read (r := 5) (n := 64) (by decide +kernel)
    · exact hAll.read (r := 12) (n := 64) (by decide +kernel)
    · exact hAll.read (r := 13) (n := 64) (by decide +kernel)
    · exact hAll.read (r := 14) (n := 64) (by decide +kernel)
    · exact hAll.read (r := 15) (n := 64) (by decide +kernel)

end Md5.Proofs.Block
