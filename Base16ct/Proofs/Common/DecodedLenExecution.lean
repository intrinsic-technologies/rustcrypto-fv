import Base16ct.Proofs.Common.LengthSteps
import Base16ct.Proofs.Common.EncodedLenSummary

namespace Base16ct.Proofs.Common

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem lowByte_test_one (x : BitVec 64) :
    (x.setWidth 8 &&& 1#8 == 0#8) = decide (x.toNat % 2 = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have hnat := congrArg BitVec.toNat h
    change x.toNat % 256 &&& 1 = 0 at hnat
    rw [Nat.and_one_is_mod] at hnat
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    change x.toNat % 256 &&& 1 = 0
    rw [Nat.and_one_is_mod]
    omega

theorem decoded_len_even_trace [bindings : Machine.Bindings]
    {initial : RamState} {byteLength : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidLengthCall base16ctDecodedLen initial byteLength (byteLength % 2 = 0))
    (hEven : byteLength % 2 = 0) :
    ∃ phase : RamState,
      Advances (returnBoundary initial) 6 initial phase ∧
      ReadyToStep phase ∧ CodeIn programImage phase ∧ phase.RIP = 0x100013 ∧
      AgreesExcept [.reg 0, .reg 6, .flags, .mem (initial.regValue .rdx) 8, .rip]
        initial phase ∧
      MemoryWriteFrame initial phase
        #v[lengthOutputRegion initial, Stack.region initial base16ctDecodedLen.minStackBytes] ∧
      CalleeSavedRegistersUnchanged initial phase ∧ DirectionFlagUnset phase ∧
      phase.regValue .rax = 0 ∧
      (Operand.mem (initial.regValue .rdx) : Operand 64).read phase =
        BitVec.ofNat 64 (byteLength / 2) := by
  have hEntry := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.entryReady
    hBindings hMachine hCall.programLoaded
  have hBoundary := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.validReturnAddress_boundary
    hCall.returnAddress
  obtain ⟨s0, h0, hr0, hc0, e0⟩ := decoded_len_initial_step hEntry
    (by simpa [base16ctDecodedLen, Extracted.decoded_lenAddress] using hCall.entry) hBoundary.2
  have he0 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hEntry hr0 hc0 e0.agrees
  have hp0 : s0.RIP = 0x100005 := by
    simpa [movR32Imm32Effect, base16ctDecodedLen, Extracted.decoded_lenAddress,
      hCall.entry] using e0.rip
  obtain ⟨s1, h1, hr1, hc1, e1⟩ := decoded_len_test_step he0 hp0 hBoundary.2
  have he1 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter he0 hr1 hc1 e1.agrees
  have hp1 : s1.RIP = 0x100009 := by
    simpa [testR8Imm8Effect, hp0, BitVec.add_assoc] using e1.rip
  have hsi : (Operand.reg 6 : Operand 8).read s0 = (s0.regValue .rsi).setWidth 8 := rfl
  have hsi0 : s0.regValue .rsi = initial.regValue .rsi :=
    e0.agrees.read (r := 6) (n := 64)
        (by simp [movR32Imm32Effect, testR8Imm8Effect, Effect.components])
  have hz : (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      decide (byteLength % 2 = 0) := by
    have hh := e1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      (((Operand.reg 6 : Operand 8).read s0 &&& 1) == 0) at hh
    rw [hsi0] at hsi
    rw [hsi] at hh
    rw [hh]
    simpa [lowByte_test_one, hCall.lengthArgumentMatchesInput]
  have hCond : condHolds (5#4) (StatusFlags.ofRFLAGS s1.RFLAGS) = false := by
    simp [condHolds, hz, hEven]
  obtain ⟨s2, h2, hr2, hc2, e2⟩ := decoded_len_jne_not_taken_step he1 hp1 hBoundary.2 hCond
  have he2 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter he1 hr2 hc2 e2.agrees
  have hp2 : s2.RIP = 0x10000b := by
    simpa [jccEffect, branchEffect, hp1, hCond] using e2.rip
  obtain ⟨s3, h3, hr3, hc3, e3⟩ := decoded_len_shr_step he2 hp2 hBoundary.2
  have he3 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter he2 hr3 hc3 e3.agrees
  have hp3 : s3.RIP = 0x10000e := by
    simpa [shrR64Effect, hp2] using e3.rip
  have hExternal : s3.external = initial.external := by
    exact (e0.agrees.trans (e1.agrees.trans (e2.agrees.trans e3.agrees))).external
      (by simp [jccEffect, branchEffect, movR32Imm32Effect, testR8Imm8Effect,
        shrR64Effect, Effect.components, Component.Covers])
  have hRdx : s3.regValue .rdx = initial.regValue .rdx := by
    exact (e0.agrees.trans (e1.agrees.trans (e2.agrees.trans e3.agrees))).read
      (r := 2) (n := 64) (by simp [jccEffect, branchEffect, movR32Imm32Effect,
        testR8Imm8Effect, shrR64Effect, Effect.components] <;> decide +kernel)
  have hStorePre := length_store_pre (p := (0x10000e : BitVec 64)) (offset := 0x0e)
    hCall hEven hExternal hRdx hp3 (by decide +kernel) (by decide +kernel)
  have hCodeStore : CodeIn (codeRange 0x10000e [0x48, 0x89, 0x32]) s3 := by
    have h := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.program_text_slice
      hc3 0x0e 3 (by decide +kernel)
    have hb : Extracted.textBytes.toListFrom 0x0e 3 = [0x48, 0x89, 0x32] := by
      decide +kernel
    simpa only [hb, show Extracted.textAddress + BitVec.ofNat 64 0x0e = (0x10000e : BitVec 64) by
      decide +kernel] using h
  have hStoreNe :
      (storeEffect (0x10000e : BitVec 64) 3 (fun q => q.regValue .rdx)
        (fun q => (Operand.reg 6 : Operand 64).read q) s3).rip ≠
        (returnBoundary initial).rip := by
    change (0x100011 : BitVec 64) ≠ (returnBoundary initial).rip
    intro heq
    apply hBoundary.2
    rw [← heq]
    exact text_address_in_program 0x11 (by decide +kernel)
  obtain ⟨s4, h4, hr4, e4⟩ :=
    (mov_rsi_store_effect_step (0x10000e : BitVec 64)).advances hr3 hCodeStore hStorePre hStoreNe
  have hOut := hCall.lengthOutputInMemoryIfLengthWritten hEven
  have hAvoid : ∀ i < 8, ¬ InProgram (s3.regValue .rdx + BitVec.ofNat 64 i) := by
    intro i hi hProgram
    apply (hCall.separation.2 hEven).2 (s3.regValue .rdx + BitVec.ofNat 64 i)
    · have hc := region_offset_contains hOut.1 (i := i) hi
      simpa [lengthOutputRegion, registerRegion, hRdx, BitVec.ofNat_add] using hc
    · exact .inl hProgram
  have hStoreAvoids :
      (storeEffect (0x10000e : BitVec 64) 3 (fun q => q.regValue .rdx)
        (fun q => (Operand.reg 6 : Operand 64).read q) s3).Avoids programImage := by
    intro x hx c hc hcover
    simp only [storeEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := hcover
      change x.1 = s3.regValue .rdx + BitVec.ofNat 64 i at heq
      apply hAvoid i hi
      rw [← heq]
      exact ⟨x.2, hx⟩
    · exact hcover
  have he4 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter he3 hr4
    (e4.codeIn hStoreAvoids hc3) e4.agrees
  have hp4 : s4.RIP = 0x100011 := by
    simpa [storeEffect, hp3] using e4.rip
  obtain ⟨s5, h5, hr5, hc5, e5⟩ := decoded_len_xor_step he4 hp4 hBoundary.2
  have hAgree : AgreesExcept [.reg 0, .reg 6, .flags, .mem (initial.regValue .rdx) 8, .rip]
      initial s5 := by
    exact (e0.agrees.trans (e1.agrees.trans (e2.agrees.trans (e3.agrees.trans
      (e4.agrees.trans e5.agrees))))).mono
      (by simp [jccEffect, branchEffect, storeEffect, Effect.components,
        xorR32R32Effect, shrR64Effect, testR8Imm8Effect, movR32Imm32Effect,
        hRdx] <;> decide +kernel)
  have hFrame : MemoryWriteFrame initial s5
      #v[lengthOutputRegion initial, Stack.region initial base16ctDecodedLen.minStackBytes] := by
    apply hAgree.memoryWriteFrame
    intro c hc x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact False.elim (by simp [Component.Covers] at hx)
    · exact False.elim (by simp [Component.Covers] at hx)
    · exact False.elim (by simp [Component.Covers] at hx)
    · obtain ⟨i, hi, heq⟩ := hx
      have hc := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.region_offset_contains
        (hCall.lengthOutputInMemoryIfLengthWritten hEven).1 hi
      refine ⟨lengthOutputRegion initial, by simp, ?_⟩
      rw [heq]
      simpa [lengthOutputRegion, registerRegion] using hc
    · exact False.elim (by simp [Component.Covers] at hx)
  have hCallee : CalleeSavedRegistersUnchanged initial s5 := by
    intro register hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
    · change s5.GPR[gprIndex (3 : BitVec 5)] = initial.GPR[gprIndex (3 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 3) (by simp) rfl
    · change s5.GPR[gprIndex (5 : BitVec 5)] = initial.GPR[gprIndex (5 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 5) (by simp) rfl
    · change s5.GPR[gprIndex (12 : BitVec 5)] = initial.GPR[gprIndex (12 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 12) (by simp) rfl
    · change s5.GPR[gprIndex (13 : BitVec 5)] = initial.GPR[gprIndex (13 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 13) (by simp) rfl
    · change s5.GPR[gprIndex (14 : BitVec 5)] = initial.GPR[gprIndex (14 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 14) (by simp) rfl
    · change s5.GPR[gprIndex (15 : BitVec 5)] = initial.GPR[gprIndex (15 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 15) (by simp) rfl
  have hDirection : DirectionFlagUnset s5 :=
    e5.agrees.directionFlagClear (by simp) (e4.agrees.directionFlagClear (by simp)
      (e3.agrees.directionFlagClear (by simp) (e2.agrees.directionFlagClear (by simp [jccEffect, branchEffect, Effect.components])
        (e1.agrees.directionFlagClear (by simp) (e0.agrees.directionFlagClear (by simp)
          hCall.directionFlagUnset)))))
  have hValue : (Operand.mem (initial.regValue .rdx) : Operand 64).read s5 =
      BitVec.ofNat 64 (byteLength / 2) := by
    have hv := e4.writes
    change (Operand.mem (s3.regValue .rdx) : Operand 64).read s4 =
      (Operand.reg 6 : Operand 64).read s3 at hv
    have hByteLengthLt : byteLength < 2 ^ 64 := by
      have hb := hCall.inputInMemory.2.1
      change (initial.regValue .rdi).toNat + byteLength < 2 ^ 32 at hb
      omega
    have hRsiInitial : initial.regValue .rsi = BitVec.ofNat 64 byteLength := by
      have hb := hCall.inputInMemory.2.1
      change (initial.regValue .rdi).toNat + byteLength < 2 ^ 32 at hb
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hByteLengthLt] using
        hCall.lengthArgumentMatchesInput
    have hRsi0 : s0.regValue .rsi = initial.regValue .rsi :=
      e0.agrees.read (r := 6) (n := 64)
        (by simp [movR32Imm32Effect, testR8Imm8Effect, Effect.components])
    have hRsi2 : s2.regValue .rsi = initial.regValue .rsi :=
      (e0.agrees.trans (e1.agrees.trans e2.agrees)).read (r := 6) (n := 64)
        (by simp [jccEffect, branchEffect, movR32Imm32Effect, testR8Imm8Effect, Effect.components])
    have hHalfLt : byteLength / 2 < 2 ^ 64 := by omega
    have hRsi3 : s3.regValue .rsi = BitVec.ofNat 64 (byteLength / 2) := by
      have hw := e3.writes
      change s3.regValue .rsi = s2.regValue .rsi >>> 1 at hw
      rw [hRsi2, hRsiInitial] at hw
      apply BitVec.eq_of_toNat_eq
      rw [hw, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
      simpa [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hHalfLt] using congrArg (fun n => n / 2)
        (show byteLength = (BitVec.ofNat 64 byteLength).toNat by
          rw [BitVec.toNat_ofNat]; omega).symm
    have hRsi3' : BitVec.setWidth 64 s3.GPR[gprIndex 6] =
        BitVec.ofNat 64 (byteLength / 2) := by
      change s3.regValue .rsi = _
      exact hRsi3
    have hv' : (Operand.mem (initial.regValue .rdx) : Operand 64).read s4 =
        BitVec.ofNat 64 (byteLength / 2) := by
      rw [hRdx] at hv
      simpa only [Operand.read, hRsi3'] using hv
    have hread : (Operand.mem (initial.regValue .rdx) : Operand 64).read s5 =
        (Operand.mem (initial.regValue .rdx) : Operand 64).read s4 := by
      apply memLoad_congr
      intro i hi
      have hNoMem : ∀ (c : Component), c ∈ [.reg 0, .flags, .rip] →
          ¬ c.Covers (initial.regValue .rdx + BitVec.ofNat 64 i) := by
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl <;> simp [Component.Covers] at hcov
      change (s5.external[initial.regValue .rdx + BitVec.ofNat 64 i]?).getD 0 =
        (s4.external[initial.regValue .rdx + BitVec.ofNat 64 i]?).getD 0
      rw [e5.agrees.byte hNoMem]
    exact hread.trans hv'
  have hStatus : s5.regValue .rax = 0 := by
    have hw : AddrMode.reg64 0 s5 = 0#64 := by
      simpa [xorR32R32Effect, Write.AllHold, Operand.read, AddrMode.reg64] using e5.writes
    simpa [AddrMode.reg64, State.regValue, Operand.read, gprIndex, Syntax.Reg.fin] using hw
  refine ⟨s5, h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5)))), hr5, hc5,
    (by simpa [xorR32R32Effect, hp4, BitVec.add_assoc] using e5.rip),
    hAgree, hFrame, hCallee, hDirection, hStatus, hValue⟩

theorem decoded_len_odd_trace [bindings : Machine.Bindings]
    {initial : RamState} {byteLength : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidLengthCall base16ctDecodedLen initial byteLength (byteLength % 2 = 0))
    (hOdd : byteLength % 2 ≠ 0) :
    ∃ phase : RamState,
      Advances (returnBoundary initial) 3 initial phase ∧
      ReadyToStep phase ∧ CodeIn programImage phase ∧ phase.RIP = 0x100013 ∧
      AgreesExcept [.reg 0, .flags, .rip] initial phase ∧
      MemoryWriteFrame initial phase
        #v[lengthOutputRegion initial, Stack.region initial base16ctDecodedLen.minStackBytes] ∧
      CalleeSavedRegistersUnchanged initial phase ∧ DirectionFlagUnset phase ∧
      phase.regValue .rax = BitVec.setWidth 64 invalidLengthStatus := by
  have hEntry := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.entryReady
    hBindings hMachine hCall.programLoaded
  have hBoundary := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.validReturnAddress_boundary
    hCall.returnAddress
  obtain ⟨s0, h0, hr0, hc0, e0⟩ := decoded_len_initial_step hEntry
    (by simpa [base16ctDecodedLen, Extracted.decoded_lenAddress] using hCall.entry) hBoundary.2
  have he0 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter hEntry hr0 hc0 e0.agrees
  have hp0 : s0.RIP = 0x100005 := by
    simpa [movR32Imm32Effect, base16ctDecodedLen, Extracted.decoded_lenAddress,
      hCall.entry] using e0.rip
  obtain ⟨s1, h1, hr1, hc1, e1⟩ := decoded_len_test_step he0 hp0 hBoundary.2
  have he1 := Base16ct.Proofs.Base16ctUpperDecodeCorrect.entryReadyAfter he0 hr1 hc1 e1.agrees
  have hp1 : s1.RIP = 0x100009 := by
    simpa [testR8Imm8Effect, hp0, BitVec.add_assoc] using e1.rip
  have hsi : (Operand.reg 6 : Operand 8).read s0 = (s0.regValue .rsi).setWidth 8 := rfl
  have hsi0 : s0.regValue .rsi = initial.regValue .rsi :=
    e0.agrees.read (r := 6) (n := 64) (by simp)
  have hz : (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      decide (byteLength % 2 = 0) := by
    have hh := e1.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s1.RFLAGS).ZF =
      (((Operand.reg 6 : Operand 8).read s0 &&& 1) == 0) at hh
    rw [hsi0] at hsi
    rw [hsi] at hh
    rw [hh]
    simpa [lowByte_test_one,
      hCall.lengthArgumentMatchesInput]
  have hCond : condHolds (5#4) (StatusFlags.ofRFLAGS s1.RFLAGS) = true := by
    simp [condHolds, hz, hOdd]
  obtain ⟨s2, h2, hr2, hc2, e2⟩ := decoded_len_jne_step he1 hp1 hBoundary.2 hCond
  have hAgree : AgreesExcept [.reg 0, .flags, .rip] initial s2 :=
    (e0.agrees.trans (e1.agrees.trans e2.agrees)).mono
    (by simp [jccEffect, branchEffect, Effect.components, testR8Imm8Effect, movR32Imm32Effect])
  have hFrame : MemoryWriteFrame initial s2
      #v[lengthOutputRegion initial, Stack.region initial base16ctDecodedLen.minStackBytes] := by
    apply hAgree.memoryWriteFrame
    intro c hc x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals exact False.elim (by simp [Component.Covers] at hx)
  have hCallee : CalleeSavedRegistersUnchanged initial s2 := by
    intro register hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
    · change s2.GPR[gprIndex (3 : BitVec 5)] = initial.GPR[gprIndex (3 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 3) (by simp) rfl
    · change s2.GPR[gprIndex (5 : BitVec 5)] = initial.GPR[gprIndex (5 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 5) (by simp) rfl
    · change s2.GPR[gprIndex (12 : BitVec 5)] = initial.GPR[gprIndex (12 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 12) (by simp) rfl
    · change s2.GPR[gprIndex (13 : BitVec 5)] = initial.GPR[gprIndex (13 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 13) (by simp) rfl
    · change s2.GPR[gprIndex (14 : BitVec 5)] = initial.GPR[gprIndex (14 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 14) (by simp) rfl
    · change s2.GPR[gprIndex (15 : BitVec 5)] = initial.GPR[gprIndex (15 : BitVec 5)]
      simpa only [Component.Agrees] using hAgree.agree (.reg 15) (by simp) rfl
  have hDirection : DirectionFlagUnset s2 :=
    e2.agrees.directionFlagClear (by simp [jccEffect, branchEffect, Effect.components]) (e1.agrees.directionFlagClear (by simp [testR8Imm8Effect, Effect.components])
      (e0.agrees.directionFlagClear (by simp) hCall.directionFlagUnset))
  have hStatus : s2.regValue .rax = BitVec.setWidth 64 invalidLengthStatus := by
    have hw := e0.writes
    change s0.regValue .rax = BitVec.setWidth 64 (1#32) at hw
    have hrax : s2.regValue .rax = s0.regValue .rax :=
      (e1.agrees.trans e2.agrees).read (r := 0) (n := 64)
        (by simp [jccEffect, branchEffect, testR8Imm8Effect, Effect.components])
    rw [hrax, hw]
    rfl
  refine ⟨s2, h0.trans (h1.trans h2), hr2, hc2, (by simpa [jccEffect, branchEffect, branchTarget, hp1, hCond] using e2.rip), hAgree, hFrame, hCallee,
    hDirection, hStatus⟩

theorem decoded_len_ret_finish [bindings : Machine.Bindings]
    {initial phase : RamState} {byteLength fuel : Nat} {lengthWritten : Prop}
    {changes : List Component} {regions : Vector MemoryRegion n}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidLengthCall base16ctDecodedLen initial byteLength lengthWritten)
    (hAdvances : Advances (returnBoundary initial) fuel initial phase)
    (hReady : ReadyToStep phase)
    (hCode : CodeIn programImage phase)
    (hRip : phase.RIP = 0x100013)
    (hAgree : AgreesExcept changes initial phase)
    (hStackPtr : stackPtr phase = stackPtr initial)
    (hReturnBytes : ∀ i < 8, phase.external[stackPtr initial + BitVec.ofNat 64 i]? =
      initial.external[stackPtr initial + BitVec.ofNat 64 i]?)
    (hFrame : MemoryWriteFrame initial phase regions)
    (hCallee : CalleeSavedRegistersUnchanged initial phase)
    (hDirection : DirectionFlagUnset phase) :
    ∃ (least : Nat) (final : RamState),
      UniqueExecution initial least final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧
      DirectionFlagUnset final ∧
      MemoryWriteFrame initial final regions ∧
      AgreesExcept [.reg 4, .rip] phase final := by
  have hCodeRet : CodeIn (codeRange (0x100013 : BitVec 64) [0xc3]) phase := by
    have h := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.program_text_slice
      hCode 0x13 1 (by decide +kernel)
    have hb : Extracted.textBytes.toListFrom 0x13 1 = [0xc3] := by
      decide +kernel
    simpa only [hb,
      show Extracted.textAddress + BitVec.ofNat 64 0x13 = (0x100013 : BitVec 64) by
        decide +kernel] using h
  have hTop : stackTop phase = (returnBoundary initial).rip := by
    unfold stackTop returnBoundary
    rw [hStackPtr]
    apply memLoad_congr
    intro i hi
    change (phase.external[stackPtr initial + BitVec.ofNat 64 i]?).getD 0 =
      (initial.external[stackPtr initial + BitVec.ofNat 64 i]?).getD 0
    rw [hReturnBytes i hi]
  have hPre : RetPre 0x100013 phase := by
    have hRead : MemReadable phase (stackPtr phase) 8 := by
      have hInitial := Base16ct.Proofs.Copied.Md5.Proofs.stack_return_readable hCall.stack
      rw [hStackPtr]
      refine ⟨hInitial.low, ?_⟩
      intro i hi
      rw [hReturnBytes i hi]
      exact hInitial.mem i hi
    refine ⟨⟨hRip, hRead⟩, ?_⟩
    rw [hTop]
    have hBoundary := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.validReturnAddress_boundary
      hCall.returnAddress
    simpa [userAddressLimit] using hBoundary.1
  have hStackReturn : stackPtr phase + 8#64 = (returnBoundary initial).rsp := by
    rw [hStackPtr]
    rfl
  obtain ⟨final, hReturn, hReadyFinal, hAgreeFinal⟩ :=
    decoded_len_ret_step hReady hCodeRet hPre hTop hStackReturn
  have hRun : Returns (returnBoundary initial) (fuel + 1) initial final :=
    hAdvances.returns hReturn
  have hEntry := Base16ct.Proofs.Base16ctMixedDecodeCorrect.Machine.entryReady
    hBindings hMachine hCall.programLoaded
  have hNear := nearReturn64Boundary_eq initial hEntry.ready.dataReady hEntry.ready.cpu.ss
    (Base16ct.Proofs.Copied.Md5.Proofs.stack_return_readable hCall.stack)
  obtain ⟨least, hUnique⟩ := hRun.unique_of_boundary hNear
  have hSsePhase : SupportedSSE bindings.processor phase :=
    SupportedSSE.of_agreesExcept hAgree hMachine.sse
  have hSupported : SupportedIntegerMachineState bindings.processor final :=
    Base16ct.Proofs.Base16ctUpperEncodeCorrect.supportedIntegerMachineState_of_ready
      hReadyFinal hAgreeFinal hSsePhase
  have hControls : SameControls initial final :=
    SameControls.of_fixedPart (hAgreeFinal.rest.trans hAgree.rest)
  have hBindingsFinal : MachineRamUnitStrideDecodable bindings final := by
    refine ⟨smrrUnblocked_of_sameControls hControls hBindings.smrr,
      writeBackMemoryType_of_sameControls hControls hBindings.memoryType,
      hBindings.stringStride, ?_⟩
    obtain ⟨enabled, henabled⟩ := hBindings.leadingZeroCount
    exact ⟨enabled, reportsCPUFeature_of_sameControls hControls henabled⟩
  have hCalleeRet : CalleeSavedRegistersUnchanged phase final := by
    intro register hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
    · change final.GPR[gprIndex (3 : BitVec 5)] = phase.GPR[gprIndex (3 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 3) (by simp) rfl
    · change final.GPR[gprIndex (5 : BitVec 5)] = phase.GPR[gprIndex (5 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 5) (by simp) rfl
    · change final.GPR[gprIndex (12 : BitVec 5)] = phase.GPR[gprIndex (12 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 12) (by simp) rfl
    · change final.GPR[gprIndex (13 : BitVec 5)] = phase.GPR[gprIndex (13 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 13) (by simp) rfl
    · change final.GPR[gprIndex (14 : BitVec 5)] = phase.GPR[gprIndex (14 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 14) (by simp) rfl
    · change final.GPR[gprIndex (15 : BitVec 5)] = phase.GPR[gprIndex (15 : BitVec 5)]
      simpa only [Component.Agrees] using hAgreeFinal.agree (.reg 15) (by simp) rfl
  have hCalleeFinal : CalleeSavedRegistersUnchanged initial final := by
    intro register hreg
    exact (hCalleeRet register hreg).trans (hCallee register hreg)
  have hDirectionFinal : DirectionFlagUnset final :=
    hAgreeFinal.directionFlagClear (by simp) hDirection
  have hFrameRet : MemoryWriteFrame phase final regions := by
    apply hAgreeFinal.memoryWriteFrame
    intro c hc x hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact False.elim (by simp [Component.Covers] at hcov)
  have hFrameFinal := memoryWriteFrame_trans hFrame hFrameRet
  exact ⟨least, final, hUnique, hSupported, hBindingsFinal, hCalleeFinal, hDirectionFinal,
    hFrameFinal, hAgreeFinal⟩

end Base16ct.Proofs.Common
