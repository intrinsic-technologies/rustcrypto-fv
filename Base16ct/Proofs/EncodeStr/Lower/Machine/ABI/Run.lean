import Base16ct.Proofs.EncodeStr.Lower.Machine.ABI.Prologue
import Base16ct.Proofs.EncodeStr.Lower.Machine.ABI.Epilogue
import Base16ct.Proofs.Common.Output
import Base16ct.Proofs.EncodeStr.Lower.Machine.Geometry
import Base16ct.Proofs.EncodeStr.Lower.Machine.Preservation

namespace Base16ct.Proofs.EncodeStr.Lower

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem lower_prologue [Bindings] {initial : RamState} {input : List UInt8}
    {capacity : Nat} (hInitial : MachineInvariant initial (if 2 * input.length ≤ capacity then 2 * input.length else 0) initial)
    (hCall : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (hOutside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ s, Advances (returnBoundary initial) 7 initial s ∧
      SubroutinePre initial input capacity s := by
  obtain ⟨s, ha, hr, _, he⟩ := lower_prologue_run hInitial.ready hInitial.code hCall.entry
    (validCall_stack_sub_writable8 hCall (by decide) (by decide))
    (stack_avoids_program hCall (by decide) (by decide))
    (validCall_stack_sub_writable8 hCall (by decide) (by decide))
    (stack_avoids_program hCall (by decide) (by decide)) hOutside
  have hm : MachineInvariant initial (if 2 * input.length ≤ capacity then 2 * input.length else 0) s := by
    apply hInitial.of_agreesExcept he.agrees hr
      (hd := by simp [lowerPrologueEffect, Effect.components])
    · simp [PreservesCalleeSaved, lowerPrologueEffect, Effect.components]
    · intro c hc address hcov
      simp only [lowerPrologueEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        try exact hcov.elim
      all_goals exact ⟨_, by simp [writableRegions],
        stack_memory_contains hCall (by decide) (by decide) hcov⟩
    · intro c hc a b hab hcov
      simp only [lowerPrologueEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        try exact hcov
      all_goals obtain ⟨i, hi, heq⟩ := hcov
      all_goals first
        | exact stack_avoids_program hCall (offset := 32) (by decide) (by decide) i hi
            (heq ▸ (show InProgram a from ⟨b, hab⟩))
        | exact stack_avoids_program hCall (offset := 8) (by decide) (by decide) i hi
            (heq ▸ (show InProgram a from ⟨b, hab⟩))
    · intro i hi c hc hcov
      simp only [lowerPrologueEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        try exact hcov
      all_goals obtain ⟨j, hj, heq⟩ := hcov
      all_goals first
        | exact stack_return_apart hCall (offset := 32) (by decide) (by decide) j hj i hi heq.symm
        | exact stack_return_apart hCall (offset := 8) (by decide) (by decide) j hj i hi heq.symm
  have hlen : (Operand.reg 6 : Operand 64).read initial = BitVec.ofNat 64 input.length := by
    have hh := hCall.lengthArgumentMatchesInput
    change (initial.regValue .rsi).toNat = input.toByteArray.size at hh
    rw [List.size_toByteArray] at hh
    have hb := congrArg (BitVec.ofNat 64) hh
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
    exact (show (Operand.reg 6 : Operand 64).read initial = initial.regValue .rsi from rfl).trans hb
  have hcap : (Operand.reg 8 : Operand 64).read initial = BitVec.ofNat 64 capacity := by
    have hh := hCall.capacityArgumentMatchesOutput
    change (initial.regValue .r8).toNat = capacity at hh
    have hb := congrArg (BitVec.ofNat 64) hh
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
    exact (show (Operand.reg 8 : Operand 64).read initial = initial.regValue .r8 from rfl).trans hb
  refine ⟨s, ha, hm, he.rip, he.writes.1, he.writes.2.2.2.2.1,
    he.writes.2.2.2.1, he.writes.2.2.1.trans hlen,
    ?_, ?_, he.writes.2.2.2.2.2.1, he.writes.2.2.2.2.2.2, he.writes.2.1⟩
  · exact he.agrees.read (r := 1) (n := 64) (by simp [lowerPrologueEffect, Effect.components])
  · exact (he.agrees.read (r := 8) (n := 64)
      (by simp [lowerPrologueEffect, Effect.components])).trans hcap

theorem lower_abi_final_state [bindings : Bindings] {initial s t : RamState}
    {written : Nat} {cs : List Component}
    (hState : MachineInvariant initial written s)
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hReady : ReadyToStep t) (hAgree : AgreesExcept cs s t)
    (hSaved : PreservesCalleeSaved cs) (hDf : Component.df ∉ cs)
    (hRbx : t.regValue .rbx = initial.regValue .rbx) :
    SupportedIntegerMachineState bindings.processor t ∧
      MachineRamUnitStrideDecodable bindings t ∧
      CalleeSavedRegistersUnchanged initial t ∧ DirectionFlagUnset t := by
  refine ⟨⟨hReady.cpu, SupportedSSE.of_agreesExcept hAgree hState.sse,
    hReady.memory, hReady.ready⟩,
    Base16ct.Proofs.Copied.Md5.Proofs.machineRamUnitStrideDecodable_of_ready hReady hBindings.stringStride,
    ?_, hAgree.directionFlagClear hDf hState.df⟩
  intro r hr
  rcases List.mem_cons.mp hr with rfl | hr
  · exact hRbx
  · exact (calleeSaved_of_agreesExcept hAgree hSaved r hr).trans (hState.calleeSaved r hr)

theorem lower_epilogue [bindings : Bindings] {initial s : RamState} {input : List UInt8}
    {capacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hCall : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length)
      (2 * input.length ≤ capacity))
    (hPost : SubroutinePost initial input capacity s)
    (hLow : (returnBoundary initial).rip.toNat < userAddressLimit)
    (hOutside : ¬ InProgram (returnBoundary initial).rip) :
    ∃ fuel t, Returns (returnBoundary initial) fuel s t ∧
      SupportedIntegerMachineState bindings.processor t ∧
      MachineRamUnitStrideDecodable bindings t ∧
      CalleeSavedRegistersUnchanged initial t ∧ DirectionFlagUnset t ∧
      if 2 * input.length ≤ capacity then
        SuccessfulStatus t ∧ MemoryWriteFrame initial t
          #v[outputRegion initial (2 * input.length), lengthOutputRegion initial,
            Stack.region initial base16ctLowerEncodeStr.minStackBytes] ∧
        readOutput initial t (2 * input.length) = .ok (encodedBytes input).toByteArray ∧
        readLengthOutput initial t = .ok (BitVec.ofNat 64 (2 * input.length))
      else FailureStatus t invalidLengthStatus ∧ MemoryWriteFrame initial t
        #v[Stack.region initial base16ctLowerEncodeStr.minStackBytes] := by
  have hdisc : MemReadable s (stackPtr s) 8 := by
    rw [hPost.rsp]
    exact stack_readable hCall hPost.toMachineInvariant (by decide) (by decide)
  obtain ⟨u, ha, hu, hcu, hip, hau⟩ :=
    lowerEncodeAbiBranch hPost.ready hPost.code hPost.rip hdisc hOutside
  have hmu : u.external = s.external := hau.external (by simp [Component.Covers])
  have huState := hPost.toMachineInvariant.of_agreesExcept_noMem hau hu
    (by simp [PreservesCalleeSaved]) (by simp [Component.isMem])
  have hspu : stackPtr u = stackPtr initial - 24 :=
    (hau.read (n := 64) (r := 4) (by simp)).trans hPost.rsp
  have hbxu : (Operand.mem (stackPtr initial - 8) : Operand 64).read u =
      initial.regValue .rbx := by
    simpa only [Operand.read, hmu] using hPost.savedRbx
  have hptr : u.regValue .rbx = initial.regValue .rdx :=
    (hau.read (n := 64) (r := 3) (by simp)).trans hPost.lengthPointer
  have hread (offset len : Nat) (hlo : offset ≤ 32) (hhi : len ≤ offset + 8) :
      MemReadable u (stackPtr initial - BitVec.ofNat 64 offset) len :=
    stack_readable hCall huState hlo hhi
  have hret : MemReadable u (stackPtr initial) 8 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using hread 0 8 (by decide) (by decide)
  by_cases hfit : 2 * input.length ≤ capacity
  · have result := hPost.result
    rw [ite_eq_left hfit] at result
    have hnonzero : initial.regValue .rcx ≠ 0 := by
      intro hz
      apply hCall.outputInMemory.1
      change (initial.regValue .rcx).toNat = 0
      rw [hz]
      rfl
    have hipu : u.RIP = 0x10019d := by
      rw [hPost.rsp, result.1, ite_eq_right hnonzero] at hip
      exact hip
    have hpayload : (Operand.mem (stackPtr initial - 16) : Operand 64).read u =
        BitVec.ofNat 64 (2 * input.length) := by
      simpa only [Operand.read, hmu] using result.2.1
    obtain ⟨t, htail, ht, hag, hrax, hrbx, hlength⟩ := lowerEncodeAbiSuccess
      (BitVec.ofNat 64 (2 * input.length)) hu hcu hipu hspu
      (hread 16 8 (by decide) (by decide)) hpayload
      (by rw [hptr]; exact length_output_writable hCall huState hfit)
      (by rw [hptr]; exact length_output_avoids_program hCall hfit)
      (by rw [hptr]; exact length_output_apart_stack hCall hfit (by decide) (by decide))
      (by rw [hptr]; simpa only [BitVec.sub_zero] using
        length_output_apart_stack hCall hfit (offset := 0) (len := 8) (by decide) (by decide))
      (hread 8 8 (by decide) (by decide)) hbxu hret huState.outerReturn hLow hOutside
    rw [hptr] at hag hlength
    obtain ⟨hsup, hdec, hsaved, hdf⟩ := lower_abi_final_state huState hBindings ht hag
      (by simp [PreservesCalleeSaved]) (by simp) hrbx
    refine ⟨8, t, ha.returns htail, hsup, hdec, hsaved, hdf, ?_⟩
    rw [ite_eq_left hfit]
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (t.regValue .rax).setWidth 32 = 0
      rw [hrax]
      rfl
    · apply memoryWriteFrame_trans (t := u)
      · intro a outside
        apply huState.memoryFrame a
        intro region hregion
        simp only [writableRegions, ite_eq_left hfit] at hregion
        simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
          or_false] at hregion
        rcases hregion with rfl | rfl <;> exact outside _ (by simp)
      · apply hag.memoryWriteFrame
        intro c hc a hcover
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcover.elim
        exact ⟨lengthOutputRegion initial, by simp, length_output_contains hCall hfit hcover⟩
    · have hout : readOutput initial t (2 * input.length) = readOutput initial u (2 * input.length) := by
        apply Base16ct.Proofs.readOutput_congr_prefix
        intro j hj
        apply hag.byte
        intro c hc hcover
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcover
        obtain ⟨i, hi, heq⟩ := hcover
        have hap := length_output_apart_output hCall hfit (offset := 0)
          (len := 2 * input.length) (by omega)
        simp only [BitVec.add_zero] at hap
        exact hap i hi j hj heq.symm
      rw [hout]
      simpa only [readOutput, hmu] using result.2.2
    · have allocated := length_output_writable hCall huState hfit
      have hb := Bytes.of_memLoad (n := 64)
        (fun i hi ↦ hag.grow _ (allocated.bytes i hi))
      have hv := hb.loadBytes64
      change loadBytes t.external (initial.regValue .rdx) 8 =
        .ok ((Operand.mem (initial.regValue .rdx) : Operand 64).read t) at hv
      rw [hlength] at hv
      simpa only [readLengthOutput, lengthOutputRegion, registerRegion,
        BitVec.ofNat_toNat, BitVec.setWidth_eq] using hv
  · have result := hPost.result
    rw [ite_eq_right hfit] at result
    have hipu : u.RIP = 0x1001ad := by
      rw [hPost.rsp, result.1, ite_eq_left rfl] at hip
      exact hip
    have hpayload : (Operand.mem (stackPtr initial - 16) : Operand 8).read u = 1 := by
      simpa only [Operand.read, hmu] using result.2
    obtain ⟨t, htail, ht, hag, hrax, hrbx⟩ := lowerEncodeAbiFailure hu hcu hipu hspu
      (hread 16 1 (by decide) (by decide)) hpayload
      (hread 8 8 (by decide) (by decide)) hbxu hret huState.outerReturn hLow hOutside
    obtain ⟨hsup, hdec, hsaved, hdf⟩ := lower_abi_final_state huState hBindings ht hag
      (by simp [PreservesCalleeSaved]) (by simp) hrbx
    refine ⟨8, t, ha.returns htail, hsup, hdec, hsaved, hdf, ?_⟩
    rw [ite_eq_right hfit]
    refine ⟨?_, ?_⟩
    · change (t.regValue .rax).setWidth 32 = invalidLengthStatus
      rw [hrax]
      rfl
    ·
      have hm := hag.external (by simp [Component.Covers])
      intro a outside
      rw [hm]
      apply huState.memoryFrame a
      intro region hregion hcontains
      simp only [writableRegions, ite_eq_right hfit] at hregion
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil,
        or_false] at hregion
      rcases hregion with rfl | rfl
      · have : False := by
          change (initial.regValue .rcx).toNat ≤ a.toNat ∧
            a.toNat < (initial.regValue .rcx).toNat + 0 at hcontains
          omega
        exact this
      · exact outside _ (by simp) hcontains
theorem lower_abi_execute [bindings : Bindings] {initial : RamState} {input : List UInt8}
    {capacity : Nat}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hInitial : MachineInvariant initial (if 2 * input.length ≤ capacity then 2 * input.length else 0) initial)
    (hCall : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length)
      (2 * input.length ≤ capacity))
    (hLow : (returnBoundary initial).rip.toNat < userAddressLimit)
    (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (hSub : ∀ s, SubroutinePre initial input capacity s →
      ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
        SubroutinePost initial input capacity t) :
    ∃ fuel t, Returns (returnBoundary initial) fuel initial t ∧
      SupportedIntegerMachineState bindings.processor t ∧
      MachineRamUnitStrideDecodable bindings t ∧
      CalleeSavedRegistersUnchanged initial t ∧ DirectionFlagUnset t ∧
      if 2 * input.length ≤ capacity then
        SuccessfulStatus t ∧ MemoryWriteFrame initial t
          #v[outputRegion initial (2 * input.length), lengthOutputRegion initial,
            Stack.region initial base16ctLowerEncodeStr.minStackBytes] ∧
        readOutput initial t (2 * input.length) = .ok (encodedBytes input).toByteArray ∧
        readLengthOutput initial t = .ok (BitVec.ofNat 64 (2 * input.length))
      else FailureStatus t invalidLengthStatus ∧ MemoryWriteFrame initial t
        #v[Stack.region initial base16ctLowerEncodeStr.minStackBytes] := by
  obtain ⟨s, hp, hs⟩ := lower_prologue hInitial hCall hOutside
  obtain ⟨n, u, hc, hu⟩ := hSub s hs
  obtain ⟨m, t, hr, ht⟩ := lower_epilogue hBindings hCall hu hLow hOutside
  exact ⟨7 + (n + m), t, hp.returns (hc.returns hr), ht⟩

end Base16ct.Proofs.EncodeStr.Lower
